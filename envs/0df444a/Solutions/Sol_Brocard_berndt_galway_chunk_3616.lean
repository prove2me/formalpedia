-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3616
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:11:04.768922+00:00
-- url     : https://prove2.me/submissions/f2e73079-4d1b-4dfa-99a3-a31ae9c3735a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 650179856 ≤ n < 650359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 650181106 1250 650179856 650179879
    0x1e140d0f05100f24030f05100602060c0c1216051b0a170607031a0d140105060109030c0b0a091802090306160c110f040203040317060906060318010e031908011706010302 74
    0x250302911a118100b100103207047c080101d01e40940c5100340545400340d003118995034403c0070340407051043d030b01d000340300798032070038207481c862940100801145003101c0654619821603582c680ca0081e01109040603040416035074151802e1020340c030002000d03912740b00118204030100d00c40d02e80101405440030140c0b15401d86d42c00c00440c440d40c800d6070102601c1050115403904207034aa032042100404115420300000c1540780d8820780142082e21380061000d0401441c003082c10302a984211240f00a010001c0400140d584c004101d800150340f54280c09a96888074408040c00e10000404003904c10501034115031510760300510840da16030340700918108001c808000180f5003481452a954420300000c104410564006034a80c90881c0021450406445000811861000843e6186c0d00510280300180342502d42502c100b0821107030400000d40c0d103042075212401d590002d4a0f0244040707001c00054030381580b1010083c01402c4241c4411517070702c0005030346911894103200c00380c854000b40030f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 650182356 1250 650181106 650181179
    0x91011160b091314150f15040b07030c050d0801080d080c1e1228051905220605070e010914040902060409050a1b1e140d0f05100f 57
    0x101042c42a5404c06207416407170543c480f050040d28200303440e0b01a07500e0000400076400c00d0b0300214203040c071b0404060305240c105660340300d5940242c003043d03081004d480c0c05132001c1503052114920f0280d195950112642c10b080c00a4a024102841d0104000340d03c01006800e100c6141a1011080c2800760008c034001c410810700100e01661940b414002000400c1c05000e04010704240240e5240c401c107010340d807a42c941c0c42e404981d800c45070500d40c1e000c0032204080d01d001940c0150f502aa010240c40d0310805580c401c3c40c280140780500b107134420303134034814800d0b80358105400350301d40d003400d00e060781c02c650601622544540d05039407406c0c0030396290582c0c04215a2411700b0b0b074020700481002004145032261a8601a0415032100c02c83c2022910070500c0c041e00c00e0030b1810b035511184801610322000700303008555450f150034000e22100c0c41480804003d203110b018a8450000b0305401090b24246601200c07030503181c1e58405949a4200b5604219440c684140003041c018000e00e111070314180d07980d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 650183606 1250 650182356 650182361
    0x90d0806010f0908030408030702030708160501050906041d15030d27051302070c050103091a0a06081002130806010501020d1209060606031a09010b0904020f091011160b0913 76
    0x400100c2d13640000314010410b90740010161260f40c2c001c0342100c40c2d1541d00e0031500d0301c401601c1800454200211403e12055010300010310080d00040d01051829580e00400a96009002c1c0e400100c602900103000303030004000d80140880a003200035000b403280201019000c214030b01105007024101406066020f00e28000c640000d0002810b042d034a01a01c024110096004540889030100013803404100e65120703215001c40300c0d9001c42e04050946145012a680480040c8903d0550707480c0c690114070002d0070311803401282c66001c1c002d60bc0380b020307091410031146c0741d0300a445194000300c010041b40c1c2c0c2c0051a100001d0070350400350025552b20202c00d0140c060b9084c00b8010a0920f0340c0090003540c90740c0414909944000415a010a6042004030070402031140c09201602403000703007480d01c1e180c3c1c001c00741540e0040c0c9c038501e80a003000101e0f140740154172002d8089044a240001041014070135103042c6c40803132031032200e61418407180240500441684034040c0183d075090030441c5d20140d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 650184856 1250 650183606 650183609
    0x618050607020d032f0d060b040f05031b01050a05132606070806150c1504080301080d03020a02030a0819050a0204051021090206070c0303020303060108090d0806010f09 74
    0x2064800c145401040a075403804150701100011340303010803040440500e48000c840140c440d41914040f0581c0300c010321120340201021071030295640e4400100b00401d180144010901c1c018910b00142c03030b103420181044160300b2040300b01c038441004110160b9003c4101c8100e00c2032800d065480d100c54407615002c0181c560041d0024018614511241400140308030105a000808075010354ad121501121094816124540c200d41503601c600c680c01040c0018000f10720602046611625441c402004d00746000c0d201980d04c01d5000006204c0e494013032090359640c01803418151b240c0640c0d4400250750b4440c0034411003c202c440d1004c030700c40f01c4114081d6594068042014070035801e1681c0d50704c00075401481000c0c0305201520a001111b0b0043c40c8a03010300314001a07030f5640d6000440322031702901506000320780c001c1e0101b10010001d0a03401c04030018500960055449141402c00541051000351001e800c640c8222010441c085d0300864203a8410020310f050744024030599030a540340c200e223 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 650186106 1250 650184856 650184863
    0x2c0f0606160f030201050a0f0c020c01050a02010e0307110f150405060315030f0708160503060f0a09050304060804020a211113181109070503151f020607080109020a020a0618 76
    0x110b0301d2040a069054004d41e0103001903030810008441d5021407501203c12541d1035402580004c1d407004005c0d80140050895001c3c2e6000205400d04285041c038215801000c0840310a00c5001d401851410303d01c0071105401000d44800e808500140748500e240c2c004e911a1a120b00d00010001e00c41c855041c40581400340e0180c1110f030a24100c0b10082d46070f0003140580c0b401485004485004000c0110600701140e5020b0050704264135210350906942000801d80c00c032486e19003424000180080004000034019956510550b007010701c10840506000d034415203540701c58000c901007002d0b4003100300126503806413500c15034002c0d10011581c00a1008007000344103240034041c0544c0c000362141034040f0391003192040c0f0940306e00c101300140d08105550000001d0703002c1c400500c4054100c4100c11060380014184204234021204442c00401702951841c0103822070014003c0043d0021040ca0140114110550a1040000c0c0c000c1d695060004081d0009484950501005c2c2c440e10000140640 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 650187356 1250 650186106 650186123
    0x30906021b1006050d1b0b13080105060a14010c0c0f080304211a1b03161b11060a03110a03050708090a1205070312062c0f060616 57
    0x345480855030150307441c4200a03040c02800085a12035456206420940300d004000c008000219220b5000c01c000d4064a080d0b50f4102520204003000b510010300341c1d4000820380103000f075080842660950b000680038900840010f103040c0a1580705088020798090b080c80c001d02d41d48154104408035518580c4100d500001c4d919002ca090f0718048020404e90b00120404401c20790758111011031070135915000f82905003400e00c5540c4020a400e450340c0c0040e108000b001c604e405450b08040b4a07802620030740c10043d51900c02045240e0461009408210390b074030104150100e50303c49030485240c0700c0d41c042c8144000100880300c50700951000c1940c000c1d8103082a2104602c10018000700030548412010540441c00100e600d036000400c0c00000d940078240000511414009407115045140d013241032010800d42080c4041b22885280000c0c03648010100900e409142d415072080d0a000701508804118010072130400d40000390030307800220507a142503031441210b14221581400000082c41c010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 650188606 1250 650187356 650187367
    0xc0b0a021f1a0f0f0d0f06110d180c030b070309050a0c0501090e1905060609030604060b0f0301291203030c040603110a020a0318051005130e060307090c03090602 71
    0x1c5544410286440e40c0100007201c421681041038a002d51036055911110322a000c844038240a81100380c014403c0100c0c003518422950303603006031407000403003140c00d00010034010800c0c1e000b802340e115084c03100448200154029102ca12a071203240c000902100f5080d40403a202600c2680030805030b03604001038580785009440d200c00000b125124240c0001d0041c0d00116500410841450055004080c40854528100d0045002d84ac00a2035075500541c20b0148000584013840b03403910980c820000025040030000030040034050482c1d0841c06a0324003110500348941d2102410a242034000e2202d40707420b1010f002500030803003d0034444880c08003105000a40d00c03040c0160040e904581c4007880b5074001000d411042d40204030b068001a480074260f000031074003400301002130361a00c0d0083c401481e16040880c0404890320400b20010300002800c40d0080141da2030302c00030700b804d480d130324040c1d04200300069516200c0f4040c2004059844040d04840d50180e48a84010f40d8010030564980 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 650189856 1250 650188606 650188663
    0x1302060a2a0813050f0112050402060403020604091d010b030c120c0301110c1b0d0f030e10050405011b0203060105190812030402180405120906040e0f1906030c0b0a02 73
    0x260443e949001c040f4181030004a428506019001a42c100607520055007428201141010704070250050303030481c50401000c00541c031400014000352000c0403002c01c0c2c500a50481b4610030000c0740381e0042c5a45040070f801111b43d40446d03407850543c4d085880196a400200c0001d080280250085c1e03455803034150080c014641610280501460500594140030107111001e10340302c1401005550203540409800d0004d051791180700d0074070b402445c020740c1060680303020072546150140103078003041000c0760810440d1f90041904025580001149030120010f50100c1c3d600c10040c00740c00c1c41810300040e020030728a0300004a13401404000100c3d05d00700300c4818410302643c03050714164000c0710484240194103044401d000e01480d8068014482c8200e0f016004130180c100002c0c040e481007040100088452000355024021140540c07403510f035060855101c2d010b01c1c10103041101d8141000b8007000454560394620045488880c1100c5c0e8a00314110120306090207083c55400c540070200018022 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 650191106 1250 650189856 650189873
    0x512060609070c0c15030e01110904290909030f0a091401030c09091503210806090103050604062703080405100e060a0e071505121302060a2a 62
    0x22002038410098030b440d485011195585840c0000e480301050320f108200e41d0380d0b609900700760161301e8a40054480604034050f82034500c0c080c04030304249408100c1a0076840d0a1061440030b0f129480c43c044100c40044440c007403038280e01c040d00e05c90321451000822800d428401c42d9100564140c030107686e0b03a00403034090108815405910480118180c800109500034440c590b074449145d1500409940350401000241814032190f0600c15001100000080c907254481c0c0b160319800b4101031000342d01d00d04010400b11008020324400c800d00301c0104081507000c1143da07042900710f203003c58100c40c00050004640140b1040c65000407100070701c2d405040c3c2c4070180500807485001564031f8129003040762000c1da0944240c2c02003a4000c0300c00306040500c0c9520403250744a481c400c1d1140703280e442109440181c080c8004c00045800002c0b10824103c4224a8035405012010491403e5050b60041210b038010383c201a806c0c401144110b0805104242140801912103a49100c0004262a22441 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 650192356 1250 650191106 650191111
    0x20c060a1701091b1d0d2102071502010b09070c06090f050c030606040204051c02040e01060f060905100507031b0c1215050603060f1009050106212c0106051206 70
    0x940701200c03c0040c03818407800c4940005c41e90525002075071940c080c100581c60424410842d09441c030400401a113550031400c81035490a0b5801400c499403074020b031044030b441420310400c210391400312307503042ca0369400e09110b41207a4140340c5200c07071070082e00e0440c0041c1032002000c0c01440c005070040e41000000596404000002c0d4150341e41c42d2110300511083e4040c2d409040c2d442402000c5540181800c2c0c0d203400d0f1401d0000f03101040500b450382c0c00c0c0c3c0c00c54405400000745101075010030302050b6041440c0d0703001420160b4821490b011100001131240c0102d40780281007015042046071408500c072001d60006d60001d40d4426030036038032050080000c243c008121029001d003c0c2c56044071541d40302d040c0c42500c000c1c0c041c12040d5100d174500055814005d1800100c01c85010700032908120b244100c40c0601415191560032091000034110441000541602c4042c01c100c204225070901c02d25862109070024a200310842c403241842d0b0141c4030b1900802d0304140c034075800c04101c000001b41e0341d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 650193606 1250 650192356 650192381
    0x12120a03060b1b0c010306140409060b1e10080417090303070615061b020306060120010509030307110303060a0311040e0a080904060602030c0316030c0b04050a050c030a03020c060a170109 82
    0x4007139074040b00045d010743d4000d105181c040780001d640907a0b60b05003030b008188102d20500300082c0c031031084000603900c0d0364414100c0280f024501448002810a480c80c0341c3e8010b80741c1410015071403d9650701da40c102400f001c0000784100480c442c2c0c450345041040e40e81c0039500c00000e006801410590b4800b00b010340c41441c000409005120f60115500300842040c16005005400341d030b5a1b0000544024500030320280540138032950154044000b80710f124013900d2890041c0d55a400c06000c020004a920b0b80a01026042001071081d16a02c01d4040000c0340e5120100500d0700c4a4440003074000c000301c8050f8042e034060308a10204104420740200b903d42001c0b1004c2100c540c030f42900b03d03580d0280c4103428016038010444541020b405210b9001c0340344c864581416005940d81d24581d0340710042e10100c07542d90001c50b0100410405100e484051746003a0000e111114064038001d507500c00240307096008020016600c0803031446035040b0031221302518030900b215655894103c00600039020a031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 650194856 1250 650193606 650193613
    0xc03120c030f0c030603080d021806131401111504020301112a030a17060d0c080d021015050105072d15020f0d0e100e070602010b12120a03060b1b 64
    0x15100f031303000f0f200303100c03e982d00120418100340b02404510000d43c07042c448501200004503c1180705d98070f85006014905a030456584203514045420402c1c81280400c00c3c1408070b4065915241c0c0d20001d811007001d400034064842036215400400d00401000790203402040300003441400300c1c000d20154050341a1400c0010940007a0303101072130f4a0307000f00040400000d1190b11401d0030003f03078500e5150810001009204090840e541d40c82d407808142d444614950040d0001c14607458040c003100700c00302c040d000c0c207000c025440310711200c080c0480e0144905006c804900d01c4284901c000011510310408641020342015000002c0070381010640226030031504212410045407241c000d85170b0094604250380e08225149400c00090310447c60060601d00c161042d49404034414084e80b5078a4011030040d041d2503040c004000d00b0b48220700f0195029000c8418085800b110014031543c484120030a920380326002c5900840240038103034000c0741700e40700102e138068240c0101c00306404d803e5074202c00c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 650196106 1250 650194856 650194871
    0x3060e0703050415180308100b0a080405160909020108090c0901180e01180c08070f17010e060406150801060302130e0703051204061106090d0f020a0c030507140102060f01060c03120c030f 82
    0x8a2300803440300d010380e0200600c00c0c040b480e00f45008648091f041031244003030307418080404900d6030718001c0c598010a0385c140c60311010419940c0004220b0341061680380644800415080820380121062180c9a450f580d508801c07413090380d81d9440780710148101002072103a0a1001000190764200000568101540e1000007074942c4c400119041103078100d01000c1d40c5036140c211001215250414410f182e5500c82d40c0385402d0341c406012461080784640d100044048051004412400158000110a82c90b00c41d041c805a03031244100c0130070340c580850104940a0703114429040681d00d51004266100300040740c111180341e01d002d4403c0c3c0c0c11355621945180307030a4240740d680701c00580b102040c907040200103520031449024150440c607401d00443d260760626584680002509600540d401e400c0b00a0911144d03c0c203c14070500d101d024802800c030b038180100395000380f40040c40b8500a1056421050007014040d1003d013031808101c0004101d2131041040c0a13010741003850840c085145002e44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 650197356 1250 650196106 650196121
    0x4030f020f060c0601061b12020706200316061d010e01051326090a0303050409050f250201110c010905070f0812160606080d0e0103060e0703050415180308 68
    0x3c1d00c00398001c3c00000c254592801c1c0c8191100b25030407804400030305413009a40041540a078010071550764640c000c20300c41d4070388840280304101ca0326689006682d00744043c01d210350008261140003004046001314400c02e031a04c1d01c006c01844004030700c120380890501090f110304ad030041d503444042400034403441d610001101d1400b61640001000c425049035580c0c0340c0400752200303801120041c22901c0c81c1085040004d025041c481d40102d000960003c0e00b48540241c0e40500d90300411300c20b0440e821401c20742c51410b607210407000d0104809030746154031101c4501c01d400c1040d1004500c42102d0f034854242c0c0c03240c0e010348641e03001590710b845402030001340d820500850008440c1400058131412000d00034100300d030b9001082c1081c81407803104000c000b26049104480c028081d000040c102640240380c054900c1c0607210189051500c0e112081100400c1c16070308590000d1207103000a0161398078944090340345112421205514038005020313003000411034101c007010380262a401900d50340c03140e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 650198606 1250 650197356 650197369
    0x5060409080a08090f0105131a060d1401020d020304030504031110020d050d0b120106030510060b09040207060f090b0711060408041406071a150d0b060108150604030f020f 75
    0x2005240721020416040d40b1441192400c3d04402802e09071403290385401d111300c4c2034a10a4424000f280e500455000802c400c120400902040c1e01e00d10118918081000031402025540007030310000b0b12101c400c0e800305083d41160940c01c81c0350000c54507401c003401d00602d50381050208942002c80000503200a14040103070420040195000b001c04900c600001c4030150050b4140030401d640b0b403005040b0341c2c0d5816003200b01086c040303030001601d58514100240341002c0369007500201407610405100702c2095000f00e4005a00a903409179407a216450040c1c01000ba02c020300c125207103840075600402502d260751074012440c503030750880d06003149440300f07854850a6030000c0c2a104108810070256040e08424103851500038025420410039482e181342c48141c0201c00c038001c0810008100d000c2d0f18003c81c000f140310060b0f418013104040c55a410301044406401207040c0040240041c180551510034410311040240895486650f40e103044c050407e039414089104004140001c02c5ca400c025 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 650199856 1250 650198606 650198621
    0x30606170a0f02090409080d0b010c0f030c080405060d060504050a060f15020312090102040e070e0607140304090e030903070b030c0f0306062505061f0605030a020c07030b0a050604 79
    0x400c0c00409600d803500010020009a9100041c9640038001041d03155507920400704e186000309000e60345c0e21607085121084030145851181444201415103021410300184001401c1d07150821031705030309907420b14200d1409664025039100c1000144581c44144907081202110001d4900340710b01d1b115100020242c030341c50300980041d13800c0004100006018a51817a00400d4140143e81c5000107900c00c207120710a0484050030750f0781d0002801c20401944024840c0c0c414042d00d0208402c00c50380780056454442c4560103014441e41001e01d540810f020310840e8014080460100429004050700d503440f81c10070a01c0e24428000d0320300000301c081210f0100c034885e4145641d89841d00800c0f8000031100c0d00042c00300e030f8201d2400d0140740c0003190000b090402902d086903448100304424500305141a600a0000c101c0e40e40d2040c510a500c40c0d0021481300740d98280c14083e4070fa41d5202d0501000740204400498603114000c4004107014110661900480c40c07000d00b80a140e413036030306000564028 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 650201106 1250 650199856 650199887
    0x50102030702010e0f0a03081305060a0e090a0e0708010e071502120a030f09060608100b01020303010611150c130609060503041520210f0c07020a0b03090d030606 71
    0x400c2554010341c0b1443d10800007401c01011510240440c0c00814103a0741980c10440c0c0c4a24001040210f027000010814000c00c01180d10501d042c0010320010080c0703005060280c007410911001c16100d04280e0044125160600b080b503030030076641c80700e07680a0300152118100034054050041a54941c3c0c0000c0050030603160024610842940c030001c0199103c410040e040641c1d031980d041090b42036000c0d030304103140101004166941032104213420070182c00c4142030098034152125540740d80100c192411180c1c5070500342800da041a00e824100f210f5040e07410300301d81c8a0001c001201d86480090007641581480340c4a9681d20b0b20307002c0c0c84010f014018040030440500020f030011740c00c600342910400160b40c022404800000b41b07450b0b41c04001c00d5000b409040400c0640110403040403440e030b4054031942c03e2456040c000c0660190b55009800096a50000519041992901c50801e002000080d488554918160b40082c0c0c03504209003030f010000e810100e000410751300c11000c14980892 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 650202356 1250 650201106 650201113
    0x171303080a201314061e0c0607200105060904060515090a0c140703090b0a120e07030615050904060b0f0604030c080712030f2a0b060a0e07052b06080a03030e0304050102 74
    0x810840b50400c0c4484d00d1161403069a01f003000d50200340381880b0541c0900031035200c007801c0762544000c403096000c03046a1901e45a150004211143c0e541c920450b4219410480000e0315845011122034040c1c121041540c110740e044040c0b201c403007620750110032810301a5580c500010700f003001c810554070414038007070001011010b061003c11000f000410030009142030103a9640b20000c0c0708030036104503c6036200e450b040b810042040c4259400f0720b160211112039a0350115003440000f8079620005800903049583e100048c2142c0d454907104020032403c0207003450f45890392450a4981a81c0e940a0b251550041c16000948501000b104244040d0300d80c4900c1040c202c0e09504031069a01d1003d51980000801040b0b4180003071b021240e122280100c5402803507160413804d001441055900000003074002c502040129544034050700c2003e010014aa0140407508500040c0c0c0321941c02c90214441c9030840000c1d40010024000011718420384050052607103140b00e40d52a4001c03481040d01581 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 650203606 1250 650202356 650202367
    0x604060e04082b09050c010305060a0905100308030f040302010b04180f0302070e100609120b06060f0c060118140402030c1201110c010606171303080a20131406 70
    0x10300000251a80071941c640022000b880181c1d00c04031000c900050450f66903a51400c1c1045c00340506c070f82c540079042030800344a9030400c9000301d980800140704030aa2170399103c002c0350b482090800d14000950700000e0b59a22800d000304000c2d0000b00071f071030880240d882c0c0004003000d8107140c0600006a4403421300c002c040780203512884130141015400328114000c04001241c0329035002c4416000d03450541c1d04070070650615002414108403a0021001101080524000540c0041540340e000e0713401c1c3d07012500c2e01c8111a8008032401078000718001d5008020000c0761280500701c0d00c1d0001c031400d540c24044c8003c2020040c035050380c1030301c1c0030750590032030045105581000401601c070994210000a040b8100d41d02a02007a0480062282c859440f00342c20010319a01c80c0031440c0b0200c020014855600340350f4082c00745481c00c500b005040c05041800a0f000044540c80301d00d00d82161612200c46a0140d45500010f0784542a0341d00826402032000c01d500403024417121000c64090892403030035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 650204856 1250 650203606 650203613
    0x11503020405040f1a06030d0915030b03030f0708070303111206100c05070e0f061e0f060405060c012f070204020c03070c0303260c16050f030418050604060e04 70
    0x1048020801c0d00c114480e8050600060402e01090051171103030602604281040c0d4105810068808180380800100c02d4084c807034001c401440420780d018034100011084100c8000c01c0c107502506030360350040714012403141c050124a00080200c54842d0342d04200340c01c41804031444a01540d048000c0d90955640002c5050519110100e050055811b01e50106295940da03686001c000d600038180c0c800301c1a051000c0541d9008c40700fa0490b83c00c030f0740e00399103084003032141c00c500700c07011401c030322a000d140750310415a11044101c601401000d01803e07950451a040350f4060403205503400c00600c490906841d00403024a00d2440714007440070054070b4114981c080001030341040d00c000c0010f000822070080000c000305c2500c0c005621036101e4540010314580358582400b04803103603d1342c0d500d008007005111820002110380f00000926102c82e40807007400d04c03070b18141729080d00b42000c0c4000600400c814030030350400010380900005c241f00541c1c5131810320065501600c2800f012450440c00305001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 650206106 1250 650204856 650204861
    0xb070506100b0c1506030709020d02270907030b0109030f03021605040e12031902130e0601020601050f09071403010b0d0605030a0b070804080f0f0a020f0724030612081306020115030204 81
    0x104000d00b1103c9851301c1c0c1e4010812030380000b41002c030b0552300140c66a403403c4040300d0f500c001454010015280782d0f4080200e370710240c0c018aa00100343e0313038030f44010316a0301456103a0080c640210255406096500d0080d545402800c11088160221040021507140030f01411040280f4200900800300000d81c0c00b501c290000b07441840704800c04000c0303040c500140d201910307161402d03122501d00310f8581a210309065901800304c80c1150040401031015440c0c10411003000340c810b80e400c2c00c042d903403100c084500040f0096200114a4000000168003d0380c0024103402d051803501004607987da281016030329411980001d014181c0c00c030000b1030490040b40c0c199446801101c05601c1e108000c40f00040c80c0e48880c805009151002c180c0e0301c0c071240e0402c400004d04040c0070080010b03605000021400e4904c500340188000c40c00c10500550611a0300440c00410301b02588050211541c030b0056116081000c1c0b0320011508104000703544e41c41405800715020340207503001d824a0550b02480003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 650207356 1250 650206106 650206111
    0x3050d050906063001110a0813050303040803070c0b070e0a0506120f040c080105010602060f060618040e010212100302010f02150408090f13050f010807080303060f0a0b070506100b0c15 81
    0x158084d001c0d0781070300d441c5030038042d0100764501c02191a550b01ca645070b015022010180204000c181203401c820006030b030000889e600035402c030480c40e07100d0340d4445c400c94030b200744203400a203244c054009101c009504100312002e0381004884c8601410344910a0107205d0281000752040320700c0d124003140c00d205401181d55041070207078070103c03100d544840b88142900c0b07003a0321140050303021004220348500459580e40c0c000404440c5a4a845914039491241d100384044a6200e5a6641801120002d007581115061041818070071901e00c1c24180d510b0005d0b110340b000341d02140300013201041852020945040000c110381400d0742c0ca8170780782c4038105c16400620300c881e082414502c2c180e65540d1140c4445050302c405035408038181c030385410303050300505046e40001180e600c225801e04c03002d50084240c9510035000d40702c035000340102400054600d60654811000d003000080d4100501c01c001c5105131041a454002031855036507034100f4003072032140c1541c90305a90030050100030750191014080d80c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 650208606 1250 650207356 650207419
    0x50c070209060f0102241f0e270d03020304060507020c0d0311101a1201060b09011809020301031a011d162001020409060906030b040b2203050d05090606 67
    0x810aa503c031a95020b0400c660480c1c06c12050700c002008500e01030308207050342031814000e0600343c1030300c0c0440b19001080042c011a046e1001c0c508925080200d0b54892600e200c58882261607005180201400039401564280c907928100380000e03012500004002c6d07400000039290360403100d5180c508850002d01c030018007640740241c2d910403081c40440c4c05062108141b081180030404d816030304000c1d81e02d000040d6200c0e00c4c0d0520300100100c480c08020380d21a44403c2c01c0034005910340301d030781c6000c5038a02d810a0401601c0400040f040c04841da5100035809820a03000580341d0b201e0440c1813998025181c4402e54100c1080001d1054011002c110031a51a904114901096a603c817010301307418090380a00aa5000c58100a506014060603000386820907042080c103046854800d4100d800820103011011f201011590110481404c0840d820300c0e030075070000302281440c0c01402d551000d0044a99241041d002c40e6803e603010490b5806010001c041c3c59650704400021600d9200201c00e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 650209856 1250 650208606 650208613
    0x50909030a26040b1618050d02030a021203040e0a02090310020a0318030e030717030a030b030f2d060603250b0f031b030714070206090d060906050c070209060f0102 72
    0x100074442c400740e0b410b40100d00c62401c2070354a1070310811218600c015500d44800308000d01e00d0188042c88018980c909448041c0c0b1809038501035400400d1030541038410003508001c0708100d5201c450004005132081d504401d414001d19251500070000703a0050312041d56143d08030008800c0d54041f00e0f40200811304003803c011981c00101400700c0710801100740b06a010400c000c103500309519040c040e59014003004815000b4011042185c2e81e600c0c0901d6109a043c1a911030015250780c0e820002017001c0188681111004c280c2c10101c42c0e95103050021061800e1032100104000c00808a5100d02c107100150080022040144030501c001881c82d10803a0704010711600421030a90400043ca007411a00c55215138070f00b440c80000c6100b0102c0c540580c048003040c014495040e5201c1014040000c0e0440d01503192461800090307694800d00440da0340c00003203c06a0410441c042d000045910b010f80c600300304aa45d00d0644a100344a0480e0096101d01a10300082541c0b83c0213048603184641031046 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 650211106 1250 650209856 650209907
    0x60206070302030703061203030c0206090316020d0f050d0e15031306110c072c010303210f0603050d0f05030c07080310030215031618060516170a09050909030a 70
    0x9075440b06d180c6140540001e074590f407400c03005580400101350041c200d040194076280783f0070030003030686c81101d00091083d512a000141440010240e01c00804c2d00201520f90107081080090300d03c1100c0d1111030f0240300c40c0d01c80403150300210300a4901c1401c0483d490505541c5e59a41c20004100d5400007035a405000d0202e0590600201711400240503e41c81c9400c0c4d0b21101a81800805514003440212071140b1006000103540403401800300c040c0704e22100c003c5210112507501070710a80c0c020301c2919140c003c00000f80880080c1008441480d034603078038a51010001c0071110ba10048440c030814810401c207540018100303a0045500c028039204144a0300e449034002072440214403004d045849000c010303c442141554819940d0044500b1300c0034403002c001018080c1800f02d80310b0b5400b031090128180b4180f0303000c1910342108950003200c0c070b00b40c0c01e010340c04403109804c003450349800076800b00008501410b2040c25240074000e038800a500b8596110812589041d098482140810301e0018 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 650212356 1250 650211106 650211119
    0x30a1e15051603050a02070c030b0c04030f0308061011120708071e14010903171512060a060902070809280f05121c0f020f0f030c0c010906020607030203070306 70
    0x260501500b10510714008181c0c01540040549102600c4105001d05c1080828005641e56552504603684240241065600c0c0c0d0084405400349034000791142c00301441e04410964070500c2c0e01d00c1404200e44101a05180f0781088514070541d24800b0100e520540d61080325a003c00d020744aaa0311520340c141c44c0c440c40d55100e00260801d08500e039030445844003520f08001e40ca442010003500c0c800001c10045640703403001014040100764501003191207601141c0d00081c8c030310920203d1000039202450031a61410410b035514000c131030721621603203040c0010950308007600032946c5c91600000f01504041d0101c04001c00340700c08c0980c00c07542152200c0d00c00b85c09001c207810080100b544400301c140d00717840c10341408444052684007240315000848065452010241c0c400540c0c40280b030f00b501d02d01041102a03180582400e0322342c030b552080c3d141c0000a20340c0000103056802e00c4c4000d40303405011a50040d28000402d002e1140960080c00004804502c650b01541d8030130414500803d11b81c0d61131f107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 650213606 1250 650212356 650212361
    0x50d03110a23210709050907080403081005040507120b01020a02150a1b030302070203120f031305010225060b1210020904090206160606060503060607030e04020c07170705030a1e15 79
    0x40b1040300300002c3e00104000d0310340240c1d4140003850256089003003843c11090041007550014801024454400b0101d084025003415503005000c000c0c1082120b401c15500150a80e92029450b829107070401c0324003080c80d40b010560510680d4060403c1c0c0c0185c0d048264054980c02c0f4040400130050075000c41280309510880c43c0c1ca40303074020780b0700503514109401070509040ca100c00104600c0000c0100700a00112181101d9002140d0800340700c101d4198605140a4840c202c949020307840b541c0000c1c40c5078040c540201d000b840c4600410424241d9039028049680450348040125402c8560100c3c110035441d00240b440c4000280001500d0326030398001510f9400451829070003519200c004800c001141c828030010f0a15401c1c40e44c21464060005405c512811100404200602020040c0c640b40da405986640ca050300c00d030f0700811b4031180c1e07a602c898510405036500c1c3c1f041100010301420040303035901010b81c101200515403848000c096a0041c4c0307006084030a000c0030804455011904e2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 650214856 1250 650213606 650213647
    0x60f2b05251d07120b0a0503071d09070e0402060304050c0d0308041b0305031602010c06050a0203060a061e030e0a0f080d110f0a0e010909050103050d03110a23 70
    0x81681c08100e091044407014641180c254216240b9680d00380030311a80c00c410349000a5000e648086010140100840c00c080c20562006400d40702c4c16901282c44075044110080301440551102e095a0319105602ea44010901c40e040e41c0c00d17043c102003030260500400543d0700502604c2100c0305128580f0100d104490110070079400105442c081c070082024011440b0481c0400078a6010b00034210780701d85451384142e1051302106101001d0000840e405028116425a003022003040f01d803505004080c0a03510489101c5d208060020021404a009103a0710f4954100418088400750225100b98000d000f051154091441128610400254099441c0440602c10856903072540c078802c0c648403e490b0900e0800b80f10017400d0200c3c013145d100303807416520040308510f04841d0380d100c0c01005032a0841e1035000400b0039820400040140034000036070a55060345982c080080600c100b0464200b40a81c0b2032003c002180c02461244142001641442225482d105c25191460020007500d4000c0354 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 650216106 1250 650214856 650214913
    0x4050a030803060a170d0809160e09150a0b24090f060706020703031d032d0403020a0306050f1b030a0b040f150807050307150302030901110a08060f2b05 67
    0x41c0b560142860b1f404030003c4d410089200017030948000110404250062034020740401091600c00030f8500d540400141400b0b1074200c030404800d00b05a50304d0f82c09040302c0c1401600401140303107540b0610f0718946440101e60400c96869041010140c10072010b40d1142e03404035400f00f020300c4144080b9a4510040580e607200352000900c26400e0701001c01c4064100c405d810303258006100c2c103400f28100401c0301071038051b8584030410358002e4035492840350140f0340000c1e400c804140c00c08010486c0b560310503400344c51400040c103110703a504100c1607020b100820054040107400d0011850ba00d00c25085000b10040041000c0382a164201b114030032107a03581e070003825079403406004101116040c8060710282c5425405480818105000f0b500f000c0c000c20014420076a00000240011601b0b6201d424071103d03005400e0340e0313004500001004035005032007481c8100a43c40a41000f8501541010f15440d0204250750202520f480b0350020040b410005413035902403c40000120b9440c16100b01080c40c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 650217356 1250 650216106 650216113
    0xc02010603150213090501080a260307080403021009120e010306091b030e06060a05010c0f23010510060813030513260c011b03020f06070305091204050a030803060a17 73
    0x1340d1095420300d03902164408441d0515241c014010024046154070f00300b030300080103010160104a03420601c80003829078a81110020040c04a8181d1291041d40618000d0303007268186000200114201d0744914002040d1034001100b550180f0b001e03640324002008141030001c2d070340380c1e912914420f5400720148501c4080700d090a10f02460781500c82e01d041d11844000801d01e070310303006000c074800c8181c50040a042c13214000c6070004200c0b1140020020540c03000765010740c640715008510f074071006808000c005508103030014196000140c985000c482155a4400341030702c45100e140d0310544030000540c00c000c0200308122101a40141480007480c0c4a070a1004030550b18481001a9140205200c0c040d088200c05c03c045a9021012814048240304240c2d6100c40d02d1505a01e0a42c95101601c0e460160320204100d071505a484a8403407001c4030181c0701020304c0c000d4190152b10490281075400780c02c010091021403c80342c00366902840242c0740ca102240c403000d00010f12a00c503040304006030b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 650218606 1250 650217356 650217367
    0x20d05040c1805040c1202060f0708030a1a0306040611041d0105100503160f0e0405040605060f01030e031602040e0a0f021305010b030f150d0b0a0e03030105130c020106031502 77
    0x640b2030342e050a0580465004101a08090b91a96181c241c144500700704d1000c0c441242e0150b540c0c1004440201b106454034640d580c186180451250304122146000d007807500075008440100c02c01d0701d02d04c0d003000030003410303031941d4564a86008048109042a070201c060002041030201106138001c9891a8034400e8100c0d80740c641080a8000140000001c00006006003d203821456840c083c0c62052030509117002c06840a04031400884202c4a81e40141014140300038403110360b000901070282a600307041220500d00056050310303003e1004000d654803c11141411510100352440620b00c002d0011803c2c805000b61145003540113002030322150104100d19045113403a201e031001040b00d030002400550300d00484000313075000081070010083c1203c000144540d05a101d002c402c003100402e144d6041c0450704100100f1001103545111302460004000b05103d03000064078100c030300040001c034142c4611407020f4013605640c0d00b400259034072140302000080d8840788500300f95102000058446 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 650219856 1250 650218606 650218619
    0x20a0b1f03081c0e0307110102030d0f0b04060b09100c17040602100501080a1104020904090c080c040b0d050a0201260a0f1401030b0c070206070210110723090703020d05040c 76
    0x4207043d20000070118901619022849000301c10740300c801d5088086162000100c60044c0e0545c4a840c12030312543e454002201100030311a40084500034082e01d08100940c0c0320400740b10725110f0781c140e90750301402e482d001c40c41d4544110041424903103c3d001c81c441500100e4060300d2a9003140d0044005600400c17a44070841c0307003501c20075004210120081000c04015140c258000300305241450240e900081c6141035a1203e401418001c1d51080060318259030320b8083c030b80ca9000381c042c89403080d410204242c065151203030598500603004030140074425200d900543d980d01300822030800340300c200e030254201ca5417168501b6108140c4030b440400c00751300344075400c0c4c06c8420041044aa03800420018008a900315075955804411404d103250307500c50303500000f196030250001c000c0d40065120301d11030000341c0c013079004440761150000f260049611448000c3c021118203049132f007148048040e00c071251400c080030f585c110001d828010f1505000540200549504840903208107148100c100300d107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 650221106 1250 650219856 650219887
    0x402011b1e0b01061d01121a0a090618140106030b0d0c0906030c09140f0901020c10060911040b0306010e0414090d0216050a090906060e0a0603050d050307020a0b1f0308 74
    0x10282503443e044e92410002e400030700b88505680c00c40d00b9142d60351400310005070135045d26010380d40d0000d09c2d00100d2680c54051002500d07090003008294410003c61654103c40383c0202d0300b410307444001441d5268200002140284a0219101c0c0e0041c8244482d00110b455011120064181030201240460460404101035100d5601130042c9178500340301c04003000702040340150412031281c1500f03000d0312820340060180c0202d04644c141c0c2e0040d03000340040d0310764030341c0b00c0d404550b000c801c18050b9101c00b040d5101c1c9400345125040001104100042d0a503216481500c40c039900244002102d101d0300c016440d400350121803040039688580d20440c1181d4040240706c070700c0740302e403044468900d0030071000c46c0b1585103a2151000d06078032140101d0802020b608281c0c0502243c02040586207010396a81380941403c1c0f05c1900c05004000c6000c144500c02c108403482243e4035001400034031019034410b81071110003130400c000890745c01a140394402071083c111000394044c3c204c0d41c0c1c403413511040c3d2813507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 650222356 1250 650221106 650221127
    0xb0c010b010e030d0e01020f01110309100e03030109050a090b040b060f06040501090308070807050d021e010603020105040b03040f050304080115150207031209090507050417060402011b1e0b0106 85
    0x1446542c040c042182d5800003029450b07050a0303e4510100d9400c500141d240082849003000f0550030480b03d41600540034002d0b510a800043c03c5418070f07082241c0aa04a03204000d80481c10b410402c0180300130b60860f0400e07070f080784950030006000c41c420380318100300c01c4c01a24110f4510311900d0920080e172030086146101c03c18201d4280389480c0c42c00001901040341480001c20a0320b0104903801448581c000381d490094019080d20300000103080025143c4040c0780288030402040603030740003c00014410b020640780d060311842d28060400032902051303040200100e4075a02c8004030003000980c01d00280008120710800030034001c0140800072500922504020342c4000000d10b54141030307500040303000031641c000d02c45000c0c915603103100310b0b140001368025140300760514080c006420b5000c00140211516560bd48070310540c0021019146c580a0310007a00044961a0702c0c43c004948640010b000e5105004034174214004c58400c1d407407182041025205101d0b100010444190000190302 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 650223606 1250 650222356 650222359
    0x52205010806040b0a0510020a02031c1103040803040e06060c1b01091d0606030903071b0f091a01050a0e0a090e010c0504080a0b18100614030d0c02091e010b0c010b 72
    0xb00420300080817845010452060900c909401401809241d000340b0071130f04450f4014055800840710101440f05d81515080c01c82c0014902d2000f00d43c1d000404000d48090310301c4140518a868981550f0402544015000300d6000c6010048005501e00412848000301d40c0c0400c82480940303c40d0016005000300d603c10300d64508002030203000b040003081d034690300c0501101c08a40f01d03160200c9892a50080d03681c020506042c250250286642c884004000c0340c0601005100301078403144c140c0140d602c0b40c1004200e20790440840546076010307401800c009095840c1403159841e980f400074100b448294829012a43d407a845209007500038000d807001c4141604000b440d0074540480250b13074607020340e1b01801c40c10000001c502d40c0c100081903005260f10075021102c0040380714042a00030f16191080e000103482c4880b80701c10b0787c1004140c01d030001165484d00214036800e0307001d010b070b2a0001480c110144501c146401c03071345041c0c101280d001e4040069003688030641201c00341d084030142829103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 650224856 1250 650223606 650223611
    0x1101110d021c0203090102060a02071419120e0108040f03180e0103020f040204051003020706021b1b0102061519050d050f07060212040504090f15201201060f05220501080604 76
    0x404030b07600008c103d9040501880c005944450070306001d41001c0c924400d082c030324007900300c0d8003002c141842e8141415901920000f2001048031070140c8851641d088080d0201e40c500002802040700d5280c125400c0703000b410007240182607080c91007203d52050300012214010400140250300340752800386890a410342d000c6151a040500150001c250100d00130105500007131440304100281e016101c41d0340702c3c000d01e00408000e410702c880c2c5618402036800062a9006032010180d071000807514040c1c01d00f00c072080b6122003401c090009008030b50088003c0b003840728500045039283c4a0000c11101d01079400ba00708102070782181c9060028aa01940440d80075103041485600c190049504036002106c00152030205450910300740d04900300068200e0000e800c900540911a401a248010a0400010380c0f035010b12404134440c001c44410a8000080000501801d80101c40301c0040c03d049041290034500c010210803105c82100e5012070015400381300400481d40c02c24181034002808031800d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 650226106 1250 650224856 650224867
    0x314030408330708010501030f1b03020d0e12030105090109060e1305100f020405030c06031603090318030305190206090a0809010e061207021c020a1101110d021c0203 73
    0x41c0d55500304403240002d400ba07580341e141c5007540505401403008104110a07072181c034100001403c0f0050034030445c2e02090501c48150407135942c40c4501170b0300307410b01c2c003101015040910040f1b009400000844d08016074800b800d4804403400c2026244445c054003005a82e58186400c0c03064041040e844070b034806d401c2c484140891500c5c3ca4056903c5401001e07080c07410641401c019242c494000ea0300c000356850003101c008400c61680081050390407e5040f15028141034003031041c41d01c02207402104d68400700c1c2885902d0b9100e900111403190007131404010302805441607000900c520760044000c200005191042440c901111182400c014005810240f90008942e17442d203800110040030f44c80000f40320340a5a0241d00c0c07220b01074002400042c2c440c2da440920003240c40c0190344041c054820b00700d40c03101c914140981c2c034001c645141e01400d02856a5034452295941110a43c0d0522184208104c092501040006076040e56580184030041d814036066460041c070081141c00c5402c00c220 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 650227356 1250 650226106 650226119
    0x191106010e040c031a04050c0d03020c0d020409080d09061b200712050312060303091302090d02060a1d0603010f170109020402160c060c0b3d03140304 66
    0x800a04503425041490001d980c0c6240a4045610540008001012070b4850300280000b00844520951041c01142c1240756080c040001e0329500540044c0145e01282c084101410824200003095101404c0070681055965544010f0b03004042c2c015401581c42100c841403201c240070704500005030300c0440c1500d043c081801404245082c40315505125116402e81610300d040007560020400c08016040b42c681916095840783d00001c010800f584ea0200410a00d24020040360041030300141720104c2500048403010107904881c5007aa84407020382210360150300e6840090603400c50740d035180884805941c03e007900071442440d03101e010716000d00052054005080d00d40d410b484022041c404003140d42010390740545071040b002500140041045861408078800d4100076900c221a00e5100b240c4580d0100d4032660100006030a110f42403010038021100421340740c002d01c0c2003008001d240454406015011900e00060038500700e0940403c000b4400207083c84420710f054600910720303081c43d004c5d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 650228606 1250 650227356 650227363
    0x3030f040303061d060f0a0305060c040302192709050d05030f150906190810140108010905190807060501150306050d0203030a111903020127020a09150512031911 71
    0x811090140b86608000c0640750b90380c51010307000792703484030441d0070502d064005d00883e03401901c0700302d019420040d19503100c460f40c018081c0660f41003030600b000c07410001c485a4a00d400038555440706035a546003c4011520611540941c6031064582a9680c14190807c0310b0f42d15000b404d402c1d45c9001407132030340080e0313481550560b0003807021101210201c5130700142c600003400540c0041c0e103a105d41c0e03031126480042e40d005903074218110086009242c5c5c0e1100d105081e00c009107001085500044000380e40b2440c08000d0410700c6018501640c05d2294541e2154100c032000e0300092845000c03172640c0500503a040c003880c030107004183c421640000c55607000c2a500c0c0a12407214081c0006003010400ca41d104000c50f6651300c244d412011482c0c185401c1c044d000702440c080829010030344580c443c20079100711080e44100d0354040c0050105614ec0100003005008525000d4401c810542c0000b0b240d80d40c03100c0c0380080c00116005195240611150700c208045807000d901c051001c28040260002d0012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 650229856 1250 650228606 650228611
    0x9050f09070e061c140603010b0a08120d02090d0c0510030c211b030209030601170d0806030f071d01092a0e0901141011030f0d060803030f040303061d 66
    0x5845907521340c96000c80351443c0da500d5800c07101e0a50726040b00c10106010007868180034003001d030000c01801180006019a110a034020750035a07038002c0030422940700002c1c0c0100100c0071052030040c200ba210a0000d2840084840b0503180e10b03215820901031864040c440c2c9a011455003401c0004810080d000b5202c0283c1c084d8001000c81e42d01c1c10040c41c2c10058020300380301c1a448400c040080c0120402034029000400080c0c042d2040c1000422130404a1300300c3d900301d88010005185906203078504441c0410002d0001d9014001c10f880d403000c0040800c407503009442c000e00b4240080383c0b41c407150004c00c00143d02c1285402e003004035201020340440300d003040d5204e0b840e03c0303440029410002658402107446200c0c0d00460968000910358007100640901c5a50440d20205803a40740c4100b2604049140280380c1e20b6001000560044000c010040220404403131011903680c0d81c07891218207603003003100c01043c0000500304200806a06110b0b1a01070702441c42c1c04020070810a40005019100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 650231106 1250 650229856 650229859
    0x509010501180915060b0d0b01080106050f0703350c19121509050603060f0402030304090b1206010e070f0f0e090a020d0c021011090d030513030501020a09050f09070e 73
    0x480f0440c0c02404265000090301c00750290f02070180e1070307562260b840540e01075882c0414062410f60010f00c6580b02d002c981d07040300e007a07a440506002960201800540c8485012000d001c01d19241c0d01c4181400200c40081001c136542c40e043d005040810315001a20042444c0200c0701c04010040380214003076002c803206041c0f8a41500c144c48140035180081c104d2920a89a080c110400000e1007541c942200384104030590554225440c2e44000c1040d01c0015140254503070801c0c4014402e207102a40031007290140208640f0710003205e002c00a040907006e8010300c04a1290508000008bd041703654681c917811140343c94070001a101f000103084d114035840c001d10032030250b000314049403103039015540d58241518041100003a0500c020b5902c41090050502541c00d00402c642c1200415041d241150700181c920040754266030360490320b980c00380749000b1940000d2400840414004d202078000407a06807524820103040c0340c1000003c0500205542c4100e85143c200065540c0c8014504a061070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 650232356 1250 650231106 650231111
    0x311131b0c05072409090b0a0e06060d090803060f03150c0d0204051216050103022a0a050313030309120302030a12110a032310030b060409061a04050901050118 70
    0x402c2c50014203280c625402103540e5000000741c100b00712104a08488902030136124200c00e240d0f034050000c29a00c030080001c0d807020140b2010460980707180406070b8003c070300810084c41c3c8003160317540b02c2c102d5540a6050700c1455000c42001010708008003966020b5108900410005c16001038281141c0c20042855101141c04030310f0080e007500d15015140a440024100c4007244000c000c081e40d03484c04144c180015440426001410f54080d1086403075440c109215202c03101100c040d42c44844568900111181c4160b86181c0c02080c400d0014002451501c20b400a80500c3c0d410700919450541c0c100d121b060801607c9440040c2e000011101d0541d180d040c150171010855040900905006e0075070062110300103801d0003019410b0f4810911035440d1001058420b035031280882c00c0001c00c03220b40030b0851642c0c0c01032001c5282c0343c400350346c45000104049180d24042c0d40340416903e00450004544004901441349850540555a03108900784000c00c01c940c50041c0c0e48407a004500c00c07505c1c0790782c2e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 650233606 1250 650232356 650232377
    0x40f0201020111040303080f06040c020709090507090615080c0909040f02130c11061b09062b09031704050607050a09091419050f040215130311131b 65
    0x24000c0d0003c000301044151410340700c0d5683d04020346807020458107031400800c004002030b030601c0d0078424050b0308001c0c2d0b0300908075141080d441c40020451080165110700c9603410004104a40b80980c8000c0e1144843d04080103100810140c213a91010380032018946d82404003100d9038940300401540a9082201034010020034000324181d82074018485c282142002611001d26401c012242c0903090381500b2070f0101d9444981d6003070842c840490052041d101000f544440785407940c054408609013a01c44080c1c0207d08010421105551240d1171003a503d650390a81410340080c400c04181c11134124906a0f842c16544541e01d0700c0c0006c004400788400451a828800d2180800001800e0281410001340c01c070708a4040e07101d641114040042c46142004c010a200e09004280c0135a0801c98004065141c0d07500300b0812007041c007045001d941044c806003440030084400324004500a401051140807003030180071311144540103200c9a60f050285e00c0c0c1808290000001c0301c0840c0f880c2560116 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 650234856 1250 650233606 650233609
    0x51306030b0907290c01050c090f0f15220303020c1519050307111005040b060d031403060f1309022d0d050c0d080901090e250201230a0e15040f02 64
    0x28080c036100d83c030701c5c0d40c84c3c02c003084541302c0340c40f00030050300300c00700c0d1003450110f100e01c01c000c24240c2c900c14103a04411040c0d1004201c181001c0a8440390f00310007071204038881c0000d03100c81404240d91080c4c0c010307801000e0300c8019080c041030941614103ca1070041c0b42c041c0114018800080580c11101040000000103681a1180e044140354814043c156803a010352040c9450181c20251420394040003518081526450329417150100d0542c5502d40310801c00c2c90260149060704010003407074001a10b08041074040e40c5040d050340d20852081760001701141503005205501c80c4204180c0300b84030301d0380d2141030507401c4203002d410700901c2140e07031044005140c90402d003040c1440b1403050304456040e4841042000d240e007d002c03030725820381c0c50720f860340ea8480c617190038090140c034200821400c1c0c81c81801500081c0c0ca043c114540300d40004901100b518114440480d004a100c44017914400e05208a000c5d00d402441c403005e85010041c01d01c50f881814000103400044c100501450b1405269401c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 650236106 1250 650234856 650234939
    0x60503060d031d06070b100b070203060f090c0d08192a080d1503060c0c030f0f02070305060106020a051207020603071b0204050f041101210e07051306030b0907 70
    0x83da00082c0415485090a10301466103190540d0341401d008074010000c03488801c034809030359209800400a0455032202e615001079603201800c0001180100190818a41c868110010340c181c07081000580d41c14082070180c0c00d4002c407424007003c1280c08014001c0002448446034042092581181d054004600d4119894031400307003058481810110608006000f01d0750b0b9100710303030180c801406a1030341c81508031703420609060001c0c00316000d91818003040d4410002c9495460075401200e100c0d54a80d06c45603d080400d030321000c01030340b1031212003040003028004038014030362242c402c44c20800d041d03000802a020040020041280311094401c8042c25012441c1032280c020b0320400082c02d1401c10908540e500f1501a90400303101c040140265109011289404542003510000218542103442c098032506595801078032804001140070340e542100c554403840190b5001a0061551514502c0e900340103202c1c0c034107500010410400b1a1003031b400c1010140c0315000b007010080c03111140130300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 650237356 1250 650236106 650236157
    0x2130f02181c121b150902130902061207051c0b01090e1909020a170303041a060307090f020409240b0406020d0e01050705100605030c1e04150305060c0d06060503060d03 74
    0x840454007a50540c1d0000d54484500b480c025140b010300c950101c0e0060062704c0b44814000d402a00400089100c0c1d500e9105e0310390440c00614000e4602800c0000c0203007100304a41c00110754590755002e00c074481d83c02c40e0340c1c0c40c01480d80c030021084070b203000d52200c558002180d0341d03107a4240e154040d120440d0786421844c00500240c441d600b512403010181c241d60307900f0845085802c0f2900d101070301c207440d074041e003100c0c4a020001c008208aa08003200c00c4040c104070b009820700c282c3c003400042207111a5021300600007081000c3c042260f140c90120303061800255000705008082004180300c440d03070225a5800c20041030a1200071103400b000101c600c0c2c41094400790031130143d482e50301d080c0c8140d504200d0442c1d070220100c41c1d1040c3c2c44010030000d00c82d2002d4443c0b1206000c19400b94500381500304188a01d18210075480d03259682c0c84a6082c00402c45903940d490301c0016440e403454290348203400141506180c107a06500c2c0c2500454021b07507002901505101d820294001d44c45290800b064 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 650238606 1250 650237356 650237363
    0xa1403030f04080f06062e09121406130f12090b030703020a0e1903060f060b0a0c0507090b0a03061d011506030b1c02130f02181c121b 59
    0x10781c1c880c0e80d00102510703216400c004100724002c0001042c0ea506c0c0901c80b81d00c000c0702164010324135209147c040c1e070034607080302484e00a000c1400c1002900d00d24844207a5892402800d02d03d0001c00d00c10038041c20b1030b1000741041c0d42d820340d02c108000800c55070402901c2071584058060300c405c1500009807408038141e4044030762100c000007040402c5900d500608419400c0e510f54001443c401410056150004102d41b8006078032104100045051904503a0304a00c020800080c42511a504001c0507800041010082a20300c0e026008002c810041107008150702042000300d108403000051a56149200242203103456140304126400b100b101203500d5444440204004265503100c100c0281d42445020082864010644d41c2810821170b100c0b1201501d9641e01c525002e03582c01c000524091402c90000e0682d07804000c803002400e880100055900083e06036a0141c05804216200340703101c1c0301208544a0880c4d01c2d00280440e0110b17160710306681000b0110040800120418108542019 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 650239856 1250 650238606 650238637
    0x30706020301120b1806070f140309010510080109021c06150314070f0b1e0403060203070c1e052a060301170607080405030f1305060309010522020a140303 68
    0x1c0c007280d07203020400100380f0613080c1007125510440359000c841100d012140880c0c111500146000e07126880881e05c988040c02c15017002c0f0164040d040b61604101d40c41030150399500b0a0240c3c500e40b4810460052010100a20121180c0d0b40803c00707101061101050f1426040c1001c1c0c100282a005002442c0b2040c001c402c0c0d840c0ea80c00c100164100201281d50513010305000400c00caa0701107202001e0360b050008840c900364060010b10120b80f20070310550322800c424800400040d042d400114081c15850345c60f072104009604080c2040104482030b203180150032103c0c40000350b40415842d01c00300107209809009410704200310003007039074a03810650010300007002248160900d0202c1d4640001001160840d607954a020390710f0700c1d4141c90141c01907100b8441c000124809000504502020035030080f82180e6802c0401d0240d0000d40c0c035201181d465800300500100b8103c55442640441840c10301c0040d601d03000f1451b0808280241b00c00f11464440b0310542c1d0714200300310f402102141c05103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 650241106 1250 650239856 650239859
    0x11103030717060f09060f041506030911060306010c170c0d020102031e01060507081c050c0901080721090c03022808070b030c030604060b0a0e01122309030706020301 73
    0x5040d401c0a16800d60b6804000340402d403281800510b52000c643c000c0c11901c80c80e102d000800c0403a141d03100d00e03503a00646071100509006429102080280b8030f0342c80102c4e17540312914110340010004d0041030702540c014020011035030303802600d043c1c07180e07044800f200c2c0d81030144d820511b59106071f045444141c401c5c0d214244d9405e50541c015440790007541040e0b0400700500b85440c00c817150a01c01c01000400501030400410317a15030041c1a01903240c4030076030440c028051100d094400071110a100c590000c00d80108658004442e140e021142d80743c0100c0d011850501e031203940503049003030b00d2260360750301c0540b042203c1280c200c40510780050105e1021a85248401800c881d120700101820152510000d02d41700002034003002d84103c01c10f41c41c295a61541d0006103504001e0200340d129032614800100d4020001c01441c044485903507844011003403c0002d00b5542080c000742c68600d240540c0c44005585d0a1651919142e941510306a282c84c0c1560081c694015690084c1ca8540f00000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 650242356 1250 650241106 650241121
    0x2030403141306030b09010503060c0a0504260120032406030a02040f0b0403080307030c1815030b0a0b04031e0804090c0806010e09040201030506130501030c0503010e0712030e01110303 81
    0x11010103c610139641840055004024807000c05030a1280315010340c024404240d407081000c000d823007201d40034504641415500c410000050741018405421001c910581d400021420b018107100c520040941f408003195a9008010f28400101180d280003964511120605820380c540d510740f10b03004002644a0070700c218584001e500c1840b42900310005010001184a540c0d8240c40c2160f0300040524116074a400054010300012182e003801c004504544550900981d9110009050030203070720100202c6c0203070041c0860b4107000000740303e21100c1108004c2c80030b281d02100c4c1501e03880400c00d1070400d842c02510844c1c010402c80103003e03000c089800b2400c9103041d8441003801c0361581d100800c6407181c000543d4040c016168150b004004840000e000d940170750416600a500649140b1600301c5442d041400c1b03400030303007040359118007e040030412450b00340200c90542c48100084e09442d45031021340d010981c0d460800805019221030140c50907801101000f00003200e010030780355603180c21071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 650243606 1250 650242356 650242387
    0x20c01060806100e1012080f03091501050f090412020309060307020c040f0603031d030705040e010b04050c0f030118020f0408011e2f0f0403050d0e1e01030203040314 73
    0x2607020042062081c40012403d11101130030303000b01c8680c001c0c50351136403c1c60709481d08079044650070b54031040300700505815540110001d42c450301c00f50b4040c180d8600f0b1428407100036801030f403000d441800380921000d81991364094903600203520081c03804510407552070503800e43c062100c400394060000b000f08120660040760300300d0990b40440e801c022031908104041c04642c62400080e0015075211443c1d03440d52051030a94a041c24010129032500e40d07240005010b49100568214080c0d44901c2c80106500309070090941201130080c0c01410909a00000c904a000500c521002040b9010b10000d404065904540c181c008a40d0711039646c07901c034402c160103440204520000071080142c5034400e5195441070481c04081c81e400351024000c10317504c44141d800103030007052003708100183c0c02d80752207d400410045104501420312007800e0380b00944119160381d413050044038807881d004504070440700303410000c1c902403c006031207850f00e040480e2052406007510305202c03030000f15040c1c182d1001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 650244856 1250 650243606 650243611
    0x1b0a020d050904140c1e271f17090a02010c1527051903050406050d06330c03050706181403090f040207050a06092a0918021e04020c01060806 62
    0x1c803500300305006d2440d202c2d5a91040c01a61212016208400703000c1c2404c40440403107542000b46803003102d0000400120004080105910204169105645045403420007081c0d01158650142c07281e40d00507000641100300344500100b50401e8403640318007000036035200d0514040d40c00c1070041103e090926201c6141c90f007070016591446012100e083c0582420303642c00e40d1603807540c1e40e039041c0707450300314140c1eaaa004240203a030015200d00c1c020a03102680c01900f04454441c030f0609403170f07030b210a50001c402482c0002110400007400c0c0b03040c02181d002801c9070060f541c80760002801c0700040d40041111805600010200000059420700c065000000707440324900443d12503940e0141c55081200301d214400000702150804040304000c00c4107a8801c030301d0306001d01d010200500440310041a038024003451481d041907400000c1c003803800c0d6032194000d040490161101c841101d0f80001d001d19041c51004909440c550320680d0040c0c031260141c03000c1d403804c84000d004e455180c1d0701051306e40c0ea04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 650246106 1250 650244856 650244877
    0xd150203010b091807020d052508120130062a020c0607021e0307120b0f0604060311041d03040617060a260312040b1b0a020d050904140c 60
    0x100000b00c4510107011070341a011790141d800070100d255200100391910340015134544030400d6001000c0555100c0c512220310030360320800d01981e60b0700c282d010390380980b18181c02426007521070303140649085141c0c800d403800b2503c4210350105c00240d1860458003910905c100d4000e220400c2100d100428070340c4450881d03c1c0b04a401340da00307800c0f40c907081c08010300884030040c1d4001e4188424440d004c0b0022411140650050250b80c4070301d44541000c40c24840e84241207074110850400c020341c21600307130030141e004002141c0610409181d0340b41c0c200145088018144600e640d01c485031a205110703070490074407503100c80030341303448594680b009805e80044503030140301c144692000801929080d6415405d60b89030400543e9801202c1010f04008502490000300d2440700304071a4600e901c81e154054451841058201c1c01c500e0f10041d001140306111408000c0300c4d0003884820f038140e070041140281d0100c1807a049498540400004001d444551105225145a24103000194042070000e0082284 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 650247356 1250 650246106 650246119
    0x603150504020a290306180c1c0b01050d020c150a09020a1a03040b0717010b0405040c090302012a020d121d090115051903051b0c07050d150203010b09 66
    0x26291382200300058403803554103210040740b9002840c4240e44010715009072001d00504e1034521841784c07020f41c030003094429686d189404501c982c000483e507403107410802c27130340c28040c4280510100041c0050147d04841d000c02a008a03a2900c89442000440d03a581d0803610741c94011f0810030200c200038080c1da04180d0240f903070303d6804a8602800659034980160341c0d880c0320316554890700c41500312607001e04100204290048580c05081d4540b01050103003031407404042c1c0c0c5a1816041208650410240c03006024105004101607030304162201d040180c400004440b24560052a11505000003002944100c8594a44045c407168a002140003007403a04e0310124201c00e070300d100d41201d05030702c11039502900c0380c401849550081c11006c9445141b900780907051040f21102101091110001c500000b039172441008106d90103038001d44445400da480040c41c2c40d404900068448282c0c1c051103016070402c1e0050b0080019410840c545040910011512035866034505540b41d400800210711900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 650248606 1250 650247356 650247359
    0x121b09050111030708070204180501090c060306052707052b0b01050304120e01035612030403020a0f03151406040504111806091803030c0c010603150504020a 69
    0x10340002103d00194000580b46e00b0040141e0800c0040d1012a140f044020929007001001032024012292a82c0c4070300d0240342d925090a034010112034036544035510407203090140a01d218203030100c1d500095503003141c82e106a91101d900765458410045801008880c105902d00c1030020185204e04942d140c107820300c000c804080045446010945003d0481071200030300d600c4040c010001d08500071418100820130026140420411030800201241c1074440f101d40c00701c806180040072407203130140314440300101c0c104400032008442c50941c21070040c460000102000c4208006a400135a402030000c80150703240c44544407500b40c503120440e442240140694105040b50058041c40000c2da003d10b80150f44450801c0003801000d402a034110610a041c00e00d50380f07504000104c8107a103015405254109401480360b00074006105c42e541445240b008481080302000700c9400010b0a9410754440c2a424801c9004009690004208084181d807084a240796904110300c039074000c40d009080075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 650249856 1250 650248606 650248637
    0x307030804060c0903020a12030215040f060605060309100e03040906080304060e0406060813060b0310020a110303040b13050f060f07030b04050f0105040207140d020c0306011401020607121b090501 86
    0x4004e0700009511644d100e50502c00d0350f24100060303038828000d10483d22904404e460304400036009540981301d5001444d03080c000d020050240000400c8240c0e031907481d500d09045026183d035000b80c0e51130400c503143e05074040322960810942c2c000d0000c0c50410000a0740e5648101d5036035020380300b1140400c5071100162000c0c6041c3c4124411076507690bd44204542d40c2c0314030300c0c030001ca0702802200d46650b61502a1380684007086901280068050300681e02c00b8200400340a12104130301203651940200b04110004d1019101c03540c00c04556a1003000f50360192820398141072199440b072007940f00d414100b01009481c0040940540402e8a081103d00300c400c0034041035481c21552680451400c100411250600b94020310f600c03801484005040c01441e41d0040c100440c0b00302420040e400480c002c0344501d8140482401040f1044c1421100c08404002075202d840040456040c00f0807200070030a1060030b0303005030180d050521010f01c00700380b520300b02510070340e9213000d10f0b1b00140d40442c1e0300014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 650251106 1250 650249856 650249867
    0x50105030d11030f0f16060501050312070c0e180102130e01060309030e01080621070321020d03020904240f141e0319080304061103060108040b04060605030307030804060c 75
    0x20981100b014601e00501c000315003000703500c1140d41445c1a43c0400000350110807801100b922039114010102d115450f1030101881c0948801012506a07800c1040000282081011100700c0d034442c04860311607507070324010403904e40c00e1880c00c0343c41d03500008800101c80008404003040d9441e40d500500c1c82d980300d900850445401180007408035440510741c208540c05000010752003031005107640410076041c2001e400da00100c0102c0c141c0d82d48070710014010825008410105040c0d080050542c030000d5a8000755112035640c80c403c2416400600505940c4a54010b4618100b1403403005900c208019001c4855082500c941060404403038008104000140603d00840c1c0004040380d091054008604803050240100154140f240802c03a4007940e00319100a04200e008089103903c91501e81020b4059a06240b500c402c095001c100300710980c1c1c0c1091541e41c00c1604074070054075556862030548000e016a4109940c14400072606070304155008620522840c805d40c03040c400c086e003400040d1107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 650252356 1250 650251106 650251127
    0x5100f0308090a06173105060603071a0a0e06120c090f040c0906050c010e16030302010c090f0e0405150903130e010e0f150d0804060338010e040c03050105030d 70
    0x500302c1c5d01c0000710300c0070601818410010115034030828400c15001c440b2001a202d00c00e4110b400340c010b0003c1000710702d400d1240c02c1c01403104803400103081460081000c01e42c032614103a4000c0c0140d12404c03034100e8459000f61400d107410011064000e040c61452071010781c000d07583c5648142d00d550b100c00d045041c28004e401e610701191b21100c45281c1444810713240c40c0c0128a04000565951407040f0200300200118140b8140700291308403120304504000342910045101003051003584c002c100503052600e25200e0840c0d404100d1070350103807290b20300141013a02010002c14141c4075a0b0911000343d0003c401401030005140c80940c5080d5104130000301c0b00d80900c1030103102c0c80d2070b00000c1d10440c083c00605901c004039855030501190004c00152002c0100311040c0c1d42000089000d000c101c1d018802c4050700380c00800031036602d240000c404801c010000500c120032001e41d00036201140d00070410680d007408000c005104030b108c203d2005004000c02d2040390300c00c0c0b01d031005500c4594021030701d40c003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 650253606 1250 650252356 650252387
    0x10c09050604091e0615170106020607050a120908031905041e020105040305070b0307030509031c0b0402040902030c070506060d030203072d0506010e0106020c0303070605100f0308090a06 82
    0x281007510301000d402c000c00c01c848100400604421492004e6591881814050100c3c2c034060300540504150040c0030104541c1c002082c0e11021005000c12030b000500d050340101c552410700e0340c800200804491100307146145030701c024200540c100800c0003804c087e500c80d800d0841c80f510030f06501407070b180581c1e00540d4007030000c09030900b41e0380c03050102114200440340107040c203900d820b9a0343c1d03d09240c044981d100e16007012002c03040c0840c0a6250103203d8001c5048030040d42840c1c1202c0702080759041c140003083c0c0b070070303594600d07d000c0c3e440f940c0643c1c000f015604801c40d1649042c000c5000940d000e00d01c00c0303416008000c00503c0524200040101517601540158100211a44c0c3c1000c0b082c029070f41400b00842064a51300f5242214004040449c423610140c845545050f20000452106800000075504401440c25035902e0000980b400303141c2116020403143c46401e02401000215002070b104080c1034003000c014480410024041004244c4200905d0ba0741d0340021200b6642c0840c215 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 650254856 1250 650253606 650253619
    0x5091303080c0306011e1d0a05030c090a11180f01021f021303120c0b07140a0c1509470a0f0c02280506070516050d11010c0905 56
    0x4030303101402c001a683c041c0301070500081a8040d00301d14900316511190010000761080342d070007003000c1c10301c58002c20588280d031817114040c00d01001a0b02c0721031540c611806004c440b40019410015608514a510700c0c1c21a01503440c50211801e05121119402c11405003074105071342811540300050701e41c011144481d801d643d051550104201a41c030548174841290740703145010000c203240825a510050312612014040d407014a0071302e5450400034074500c00d00650304e4100503200c81a404582c07034600e081c54041c2815669180c8110040641204441160301d06880c2d402080b840c0520074080c02841c6640904400c0610038848424040700c1c5050100b030341c0107207101c80610130051030035000981c87e48041203c111820003a011181700c9503a200c01a402079054500040307102c04c2100e90b01d8101076000c44030700c9950310780c0359513080f0181680080000018a88008100300c0ca000f0360203603480b0090f60101030b10540000c151881906865065501e004981280c05016000c50000c480340581328 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 650256106 1250 650254856 650254861
    0x515100501110703021003020912120406030b03011404051e1906090f0b0c18030303061f110a06090b010501021f0b01030f0501080d020c18040b0c0412030201060509130308 75
    0x440d40a24891a199203d205a40011005036241480046038502c03503500142c445a181c000c00c00e4640f114140480c0701c0d0403580c16501e2480c2d4100440b01900d03036504001c2030702044840070a004004150046000c42035000520080102c0850400808248180000201442034803a02e07150380d101c09603400c03c8201c84003850001400c6800141c1014010001d0400026182d01c1d0341e0301c415411980c0c289490b90000b00c5040142d069000c220566000b900214250301d40500411544407030201d5960311410b0000400316810b03c160400d0006890b04005d4900e102c000380f9040c4040c08143d00115161218000041801d5100203040b480e94018160b138284008040c5207100002d0140620b024100340c1c8442c10302100d800d003401014000c0c058400148a0300d18807900083c1013a01d8007500c42c1c4152480e2400700c034580102e03049160410f0308040c44007015102c04a0340e480f584202e51100c03c1d90f42c2500b800e11305054040d40f103081181d07010748103a400303541e40c071b41d2400e00000000002404104503101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 650257356 1250 650256106 650256109
    0x70806040213060305011406010f09031a0c0705031b1005040503090d05011b050909010e06060f0f070605040b060907020c060d0b0310020f180f0901350a05151005 71
    0x20b00c0c510401428005441500e0791696400e40320850070540090700c5c5007050000c1d650b842142c101e050721061034002101e504507a20902c0f1002410599075400303401e800490308880101d0308075880181d0000859589140c4a00e0318030365101050356444070743c00f8500020085109500613030b03205a0348500598900710b40c0800b006004804d81f5030170b450666846e4a0003041001195882001c45c0e15911541e80f40c0d1902c04c1002003100c0f0503008060703e600c0c0c0100340a010784500040e40d0071419051505510303003c91803200c0c4600d028200f006450741d8100014002801888292140030780c106403404945683d410105a079154128000c1ea5002002040f1000b00500d20703510103181d103039009007030b14102450740840c041a42c1203420000c1030004001050001800c411071442c604076410344d0701003031102c2040300040001d001441138103003440107998500a0411038601001e803020b591803d4807400da1031422600e42e20340c448031b000ca800784600700740d10011010045101c0c0c0f103440000f4400c40301c24100030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 650258606 1250 650257356 650257369
    0x60f0b0a0303030509012d0e0708070302010516060c080a050612121e0406031e0b0d022b11011d090106141e0d1107020325080313170708060402 63
    0x240039000d40e551f1500b100d60003441c54820f104440344000640440c0b80c1200201c04202d40058400038580d50000000704941d43c1c1c00308034001180d80900780191240c44d0f000510060400c89400142658503114400303061a402030300d1b0a0207801815410000c507a586814003108030700c100d049078a070303600c1450010443d4242100502600c1054821444030514403c00b030a06034000e03802c1540465100e180b48540c0880d0054403c48815000c0340078041c4028a40102d456150440030280c000d0082540501343c04903424200e4401102801c1d08107500582401c1a02068041000b168002411250444a86221517070b40a00b2032100904a07403843c4d29210060f00d0041031883c0395440c00409101d186441f245038100800a00c481c118107580d5460390740b104100302c80c0003e0190441000611411b00540c42c0028501800d050314101c00080700b941a08400c0020b2603079102132564400040c8000f080580c0007141400c48910b80150700b4020300c0d0f4503070359407520350601034410564407030b00014000d442d088 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 650259856 1250 650258606 650258611
    0x151d031e010204030b0c090f15090405071407060b090106170c160210030905011103090303041205040f09060305060f16080402130204060804020f01050a021f0e030307020604060f0b0a03030305 84
    0x1503000500c0e1555941c0c8900c001c0100300c4141002134000320b2081c903d030030560301d8455240b004442c142003000d43c02c01c10b01c0d40350054015050203569035100140a143c064800c011082d6108076a85803035034a285410b80c0039100c90190240106484000001c0a074040c4c0382c0d01c120711800d001003900340d035910030703c1c0070403508415415003038650651550380160301c882d4030156a203009660045448411402e150b82512905031003905264010405c11880c0b0f80e01000340d035013203584040180b02c1e00c1925101201c1900544e04200c0f001c04c80c020f0005540c0d91164040c1080704c0c481d0060b20519951010903101c040d400302d4082102a5805d4641016240700c3c00301c640e4000c4c4000c000303c044481d903c516a040360440d802820100b6000c9080c072055142c0034030200b2134000c0c2464510301d41104d03000300a441d000161120000f0800c070042032030203070600d90802d076610341c440d4040700d86038504900029a14201680d0079a80d0510700621280f0905050081040e180f0000d07140288491031540c0c00c50092000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 650261106 1250 650259856 650259913
    0xf110a0309020f09010f0914252d080108030a02150c1c0b03010f05090c01110304082d03070302030a08070302090901090209100314160c050106151d03 66
    0xa4448540ca144c0d10a458180a0070f0005c40c0590340a040103a00c0044461590a66040d04015001c202c200101c00c00702c0c004103100c5289005440f1b50071002a0785000754100d101c1d51000442100c0484940098014a65904681d40350001646d845201a445e40301d407012580060300902d1002c590311902e00c5c1119040315020301e2403403030441e5002c50b1030107108040040c1144103480e08800551441d00740907120b045c2100401c2005203080081c001503884401c5c002050500640302c11203400e12100f401520014485071741038401da43e5010f500d94a207488481800883c5070805803041584140000582c0d082940c560001c1d480c00340d400c21705581001c2e005007680c0403d5001c0240c05117070b4540240e158001d024003100942c80b5503c0d1410006480c1070700401070205494050b810b603609203400900c0780c101c0310780076426801c200c5484c1e00700d50b450300707012018109608014000038000c0d10045522680c60466640402d03200008152041d814441a0403030740c1039000c1c841649001c002d91a028001044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 650262356 1250 650261106 650261119
    0xe0f01140610052206020102040e061c0605310201020f03030c0703030b0d0f03110c0105130b0c01090b070806090c0c03031504180602090906040c090e070c23010f110a030902 76
    0x82c410b20184000c83e0172a10050750040340402600d196041115080107085030a40400c5481c0c4c003840740101e4400a002c1c01240d2168003040491510b44400c8117103034900030100110004411001403520f0001c075003280144180c40c1000e40c0300b2004130a6034002c1000403d403614010340c5403411000f810400e1a06680724005e0031482d40014206a0b214400303e1080d21201780c440d041c0c100c5642402c9800744854180700b07003084560b8611010920341c100b030b12180d541e0b898540c288001d21500510f00440000c1c05c5181640038081859044030b40148a10b0044404c0d00d80d6686900420b42c150040c180c0502c03050f4028800308034211810b444080124070302420020f601144da075007a84802c07414200690700207500259840c20b605208408642c4800c0c19a030a116540c1600300041807101303244161603035880c409000c525801d100b9010610f00310b03000100640d200010b803e00c1c41002920400d9401f19620309180d40c0120825802000c40e140494075499080c001d10120030f8010f00762604080360301c100c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 650263606 1250 650262356 650262397
    0x3030f030f1d0d03110405030a140c1507060e011404110112020d06090614180c090a150f0c0b010b0a03060306060e060307080c03070b090f040e0f0114061005 69
    0x3904a14001041591005000d0100f00e16809412103c200f4100355001c0e60400040c01203031000185808210f5000403900207040e075100e052810440d0600c0182d50005900c0260410710241c0030180c85c0c514022041000542032041c80c1500303e032a8010414076412941000401081440c2e100d605a00e0060420290f0003079034000758012a80012040a8010358a00302488044014403038035028010001c00d4002040001000500801401800300c00e0000014000380300010064103880c441c810241940b0803050300c900100c19004204030740e11000641c0d42c890200b03c544a96020f10400da008040e1a400b0790a00080c440242d110031407103420726894620000019041d8811400140364403081c000d0641048010517041c00340c690b02a2b100c551150304016581d540210301039040302d42c000c55203a918210040450101c1c003641405581c01341c0b4044442003c0c1700049412020311103104000c1194054504624041e0711040e16000e8011450904a45c0c1c0180503400a08100310100c41c20322105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 650264856 1250 650263606 650263631
    0x7050102091002011a010e09041e12080a050703022106040e19020306090307150207030915030c110a080f070602070c0b040e010b04060804020f040612081201050a03030f030f 76
    0x400c4240703402c000503951070403400c804100c2c80403070311100c410900e816401c681000c8002105410042c2004d00450604807a0003460f0400036001101c4d91f900400750080044c840d07901402e04a030032910725103540e00342400141c07264440d10072a00e00003228a1b4038602c01042d502e80e80c00c00c0c0e40052115801a0f55580900c01030341c000c220103049001d0580e486284e454540c410315081c40c030050500420355100384036040000f900080d1529821804080040e00c490b4107003001c0f21004500d60210210711410340c603500c60310354160025110102c00352140c0c540b160100c0c003000c2e07660844100140100c401403150705078070140c6c40000d2060600482c03015050009a0301c0f68501c00c00584c0c05030280b500001010040e00746012006801040141381007400c007442d08030302400c0350800503c020310845103e01003206542c0c0d56480030010b00030001078004c000945190a032920307404a150170881f41c1c03090000298514110082d201600d5140d5078940b100c2542c1c000a401500070080d10b000c10350344523815580b41c2c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 650266106 1250 650264856 650264869
    0x1a0a080406020d0e010f0c020d08040b09190b09160510030b190b1b0102030f0105120703051b01020f0102030103031b060612120807021516090b13031a1005060705010209 74
    0x1c00003007800000707000c1c40c4082481c044404a01c7c2c0403003950070085440300c065421040403980580c100c49817522940c0c4007900075080c002034001c404503480300322240e48244070804038031601ca500890111001c0001500100c41006030038454035900070f14509080c011184650421302181c1c00142c9036005407240b40d07601010f0f080164110041490300800c2450795501c1103a00e0001034038006000714030f14109440a001000f00501810340180945078010300f48040401404000319088010b4900e0424030303004880791500680066801840354001412110344107100b141d04a03941501c44907414218004014075440d154072040d15070170740d121000100c00d01a6103580c40c895129080b200005410300c500641016030107400c0000319030082c44284491450004038640003a500704084081c6540088221064002c680003600703009000300c0e050030003802340c81001d4140c03882401902c042885154103011000e40803101020310090301c040030007140c2400c40080c20b4043c0204000742c41c016000010422 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 650267356 1250 650266106 650266121
    0xf040b16021e0307020a12020f0f010e030114070e090c030a09030903060f1401091b110c12070f0b030c04060e150307110607030b060304290415061a0a080406020d 71
    0x385820001320030046107044811a0050141100880b139450302980120b400d02040c00901d501620704144030000503030196844141551005000b4441c0f09045021002006020341d00100407603401c070f614040b6803a10181052140241030700d03a03411a56480710b1540900b45048060b024080031fa14080701182c1c050003401803007401c031a0042620714a086900001660517449140060710b0724603000040c40081d0a4400900d4041c81d1000e151454007043e2410054024180c50b40402c2c0300000703400844001c01e022040711160000b1031240e9035180340580c91440100c5a200c40c03036004120078420b10340110301340501104c001d0900054080c0d08100d290382035006075041000b00d0441000089444810800b480e031105880c60184031004443c6e011401c1404068030003446034091546051000700840020140811481020303090b030300305428014a1004501d084200380d07400c000000c40c0b2403001c0301c00802100741d031504a03840e08100c4c041c11100200b000c0c5c000c940044c4c082060814041690145c400b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 650268606 1250 650267356 650267413
    0x30c010c18030203060a0903050906040314010c03021207050c011508010506030d0212070f05101d0727090c0b270f0603010e04030302070f080901080f040b1602 70
    0x49011030104040e0000900c2014015003101d0100e0900040e1008a01c00b900b002c031841001c241c00c822031a068400b80140c0643c0d030703001413010500105010642810506200c0c5c20f4000300070701c0f481c040d8210306038442c1c0c009070441046880c0100f00c0349071141c030042240841903800051643c0d982c030281105244141c1c402d404c1a07440f081030107200e180501c240302c01c07100540010b01940c400d134906c0c0c074101d0051601c00340c40d100c00d451020052001c14050102400e1003103000b0031203500700a0103105040303103101440310075109000e1301007012403811682d903210030000c036007032150700010380d81060141c510441e0881d41c0401e904c200041940c24103026064010302c3c590304c11014814a55152107204000030024403036004062401060388960003201d064511203014942c0a03625824158083d20420720001c0130040c012040c1024000014060000904242e80c0d60046850380d9640b100d280030300361401b900c540311600c0801e500c011040080340d40c0c01400c2c0183e81030a02403d0390840d0070f120400d03400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 650269856 1250 650268606 650268611
    0x1207030f0e0121020a180806181b060309030c010e24220c030c0303180608040302061f030515010815041e2307090f0b010509150408030c01 61
    0x4048880c1c018184410442083c03810000c1c0003800a550040781900d003051860385a800208242120f100e60810100030410302c2c84100c07810340d68a5101daa444003292410002041086118072465010400d0b07424425040ca103203042c10b5040c010020300b54000391050b00280310810403000488420f00032030311101d0000016095001100c002c4440395054005c00100300b070076810800c107003d4084036001d41e0010302e1145000d04200340d4903000d607410300e641e0005400011407000000c20182d000300c04a5030148484020240305a0701c0200317640b00e901c00c1e900200980c000e040000c4040c504501c050f101c14003c0314204d00c55607981d40f5007074100405a640c12005e1100d003401444500420401c81000700161001419685016111413004404040c4140010030521802c1c0c02404134904140105d83c0018854818a05920420f142e8800013841503888440c00d010141208034414890804d20450603100c00c1e01d012014800c00a41d01004103164125400500020a00c640c00b0406010482e4150000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 650271106 1250 650269856 650269877
    0xb030f0c030f011a041d0610050c120a030209041424010c080904021b0a0c0e13021e0a0b07140c210304230411130b1e0f0403030314160e0f060c07050f1e1002120703 72
    0x2c051000b140099065070300c1ca00c2021440f20350360b02c00c914c1055107070006021510380744042e0006010303209102c2c50850a042d6541d800c0e847c0304000c01d8030f000c0e1a00c500d18000f0210b1341d44200703c10b1008100c4400300040d1116200c2009820a180400c081d0341158490071900c02c0520001740c0070706c8094001059140c0701090300c808008040413415441300420009000c04003010001a00c403a082061040c1043c100c801d410a10070310800584014083c0b50303a1000c5814680a15a014210b01d003000511a41c00c040c140c11800c1004003c48008111740020204e00c2800e00902c012240d04c80c0008001303001d0b4100d0686100d1810700041d01d900402d0102440d65145141402800e0302d04101c55560702c44100b20601c0002107040c44403000454141c02e2070b101c2c09a1800000e2000300004201c581c001c4030000d9101e251aa0101d1001c0c240c410441e0700d18104402007003409042c42c900c1800000c010342201050101f4a4064003084c522a50b0b4030486108001c914414541c503040144110f0108426400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 650272356 1250 650271106 650271121
    0x5010305090f06062b0b0702060a050c090d050705040203040b09100204060e0d0f0231110726040b030f0c030f011a041d0610050c120a0302090414 64
    0x665401c140004020218124034400350381d2030303600107041c0c42d2103800301190962502c0c1e45000750340200d080001000c508100607051880c0040e20407140c40d8014083c00300001c14001161003000d01030480b140070b03141030428610502c2407103940c203101501d10b4841c408001580e542d450001318402c82c404c0070912020b042c250909440d10b000168540c5400b40140018045980d12000007172000c1d0003100c00d0320120034981000c04030090300340b002a4001c1c6141d5086007021282851201945d0307071143c410311440c000502c81034216100c08804901e04a41000701c18007080034101007000c004100140d8000c0040e544403110110f038480d51226540344404001c21a00a046522640c0c1c00020203c0c01d5165140198a544082405009126500b10034081c1d08920707079100400d0758081c040d441602d04400c0d029494204d4020340031140c1502c00d800707081d002c1e0a403920031b10540e0440e0700b003c4024102d0b40d0100162160341e802800905007055420711080c03034075590394000c5041c09020510201480d060442 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 650273606 1250 650272356 650272361
    0x91512040b3d23090a0e100c02190309031203020c06130308060f090a0e100c03050109051b3f15011110090819210c050a081005040203010f050103 64
    0x240712074003140941c00d030340e0301e20f190303039800e103d244a41101e1100d9117030b40789104d4a00a01110080700024411403c1034400daa52541c0104460412030b02103030709203400700c107042144d52103c00c0024000b4556400c100009800181d02000540b00350030050304013120b000420b03203003e008030707625800880c4005108042c0364100c0100c80e000305050701c103142d22079503500c0030451500300a401600150395a950300340418900f17000e00c0d01001d083d9141400005003245000b4007522081c00741e03104603880d0801049a000101428000d06203007141240c0c20007a0700394850620145070001816500014013120310b804881140d01c48181c040001c150019052030145550b084410030450760502421107900000382e500021a8600c0380403040d400700d0071004610741048a4060304079691002107003400407030301080d0030810501ca0141007800464041d1f010700d224809880300406148013040c81048090308841c0b00d8100c0c1a07011540c0304404594075500c4e40414101d0380243d100c50446503560f0001c0c0650343c1d060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 650274856 1250 650273606 650273609
    0x260304060c09140111010e031602130b21240f060a05010905060a1205010803040303140310120302030705161a0f030c090d0b07020102091512040b3d 65
    0x20300d09000300900b001c2c000300018440f20b82d801e040c046402007000b00780c0401d4000d00c500f203c0490a403a210b03007168801540d8000244400c03803080a4081c48010b884480748602900040001c141c0d18110081c07840301080d000c0241080b018600030003900e510b041d035000d09001c0c0c0d08442d419440c620b515100c07120b07811149010380040d100380c40120f130070841680c1c040405815504129042a0344038402c03501590000c00c10928101751358140800002c3c1e00c0303c048040d20449000b91074000b00e080e889501c81a2511085030000030303031124103e080c480c0b07a1047d4210f55403d482130045a15040e07140e1110382c030380050000c1c8501c988250010070311198203035202410b0007070161210b42e81043e040c000308940e46c1c000100a0b611025000ca8100e1307180d582e41207019072180c0c01040c003d88e1810a02e0009010390300008407170b405481e0050f9406450f86500e01245c0114020f001c03066420303221507407450619540500401012500c08154141102183c0c0c2e55034413241502d01c101002000303854050510f64882d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 650276106 1250 650274856 650274881
    0x7170f06010c060e0115081b0d030c080322050a111008041203090c03030804020415030803060909030c03040e010807090e03120405010603080c1e0606150726030406 72
    0x205090100903600180c81401c000c3e8400000714500d800450b000e070040400c046d50401201c50b0381c030001071403403000c03070380c445d85844030001d80480c5980c96050021000d4180c1c80103000894102e0000081003a20024580081c0031548003c08803100804044070422040004d868603003241030b52800300f2800040b41d0400003402c0d980e4800310303611104060145280100050800b081c0030412420403071080c2d000050f01a4081444541681c8905005001040488040340242d141c24802444180912100390449038068151441c2d542c520080c0714140c08050f101042c1c52005101160759440244003810140c50424100c082641c94440002c3c50450b0701d0f07111290582c9048510015040d000c0102d074401c009099207006203484074680a401002030f42e102600707401c004141006910030100361b0a008851000710600c100500801c6a5290841a110250f100603000d00c14074a072900c5070701910b0700500a00380c1e486a51048880d480d11103a142c2d06c103088000780042000104000c600c40c00d02d02420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 650277356 1250 650276106 650276131
    0xa08071b06020c1003020c0c0603070f0e0405131113021813050603070510090e0709060f111018020402040308041a0307090608190f020a02010b010201090506060103230717 75
    0x1500010031350441001c1c0e43e082c10150001441500f00c5800c001e103502004d4098050b541d24900b90f40c0050440202c82d1960002074002d500c00c40052905000307142c02031508007200c442250a5580d504075414626400c5030704080100500040b4020b140302500740314035521040d0702c05202017000c100c00c0803e011400b142c1030f4a0301042c0005500c00041080aa950582d211070a02c3d084010683e00da41643e400886004065010407208036408001d0004444460300c3d0080720b0b0903260740644407940c00c80d87e0680035a20251b0032600036040d640020081c04030200000b00900320b50b40120b0180d13801600151713204540050100000b00c08403220045140304140c042e8114202043c004180b15810711540f8100f1080f440420308001a4516410084c80301603010003400a00103207000203900032484240c003652138207552101a50040c050507019aa00c10090f115684d1407100550003091800c01e410780c208070b500501d0094401d4640003030301a50310381d2203602c110703003c0d50009036110360014010180c445 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 650278606 1250 650277356 650277373
    0x2190503040b0a0e1201150506071a071e0e040c0e220603060e2401030b24040e01242607051306030605010b07020f010c02032107020301050106180311030a08071b0602 73
    0x10103141c1c20340c842f503404200c01041d0745c80e0072204a0f040521059840e40200700f080080044641203a0000490042603500b1702c54138801c1e40b015500840080001c0e03030070103042c0000504000d40242c1ca01e01c2040350100c0015100c0d00c9071218030442d504c12849980b103a0008025080c40c44500400039401340c0d161007441219070540e41d92100640e000340031030000c448030b00d002030009212581e40300c0040318054403c00070078000c0d04074940a814510102080c5449411072081030b505030000c4001a6154907a13060300e061000c02c1040c80007054080b4514450091000205c0c0c0d941c0c480b00c1018008210440206015045042c6001141e506070310841d509c04041003050016220b07a40b403404440f0007400c0c228074400c1c80303002181c1010808440e208580030104600c0603140881805403030024000d60080066a803180d070305641c1c214034030740d064410390f920580400c00582482e9207420210006411307258a000c0342e0b13940240507002090304a9030920984102075032499941d02401c000d1120f480100810b5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 650279856 1250 650278606 650278613
    0xd05090f160608060f0904050c0103050702010b0f0904021c08120109140115090312021b0a0806040b04030909020a110d0306050105030615121602190503040b0a0e120115050607 77
    0x2410718400d600c01c0c8440000042e8480d5690910301307442460280251030303e45418a03100c0c0d103428070106800e000c68038110100d18444d105100d16681241d02424040d00a14008100b000c00d0000900403a4000200044400c0342100c0d071030b4400d0f50a124801c0c0359200d50301d0300c5103495081c034141c004500c01c0d850700d2110f00321346000980d120704454218107400c0600c0b9641c082201d8104450300040d0445000d079541903212540050300c0664000102001040d030440304c401c020710714400340f0560a5130b51144c004900402e80700c41c074481d0414807a0900307a907003039036501030306084c1d810480b005030200303c4024001e0300d010030a20013164607070303442c0c0b908110060921001801501010305468021503d008021030f12004c490100d411035003603c680310400303150041d4120f010300c0740210b50600600480040307080800c48103240d000c1c0180d01c08003540c181810035a40242d1b9400201c1c0c101c0400180380344038600d40c0c0343c0c04103a25680c03450400202d1401d500c03071002003000b8072590045015000401282c400b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 650281106 1250 650279856 650279893
    0x40e01020c010f02030907140a06030239211b0f0f01060e010503030c101a0301060b030612061306020a030f1b021213090b030c09010608060306010f060507060504170d05090f 76
    0x541d2b8142c2001a100d1281c1180c0518020b40d61050b440010a400304042030042ea01000400351008001100c00030031050720894008080e600200400c1c50b004d014201480819200e141a40c1c5070140458003500c84802c0d42e603140c40381000e98030030076965034003040c0528400072150343d0241005a00031403078003100342c0301144d9411620b0b00b00c400c101e640c1c080d0100216401d02c1039004140b4010000e1048030380380c0c5480a4140c0c41600c400c0d00c2120000100c076140d5902003402441020306103010056540d194880e60042e500000c103801c1010354400c0040c115060b80c0c0300b45546519482110031b1240d8240101030301d421002916013549100c20b00500c0c807143c446403072040c29140383d6600461358401010109282a00718110320340d00042003c00400d081b0b5211450510030342d01201140c0c41039994031591a0103072414000e950018104016030000715105400040d0010300c034211111815803040203500e8541c204040c5104a103455500f40500b82d00c04022520368000f8140190038185030141100381d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 650282356 1250 650281106 650281109
    0x20306070c0507050d230a0c120f120c050c010914010c17030c0d060501140a0813050133120f0302120f040e0702060402090105040e01020c010f02030907140a 69
    0x40120400706801001000d00c000e10082c100a00400a490481e160080c042e101107a00c182d02d242952000e0b111101000603400781140d00482c1d0845218180203208101445400301607507120784c07801d100000102c0070841c00728425143da0726420310000529081d0f0a1091003480e450401003001e400f8403616415200c0300340e41300000d007002a43c800c07681c40c000b98104440030890000301c401000300041c0545440c0240403007206d01004029040d1210b0064072268290b40900c0444001802289803483c0119050b81d042a18003074890a80c440c1542c60070f0945400b00079800006038101d031100480c42d0b521240780c5502181e02800d80c0c0b041d091515120707450194441c050000340300008010141402407000c0ca00303020700c40c0b01c9583d81340c6640700c0002040d4000d20400807404803410010b207085101155a5028a500231311000040e4a0304e020030020b0901c003098406107541c02c11003c291803000f441031000e5001030780000360302e070700d048600b450415545601012455015110145007a540d403e9001d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 650283606 1250 650282356 650282371
    0x40908030a0e01091a160302030106090b160b0403020c190503150c1e03070f1d010e012a02191a16050d1106070513090507020307082b09020306 63
    0x790381d1000d00040b03405000c8501d00504a43c030101e9a0780d84044034500f64610030f07004a8011494010079090450881c8024819000042c140010500042c041c0f9002040e1660000407005051300e01901e4140e00603000359000c90140c2c0c01074152010608119818030351040c540d01d6003580c0d0b1840c00012a454140603004042ca461032100040c80c0000c80c6c009480110a03a40c142180d41c5c1541e09000040c0e80c000e8803a0b0000c00c00405514102900c1000114040e200c080020400380030054015180d0000d600501410321504084020181441c100c3c035805041ca4202517500340340040c018024078154051114445003c840024021400d070050050400182c464145a0f80c0d40c403407410482d04100d00900070650f010361300c1c85010b07030317079003c0007010502c1e06a0090340c84a031103240080da09881105118001c6829104041203044da01e6030200368005620b006580c41c000c0b8a0b958408a9804020000300070001c0c01000c200314502c07142c03201c03541240c210381006611110380000355103800050914 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 650284856 1250 650283606 650283611
    0x3040303050d09020120060609060906030d0c020a0b0f210912030a02040e04051605190b070606080105011205010e16050d0507050603070e03061501230c1002040303030506040908030a 80
    0xf070046910a441480c0e4803e002920421100d80d00c5013103d850324403e0b2249446110000040f80052030640551030003424002c0081004d82c20141040e41c5100810300709a130b106181d08030005510f08a40010b050004080c2122641d60b010307450b04410381143c0070b001c0b0034003003403e07810171100039000501c0039000300388003429a44a42d110246003020340704540000346101c542e44140030400c60000340090601102440d0080e02076200c40521401c0c0c00c1c46144202041c825000c10444040071200610505010f1907003c541da60b00c0d5071a090a4400a078032104400310300181d14003d001c070a05c91030380d1654000b0041c000140070703440050041a480e000d898441c220840e00030301001000c000c3c04009103000f51401d9101d2820340c1d405042a610300c40b4043c028005c23000003441d035002c520083c0f02c0108058484410400c40d4140040100e03aa060200d02d66072810001401e00c41fa01704084645185001800360f926815031400800751030000e040c01c1c2c010b6041c081000b000809810541784e018900340d200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 650286106 1250 650284856 650284871
    0xa0f08161a0c0a15020901031b080106050703030e0d2d08270601060905040b06040b0d240803031918060e0a06020301030c060807050705071e08060a050106020f03040303050d 76
    0x8203042c8814442c0007013000036809501d02c00d514040d005020207010980701001030072901c035074408060840a040d10006100f0000600541e4000d41c003805100340a490002450208201014502420300c01306030007150280041251003820540602e070080381210308001d41012002025083c08005090303c050745034401010081144d807480350210300c00150046420550f55001e016111541038029580038a00b48240b44c5e0385810804125801c940c03694124a140034500d0017940010310801005c07500001298007045515507810450502510f4a80d02440c0d890422418404100492400e001c20075401c03c010703001290880d407484420b40341c01150206038070380e500b900c29007407501d0034400411a6102000100500c40b0004c603810503203e458484828544a06c0c40c2030790070b40140c180c024020790080c0310038010496940107001d252213448001c49145501c0307110850412030105c8440940c40d9860b0010461b82d503042010030000100340740a10314040c01c50714010990b202d0018440407681c0c03103542 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 650287356 1250 650286106 650286127
    0x7030806011b0510050103050f0703020a0b0f0903100c09170a03110c040e0f1002120c1303120c060c11030406032013030317130b04030309020a0f08161a 67
    0x302c01c0401940714041d142424200450345000b0402808107990740c1c458200c07500c3c0ba007040003c40c02d094903001440201c035185400340b0b40140e94490710751020b070054103000120854504205180d0f00c205800c0c00440c8090381ea14000b0a005429407000a08040035641140b61400104141c0b44080d09854400d101012840606203000e60440c02550040e140c464240800c00010428a0390b0800c44400e0b10300390440e2201c44010b90040c4444403a211080e00081503099400100810100340301840008846580392111030305a0400051348ac0856941c0c45104100200c40c030508905100707508120703041501a00701d45649014078021241030503500c4006103120400c0e007030021a840d100091890ba241500708500410145611045003c00c2d031601c00340e03e00b021480c1d5400d12500b8130346418400328015489004071070401510503404d0581d107458a4000d81c13580e00078007014205190040207283e2070031841a140c250201001b40c0a0a01c030308060207120a03001045090068002905445441810 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 650288606 1250 650287356 650287397
    0x10504060c2109061706090123091005090709030b0601030c0e0a0b1210060f0516020a031b080c1305091c1701080109030e040f02090d08030103060b01050703080601 72
    0x60702c40e2040102100c2c0c0c0e0b50180d5102c01c2042c00c0d100039503141020101c2001d0003541c80071080d50f01d0350b1300007804801800303a451040303240c0c0d507d007039901d1003241070b11000c1c00466200f010035140c001503000300741428011802e00300c1090360030012915116000f2403641c0c407080301000c40a8409410103440b6252028014410840040c0c0c9401c024552840b0f0307540c407030800509502586c03000481c4601c410009000f48e40c2c044442044401680f40c1d081c020030300d8401164140e1011809610b9809118070410150310b031929090050340c801e60a40c0031002e000110400c1391f590aa104000c664040000039a8a0b284c28401c508402101640800c054460403100760402003201c08a111754950060b01700189580b00400f0f00c10882c1e200080c07802a40c03034401486c2a541600d00140200300c0c80345010b0203a04150f0300c00304c661280c0362001418040303014005008000744003015aa507140110040c800d010461003002030440007402c009145c4490740c0d6000d4805100201028140041a502540c50740440d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 650289856 1250 650288606 650288633
    0x206010b0315032a0904031b2a081204050618040b100816081e0604020c01020d060315060f0e150604031a0c0301080c060c010213030506041103010b010504060c 70
    0x2000d5401190030508404664402082007141580080c80f260b036503810501990f80c0a147c00d0703900c00b95082c420702c60341e1118038802501200c5100d4251402c0d07585030342255224010402e26142c1a0441d454009454a08018408240000c1c0001c10041001307566000882c2c0d0640301070b64030042d540d42c0520005006051089046e40c10150fa07400d0020311544c800c42041c891a0790250302a100391003036408444620084400c0d0107440c8512003110302d07901220807417603401301000b4009490f000e000141142640c0024209903100b030b0f19020309104120042c4552202031f2209202005464900381e5002c1111f2a18407a0600a0300008045043c40d500254044807448c0040e04543c2d0781c0c0d03901d103400342801c554420f043c108040028081007144103850f00301c0e412036400c5c07002090344290040410035140c0c40440c960500c1d43d03003003283d158041c28008401006501900203000c181c034290515000c11104810307841c0c800d0340b621428a00c00e0380c002013604e050700c1d0689855103076650f852030028999500c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 650291106 1250 650289856 650289859
    0x80f1b0406080118050d0c030f05180a0f08011812050a0203130b190c080a1d0306010602010c020f030903031e091201020d11180105030603070e01141806010206010b0315 74
    0x8103c58100c1501d50381a461413094800d13011a902d21910003000c43d0840d14484000b400280801221a40103105e0009084503d0f02d0324180e0141402000000300c11000c0750344040d03050042c0308410401c050702807042c81010944024114001a2243d4925005510602942060100100744151316610030416203c1842262040034861926452500f10980042d003038100e0591844803d140114810b00074040400e60000140c0d043c06144001a2204d46400003c50a801062102808550780410047c4e00800c80354000041112001c50020708000440d4100713907281d4401c0050100c191400422a00003a60240003128251240445218103214101d101984039814421402c10716006600510886036040c3d0704004800c5048088001e9010b0118103070a0413500000800495001c1c1c802158000c0e00103080d1510162039455541c00c0810a8204031219040100d00040c0381c185600c68980c42c0107110714a100300e00d01540001d41c0c90105000b960b102070b0700400030496000c6400145240d0000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 650292356 1250 650291106 650291111
    0x2070b0d15051e13020c190308060303040b030114131d07050d0c0b0309031204031806210c03110d0b0a05060307050d02070c12030e040501080f1b04060801 68
    0x10600c285005458203074405a04800012400540307031a1654840491044110844000756803003c00c215203000d02c1c501407000349400b048032546600092100f120b00e005510b40c10b070717669192410020080d400042899010740d0080105020000c004020b5904441c1c2043c100740c003c1100501141c0c0c840c1c603005000500c1c50414280c440212848441c0d86144c40f042c108491a0b6969501000021a13001e42c000e001c00b0790141051048078040f500461b030103401001242d10381003a01d20380f441c40070400c40b020740015505641e910301100e140a40e010007881c140c42c0202525441c4056a181070b4400f00340c0c8140d0960398508030769440d0003a000400c0c4a0036204203d9187c1d80e0ba000c042001d044484400c0780714100742c000100d880e00d00581030b20f002e0304d00c07644d6440c1001c01200b01c841c0258082c05050b500c94540f5100040c022540700c00a001d15403003907460b0194050804240001d0394410f0300104420340101c0d405256007613001900103800c0b400c12070700d00440d0034110003182c0104181d8000700100d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 650293606 1250 650292356 650292367
    0xa0b040308030403020d0e0a1403011503050312070503061008100e0a0b0a090204120f030e0901060c0b06040b0102120f0408010f0504050d0309123c030e061e0702070b 73
    0x707202851003035000c0c0c2c0a94034800d21708032040b5420b035000d5240941c40b40c80d81e2018003a42c02d40180e031501030040035000054815801400380540042c0360700883d5241d00c0010f01006e284074488a154214000b0700f802415420300c0d400081d40341002c118020104911800054100110826484018440c1c001c00240c28144441910081c00c200721070b80d40100c440c40800101c8481910890b400c41d140408080c0c02500160348d055045021a54140c0030455006460040b075512620b6440c020000780c3c80300d881c0d82e042881d00c0341c040d4030001d040d5849030349840f64400c290398010442c0402e0004000c00303603548003c25031003001c0900580c0c000900541c6032043c10448103010b680300030b004030b008008407002c4004041d41101502c5191030300502017011021001c0c0e002d8000d43d1078070501c2c00010944501c0700781c183c1290200242000300c5a400b0078003401506811505442000d00c00000b580291440b4a0f11299107605200083c4032901140c02080024110a109010040152102040311031b9500b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 650294856 1250 650293606 650293613
    0x921080a0e0123010f06051317031308060610180b0a02010e100b0102120a090515090409030903030921020f06091801061d130e010b040c230f030a05060a0b0403 70
    0x40f024007030703142d4a00070108041025800b0314180c07610030f1082c0600301d02490070080760303102c904282c0c500c0205a00c024000e48424090701c8c20b14002030682400180120700c2d0510422002050410800050182100c0c2c5404403000d80003090040c0e40c20310341403603590041494124010007036250780c444680154400010307400c000e60801e0125440036800c55031500225407005155100d451011000700d54654000c0109061851103403030408203101815003400c108002007429140743c0c0c0001c800250700200705204054026003454054281804511202683c00c0c103503800c2200700c040068821203082141c805a9078035a021143c1000e030240180078542c171080110482a0740a000d06004600b2461300c3c81680001d0030000c4043c910000d02d40f0103002402c0c41d914006000c00480340c80b19540317905400440d912280281301100c02d0310b90380ca40c1260031480103421031105c00c83e20765102003003c200340f0000da2000303000c1c0e0750404c158150001d400d0b1203010019503902403590290403417400110b00001803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 650296106 1250 650294856 650294921
    0x406140d151103041103032802150c0909010906060905040f0f062408070e10020f010c050403230c1903200111011103010611030c030d0921080a0e01 65
    0x40d486045004144171281e0308068903800740c0c10080001030300010010b0700329076515030780c0600c81083e1b0043d181c11502c0c0e1035081803c030800300d07104407289400007100155400c0c1940c00900501030814208041c85c142a8003c11000b280c0c40741a100d262104000303680b2700199403252107005c4041008211556980fa007c3c00c1300b01e1100d00607084560101c0e5500000d41c082c00c0d00c184501c807035994801d1801010001c024021002e40703204d4007140b0034642090800711007441650b150000da81c0b159601c8500e1403514041001c10b01051030482c05003d030f91000c0c04040041c1c9041988011580700c01d09881c400b21740c41010710254405070410b0000d41c07801c0c0c0c446d0040c3c8803801d4511001c0c0c0c1c0b40307422040301c1c80c001070076100f01d01c08a40120904000401489100c0c80310003118041c001c083d42d01d030608200e40303d0729580182030030350003440c1d480d60b40f901040401895103d10a40105402400d00c94411020b0441d0707200030024801c00e0707110030880848039000c0d0f015150003190780c001d02004591400c1c00280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 650297356 1250 650296106 650296111
    0x1081e010209040c020d09060c050a2907091502070e0106050f07050102040303120609020307082805090c030120040519030b04030c020301060902120a090f0209160e0406140d151103 79
    0x11645000e4040b03555442740020b041201e40140c01448220f04680d6030302000390410200440110035900c01140945403c9801802120140e03078111045090071490303801071079180341800c1554400d003002c11031102001601c604413291410302646a600c403480e01b842c1481846002003107548002804002c15410291a00d1136100e0ba5408004041d02c03551440128441a1648004210003100244100d090548a54040c0071903503a05685450300081c41d00c10368030169106212504111454400c0f82024030841000350000c845540c1d40300342741036503491284114000c09014902801691610040d0180d1420042d1740c00304000c0c0c514506400c1c010314900c00e60608911079428248006a112464000d89445441e0f406064080d510f030fa074031460080401c144e0890321070f004036010340701580c2c500300c01911400c0ca04510310301d03840c0c043e08002c00b80742440d03411620032490b010007440f10701404a0003030b8020780d080d070303044890900c2d900b8040b400b5020b8503581340c4a14101800700d02c8624240f0091030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 650298606 1250 650297356 650297383
    0x604090501091a13050c0409020a090e090105040c0311180a05100f18090f050708100f060f06050d06051201090314030408030f04080c011407020c0901081e010209040c02 74
    0x240910a0007443c01020042c011507001d0075013030030000c4c56002d9501480e0450150b000d41c40c85c0c50f40d00c20200d01079030231546001020403095081088916000356850340d006011800801403803a1644e218015071640340400382c4211034101202615071503d80510f42078081c0c3d2080030000c0c0c500a05400d0103090103d034402c3d501310705044d0015100c01311b2210701c81030759401c91088106208540300e00c0000d000342c1c0c0f0301ba10660200501040490f8040c031080300501010b80241070451840641a41540d900103803001e01c030340c50000c00300803c00c01c40341c1c038030309442041c50807990f04d2500300600d502900f1941c000d00e0b4803a0646015090003041540812400c901c643c841610013800c0700c0804204c1d020403103000d0a10001000010030100b103c0078520384c4207104d15503003030800000010a0b070031103844060101002421324203000c84c25804000201d40404125642c1b0090b40c1082115a00ca03401c031450320103040c040000070941c0074400c1d01039400d00780c0041c00030042c81400b200c0096440d00b0551aa0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 650299856 1250 650298606 650298611
    0x606110106050a030b0438181c180b0f070b010f12030c0305132402150a0c02120d05010f0803030411040510080f0109060510140f060405060705070302040608030c06130201090302060409050109 84
    0x11540d180c0003181101142c0c868000701c050113002c6102c02d0728022030501080c44103544c0801c000c02c0e03c80112f0301814403044c41210541c0c40d00510b140c4a070488506170000383c541902c0314020440001d1030709103044007603814034140c0701e0505240f4098174540075072100c44003000c90400c0d000c2143c0c0c076030bc059254a50110004612080e581e140d0580c9c940e20743d400c0b9280c0c051040700005003240342c150080c80714042ca0f44102d46108000003002005608900e003903240441e11381c00100070101e500f402c210702400070007011b1480c5003419518200308940840c074181c0501c0d21400040c1d07040d905604110000c069410540c3c2c04110441c0c120740c0202401c0343d00711507862420010035002c502c00c6854a058414145404c080c5e500c1d02c03230400c1105400b212180754450300c200008604ca0b1a41409030a4841c8600020f00100d0704520401050301d170640c02c01d00032a0b001384810182d034180041c1083d0170442c8103440c8074000c140d900048400908541000c1d401450001d40001c2000c02548018100d40a41804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 650301106 1250 650299856 650299891
    0x5031b09070908070e04051501090510140907111603080702130b0604060c150e030d0c0e1318060504120305132001090302040606110106050a030b0438 66
    0x15100c03100c2c14000c0018a0344035034020302c0b40f00141010386070498098412141d0200380c01f03c0380c0d4840300e026041145da10307440d4020302c0030700920f2105140140c0a11140c02200c03501d40c1000c90184000280780e0010800101543c0345044024020781058120401c10708400f45c1e2241007000c40c1d40c1c09800100c1c000d240d5589603c030031810b10700ca82d0000c5076004000610340b034a0020f0480ba040d2054400740d8540f1002c41c2c0c07480811085206151030080504059038441c51014007000854040e60900c005020b070240f041c806950b40c0c880c00358801d40503550006115020400300c9000d07002641001000e003403500062109001c4480f031222072000c440d64003848207070b941498003001c0f40e6800100405451198543c40e540110768541c29482d84011302d00003c0041e030b25000101900c6103a030025004c01c04651044500071001e021b014003804059540d90302041c5155a1007a18207002003010b885100b03000c081c16020500413100c41040152400300e0405640d4030403000ca6502c000356084204802410039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 650302356 1250 650301106 650301121
    0xd02031b19080615120c2b050708090309040216020d0b010f090e0a02040e150703050a150f030605040201020a1a01170c130c0c020d0c0608071e03020f0405031b09 71
    0xc10140f9005084e2113401d00c400240c540c1d820140203843d60368162020b03c022001007100100d040c00701001100b03100201035881d0648811224050140410000306500704103030700c1d50010895140840c16140141c3c0c07803881d2031034420602c62603c4020342c0040a01c129a041c410f041c00c426040c0c94540d40301d02a040d984044400c21074020030b000303a6035900201d200001500c0e040e0300c00c0a10024071000d94074020780124550202d003008440c1c0c240801d9071a420705c0201c103184d00c43c412091420f400b02002c1c6604044d0280c12801003440000c03c0715450f9800502103910a015500d0500e50007281010322079007040701046250f0090142d014010001200d43e04088000944000300c500c003d4034000b048440c0d80805805030144c030f48020144240f0710300c3d000043c0c441c0e03420603101d217005031007a07034405007401c41c01088078030050000c0c010030811172262813108100c0806040030002321305005030b640fa03007250043d0042c0920ba0285505003d40682401d1448901c0c1d040a541c030000c84030400d4950700c019 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 650303606 1250 650302356 650302369
    0x5030a0507030605063d03110d110c06071d150909070201111215014104060503070206060901151103072a050303040b0d02031b190806 59
    0x1801400c150700401040010039040c1e840690000d80240ca0541c859651400c40c0c00c4010408862400103032000c030708030008020382c036503000c1088124541403204152005181540b401410381c000f038180d0780c0b90140a0700c0e104071400c5442c1585240151485847c00c2c8401621210b035120340d00d901c10080c0c21b1440045d03c2d182082004054004148a042440d01c1c4284001d0080c01803543d4299917840400200c81c00c105d10180160310a00483e0340380e40d05d0600c171243c1d480042240070505120411088604c20004d0451042e0721314103c00081c2d01c0800c0442d823420140c0102c412640c02d1130700003d00802d04580c020021841448180c003140c0043d01c2c1c50b0144540414240f20f814602e500e02218510301c1403051403401900c11030f0904503070510200d40c80d680101c0180c2e600b054981070301580341d800c1e841c11880d0340e40014601240038504091a04603040480c1c400c0840048480342d0020021702d9000b035014111030000c800704480c9072a4204204483c2e40203030300328003400102e0500c400090f46d134a40340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 650304856 1250 650303606 650303623
    0xa050903040f0909020102210918150105030406060f06030504050f070305030f210c04030302060a090309091e0f0e19110d080c120406140309070b0d0f02220503 70
    0x101c2c1ca0059042c9080e00d9200206808a0300300d0450040b80c00494007160f074100c0d44014100049103403076036040d5100805c2180e05850b41e00d0b1403c40c000d001082400c86103040002c410000c01e0a149599a07070b5450004020030a035006910a600483e001003074066066002d207102d94414401c42d40c007400342003510740d52540c1521008003075078420040d030407403050b086010780f103020888014004e40014104042c409000300300e8400020640114080081c940e040040a42104003d001007100c201661401404410b0310b0040800ca66117038042a0070900c90f0b0f0080c0e0354220b0302406c04100000801403200c0c0502400c070101d9482e84180c5400c3e00310080c10040300c41c49564000161303d11203640d001403100242a0a00545001c00c06101c1000410018030121840415044829680b5410420043c0c0100800f0780d800e5011401401007118a00e00011a4819142c03003441c6541c075981400211009400142c044040b00c500120302c0c01c110b480c03824651013519003524000009140c943c0c044c599120b100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 650306106 1250 650304856 650304869
    0x905102706020d02040e0a021806030705030a091e030906271a07080a0801031203060b07020f030f07030b09070e07020d05030618040f030e060f1e0706060e0a05090304 73
    0x4003600c10000031001c0e4010801070f4510103025041c50341e00c00c400301c0c1d110400c542c000e18407500065100340718078045040c02c0303868000322110744c198205040028040d000c001d0980d80c51a968142c0181841100c0d6903500003c250003041581e0b0119500d00108005e68910440003c10014201c01140d5049412510041841c0c0c84c013000c0382c44c1c0b4001d5440444805074903039201404042101c200400c1d451402010380141c030785c50785c03281540745190111442071030450100800d4a0454181708050040d404c4030b40d9243c04031340090600c400c3d0300008bc1800901521410640f059003800402c00c0766211400f841014914152170b42c065645099070b4422204807800001a040310b0000c00e0460f010300080d40e006117001e8030702c9641c441d480d40d840c5600d0605031825541815407540c1a01055400004a814040140c1d4424182003601c5800501400b41900040000c602c1c1100b42c81e020100001f9030b100960800400e01c404d690f0f40d40180d101160540f40021100e00b030000060b0486000401c41301200c0e034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 650307356 1250 650306106 650306171
    0x90a050714030406110301120b060102190206130b0c2a01080f0702070909140d300b06070b01030b150a030201050903030c011b170f01090902030f01090510 68
    0x82419201c03040d44000d10442d825079a44041220044020700a54060700810010000803905400d10394401007000f841581150300030844003030300b06225904c00c00c01950550b8499111800010800e0080400b40c0083c64540700c0414100c44143c80000c040384161b404420090030824200b03485140c040c0b030740e802103020420040101b02c1c2e0400c01007075598811420b1050f582d00d60f440c1c000413000d554640300d003543e000004051809400d8000e214809080c541420880c014205003410784201e844402d0881800112881c2c21404014150700030140b41000144072998418951a040303045900a02040c1c07800c48801001413880d880700c030031000c40880010841e989482c81c5500465260b44031070a03403030305400180000b00019100f405840d200c0380310164014038034940c1020040c174202d401d0407203046188001e82840010700340d404081e8150340707560002007000356050012a190011a0310140c03603e62802c500384050007000f113031044040f81c24074002e016500c180082030303a00ea44c0c0c6c4440c5d10710340f06 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 650308606 1250 650307356 650307377
    0x1808040b09011b0503030604050705070c090c09030f0f0b18060a1107150504021201060e060f03010905070f06300906060503070b07050610081c031e0209090a0507 71
    0x100000d01519410505140c203000b00a406090401d509480c8541115907601c04001c0c441e040c030303190007510383c0010340745003103400c082c0d07942c070740042c01c6401e8030640c0c10640d40c1d010700c81c2d1410701c5001007401454005074100711070170b12032401100f0601c65100681d8030005550100d5840521944000400400c00004001b2500c40416200052202d000700300044541004030a001800541841c10034061190001a0030301d8140144280311001c9011800c581e403528000307009002e00f0059541d040f52003511340703414015113607011900506080c0381c0a8410b108820001a40e81c44c844038100c10385a10340d42e2900c0c17169041c0c030500c4410340418800948004c91031131541d40305450394800000c0c140100c20100da00340c2e440d80441d041c01940d07000050240350001e003c0d001d104040001c03581041c41c0b41c08650000c0d02d000314440d146d41c4d9a101c0600c10f00400d5402010140c8203410080094040c030151020f42214080c5050080d40304242d154085c81d070500003d00203400602c282d42c8211666211020070f403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 650309856 1250 650308606 650308619
    0xc03030703081504090f03091a070b0c070f050304080c010306050d0b13021e041404050c09071101050a05010602011803020331031a2404020a1205041203180804 70
    0x400c40241614103189102c0203003c010b54540c05180142d9000d10460903c2c20392504008081030881e41203d1000010310141c03030b8050b082d6604460741240c0121044521b134613080c01000d4a8401ca18020f04104620b6507035006001001c4010320498040408540070707900044015420340c4c4a9220340d41e844064190b0000228200d0007109a10000385200c0004c11150f607400210001110380c0c0c04290080c41c2c1c8040c01d5607050510442c400040f09050144070b51070300d03030fa03400ea0741c0540490490144001c8004580000d024031100c01d085070400c8000c5c000740c071304040b074107005010034440d0800641c2002c0143c0f0401c0c00c150300783c80d80305070550b01452510310301300078541d010155039001d4009a49030040400320080d0304030817907000d584115003041c0290003030301da0365100f020003600665100031050001c000715000c0859030182c89c00e060f50003580703e004004050fa8004403401d01800443e00b0401000100000e45885d800400580d490401c61000700e0895541c0c0c40d085500c00a00382c040c2004240102d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 650311106 1250 650309856 650309867
    0xf010e0a050702010e07061e0e030c0f031e061b030f01050609061c0b041104180f09050f061b04060206060d05012d06050111060403030c03060f0609030501060501020c03030703 77
    0xc02c140d0300010030808861844640391482e103a0240000174a0564100c4031403440c4000c0140b030382a00d01d0180065112400000d844040801d440c511500f40468003500540f070910080d046401039a00c40302055202d4042c45444e030100f26501c50142d1a0050345540701c618080a89004004240c10016282e08280903c00c42e94080d000d06984081e092183d881c0000c041c9600040c030000755000407801c00c0c0010140001d0b101c600c80300c0681d8102c1408184404800e600e0010302c1c44d598080d02003800545d0741d00d900007d002c0040068040c0c02030302c030000d0034401c0008200d070040d070900e094110a21100f001c41402402140160340040e0001004940203140c00b04402070054002c900014840d5000c46802402c0d5650811990f22880c284001c11003804941c401c10001702002e003008081e0400350b2412a0f21041d005000400741582c4080c100b58061007980440d01901081e01140449500e03101c4c05000d0301070a2004803003660030b141b008202544003089064490801400071030420490303a405445 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 650312356 1250 650311106 650311111
    0x2a022b2003120d06050d03050d0203070c0c0e190c0c0807210207080c0103050103080a031517032701052b0204092901050405060a1b06140f010e0a05 65
    0x1003003000c0c000030aa8090044001d005540c192007503a5004820410042d50042d9000600c9205100c280d0340120350440201d803520000900c0040e40c941d242b8805a90110910170058030141c812a80030a911605151860040000c115900801d4114034140f03010340e110514a200004d40180e10b0900007109840a419120b00c100641010f40c0c0540c51460180d01d0105450001640a42c00c100b00e840710030320000e441c0c02000e2a05104540c11030301c6030182441500700b414100740e43c5181c070100a080100a00028000300c24403030780080100c400c02d9640c0c1d0420032041c1c48200782240307500d01c0c600c40004404480041a1030301801c0a10031044941c826160a82c0060b0b99120310a600101c8281e0348028000390607442c000040c074030041c0c001140c2103072810340300c0748008507140086030140c0c1c0c0260940d801c54400310381c490740e600d149900403a15440812880380c11101103c0e040c50800c6100d8200744400c0c0c090150441c00f540c0d60b5074450594400078415489081c08241c04074505410310707004144e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 650313606 1250 650312356 650312393
    0x615031b03052d010212010f090509060f06060c0d021b0315150604120c09050705030f0c0f04030209011403010b0d080708070c0803030a0c080c2106012a022b 69
    0xa03c2a030044a45080e030340811980c110742c0c88904014442a528901031030040e0241c40e07810045840e15030100e0350b6a03d0b0181a071000ea842a000144c0c407552a941111446502c1c5070584460500001020f580c46400200f14184891083d030f544649081c00507a484107040010300020030307929018071004501201c003c103507420010400000c50016181196440110b100d002000702c214600500300041356800382c40c000400101300140030b240200d000580350808011300d140740d035841071108040350740e22450f4002504000050000148050503082120380c4001c00c0d0b0091010713801400c2042030305111188000c1c00742d042804050041411705024004951081c1a10320001340ca44511902d143c0046950100140d152528104e03040d6100c1d01c081c2d08650042d030241c0c2401c00c00110f801241344025500484880303040001245684646206100084240c2c24989100c680000c401a2241106c2c0d081c0d003d01840c6940e03509007140150b0854503c46a25040d0440907a161340300b0401d0b040500401b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 650314856 1250 650313606 650313673
    0xc020f091b03090601050f06031e0601111e120f070b09010906051503011a01020307061a06030c04060e03060402130c0201060e0907091406150a020106030615031b0305 73
    0x11804200107000354010602c11000b403a00e50314100420400f05d1307500a404c0d003c0c50051060001840d0456a11480084450740007041c541c3d410004981d60318444070348141d64481e0381200741c150383d4010f03030001c45201c03003030140c81c02e010495410078101d01c500e0f0040c40708403400300310307031400700d0502000503400050000001c205e40d5841c0e10703488107688e03003502c4e41c0c0345006981e1440d144a103000d204801d02d4181d0b41504d484c85041c444000f030745900652201420703058540c0c2546804001c0c02c4c50104001e079004080e140c507400c0070380b600442904580100c4010610b208400c0e00f05240008185d842158000c00b450000308400c0550700107000402c1c401c406541d00d031080403505072001d00030345d8820a001c05c001d2a5807460075090030151040381e8480002c15000c5018042c1e107450b109100030342207c01c0c00c056581c60b00140001c0340140388a5002a201c58504160703a00035240c881e00d10000c0324000c0f0f440034a9180000a60103c000b4248001401c50b441200038078072002c003d80c0007240d03200010041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 650316106 1250 650314856 650314891
    0x7060608010501060806040b09160e0103020904060803030417090907031e0c031a060c03070201080702240411030349090302060c07083702010614010c020f09 69
    0x1450700390b071420781058011032001d800b00845424141b00c1c0ca80034003011114034219041c624641c8120021003440c10081000640706258264001e404484d080400a04101706444c3c3c0d0f82040303612500241d40448407240014410b0f0150f0b8012401e0380d5620000030401d40561722031810070780c000d004a0040381150111101043c440148901c2040c01000c6551008140000707042903510807681100c6415202e18401c0c041550031000010079101203c0e0f080c00c01003030507210b1100c01e034035103200c4a64060050007985000703030101e83c015060a008a200741150741085458504168590044411a40c00700d003240f0400080b60031200c0c0090780f920030700e910501e50b00030441c018290144055210707021030303501e401c0c100303041582c10407031076500c429904415814400c241ea283d244d00d2081710322090044070061108020125003550b01140c4001c000783c5240d101e086482c0181c080e01c120700c0742c3d001400c01c0000c640d40550050307c8891032150b000300f030b012094030380e4010401c03c0301c2e014010b48101d0802c000d6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 650317356 1250 650316106 650316119
    0x9010305101a0a091d0106030e010c080117010b030d030e060a0e0a260a1115010308030c0c03040b0703030f050115020703031b050706020a0c0b2802010902091005030f070b040b070606 80
    0x520714421000d14103105c05605100008d420740b0203005c054807041e80b4211440748000e91208550303064487c800540e02503082904c0c42c4a0240c00d02c038a0b07a0b83c1c5400791601480c052a09a4031800003000240300303580455031040d02c3c01c07040301c0c07401000d03842d617070000c251203c00506070280210031500c80c540c1074940d1a00c01140c2601d44e421040544010556080001c004e03902e080040034000310690725110300035810b40d038540003540030140250958600200d089054001c081c401e1780d0290100100381134561045042c010301406010020066041c41c0c5400440c00c0802c0c11086080c25101d90000c0040d030f891540c0458130413510059100080c14950441d0300013540c2800420f0040c200303a03000708846007071810300c45003c800c1c0e68440b0710f10400401400c2042c030340c950f410300c89491402e91041032034030241c14182c0c0034003000e1300003c3d8000002010820107602a01003030741aa202903040712107400c40300b0342c000e42e106980c0c05002c2800106220070404030184030003c01d9058480c10011803425520790 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 650318606 1250 650317356 650317379
    0xc3d181101181403100b0a0302060a020307020d1515051011010e0d02010e0d0f0c08030601211e1406040504170d0203070f03150605160c080309010305101a0a09 70
    0x402060740381500f90806000c525003000580300c0790b4051442084541c225000043c903809642c071000340681d1004c00ea0811803802401039035000e0390090010070303e043c0d40e490200300e060321401c1080c0005140410540e42c8803440742c01d400555501504c1c41ea0703108880e850544800c10340443c1300400c1d64951141036543c11091211a1491000b034001041488007520b0b030341c0c14800303000303403410070000282d540070b92241c1c3c070610720170a15400030340c040c0e039940718a00121079060a86070700c41c2c1c41000d1601d1f042c6502005038003591070459200342503048981160300d920305481c42a0403400e54144504c0c0031500da46444d50046411a116581101c2001030700d5101e00b0203a00016543c5604507404400c01c40c03282e0b002021058200581d00d030800600c0211916500807240340d018040400102098150700003000d02c40c0503812035040f00d041404c29a56040c0b0541d42d0740081c40d1180041d00307090200300c3c52900f4040328004d446000c9800c03040422000c1c00380565402c103205203001c00c1400e0000040d07907200c60 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 650319856 1250 650318606 650318609
    0x80601050306300607020619020310080303070c030f090303080a0e0a02130203040b0606210a18060207021005041809021914030c0907140c3d18110118 66
    0x59001c000403040703c800c41410203c2c000d04200664003d9400c000d6054101d01118500c65030f84680145c0366140c03040c4440113001145c10500003888000240103810307400101c00c403941c504c266a03088076495200e07001c80d0008094400240450420300100c0c2c0c0380c401030303007040b02d00218a00403520307000c0e85a00013401850700d40c4101c0000c0fa50010500060003405030020b54049001d40306146045102600c01c003c642c404000f107094035030b244003c40c5450600e900144c130081604035040c807010015040020007588645001ca02c2050801c022100c034500400a9038100e8041640c43e4801508241446024003029a0220380c054130345596800317550151100440a00700d007090b200300c01c640b090217142c6403a107800300d490b101c0c054590030406110390122002c0c8a510f40381d82cac50341e00c1e4171041c41860324002d40b1003d541d003015426807840510140b9020185801ca866400410450800d00200030031180381202d03070140e1904451409001c50342146549102020614100207074900c550810700b0014000e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 650321106 1250 650319856 650319919
    0x21218100909050c030c0a0507050a15021201050904020a05011409220e011a041d060412090902162a032a08150601050c06011203030f0c080601050306 66
    0x5507030207100034030751881100d520071220030109180d41412409842540540c4041c2c104003c000600b940c200710f0188500c1001a50203a04001a0300302185988080c0d0001d10380c0c83c4500d001c402c00090f842c98a0141c0501072500070306580b5500e0b041c10011101e80745140340301c016240381000300c011213840b0410481c036061500b260041d034103594903112009556900c40e2070038a9a051004907245003050081d1160481000c640000d8024080208418009105c036038800c8940207481c00c100034821500d440e40d0005d01c0c2d9545a401c0d580d2a130f50004101c0c01441da621400c8203000380644009032001c0281d00039049410300c000000ca01c40c11a075041d400d107d40048490500b1981000100600c1c8440c0c440c11007501e110100c1e001e0300704581265075810f01c2c684008014001c00106526900610849850400f0b000a8512541e12071181000941d400c03001280080e00e0300340400c5100c5001d200f01c2d105c1c0c0f8083c2da1000c0080e20740d540112001e4201400740340d44000540411070f0066007a004500d1100b88 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 650322356 1250 650321106 650321117
    0x6240f090c03020a1d1201330303020a1203021614070920030a090203030304030f090f230a09020a021e01021312061d060a0c030204050102121810 64
    0x30400d80505854000c0c0d080d505240c01888950101a041600003034002c40d0140714184602621001036010b10760740005d06800e51900d402d1030110710941c01884000300c103124415104130030320212111144070f140320282c0180c0184d00c042d4002104121a0303d040c41c0280b50240c14031042e52004030840416500840d0850f10402103c8050f10007403010f107000341003045040285440d4844010f84c075910741d0216031880e0800000040400045500c2000100c0c0c015040b291289028030300a804002440304000100d40500d00000d200381e070b8400703800c0941da00c02c146120003007003a02185422100d00c000e00d6900c50054a004513030070019101802d845180740e402008128920b5920301c11822850180400c1c50340100042516100d441c204041151605d43c1e007060149201d0400700010324680161705203040e400711414480d84000540c0da40200b02d209820032001c1802d041c16403c0344118420240035070001d40014a12a070080302511102e00c002d50307100c1e0368261150010380030642d06042c0d46d001ca41c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 650323606 1250 650322356 650322359
    0x9122006030f0f0630010e010513060e01023a051e040512130e0c0405030601060c060b04020f12062e050d2f071e150606050903010b04060506040306240f 67
    0x1f40583c0b52010b000702d00801450404940813241d81c00c6062018100a840b40880400e04200b5812121280300750704011103410b880e000324500106c82c0303500340610910301d110161450f08241c450b40c0c0c020700818001c4601c0060848508010340c8000708242d41c640985150b04811403d124018250721a1104900c0001414038440814181014008200c0c00100740003e003d9070304c0003d155411b4480a00707202d403581c9442e2801c900a0125500e1082c2c00a0010401103070544d507203000703031407000710f80c10740143d0b1540c0d0f49040c841481c81c000b04c010307841100100c41024803040f181d13111625042502e4441e1078500c039001010195203005001160042d03404114920500b40404071000303d681c4010494640811070f102d003116101c206680d00c03030200e898816501003100345041340e400a60364003010300c001d41d95800c0190541d0403d860150080d405d201c4403103814a000e100346810b80764000c0c0003a042c5411078442600500c6140d81c00300041c02405040341caa00407000881e0000c00304024202c2159 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 650324856 1250 650323606 650323699
    0x18080606011d123c060c0c19051027030e0105132904180c0918050708060f060313050a020d0b040203010c0305060607030f09122006030f0f06 62
    0x91031340880f0920700e084500d01506001070042011a084003e48010546882410311a40d050401d40792130b001c10000200464001c00034041010f40708031440c254200b10f0240d20349220000d006007418640036141c0b440c14032000090080c3da14140002c0185050390900c0c00d50704588800f11250303008a10110720000304288070041e04070380401d00b520050312050a0900d028034800300c00711108a40b1520710780307400307274142c503d0321034580140204036601841a03017600c10410007004003001d03502400012000c0002418030704101800d94290340014001510315600d9400607146440c010000700c5a034000c181b4140c0242e80e0307210001ba5105d00960044c0094103043c41014219909000000d06050503c401c0084551b10304082d6804540c00d81489105150754500480d0300d00d00c540c01010244601640103800d000090300004429641401c1204884e50690300704400c0d400110745400c40c3c500d04c1c80020741600c1030766127100d8010ba40a00009912900c5030306000c2d100e803040c401928900f450301c4608204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 650326106 1250 650324856 650324923
    0x209070207120b0108060912040909021f12110405031b040603063215010e011713020a050a05060f0c0a05030f19090333090318080606011d12 62
    0x4107180c3d000505c02d4484c1d85019064038082c60ac02d03a40020351752084e590644d21401d90740c42c80e040310804c3d071070300342c2c080700401810390f119904202100c1881e1141400b04ac1c2c1c1d90744102c0b0280d840003401811921080c03595099041c01480040760866290680007000400900680040b441c1a00781201e48030401c80d807014090602d0620010490f0101043c031880524220310807400322402c0c60050b06007500080181c6401501c0389450003491032040422850041c9141c611203500c1c400c0f2050b5401a6448041111040450203940d5002c0c604000d41e4a18042e940000d00c0c198011009603251881e032601e07003500315000f19a43e040420800a014601560480007290710290981810400b860075521403080540408600d5058007100c1c000c0300790728244001c2e51500150800405005030080c0789801030440442c81c0300001c2c051a1014003168410340429650701c41c40041e0b44040e820000c0380c071104c070884010020310744c0143e04502d40c1d13100254188100c0648562580c0c84550060103918030940 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 650327356 1250 650326106 650326111
    0xe0d0f0f091a07050102070f110f0d080f03040f05121803012d0f0e0c0406060f0e1003230f010b28020c1305010311040501120209070207120b010806 65
    0x420550300c00030300c210a208102e102c00745180e2103150b62648810304d0011300a1182000c09000c00071600048020809032080001e4882c100350781c02c248803c0700900384001031085000040020406021540165100501a581c81806018003400d0080c0039287d090a0441503403004806800009603003400d50802070b01c0060b1100c00f940200203030b50307102340c1c101c030b070b25052954800c04410900d052010b00540703a0004446800c04400070404440d458001682c0d070040c072804580501c1c1032540000344980141e0920200480c0ca031600c0000000d0340040045014042d682c02c0241a0b68410403900e101c10170f030107140c0115032030440701028206107046024842059024a146400c100318a204240d0700c0000600c020016160700124589072850a03800c0c1700314098a10713017000605448131089405a0803c504a80c024140404000c602c201480180d8009006658983c6003c1c02500014140000b2140d0b01219520503120305680b505c406000c2800c600750305991001c801d00052000341c1090140303e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 650328606 1250 650327356 650327387
    0x305011401020a1203110a020c1306260a06180203100c020c0613320406050a06120b03060a06140f0a030f0c12030c030f0207270e0d0f 59
    0xc010000440001c0d80c1d1129107100a1080082000091005020b508a039041d155080d02968a40300d007a4002542c911042031040d00c40c110900145200f0740300b07031240009032440f0000c400003145c0160000718490031020000c140c60b10901300500041407840c42031030303074244041c3c50f48181002503004046c40c000c3c5407114000040d10b0079030720b18126a00010405c80c440c400361081a11683d484012081c0c60015501c0386c0c03030959004000000c900c4050407031141c4100040440b801c110280d80c240000c5902d0741c09496040070000800307002660181e80300c1c846600364071b90301007948604100030a08242c02070b1804940340d80c80300d1061056031401e80c5a082d40000541d0014800000f02c00000c9144501d07200140880744218820824400c041c00e1090141c00c048a4404103030185240040c080c0750030040070350000b107094050803151440801d94408807004103038031212000440e840569107200b4050300d03002c550f80d503040e035411000043c009000c0c03541541d02e8180500ba048100581075452984565 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 650329856 1250 650328606 650328629
    0x30903180b090d050a17030f1b040e0604150311010908150c0c120a05120a0509100b0109080a0605010905010510050f030613050f221110230307030501 66
    0x107008606100c4166441c62500303d030080480ca40c941010303424808003440143c216811a0703403404c42c21507020f00640c054030720118082296039a0149001e010705138600200c0440104000400440c400b190070150010001030001441807403031503240807807a516500c02c484c2c0c001c01c007448032a13940e0007880c1400100342c810040e2003200e00d01061080040002000c8e8800000b002c02c0401d80d200e030811510b80d0034055203150320741c0e0f0962803d0240081c1c01c0300441c460700000000024a100758103004040c003440d0094000d010001c4043c1004000e04000f1100d01c0c1000b0713032050b0014075000d040143c0c050307003400f8110004065040102c5203050f594142c10150040c00400c12000c902c2d6845030490703c0010182407421784a4507160001500810004002c00c146801c1c04180041c5101e000620b5000743d4130a090401d0075075140800e29025403c0103c090000c00c003036540b002c80f47c00c00070400c641c201e00314600b0428500128030a400c42c240404c440139502d0360080104000550144aa980502040000d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 650331106 1250 650329856 650329859
    0x15111911010b190302061e03010b04141206040b0a0b0604030b220506011205010f060b1201060206070c06020913021917271f090501060b031003030c050c060a03090318 73
    0x200014600c1c02c3c0301c000d0140314009101b80125007e03080c0e06a4a030000c09086590b545d6542035454160031600130310102d4400075011398810b2406201c2d400d608a00310004e410a65155100e1003e07014004000460268450074411404d50312040140081c40c4118080c00503414010b281401112102001031048220b110700c10002c15000528581100c0c0c8041c080c807901c000d1450090302401c402d00d6940700150400700c01054008031400a028032203400680000700740c6c4c0c0c07440300f00c1c0c2e40c0c007007501d20030003040855100a012a510703800601030241d0152980c500700800d00001c0c001c0b1303440901c8080004640e804c800300041e0380100003680358541561100c101d410924040390b0003c081664910301d0914407101004044001d20003490511034111400d071404c800c8031016405000080f40460301540b800340c01086000c920b905580c020900401d0f03960300e05080d80d90036a0202e1441c40107032440e1062220510542d81c4150041070003075190794020403004c002d8a4080c001c00b01d4000c030040c3c0c18440140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 650332356 1250 650331106 650331139
    0x1d0106050109030803090f060f0612070f0b0708040e0c0c0d020102071205070f02030706051909180506030a08040b07060606080412030b0d0c23030a15111911010b 71
    0x742d1050b40d4000c1842650b9458003c0703c68038081d44c2101c10803480c09061708001c2c80d4203208801d18030404042d59642054108540c60f035031200845d0045150124080600b0f0240c2030340e0401030300100784241c01c141d05c0c0c15121403113966100307004c640184400c2d03400138204d81c03100c10521206d2103454481c0000e6051030382c25510221305002a051030400c004d001700e00d403414480344107802c2003a0341d00501a80c0000391203010040190380540046421605032100c6560320b94440d01b0344008858503c0020728440c9400b040003c05818007605465251103000c000801140c0300c0c400070801400e0916441e9a202003e1504c1000c1d1602036024101784040401000085114441c12602040c49480c00051403600c65001601044d000d62000d0b0020402400110703040006001a448844d0041040f1015402c0c400415907102c2841e000103202140444e1203900d100c030240c01007079905068104044c1821100022005808038014110300081d003011010b00b5001c40a00c1542c1a040c0c0c16148411202101d98 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 650333606 1250 650332356 650332367
    0x30501140112030c0c0b0a0c030201050601180e070203090a0b090306060d1e060f0c030204050f031f110d020a0203070c1403070506070515010609030b24010305130501050a1d01060501 80
    0x40d4054103100c0c85201c501c081040c00500320700076004082a41e512900c01d071400070111140c008c411800340d07180001248496000d039100c0801e104c2c2c0c005000031014108030703081600c1c05000c0c0400042d44014070035900c082d03407440041800380c0461010b4940724030304002010714124018007524080c0108a04000201c0d001010070541040000d4001540c0c00c098901074009001441150640500c0e010415206a5041d001081200c0c0100c0f403a03000c009403001003588a101941401c0c4050036005100040450180c000c0c20400c0c03102024981004440a2100c0c02e0b03901a018a8005800029940081000c4004840050600d044a603c102c403070000201369150880d01981c1d10500010034000100b02c41008400e2003c404103014620780e596503c00a0429035003800304892049840700010503040f03110441450400070b858140c0e40310081000158000c01d0041d022941d80700c0c0f040c41c0640414024040c4e140160602c01d07000130011070700508401112817002d1020700590421400308110780e0f010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 650334856 1250 650333606 650333639
    0xa0b0106170412020c040c030e06010e1510030e0303010b1b0c01050406050d020918010503060f0402061204030513030309090e0a0f080a1b03120b06030f0121050105100305011401 78
    0x40c0f0079042c01c0d0100032050345800c2c56085000d80c0a410072151043c501d605400086902d0f400c1c4c4101d40140e40c81d81010a82100200c0d0b102d0908000c10400c2106071500501d6110940024100002d584120800440c15540243c1100c03290020004550000c0d40e010024a00840019000707800040a00740009285203d14811101000301c0424040c0b00610150304548810000804444030120b41940c07800c1103d100f4070880d807090103040c0004500700c002da00f905109660040c4542d150130710300455034844540140064080007003d07c105800c3c903a01c00004805036020783c40b4044e91500c0d05100400341d40190070040c05a070400a002c0d1b0002d12003003258440181c1c0201201d4581d8400c1004071982580d215052524001480280085c150041403c601c100c08450080c011859040b01707100741440241d03075070b000c1110ba0800403c0b1655a0f1a60300c60b801c44104000051148241c540d071303080d14001e640c1d00080c581032000810070094244507545040c00c031b08201105540c0341003a03016402402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 650336106 1250 650334856 650334863
    0x1d030309010c0804420f1d040516020f03030f16030608060f10170a080d020c0a0602041d0f13110d05150a0908120403020c090901051b040b0a111e0a0b01061704 70
    0x510400c41c0004174011f4031a11043d40548104568907060040e014801001a00c01c80580a5840b114910750b1010044901c2a030b0414004280740d1202400400b03c101c1506005080680d51070000c561032400740310071030080031250080100b03410003100b102e20015107940243c1804400c07038286c1e04a41e00104240d0445c0380c00c090b040e03458138000034005010340720b041a400d1107030260010782020000d080e4040d005845c21243c9141881c84000d00c070361442c003030544451401001c11000500d200741d1016290b012244110103c1009801040100d03820020014046443d40c119002a1f05500c06955a19900c03c0c9070300740074440d80c40e1a843d0b6204034480d07254082c2501000c400043c0070b06008001d01c3e04100030103030060f25940303030444d41c0703500900c4107403146e900c0a00b4800d261a1012076940030b84040c1c9020440031490003c042205850711f01012014070321134001c07006200a0b03150031419592142c9c4031b02018200300010f0b480c1c44001100305800c80401d02c0307451001000050711018149034041d90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 650337356 1250 650336106 650336117
    0x3031509060d0206071a090613080a030f02040f031103030a08040f050703120809012433031e1506140714010c1d030309010c0804420f 59
    0x101c41d40840d800e0054074402035086480024081e0401c01a1607020351510380d460344c0400944c4070b885001d611880151454112800042c907072001113401c64000f8010701c0302c1c9041c0040c16180d5616107400707a811a6120305070014a800d0100288401c0da548611524801c0b00a10324040c40490301a022900260000d0b1999283c0f4106000f042810000707400610380282c03407124200040c100c01071142104a950744101e500b42107024000707550300c080f945a0004030002c21100e46041411521402e010399004900007200e0b001841c05481700d0007010004141c02d03903400b00b17680b10b4401d0303100d26411301e40040d11401887c08643d030f2030f074901c80015039040d1849480d0105000c0c0000d08a4a0070703010707550740031300b0449210603180740d070080542c45501142c00c01e8550886140200083d0381070301402d03102e4241c05400c10400c1808070b41c440c03490004103500c600104e9003002d4484084081c81c1c0ca40340b883c41c00e031030070b040c0d42c80c18090a60000221011102000951034160143e4001c05030b445440d440d030305025 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 650338606 1250 650337356 650337361
    0x30c0e15130e220f0501181707020307090b060f0c010f0507080f010b0f07080a0306060e012303090106030c03061514010516260316080106050a181203080f060303031509 74
    0xa840c0700815104d50000000e01024804a2803010140e101440032505c6a17482001c0780445030105081e980b81c1a0020041c0c0b9010380380030030030030190020120b000e91046080000d40c242a0303400000c0c0808908070000041d80e0011407611508881002c3c007440e050004200410460340340700c0c2181c034191822006202d484089264500005005051006180340e0012074403c102c154103510070313422601d20341d0b034200f900000c3d0001910655001c0c80350207101c000f0300c003140403400d80100047d80c006400ca400060170b2a034a44401c460001300c0d030000c841c05600e0b0346003207102e4020303540d0034030240400c50081c0c1c15800200300060010310030024407001d180d012401a109005152030707542100c07001008480795a030403008448080f94011036481c43d1500c24440c481c15580d00c100340c1141a25241d469aa282410b80fa10549036810540810884d030004d042011408945a0212441da98865282e5140c0c90500843d00c00001038000c0c100f43c000d520030f2003008448040040d81c04000303142501e01034002d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 650339856 1250 650338606 650338613
    0x3130603090f3302130918060b0303160302070801060801020f04052707020114090102122e0f03260307110a1202030304030801091803030c0e15130e22 66
    0x2003c0341256400710401240740442018102d400402200540d8a404800750380c4a0903c14100c1c0c85c0ca64036103004e200ca041c0741e5800070341d059101048401c00181120b0030000181c14281e80340040c04800c40044e0003944080002540034011071003d4000300e4021340c24044000000e50a5000c0d0384201c5c2e03c108140e054000f001d0b00543c00e20340203041c20002014443c606030070064007804081e80500725161a1030001841d922043c42506e0031042c0207008240d40e510384858280d6445060b41c096401810f02c126140d0100000c55890001048115540c00c81d8600c2c604001d058041a15054100e00d40001ca401c1d00c03290424080780e5100803a4101090321016404a803490540d48810060500f400005070030919038001014512171880782d42c07420566a200c004105c10340c1c040c13201c1c00f0b0211101400040c0060300a0b04070030388501685c5080d1030704195600016030301c2c1c01c20180c030f12000d4034002422841940e42c00803110240c011960980307101d01b8003606084a0704100905149501c1141c034407007081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 650341106 1250 650339856 650339903
    0x1202130e010b031b030c130f050a0506070b04060903021f051009020a0807031a15070204110c03090402071406070e10111f02091908060604060503060f060418030203130603090f 77
    0xc1d041f8900c400058a44030180ca480c50480c6000b0141b0a18118100044034034212040f18a100e0f4070141030704840d259951482c3c090000b000c803c6042d4054080e042145003044192103052400e40c00c004511030070890b5020511141540007041c510380100149203485402c01d10300b03a0803881a20b40003031010011020380002024001e03819920200315480c91800b03e1044014000e03240c003c941c00c02010084440d89551351151800e0300d00c0940041c40803013064501a8080d008030750040b0054134810760008010727410601c00b110044080f90b51000c0020300c50070541c1045500201a05014624904000c242a5502045407190b00e9044e05034070800c80400c001d805555070b28030003034408892014544401c3c003540c1d80c2c40c01442003602c2030f200042d1452410b4024030341210006009880241c490f10694070024200400d01c41d00b0648810120f01e0007140a000c5514841c01b9502550301c0340c8603100c0e03491000d94507512050401d030810010801107030f04124102c03c1a40e024030039541c3c10003090034000b003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 650342356 1250 650341106 650341117
    0x7020f010e04021c0b04060e1609031514060102070609030f020a0914040515060604060c020f03030c03070204062408090f1e101104090209011202130e010b031b030c 72
    0x30403d001080c40000c10b03d4444426110074140302c0b0a0002e0340c0e40c80140701c1194003520612031440d500d607011900841d130700501c210301d4200520308841880d850b502c4001601c3c400c4119038241b161745804c10359a03801c0d1418603603000174007407015202c41407500320014089080d500015102403006195041155100441d11000b0300e03c410b401c0c40150b82000280c4a0120110381c00d1760b090149a00c0002d04084248490744642801088541482e080160071030341c02c03525201c200d8010300344000c614055601000500703001c1021100450f07941f6094414002901c8403a8031000c1a0416400c1c071050452164440c0c240d21440d501d01800c10355903807400c1d145000130b1011442c41c14001c030100d000e5221040c4054415029101045580240000000600f03d8204104103051400184400d100904180e0020920000145468180700b84c000240c8002c0381d01a034803e00d00340800c11000c0010014004200740140302c4590050300f1490705d090f00d1641280c00c8400b50661100000000b2035460360700d402d946 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 650343606 1250 650342356 650342359
    0xc09030a0f030f080f0907060e01110f0304090612390f0f082e09020306130204180506061306031505011a2b090f0c050f01030203090307020f010e 64
    0x1c046401e41c10b000c3c0049403540324070b50004141d1400104084615220980a0b0034960003c0452500e0070208954420000300039030304000405a11262815003000780f05d400f5011074000d503980341e290052440c21551998020480c104800c00302d400850600540c01d9070300c0c0d4411a107504281005a0210180c0f100200a2030601c00381c2030010880c4031902c85e804054403a062543d00b040e5490303d02242d55443d40101c04e81c11522102c03c01c1085050481c050341d0240700421001c00c4103d46980024140741080f2800c4a1a540303c0a40d0030035490580188000903022014450340c9d60000d40304c1d02c1c2c444400078806030003072841c00b07691403002c200d0740c1c400b00003141c00c903504450716090a40960b010705400e00c40c0c4105e90740072108400c0300e0000001203469034000905901070342448941c014401315078114141d210503a03103003401d0703012640c08003001c3c45180c030aa206e102c09031b0810040021150340c441116040510510410140c2d00c2c0001c00c43e50040d03012200014103c448070300494031000c0c14009c05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 650344856 1250 650343606 650343623
    0x105040308070605150d0f0f15060611010605010804020102070b2a160e01050d030c17070f0b07052104050c1002010903031a21070302060403030f1b08030c09030a 71
    0xc400c1c00b1080e40028003502e0081c072099400e81000080081403000341001410400c0301100711fa00085165000641d401c0c400e0050240c030300e0b040d00e4088100c07000c40d40301341c0101d240c901031090340c00001e125800c0546400d0078040d1080c140341c0c000035580c0303541e405200c02e030700400a580d540c4030103c015a206034110800c04000700d2069030255649898580012070f4101c841c645000ca1912204186d01c0c0c1238036400b8000e19510301043c2c40448985004103000e5812070f4281e41825400454a80240751090059a0f80d103100309813031409042e8071200514500c1004814060140d1513540100000080c2101d1400a00700d92500e0410341d04004c51588000d501000c001c070421b90094064200700100d500a0700d08008000c0a5000420480c0484071002d81c403070050041c10045074401c60502200c00d1200c03007121411a1030b5404a00c450344183c03c15008030740741d400041c2510703500000c42420b012080f000303001240c640d6980c107180d5000142c06c0e410002d0000c2100d6981ea14100303d440e48103900300c03910 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 650346106 1250 650344856 650344867
    0xc0306040c170714040f0e010504080415180302010e03011b121505030c0d1a07050d0b030c31061503050705280c05030a0f030507030e0316020105040308 67
    0x4452408414410b81c2d0001c03401c0041140c1e00200420000100c40c8a4840d104151400f001008000c0c42405500d0418550359135035400015424400ca5100c0c6108040d1103940d40c0c28111121604000b14030240c0800c80203030b501c108820141c02404040329420708280c1c1d4082840780002c0c1c0941040c24042c00c41807010306040c15459807004401c04503c58501c8104101c100403035803111800795134020103402d039008000303802c61814504001c5040c280074136a0184234205480c411040000103580d0b0704001140403800110003202d030710422140d000d08a00424482c03c0c0400800d000102810761490918030304548580d18441e0844001c50030f03000c2d0001001740c25100c0841c03000d54800802001d000928000c00a005c45015408407000a6840144641c420310031604150184c202001c0e1501009401420306001450420252045000036102e40e4060138526a0090403500c0081c1030104044c00c080108007440404400c035104150080900c014540d2035000680d801d105641c4000d220140c00900c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 650347356 1250 650346106 650346113
    0xe0409120207061e0e060d09050a0605040209060111060a0e030c03040f0e0106090302010c150b060c0c03250b130f0305060f010b040f2105010204170c060406200c030604 74
    0x80140a4510644601d003c21200c8500b00700440f4130403050720042200000b800c111481e18101a1100c102e079072034040b45c92951940c90700e042906c0007c0486555444074203200841ca40003c00f00d41c00042072070000342d941c0030149615595000640214250317a92520306074200c0b80140115030100c504081107a40d21503541c02840704103035044c4102d40f0f03411601400498454070400380308040300d0b0143c1d41c000c089a0142c0310311415010b403491030300c4600d07910790801086840e80405080380340c601402411800e1500740078142400000c00142c1c99175104820b0404421041221003c00d88050185154441148030390201c6807071038030703000000200c0184a0020400500003045441801190b01c5d000e80c41e41e13078040e050924040d500454071440e1000c041031145503103c24007402100c00e121700365195903044c0c0d04d4440c00c82e8029002a075041040c452813090740c2804001c40070b41000c0550352586481c2c50118000c00c0440107100c1c04801e0181c14200d0b00021208002c00902c0010040944100d403c0c94034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 650348606 1250 650347356 650347363
    0xe1f020a0c0b0a020303041205090d2406081e070b03010801060f150905010309230607090e0c19050c070f0608071107030b13050f0102070b22030e04091202 68
    0xd0448071065010008104030b50b1075400c0da0100308071500118110703202d03990703054890100d0044060030018184003118099a840c40300c0020701d8051010510741040c510504000c2c0c0e010810103400040c180380041020400010740e08031070034200020102d0300b01c00c01e41400c1c14102d0552102501560101c00030540b18010341c00002125214844100b07039a07a600030400d0b0900c84611840c0114401010030491540643c0109400c5403040c1c00c0c10131814143c1e240130010fa903c8180203c0b499000108001f0f9850b08003565101034420203007154007500d050006561a4170400040c200d09842103030702d44802034040c1e411303603c5406042c0305862985480d20702c1020f05490920440c0b0020300342c40045038030303176000d070303000030036144200c4003a1081c0c40c21900d990f0030b414006842503e6115140611034007081050080c100c0000c016030025a840c025400c158829040103030030b0880c02544526040c4170800200020504c995060401c090320306240300000b0010010000060842e148000e000d10440b07a010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 650349856 1250 650348606 650348623
    0x150a0e0a02210705121009150602010b01051806070203070812070611030403022a04020f0c0105100806041707080a1e0302031006030504050a0204020a0f1d0d030e1f02 73
    0x9003180c044002d0841c664694120306071002c00201d88100a20903411003500c104a0340043c0d180c6200001c20b42c0c40520310304565401c51500f0024151030001e01550f5428054900c0700503003480e081d41006100c580e5150f0743c0c2c2c55140303058444c01d1700003201811510240f090000a10b00f9005480c42e101c40320121084035400070303100b00c4130310340741150300b03c580071514080d00d0185400d42c3c028106520724100707610b40c0040d40c2c00e0611040340c1d040c40490556a8900007060320512802060381c07210f040c08003460070751740040c0450043c141010b03010b0240700400541940d205030000182940c0040d009509840d501c55490040c020b888005541440c441d0842c10701d010b03190b010f00000b040411461004c8007240025242d44200711240f6100304003440c800e801540d0400d0141007510b02d030020320741c0082c0032680034049040101c0d0084410207811600440011415442002c0361407003800d00800081d400301a0400c024184482100940055120302d2004c4407032441c110780c140b4040317040180c041e661f50101c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 650351106 1250 650349856 650349877
    0x19120b04050c04091a04050a080c0102070606080a171e0f0c0d11031615020301141e0d060c0e040906050610020a0515280203070f0f08150a0e0a02 64
    0x180b040c016003609061240010680d0802e54045145225a1304040c00d124040c10a8a0a200d03980152001c00c6600000344401b01d003103000140d84240929001c1300b50780e4913520814858012400080126006a00a00c01c02c10305a915695074580344d034400710031400c90505040e80c07400128600495012101c0108080f82c0c4060494110000d4407008071900070a41039050040d810a11213a00c01140583c1c090390200c0c414207040d030441800c0007000d01260401d9022001c4000e501c1c4d0b0109a81c00d089880040852440103811240c50001780445e8000c2c0803804020101ca60b50740500310214422030b00003610760320090007030041d01160708144028210580702c29110704488100e885d1600e000150320201244d115014100b41c2e039a5140302084110010f20306040c00c402403030300902ca84651a02e021b9443c604e00300050f100e0410460060210030309032009010300c0f1828030220a01d0713802540c0203502080042c060b54004415102041c000180c80d444400c6001c05041880b4000700c8680150900d00c42c0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 650352356 1250 650351106 650351113
    0x3050706050903031b130b03040b01090501060215280906050907210206030411030a0b330f030c100e1306030c0303030f02131805101419120b0405 64
    0x10b4100895407244010307180d04941c16200a031200150b08108040c01c8100786070348800c41c24503a9402c03040070b00da001b12011581e48404c0c0d4018030a11000303228060241c00d4a100030241c00015041040030b000010702a88001010840c500c1c00b1521403038000b503100c001d200f109201c030380b00901c2c083c80a00019255007415024002c000301d040b20140c2150009a400300034649403421942c0c0902074540d2000d842669200700c3c1700c0c2140d80e151810001c2e4200140b2410b210115071503c00810303c4013004103484d4081e4800003101002903040740a2240507003000c01c07954168809854400640f6109032980c031290040100d101e12650380e038100207060107452065900e050210385262080003141e41600008008105241d8144042031081d40165120303801d05030b0052804000208015507125183d0060084400780040341d00d80950b01c0c09019040b440e41071940e0242070074806041d81150309086010b004286c2824034003886150a21840001e090008284061901c10708000b03901c16011038003501c40d0310 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 650353606 1250 650352356 650352361
    0x303050a050601110307060f0f05010315110702090f10051509120f0d0f0e130603060b1f0e0114030a060305070f03020d03120f05090102030a0c08060a151205040305070605 75
    0x50056144907102c032113a90146180860550314440106024284001a0740d91101440903070640340c0715503400f03140103c0c88441c190002c00c01c0c3d102619903000318a030703402c00144806001600c1c0d4690494201c0c079280b00740900d40e0340d8410700c0c2051200319800198450342c05240da62051120f0380c020480ca601c203540c4011000300b8030b804103030b56007004804400f8640c000c0c1610401207106a040c210715481b28641080e0307050130200000c440c1c05040d0b150340c1a40341d5585080080144074450001c0155095a0401c2500d81140c800c8a049501c0c04108051004034a0201c5050303108003a5841c0e448028a061503d23401c100c50480001e140e1400101c840c1d01c12000c000c9170400144c250607044076801020700d00008010368088407048201003103510959200c2d4010140240c06015540c807481c941e81c001a100d1400c8609501074490002c1203405000c0c0e01028071403103844514068055440c800c0000aa50030808000c8500c2d034500218001400d2500051008142d403020007004402c0c01001c05000e03e8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 650354856 1250 650353606 650353609
    0x40c110d08090d080f072123071b110d06021602030706020f0309010e010c120206061c020906100504170a0b0f070e010e0f030706031d030405090f04020312070303050a0506 75
    0x20b5003642d4807017403501e8403c0080d891071b12030100c41c07420304103484400e2425904030340404280d070b500f035120b04c003045a03035240004054000b03e052684a505403620032000903001030a41102d401c0d1000242101e400c4031142c11068503520924420203502400441d503070190321041c031401030401c51040303201c0d0040c200c002504a100180000700a000d0310040e600d000c00b134000640f030701d6041c00300c0710303060124025100c408910301c0200e0381d461500c2500507010300e2910780d00b080740d444540c1c034550801200c04080384001d81c50f40071003950312150559011440c035441d400d0941e0b1074011a4081200d8110300302d0b01500302100401c10000040c0324145444060302d0350510003049003400c54007400010041801500b007503108242140340020040c003070482d10014000071900703000e000e400030710101c1d481e05100008901140580c1d440301d0805406142401e00b084001036802a0181003030007920310440200f001d65809110042d040314088002070794402c803a01c0e0240c06420110f62500c2614508000150503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 650356106 1250 650354856 650354867
    0x1b05040908031311090403170c13030f060b09091509060402010815130c091a030c0405012118031701050108010b07080f07030509131802040c110d08090d 67
    0x640d80150301c582075a84031500000c400c001d940302680c00480c2d0300000724041d2690340c03540b0b01680c0a03507604407001d0424007800c91201c034098031010b000901001101031004411458200384ca50200d0320a241c41d0250505402500030f0034420f5900442540038480340001c0000e8012aa141040010131580d841060741500c80b80e080b00d010340824072401c00034000140c50b80a1a01d03003075005000380110a441c2018070102c1d210a80f581d004614000c1042c880701e4004042c0401c0201c12000c2c0d14034510300032000203d980654410203052184d1201c1c01101c84c40f00200d11b814025480c103082103444203e00348140c07520f412078410380112709600066009030921425641c181c49040c0c40e0414282d10b04240c000079948002000e6038120030034404000305482c448020a5528001c0d62041d41380c0041d8420811000141498483c00c10b02d400f41c0060040f10491500d4071240c0c0460340029040780d01502943d50f0241650580c54038001c5818480f0226046080300d40544980812940b0100110200303036103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 650357356 1250 650356106 650356121
    0x2011524090806040807140a1416140d080c0d05070606050414010e0c04030605130201111902100314040614180a2909031c020304030f0807030b06071b0504 68
    0x10b1600040b00080100b00418000d1420318420b00350403c150000e030708000d0400030603810844469080c003020b0759034032004001d0310325007404003151400303c030f80b80c940082e811074080c06008d0300401948007407000b88448141a242c484501901340c84122400c2c600007070056020801c22924149081e00218140c02e19203c0c10401c80d032502c54002060342840020200030000409101040310100400b10014103103000d510f001720801c0030f1900c030040d00c51001406076200409039034282c4e440b012000c4007868a01c071290700602d03010b8a282212400c000b0044015051241c1c01c00a021845000c2c401080a07070b42c8200c0d4440c41c4030303091114a440c3c290b0340340c50030707164020507418542c080901c40001ca07240c416855174800c51010382d40100e85517600c8240b0410811284d235101030b000483d1400e400460110450614140c1180842c51440c16030740150101092000500c01c10501a00044285009500c00103203044c0041603180c49910521700081100d2460342c884010342e02c140c078001841d0810703014045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 650358606 1250 650357356 650357369
    0x92707021f090503120f09071a0a080402040b100909050a05040330050114030c060306030c042f030a1503020a03080c070f090e100506090f040309091404050c010804050d0f0201152409 80
    0x524040e2b0001048484590140003a60f1040d6500b0b100440c03641c0c0c46c1d407420407040040d00c4502800d07140c0003c9400326040204180d81050400c000c000009a00c80208140654070841c41199148050085011034904040d61542e0524140021401040000070004003160450448804440180900005000a840caa5007651182105503080c1c6010b410400650074141003e8464058803066680c4903040810052403a04000060110420b141d000d40051706864000c3c5c51105841c42d4085104880c203484054038034000400c500c1880e030070601004c0c5c0103201000c0d4040b00c003038880c03099030018a095440010140310f00d500b0300520078158061a4409c01d80141410869500c8504108200400a10031401c204a03c0c001241000720751080d12810804d0740b800f012646003c3c03902c64500403074059401d05101d0800c0070000040c00000f0030048688c02407034402c5600700d450320300341c2c00340560182502c0f01d25000000414004550410f84c421090305800b03104003681c10040030b984a2034a4000c81c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 650359712 1106 650358606 650358659
    0x50f0706020913090203100b04090b090d020d110601090908130620010e0607032d0905010c091503090206092707021f090503120f0907 59
    0x18000320640c00d8040041d0303105600001c0e520000c10280d87c1856468031442c28141c1c98681000c00b040e0350107215020705040c002002e035101e041d01540c41005100d5584458407442c852a105a001d0a40001402642c0d00b41a40e94010305030751071064540010420510ba07404440c1c1960000612485e596605020a82c4034007115900c00408001c9003681030007094090044007294640c2c02616500303001a440c021407401d011005000080001c0030004644610443d0455410070f1035038910030002004420f041c070406840b0300c9840c5c054141540a03076805010914040d80c06010098002450340c0d003068a406c001540b20302c9000c40c483c0390030002d1121b074042180c000c00d0031500001c0074000740c403409000e01c61400c075601413000c0044401d0b84617617000081c80404d008407400020200082041490811060308035610191110f240d0b903c030f00d903000119030115104500750703e00a044407 = true := by decide +kernel

theorem cover : BRFrame.Cov 650179856 650359712 := by
  have h0 := BRFrame.cov_init 650179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 650179856 ≤ n) (h2 : n < 650359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
