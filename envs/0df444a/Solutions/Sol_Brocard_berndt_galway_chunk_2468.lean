-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2468
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:48:06.614127+00:00
-- url     : https://prove2.me/submissions/0c04ec89-1f77-4204-a943-c9611b53779a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 443705035 ≤ n < 443884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 443706285 1250 443705035 443705039
    0x30f101109060910090b070807061d0d0305090708010e0105100602070f0e06011704050a2a0e040f050d0f0f0318110d0501050132010c08030901061a04 66
    0x150a00c5100904441001154240740300000000c440340900c8468900601d40c44514102152140c0c0340c0030080d01305500c406480b448141000b0718a50000101204c043e440d1954400c0b1004500360035186030314071100141843c05644008901030707c0082d00c0c51415102e500350128000d2028080d5601410402c00001102e16240c10421800c01003640034400399000000c0030310072605410144070550307100c00034803070a41d12200c0040f034205000412404200488400307100c1005004107038000e040d4040c03005544940e07098030403140d90141580001c01200744e00b0300304002c422040c040c01540907019525400d28040e030b84c0c80f020b003040b080010042c000390303130700c4000001646c100306d4441d1600c1c0741c0d00d0104824110045c518510f502403090103401e041840c0f1400c602941c0e010301e99000240d0000082c003003569644030b103180031905900400070f00075402d4613905050b0403910714500310200580d200520a83e10380c481c001359a00c040c4c00c00b00e080d52100030101e24002d80c105070010794240c0039822582d442c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 443707535 1250 443706285 443706313
    0x10c030b0f060306030d1803080708090310050906162105060a0801091e0212010c09090e03090d03031503120207170f100b0f0901030602041a03070c0f060605030f 71
    0x40901200c511850b03040c800d10003103445c0052009044210341c10030340f54a10303018514069203003c1d07900041c00840300050100070002d54201030075110005800311101e0018101009080c0c44040324402c0700c2c4e82c0601d0009401c404040402e01000c07030941410070002884401c0d94215200f1010030040d8280c4510900c80701d401d0030222076004102980081103000c1203555190300310090380f10306100f070b00c400c050300400755030f50031004070341c5010520020000040d2225016010800d54841e10b94030724a0900400307400039010081710083d50700200059520301903540d040e0020440214207551048040001000103062001d2441503c841500103041d241d1800500c0070341062300182d00101c6410007080e115140500041151840a91050116500f6815000b14425000c44028294004918800001440041c0d402001a546542c421000e50030300c09800c082c1500c426a255070014001c0364500000c11001056520254411030020a4145da501c2c000392401d0380900f07100c03a803504000545000b0f4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 443708785 1250 443707535 443707549
    0x92021010203150d0f111503070f0201051326040e01030303020304021c0f03080601022e0f0605011b1b080d02060108070503071214071509060207230f03010c030b 71
    0x8207400c5456180040460340c13071088559001c2802400301007140c2c0b6056847d50383e1420410040c008204864032840c4c410b00c01085052040541d40155117081c0103d0b94091b020008180c0190b0060000c040461485000c1c0c1640a404019845501800e00c0041001040034402c14000e501170340d800b43c1c40e41050b00410684580105403003015000c100d4401d400204e82551480f003040d05030070546083d645010041c2d080084e03001c0703103007400341c24200700c00354403521002c0052031130000b10350400c03400700140d0380c42c02202c64600030303240450005454010301c0e040005160b8249403058580034501880d41100c24212601904011029000424540da8055042240c0e03030040c01407500410380a8a071402090300d400c483c0c01a00240c4200b0343c4100140b00d0148681140d6102c400101da0616070f403010048d031340000380403001c00010039013500068a2480040e031142136440040740082420100c4807144001400541c801d600b08440282201980e9800c0c8200100540c06480104420340030350200480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 443710035 1250 443708785 443708821
    0xf1b07060924032a0f090e0705030610030f050a060509060d1509050f0a080a17070801091a030a0b060406050d1716050d090e0a092021010203 62
    0x51182c1141c0d801d00c40c807011a00d502c40c07040c18100050b009074586682400142064010b4084d42540460380003044d5000d044c0030b00078144d50b80c03101201d645a41c210381d0303040700c00e88a04000400c10700c00724026181c00c503050001407205040000306650000ca04109031103041300c0122581e540c8210400480c00c08201040c1c0c000402c0700d04480c1c444440e5a841d10a48001c60584c2419640e500001e04000e0104511314860078644116140300070b007444d16407903503805440304000143d54100c0f000366800d14440d5a5005804a481d020a03a0303080c1b44002c00103000c003041c1008452100609414161820300c0300c80c101c1e502a10000301c480c60554144429103420380c0c4020f01840c01c3e00c50b101e02241c1303420a00765036008076503001036907400684000066284010006492030081e203400800301904109520200e5407441d200d1103403607451450440403500d9000740901000900d00c100f84070410902c81c00d078020b440c020141d48400c2503011421805140001d00c28005a42c00014445191104640114 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 443711285 1250 443710035 443710049
    0x10507050a1101020705060408090402040801021b0c0a030b01121a1303020f12030a0b150c010b0f150d0c050c0708100f290d0b0c030403080117070b0f1b070609 70
    0x11405d52141d403555501e403c001d0001d4280c25003c103601040ea0354980498000f02401d2000355104c00d50340c559100c0d540500c024800f40d40c0725840c0c840003a0300f0003805000403039070000c03000c00442e0303e042c0081c1800030350900211240100c1e0310099414040c40c4a08501410941c03414a044c551a8a0068a801d50040070b5204513405000b0800703010340d03002e04695001540707050205694095070042050b20700d42c0f02c0000b650400120300b030704200c4015880540701040488000340c020b00c000b81030100c0c0c03080075210510b56100c200010070100317205800131000c4500d030b89080e614004c0202280d0f801c100c019000480b040d0040c641c4030300102194003911016031441c80080140c04100f00184248401c0d1400204090341d00b80e03101d4025070f5480d9040380516400001030b601524005a40500f1980200d070f00701c0202c1c5460001003000c80903801c101e642c550300d1b040109071103410440d003042c280d04410003200000e4810854504012400000c2c13000086c20900103015450404201800048c1c981d04004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 443712535 1250 443711285 443711287
    0x80703030515042f1303051b100507030503090a0210020c0102011514130e060109051602061512190309030c0e131415040c150314010e09070305010507050a110102 71
    0x14405002220050801e00d070048110902080d0204c0380c0540d0207214450492484064800000d004c0041038410301c4045000540511207540020091501d92804030580040c00512100c4c0c00240110300841d0071820100869a030507071150b000a00c2010034405020041c1c01003402d0f00c0c811350b0240640c00c6c0c4410000003a90125003424442c104812405070300900c10f2450951103080303009540c5c4104800c0c1c08030b5003a184950303126401c0d8009020f054ae0300c1d42c070006081e40c0d003c040c1c42c0b011480c0f501403035070721160511541411081003024502501c1c0c0b4207031070141c40d1003250090b41d4200031841880c4280c544071401d030719606080c0750110442e0300032285115141b040100c951070a43c94840d04030317844500f042c800060043d40916101e062343e040d9420811b46003d200070300c002c11044004540c501c407500c0c0c080201080c800c50135513144500c042c42d0041c1e42c00c01840a140f03c11240b96200e21400304651000c0d03526102c56003500d1088d02d00b03002103032000520301080c541c400060310600d00504002c1d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 443713785 1250 443712535 443712551
    0x110a120506090c070309030c08070f050f090c03060a08030301141206040308060918100914010204060e100201240f06110a140c181f050907081308070303051504 70
    0xb1460355031000304591403c00d000118081017600422015001c0c6802680b41010710707803910704550352100c2c2c60040ba54250b41c0f44000050500c0e02700107160048201030325100164031741c909040d180d500081e0540768402ca070300c1e0010602e290200040d60081052210700b000604000c024031006400346440380c0c6e03064000908100209800140c11500702e10300740c511246941c0c41c11300500420346c8254503008503019200040000000e00d4200b0303004140501003a400d083c1c101247c82d0300300d204500c55200468130b1500a40c02d645000d00e005a2164201d00001c1001810802c1d810300500b480d51500560f490918014020b04079003001e01c0b80038081c5421700c00201d8080603052503440900c0340d0024002126407908030100c0138203100020040c40094007814512149000c0081e614204651403440c400f100400740381c07440a10201c1c14100c500240540015868684048403143c600411985030303512041085400503c802004210b0f0900985e000156400c001a03400090076202070924812401c0c00c106d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 443715035 1250 443713785 443713789
    0x1080309010206010e10030c1202010305010602010b130b0d05010c05030a0f021810030b19060e030c010f0c080f12041202010b0102030415020f030f0307020624150904110a120506 78
    0xc0c5410348000640b560000d41d00e591b51030a650203250001440f03007141c1c0c0000558010303c604d010344894401d0703d0a00060385c0f00d1b07070103c0c02c84c5c240a61807980030491203441c0c600d606540d440400708843c058000700e1740c60150786401c0d0035036820700308120010b10000100139071050103100b50380101800c09415440e1a54841100c005d07103100e07000d050300c40c15084481311074a074020b40c03150601e1913018140d05451800319070a000c1c0c526176441403101140740c007503600f8890314001c6221110514141c449607408240302804554182850104556a440800440100c0800c0002409442d1400ea810300c1c2d035880c1a19040407800c0903241817806580c10900702d00d070700380c0e000310544d810303100d06a006109808060004900d030603280c00b15002c45002c002483c1014a062340025032150300c26400300d0b250b5462303003525010038000208521580c94144009000c50f850300106541d00035036000d12003418203074400009005c4030781c01c2d490341085260024000860175042045d00d0f50110708510704000358502140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 443716285 1250 443715035 443715043
    0x70c0f1404050a0905070e0a0c020a05060117031e041a070b01090e0705040920030d090b131809020f0406050d02090a11071103061006020309040e0c031f05010803090102 74
    0x39034032071622500001e0005800d07510007200d184d00300d800c0f03440b166a1030401c001c1488040c0c885444003030811885400c124000500c04c0c14040d0f00000a1000c0d80c64104904a40e07003e014081d4224007007000260788000c0c400d0703061030710300690511440c0c0e035500c1c019101c0c440c070b0303403280c1201a1101c00f44841c4002c42d1040307d8040c119101c040c8041034449d54010414184242034220740c0c0d0052410b041e08007845070450484000d641005020b442400f42c80040550318035240d1800f00010300403600070300140681c200a000024041c1d00030b5901c0c10b8807440710020110782c8581c3d41d8125a5503400001c1540741101180d0030080040e542088414201404582c03221045d03035010b8083c1120101140382c0096582c02800b410441c06880341d101d403072070321b00102c01c1c81804444511030303c194008240131040c440c20360011180c8a4000390318100100080c000a446031014400307890145010306c0465460500550603c601c0d081003051900485c07421520440300180c021148540c800d1210341e2060760001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 443717535 1250 443716285 443716319
    0x91e0a0b03190204060b0a050c0c06090d060c1e050a030f0509190804120f060b03060c121b0a030b0108011401051e13090c0324120f0c0b070c0f 63
    0x900300b40840b06150011501503c2140e10028402400044e1044042d03800f002800c03405c1c601d070040e1040f00c41c0f98001c21105007e042441c0750f20000c480d580700001503541d4014a0a2035450404165402100214444001503840658042200000c583d890603500d40310ba00205091900104814200030600302d964000424a5001c000d10805500051280481c2136800801e0040071401560581c0c0c03900241c410602e00c1f003116124101841100c40746400300b040351045140250032400c0c401c0010034103a90340e0029100ba4001790f2440040386c40c1440100041100b450300b51408560800400001030000605a008004507101d0341141c64a0340c0c0e00c4802c6030507a59000c00a03050540e000740c80e46140b44150948001248041c0d240001e0400172074000300550b0015803000c120450f259807840c54190038454464502801080d03040c000510540f0f4180001d0b402902c0c0e01c102d215aa540d240e030a200103400210190601050304400c00400d0f403030010140207500c1140589515009914000342615 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 443718785 1250 443717535 443717563
    0xc13291f050d021803010507030b090a0902061c0f0524060f030a050c0c031206010923060a1206082104030302060609152d0307030206031b09091e0a0b03 67
    0x40c0d0840014018444d0540c0000010002c000a041034000a80244a180d0606000303d4442000644020080c4a101002c980117400e03a4600142400b420441c0b004002c10401000c0c4e440001c1603903221648074071485841741903401000e103085260113030080d403000342038580b040c042008080704441e024400d40b0703080480c414021981d071315649151144c0f07015400400c1614800414902000c400c60720009000782e4003a29007050440e110781100844035008100074010141080d00361800d0b0500500800c1851264542498600381c540c5041080c0c681980c401c0b00c07540e11007805030302c02d40d407a02c10810b071801c1701554043ca09861503074003135241d61004019500c901c0e000000162100703a02c15003482c116000900900d0341c107810840745200007006000002d03c002d0f040c0150740d454280000c0c8503003a1394004104c2406d43c0d4407800b55820b4450051464403491206100c101e00d151030b010020741c0280254214450070f0144810b03000030399203004080200c41420b00c1c0d15140c040d00c01103207010001c201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 443720035 1250 443718785 443718787
    0xd021504030c0f0605010f0b0301030201051902011e02040503010c020d0c03030b01021c02061f0605041208070c0b03090d0203090901140102011e0605130903020c13291f050d02 77
    0x1181400c0d03410680100024007000020003c82d42000300f44d9010714140c5a1005401645a4071103100550034082404003d0200700204180000d800c8440382c140c4c1011a58400030980c910303541d070b851401d0311b483c11000b5171154002c6401e11080c5000c4c09a00c4001d0028801070100d0905108001e020400e40c01000d010b143e0b54244d4100140d01c24441d441c600208d02014034080200c9190003507444500700c07804074050000346001702c104404c4d10060320485500b942c9050030141001c4100720791740000390040f24100d10800512000032120b0b21007600900468919a41340e182000845081c020101403e90854004211a10300750355010718030b40c151038047c1505a5601801001030f0700500408040d00e4007100250b014400718903058001000340c2e8015100e442110322a45420402d44d00071000047c0507030046025601d0300d041c02c00c012645600d0800c03021401c100d22030103401d05070040348002e500079507102044444c14100100c44106c96065140c80c1d065501400d80024064054601c8040030660 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 443721285 1250 443720035 443720041
    0x60b03060108010312110d0801090506090906220f030807090e010b0703030f0b0910170601180c2016121101081305010510030212120712030e030307120e0d0215 70
    0x8429403081b5405405181260209208500050b007049424421280043d0034080060100d040140329280286c01c648028180d541310104c2c6c038039118880d284204a4115100d40803030101e450714081d111240c1c003c0d1035091032400e00502c0140000400d0f04007020012560300100502000201144c00c19038042c030b00015011940340122001d00525132116512003007200c2482041205413401c64200e969829000401d103c0c42ca80c10b0303495840174407811010180c2030300104801d214070b40020415546a1401c4c246605481190543c1380c0103c545c8624603a201a12408620103d418003801602d07980400c4004802c8a54405503909020119541001a40c8020851280da084041702000d903001000344801d180c600052442a401407006a100340c134140070510003580f020449415900ca6038070014984850390f215012000b4103505113500f09541c503072160011402c140065802410f00341e40781015003152030102c030f00340c40507020280000e800000d00a0341c2a82c002403032802c7c2251900400400d65 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 443722535 1250 443721285 443721287
    0x10e060922020a18050114010c050c040504081c0203160507050a0318050607060e0d0302070314070c15020a05070503030f0a110a0209040f050d030506090708190618060b03060108010312 81
    0x1c0c0d095004141340203c0c00d4020640e034020741c00c150f050324000c90042c08811411001120810b06285001c4c1c066040050302d4582401c7c00c0e005a079106002c2c1d9400c610746040300c1e591002c800c5410000080c1140d000c800d2120f0701485190070500d0a106190079030810918ac2c603116212225010000c0500c9544060b103180d01010300803001c01008001c0106e80c40381f5a900b40750020307050000d447d48240c051038030a05500ca000e4405e07910155017541e034109110020340801c02c41a80200c0c404c0e611805c1c511030016900b12085640040d00c0e05e0b581c0a0004509646130152170305071550021882900180104516884010243d5580c00098a0282059a014030130107042c081480000303900b2440c10720170081800070204031122100c2c8501c0071556030300c10b4640304a003141c030203503032103540102c8171004159090b200e01d4403550000030a484050024051040751030489400750b0000308460889a2070311500e1000c2d00c90603000348510640399140d482c0c8100020000744050000410b100c000708000c403122 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 443723785 1250 443722535 443722549
    0x1140a180213050a0b0c2a01080703110d0c180e070e010c17030403081608060906030f0a0b180303090c0409171611010e0904080309190605010e06092202 67
    0xb04005413030720454545480101e545644081d469802921130001070700251003030001911007401c1c501c440c0c11402c40080004503400b200103400f210401d80c445107010303a00d031903844c0180203891805400040407003540f40c010b031000804150b21903840e01e44210400620202c2c0828a0f8040c02505e072021030701b11342c000113031108444400f02030307c11071003c404002101010720056000b6400380e1903250565403111101490811050303040800104181c022420f41d040107408290042001810f031007030b0144680d44035242070325100d4287d94080c000340a11641c407042a1840d18455002400345245181c0380344c806946036a1401150300440e40c0f2040d030018080c0210301e0010300309004034415601c5603241110381c0303490900f18062710b41000700b00003041d45601071407a0300c00d05280a45001030039030b1030f03842e13420094000420f120340600900024005030305025040181c15440381500181c0355041484d40c0c01340d0b17200181441d020b01c021005001c0030746c8800414569103191110f00b000130114920100340d030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 443725035 1250 443723785 443723789
    0x40f02120604051e0103081209070803250203031c0b0f011d01051b0c0a05060c0c010c140a05010e0709060602120f09100201091203020a0c08070606051801140a180213 73
    0x89101010020040202c08002009a10f00130b000301c0030348d40c0300c0152050701c5105c00d2085408a81c400c00170800301c00f518203258241c008041207402002d040c19000301c0e095900c01d690058100e001c003610341d403441c5500c3c4a001b13100c0e00240c551413011003a8071300103000b0110b210410405c0c0c50031520714480342c1c2c0c03085049442005170310a4801040b0f105111003552240740b20b80b410701c1850140e4010449050082c141d500c6105900000e001d07807040d180040d150221510010355003000c62080100c8181410070020301114442c000001c2d1400030000c0030380c20901c0d20380101c5029400c00008200b0a42e000403480b1214114a034a070341da40e42d0f440d98120f01c900c0b808903a190811050189640425019440901d41c05d0003803404d110f290000c0c0e40100c0c201e205500c806000320f9a0003e041000c42d00c0d00c80608001e902c41c3d040000c5041d00c800000300060f0801ea000340201d080a4010f000d0f40d14084440500c0c0d01d419680a48001e05100e400b0354038003c520190b0324150350118500700404541c07411400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 443726285 1250 443725035 443725081
    0x4020912070303020703050f060f150a03060e151005010f050313021509120705010503160c151b02060106080604050a0b090c040807050d0507060f02120f09040f0212060405 75
    0x1903450782e0707450301a40f281000e11017521140103202e01c814000101081117403040e250310040b50403070f42e1440b030751841c0c540b0f440c50401d03008141c40401200180705882071480001c4a030300105210f01e142c40e02101a110024146a0f00d0140120100044d0340c101914119216450816640700c1e5136240c03c100e10400154406503000c0562131545000d0034844004010340d85060303c00c0c9180d140407c000942d5400c0d0340c41030034000b800030000501034801c1c540401218880754684100c2048164a860798010749142024000310343d0f440c5010803520168940d16045031013400903042d00d40c504000600064402004140aa600c960018590865030342c007031400003c0040140c0b0450a00c200d685985801c1400303814035610400101080354a094100100c0c20f55220300140481414044200e1723000c01040d0b000425031054042140c00b1400640c040e082c0c403140304a1a5403182c002d2001c20090381d04081d070200202e2710400c01d901c00e0781c0c200402c007980800181c90120312a2989544e000f80c1c0c080b03080c0c0c2d0075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 443727535 1250 443726285 443726293
    0x1c020d03110316030e010c020307030b180f06010f1737030305060f030106182a0e040507050304150c1b031d03030306090403030f0605060c010b0a09020f070204020912 73
    0x20a4a1044810000d10f841c042c0c3e4641c681c0e04030700e000644041c440114041d6155202002c00c10000c0c00015400f54401201c0f00400c0040b00c034485035518003503100c544800c8a0300094014070881c8040540d070001801000804120031054024503612903401d92283c0c03558183e00c510302c0044446407802d001000c20305003681e6259a0341800c0007002400c0980b10180705920019815000f07107014000c51003500c00444841c07012011000d1480010407400583c0440c0740811000c1e480070a501c01680300b91100c0e561124004030180004100441c0c0004150005210090043c0400b0030401d50035611002d02c08140050300200c03500044e5103c0f42800c0010324284212000341c1d041542c070580f419515142d200030b40d00e010307141b1010580c03640002c40340c05401803020800600428880c0d04540c40082e8a500c5c00a0020748070000305500741c0c86004c00d00071580d1500209002800c01000708401012046c41c00c41c103014900e040d00c4494411104080c0c40b82e07402048100140e5034001040b00c030a0ac4042c115 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 443728785 1250 443727535 443727547
    0x30203090304050907020307020117010b090402030406090f050a150515060706090203030301091e0606051c18030309030813050c060901050904050a060807080c09010911120103030e030c1c020d031103 87
    0x959039405600204c7c00104410803010290b00e00c2f20b445030598481541c8282090150824000250802403042c0c90280d00d41c24190040380700daa0785010428007a502030310b00d2804c43e040c012021440150b0b40d0154030700d030404018560424070442d207924a8101c0e140b503690075803030918102030b008601703001c0d616001c004000144a940355000001354404583c41c005241c0c124007a40e4211071142c031820b00031440401c081116444450011042654055800a075510307004042002d0980140e2040b4003003692003807d04240764000c1f003580c2d400102c4048402014009640d031a03100c171100c030f9007103004000108040c00507a000354107907949039602030030810851030141c0480025050b60f204120450141060100d004e40020405004c200b6000c5c04100c09a40703440e890000900841680c0010030f5420b01a992200c1c070320245a60085020b551440798a615250030541030075030040052303215a030a00e10909403810103800b904141a0100c445030701c43c00d440e08090703846900c2c0b00c0c4030003440c0c0000160 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 443730035 1250 443728785 443728787
    0x5030406021216020d03020f030c0309070e01090207021816050c01060506070813051e060d02070b0a0b01110d17060d050a06150e280e150103051615030203090304050907 74
    0x600c49108642ea422a03540f48103100051b0224810304440c1900440104005505140c0f10300065800241210440f448a80d50740c0d5004000c1100303810540485400141c000c095246c518401d4900c0554403910400768200943c0d0084400c00c1030191100b40030001c6145581c40000794004001404064801035850360189030424103507102034509200192110300101765030824035091070110803070700c5011403012421400c0203110b800c085080500e031902001008005802041954083d1142110120340715618000240125110007440020f1764848807402d03140f50352084c0c0420a04401c0e54501c00d59460710004030700e890a0b1404090107901c245a903038000c00140d94021100c1d040c84100c110042074070344040c0003c810b0282d809001405c1d5601c908505103079410788121024a4400e00090040d0340c0d0075650782044036100c244009074070307a240100305002d01840202c858850000312440e10504019540700d1503180c5403c00710815a0210000d42183e034200308441c080c2a00415980c15842d080c40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 443731285 1250 443730035 443730061
    0x7031b0908150705040306090c0513140c0c0a06090611160501050105060301150f020c0405011e0914011505041a03090d0c11040b01090e040b0106110705030d050304060212 75
    0x10440e031042c854060700107a004810240940558125515540742900d5501c40c0000341c071340000300f80c4034081d0f040c0c800201079a48a5003804e8100c01030902003150040c0c0c0140030920b15006144420071178042141c81074844000c142c10a88584c01100014980041d01300320005010b10b044d0801c0c001c10000301c44001107021510b440840340300c0c0c0c0090045a88400c00d000311400288905801a610380305084e0149000705c83d1040d1001032481160391040c000400501522001e9208a0074408520342c000c800f00130118405002e4007242d40d041c0949100a0603030004854140706203180400300c4042e54100e648100100c1d002801b03028101c0d9002090320360b1a110360b50050710404490b1040e407103100600da00892010440642000500220004800902001c0c0c0b00c000b90081c1002154400820091b0a000005008600415098069604143c009131019401040040c410350000200b0081560005010000403816107040c6031281c0311854081c1c0079004a034101158131844104010342144c40d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 443732535 1250 443731285 443731289
    0x90204110c0d090f05090a0e1204050a08010216080307050c03070b060414071224080a0605130503041202041803030e0c01050f0313020315070c0b060906090f07031b09 73
    0x1415203100260b1900151440d040c14400d0413180c1001c2e403001c10091400c070030095072150030342c40301150b49030041031204d08002c010312282542503400f14091107581010010b82029001400007145080d150481165401d00f0310035008161140000024190910520035038016002800880fa2108071070312740f00c03124100c22105980680c1c5480d140c010f940100c941c3c040e01410071a00c904d004001c0040d084005459913820914000102c00c4404102140103079124000302812009080c0c843d403103107440001d0766000b07842c050140780d07001c01c06400b01c0c0c404422501103035001101500c1a448a20208000d0503c14010802000345444960140768068021103e0741e401c51013070f00c00c0e900d0380c1c00041d07520340940044904d000c2d00074800542c035400050300d41d140407400202100c519400003910f24032650400c454090003c0c1d48c42ca607200402403080860707500314208171040b008914200c80410300713005004201821131280c80c008510041e02990040303030343c4040c5481e0300c090600b07a18800350001d1618 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 443733785 1250 443732535 443732557
    0x408090907030515090901181a01050a0f06030509070f09020a08090d0203070b130204020a05040f050105160201050304210201140a050f06090a0e0312090c0306012709020411 76
    0xc0c40005600910912a1070f00c1030407605500c541c0c09800700d00340312400000521451031503588001080a1440038036644814500c02c4da4194840012820008100382d01a807125002e003d150f44240700354900030f1142000d03103034a4900000c1507504c4030702c81460029564041110191400c00206007100c1d5034004000b0401192120321058070341c201c07015030390102800032000581051010720b0011740c0203d50180c120845690780407410301190000380480c0d0245400c000461000501040487c0184e800003004100c2420443e081c120728070300265020320582402410048008009020450155558038011480c154a80c2803420b1415020b4000c044089042410000c03400014616042d5409614454051495501e074162106000e01c44412000f90a551110b521202c00c0741c00d8017070801c080e020510080c1d82c0400c07035040c99006d441c24802c50b0840c40b400780e003141006019000e240c2c1044e1855100348189820044171800001005111044000398060705010004c0b11550309035000d80103c0c040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 443735035 1250 443733785 443733799
    0x4050102010b09061513030b0f0f150d0b070203070611040603140603070902071a1005010e030f150a0905010f020d060b1305010302030a020412050a150e0709150e040809 74
    0xe800801060310400c445443d4000644c0c08101c6108813900c01400c89010b9858400c8495600c1c0d0343c5004010204942c1a100c00b00c270300c3c08205000440c141002d810422000e201340b040c542880c0414070f5070382900f40c081c000742121004584020301c00c004a4040b0368020030108041156410040203031361207031045800090408043c00e207440591f00c1094081d120040c02040c2251038115807501a4100c00010350b2000c407003800850381d8480820030248140280860402441d0505001401d401800b059280c000e5100c0c0200b00545c6070000b0305117401e002280c1e0341d0b031810f40d2840d88010181a40c00d200402a500b404072200c403c144640203030484001902c000e20070141c40f000c43d110203005000c0c8100f003a4000a800300075550180c0e0045420451010000d03103404e4035084410958018804126981d80c0301c501981300703100481420160034852141c1c00c1c00281000c040c40d9a90700c00f00d0180b4802d00e0368400d6000485031200c54144010260000b0060039803400782003a039140d80007000c60b01d003e012 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 443736285 1250 443735035 443735051
    0x503060f1003050415150e060409080c010c031404050d2f16080a08030712090b090a03031109010905010e0a031e0c0e0402010c03030902181612091e170f0405010201 72
    0xb0782e9008100c00301c42484110f02070313141f9001c0e01403442003011780302e21307089550f80001c000410103e000400700122074400108214480c0030380141100c90240010890035903000078040003400c08940310101e84400d00e4040c5444c9203080340e05500780c05950703801c82806000d0000040d641e1000c5035111801545031510705401760f41c1c0100c540c4a42c4222801008154100001010b150103001c080316030200b926400510813140d680d640000c00003e44810411b54010086001010342c14048d83c2c5000d414000110f042003040d40028207284000d0080364140401c810a105e80e40c1c540214441c002c541080260a01d801e5805202d50340a01242054510408040f00415031060803007400c0c0c060303a410382d1011100384c3d043e2821002400d80340d02c02c907802200c40607540d000e030701e440070118001d001c400141c101d0b240145501500401801e40042c0241341842000c0c4041003441d4010b0b0001000700600b403100081d1490401145500e2048006401c400455054001040c81000d8130960b20203800800c0845 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 443737535 1250 443736285 443736323
    0x6021501030302060708150a12060513050c0111150709030b0c0c0709020a1803110f04060506030c07030c1407090c081603020906070206340b070503060f10030504 71
    0x58424040034015034001c01c08900c0c034038440e0600d658024040090b408000010340c0024800711020f5014005405c0641e5401c81408040c0c498560002d4002d08084800544e030340d5242d403150300003181d081c10b00620310603c0d6000001800064080010006030b0841450034440c05422524075003c2580d00d004a280021782121111044a0981210704000c0074000d25103c0080040d6010f0f800e864100001d03c00a2514810710800d158007840c8206044c201500c818801d003c0c4c1180340140380f501c00c03030130007100304a03c1e21040201d80d0800c200e05501941e6101c20f00f400d6030001c01c1c0c0800209001808041108094030105484066440c0244107100445040104540400b400c2e5140b6641440103c003158106019a0007001c0071000540003c1c1443c490380c0000701c03d44c200300e0760b1002c40606d00c03248030703070710540e4900030110114000c4165640881c15201c205d07010100078000020700100001055440d0790b45541313903030700ca0700c001c108420241904000038040c03e415101200e042494a4541d440c032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 443738785 1250 443737535 443737573
    0x9090a1a010804080d09110909011e2a0912050109030e10081f0b040b0403060608010203040816020312030408131712071506030305120606041206050907090e070602 72
    0x210303040f582090a20201050400080005010440366885218080d041f241c40783c0402c0e03032080c18050300001d000e032450040045150a800050305025151040e61b1659011005031803e64078100c0c2c4000c022007040318030541b03200c0829000700540034082110041008015013043ca2802d10940e16107100c5107042d4140451804400100c10100307a40b040002d0411130003510307150341580080d04d10101c2581d03039030171428075a00542103180c0041340050141b0902c500c600401c0c0081c51000021840c501d850348400406026408802500c00d108002a034150740e804c000720346054403004c109565034113191506011301d9021003100303811800140c40c0090203513001030f08070f9540403a0401511102c1e03003045410b001603000303500860b40c1002c80c200d10000507003188600f2001d14030944175290368008030414103030503540040182d440355104007c18044c4115a40b1211f40d569440f00002c01c01c0d8a4000c0940c3c105250f50300403115003032401c400c41000c0c1d000014154201c440030b409440f00342c0e642c41550881d07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 443740035 1250 443738785 443738791
    0x70c08190f080a03110c0a0308010e010e270607090612140109020d090501090b09060a18060e01020d090b06040c03020301030b06120f0312071202070302070303120209090a1a0108 78
    0x3091040400c0d10300070503000302c003c1c102c4100d1460000f429191320464041c0b076070032048524081e580146141c104050f000800140036005180c610880c0398134000061410707480003000c41003140003c0003d02001ca01090344030780c0c081c1165007690520302e8100402003c540d6a441f07407000240c3c441300b440054120600c5090344a00c1132100040752603007003010303090182d84200c8503518069503407031402011403400e20405441030322903000000d032030a0110341c2500d0007201a18048000e4a043c0d521444e000c000b83c00c0d0046a64414004075103820201c0010780240150060030602d02d090900c030740b04200d0b10000705807040c0340c00c44003048498880360b8102d0032400309000c024034a07482c0c40c000c5003007460455045180310b4803102c100c40c0201c00c0326011900b15000184070490402610080c4000260840341803d009171080c3c1045090440c1500c009503546400c3c8030140034424062201c0e03420314140e4045130050700307014202c80000c0c1800c5c118080100540c0120616131790f0340d20303400c0107030750f00c59800f03140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 443741285 1250 443740035 443740043
    0x3101a1f0905041d0f030702120303071b03051c0c0f020a0c0506091504080c030d031a2407030c1202060709180207120e15040b04060305060409050102070c0819 70
    0x51081c2000c00b80030042034001401311072100c000301c0020859400b00501c0c0c0c01da5041c100a142c89880f18810302103424458280b2020300c0d081482003015180d4048032100d90000031140d00603892200342001c2c0ea142c0b00d0000c0650040e82000b040f0711045c5196080022038000c1643c411083d11420142240c0f2444c0084009128808058040185261010240040c510000c08980301460542d0f4448025805580405c2c650742042c03842030704900c0c0511140382541001d003014801c41020021420000d01e0708580103114070103500c9200c00104018006d612156520a006d40e0794030440d080c082e2410100c100700301c1c5d01110001002580c0351000c12417a0045c021501c50f808200d003018031001c821003103030103070b07100c1c65600b404110046817580c5510340c1c80e0110ba8880b6030075444654180300114102002d01007803400204410041c40da0441c0440301280c5103490001240c1e261000024003070078207884040e01e99800400c03004148101c000c003400490f1041021071302c0e40344c00d05040176102c0c1c6518070064 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 443742535 1250 443741285 443741297
    0x30e0f0106140409060f14180303040b07050a12060602030702030730030c0213050f06010e011b03020106080a0813061404410102070b030411010e03101a1f 68
    0x4006043c207411058200380305c3c4101064600c2000c60b41c0086405425988208021003014010704065084108400f0344482001e0340c0747d0310b03042e15909014003018100c10200b102c0062a10341d0284919124209a01ba014007031001c00d6488034029660b400c814400e900c40d004400cc000b905910b032110000c8940010319107005003401079400031684440d240000c0e410b201c00d81c64041c005a481d2903040010500c0941c0010382400e0190b000380c50020000c00e02c030b0511a00e42140c1c0000d81c0c00821482a0210300c541c03109903140c051178201c2c0507188031f501c441c940c1d200d00c008802c1045404d2002e01502885280f036a03244542c3c9850490303030010059000e0880550801c418004031200c0060b01d081e01d0807d003002404140b0000c42e2070300180d481c20504003c01d02402c1c00d15040d40c4c0c1800900028080c02070043e0440c141034550240603402d4145540c180109055140c0150310140212095020710020401c4003140d41420240c4481030203030322138811041c0100481c030340c000401c018003040341a50354030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 443743785 1250 443742535 443742569
    0x15032b050310060509030a05010608011509050603070e18010e1507210c09080a3801050d030c1202030a1404080d0e060408240601050301051509010e0907030e0f0106 72
    0x507151a0305c406040c03601070241004c0390000c03400c03d014205c01004061700000324400c1d0f11035115213126894200c0c1080038101070031311009540009012003900c2c0010301c9485181c0381c0e140c00780030020540c1c21580007035083c0400c0090000001c1804201200c06a081100c80e64034138a0490300312625206449000c01c5241e000e1550800301d921040c141c4149050006800d615144540e2428210500850ba0500c6c01c0e8108855040a6200c0400d0690360104030320039040d64000c01000032805000d10ba01410145000c1c0b000d040c4510305000103541c210703004594078100036100944030341c403a401d41c00200e80003036a50031030f070032030700b42100c007100d80b010b02600001c0001001118848994090540d01030703020300000c922f2034010700c1003a0056031110b11081d5105848000d680440d480205194103000d8103100411140d140c0501d41c030440c01d242158a59030301c3d05c04005072056483d000c00690082022001c0100b91a05a4098280041850100c842400c413105295099814070700561401100344190 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 443745035 1250 443743785 443743787
    0x50406050a120f0302030915030402150405060901031503060230010b090607031e051806070f020d0f060f27030e190e09060105190807030b15032b05031006 68
    0x1103518084c031901c19603140c42e94031000140a54141459500b01201c00020701007145400b000d44c85a0212910758241000e10348400150741e03025030924a41815210024401050f450f80c81280c091540014115240c5194200f00d031083c0c0110707001010410307a0001c0c4039050f03500d4841e10703030704880d07080803500d140101050070310090303401c5207004405210045099410101e8009031840c4051200e41e21952583c4d414030084a14007901d4041502034002042003002280705109074009060b01510034410b1041203182c03403c101c1e2140c1d0406004d03503243c410380c1500c0c03004035044100b40b450407000c0088041c2c2d9482003101050f12515000b070100c1c00c41803072182c0ea800c000c1c0001c1314100c3e9100c8254070b200e6460083c1c05100e4000c842907951380d00403a00600ca00d1400409841c2410801e0080c170442c5410703c2c412581d110110b01000c0d010072030010015969100302c44101c024120080c090f48c0307034182020040c4034000c105c01c241c81e00c1410748403d0030b041c0382c0c800c005480c400c00048681e0600700e490018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 443746285 1250 443745035 443745053
    0x912010b06091c210917030403020409080c01020c0a0c080c1e010320090907140a030f02090d0308100b090604170c0901031a0a05070f0806030c100207050406050a12 72
    0x2c44109503c25401140c00480c80032607030240c442464408090300050005002000b10145800000d00200305a858900d8000c0000c183c80903680d06803400034a0040500300034084c2c1c02850b000201c02e40c000901c0c042c9288000c40c00522062081da44a001680c8403400c640d12400001c803240d400c200011001e405440c40030401400c1201d06040018215100f40707580320078200b01c502d0305203403000002684076250429910769036001d210383ca0601d20507203ea01450390a03110300a0001c00301508c80719400c04065440d8101e80120100400041220700302d45005012082c0840d02c03400034841e0b4200004064101b001158007400d8001d00c81d80c5402e0401c0c4e62080f030b009410401c0d0041e071086050344021502c440315050302850084080400300700c0240000d5010f25002400000014100014003881c1d83d0000c22080c0c02410703d04041801e6600c5001017841c105100c0001940700e1040d04100301c046802140342000e459069074203020341c50700c1d0300500034031941601ca54901030301d59003c0480031400c110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 443747535 1250 443746285 443746309
    0x18060f0308072003060a1e0908040e060a0b030c070204110307180602060709031b03060212090607032717041511120a081b18040e0a0b0c1b010e030912010b0609 70
    0x214800480500c0c0001c0c078021100238800c00c68403000005000c2c0000c001c4400b00d1540b05804856040360300d410407040c1c1d00c2501002d07004100c103000c00b084410465403260400d0740c1501981e07105540b2841e140000801d99400c4010840e15005082c0022810750310126065114165039183c203182140b4513640e680c2c071484c070521a01e221030040324000c40043c2da54001825086030541e00c80080d8281a1103540c2011005001c0d0400d240c42c1401c500044144c0040b2004600d40e1a01110380440080c1040f01b10aa16494800d80c001000203020989a00c14a0b50300d400c0d481e1652940c1c070030b0285c41c2030903540714040ca401d00c0404200f40901c441c840d21031225203034880e40381550081510840e80600742d0640080780000c805c000782d240c8000280c02c20f80700d50311010340e41c000109101011900c0b0100999806851403a440d0030000c0da841c2d401c1c29000014406505490082190b100060075241d200c5c0c00400c0c00c540706040d0401d2803010307803105010b003c5040780020029403908002c58204550ba02d110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 443748785 1250 443747535 443747561
    0x703030b090a020c070e0609040f0203190302010c020f0a0804031113020a0206010905071809110909040b0702060f0705030601120b040c080403080105030a030918060f0308072003060a 80
    0x490384000d203034072007a402501811180002503101d8001da48003d0070031800303400c840d91000c2d0311020402c041d680d10781e006070099041855081201080d00109080242002004240c80004000001010340c1548000c0d03900c03955500365010701080d011010381700c102080740078052140c02d100a10214811039107081003047c00800d1a168440a1041203080c1d0300b28200a102503040342c1c00400c600c0d07881d1f0207240d41c0b21009140a52905801c0407580750f02d00d20601892503010380c4e51030046104210081107038a0380070000e02e02e6245290030f280081c0310721403c5804100600441d0b0205110104042c0c03024081c0c2c42d9511210706550f103c100464555840c40400c1c24a45d03158103e8040c01c1d100d910400c00c0c40060703a595205549040c2c2000343c00f204041e40414000c0c2e1000140d00c0110f03500c03040c4181500d00316401005007140314180b110282c140758004681d54501d00100000b048103003001007c846104003002d0104e245030b01068400001380820660309600405c0000300e00c40085d0348030303040c010a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 443750035 1250 443748785 443748791
    0x3160e030a05070906050a06121104050a090e0c09040803041e0b180d11030f0702040608010c020304090506040204270e070603060501110102090102030a111507050a0809060105060f070303 82
    0x2490410704001c203880701d4100700c905000e6000e1380e0066002601060360f02c151014505a0002d140e8025110321201d041d82e41c1100b600b00c03801100c1210000c2800604e00a9540c1d02c0d115254010100c0071040303092031003105c203010396500b483c407956842142c001040c1d50465a9540350f111044504440c400c0080101e1000f807000a01c40c00e60340e501034114100c124032003404103100d880c80c1568841008040c0301a00465003075448000040718000300d030181c00315440e10b02600c00701d005851540c0103007900d9420402a040c100e0780c00000f5004840d58007005001c02e890b0384c4288402c905c26809035913036090040300c9860043e07112054686201c80c0401c030024821040714440c43c20042140c000000003900c52504100c55a441464050404041002180f404200b4400070307540344104603407901842590b6048a42c0c2d010180020301c1098500b040350fa030507140505009141d0782c00700b440080071801d0000818400000040c03910b040c1c4030054000da1401482c41e41c0e86240790801d903800ca0815403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 443751285 1250 443750035 443750057
    0x321020d090f0201020609060103020303180f030102070506100603090b01050405041406040c0609060908070e22030302031b0705060a1a031905070602060709062025080a03050316 78
    0x980c500c180c1d05850b01a9005220520b0203100081c00c1c20f00140c80c9898a6000c1d034014030150340d011007111450200b8480a140d58109603000c02e81302192801807a0345544081200b1082c030101155291080c0200032440481c01d86034482a401c4404621001e400c40d1407c038010300040c207040d030015400502440d041031190b9050a2102e25211381204c0403914031207900c0b41042100e0b00070381c410000e420107003010200c460820320106e90350100f610444050350810f00c00300752080110110f0074914100201d4031528541c650801502950042e00c80b90040001501e02500181c0d0000c151004154444083c100030f4480c1c0c0059005090300400f10000513018101081043da27003089401e0a8800200d00400e804809042a41c01d01c1d00c140e00100540d00810100b1940c141e10085100989010f07090150300c042c0511044484001c204811600e40d100e10603400d0480300d1803401e108550031054504642407600d40800c1521884003507401008100c0c14004101015096820b0610100315031030f0840b1110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 443752535 1250 443751285 443751307
    0x5030609100209040f15091121040c18021213050a2003150612010b0d0803090703081b07050a06020a0803130209040305211e1e070f02010513032102 65
    0x1803400e103c40c0c91040003540f01040848088c7c0030f0546968500e21742c241c2860240c244072064491007400c69407016081c070700006e080007840071500001d8402c0080300350001410b070107014000c2d40040180304a40b045c240003d5012480d6131401904c87e580714014281316405682c2d5411140c03904000117902d58840c400c2a10079840c10400304054040407040d45080f8102801400000301c603c03000d00c01640d041c89100c00e8103846071b5407507581095004195a61300e541e01c0c040f07241880c0894000a000010014000b51004187c0d00109124440c5405031b80800c4e42d600200f000344c44a612600c1c0258201007609004105484091a0300421000e510341455119030b00150603400115411000f185c000f1a03201012002d60001e10f41c10901e20036404011301b004a800d0405c4980014200618003004c0e00041140d0790a0005c1f140300705c03014401c0d07050380c00c2c040c0c0007401580da408001c200561038100004c0b420243d0851242c4001c4e0503840da0035012604d44440380041c400480300c2d1740e600340c003044210110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 443753785 1250 443752535 443752541
    0x160f091515170606040e130f0602030f0f0604050907050d050f060705130e1504110706050c04170105100501050a050f2214090f1f0806040c05030609100209040f 70
    0x504000e56840c002c0590712000c1101402c0b000d0000390049800f4042404481c14003c02960495440703035403107030310810500e072002c14030741c5066005014500120500420005d8040b440e070080414007000d07a1980e6030001848201c1d141160b0860083c3d0008c0c0307080101d4280610114805402601502c0d441d4000d41010b501d44441900c4100016070001f80340d20b1500c215056260203042d002003c84c0c0c1508012000010b010710340d030307030742ca10a03940ea10546007003202c050200c0f5941540803c1c203002c54906400c0c9103030a40c20900c148001e00c10380031031300c10b50030340c041c41450320070895850720841d12424240111030607040440c003c014008108940c1031545843c4004d4901044080c0030050507055000d01503103402c0c0907500800e000081000038810030790f194010356502480c02d1045c14000e80d10180c50750b5100041c4081409180903111003c9900030300401e405101e180138000c90500c02d6030301d509250f507840085502500341c1e0031071801008244001d400400c0f020000500100707000320803020020031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 443755035 1250 443753785 443753819
    0xd02210a1704051504030f03080a020d0504031110060609170f1006031104051501230408030306030f0f0d0c1104050a1508062202040f110c160f0915 65
    0x1e01c000c040340070032036441e2090b5036000c55000e482129040c58a16039a014500640740390040a00c02a1400602c1c107401541c1074034600f941c08001801941018100548000c1100240038100d004400b66801c071300842e40101001c441040d51003203012494001032812020080000700c080d0b00903004142d81c9a41c0c20040d18400800300d03000050514603500e0a0294000c044020602440c10b0400b000b600c040e1280c06450881020b0030303d09031910304650003030110303024101c0c0c04000c0040414003090300800000a90b03ca0801a02201c040b51040300d40303d640c6913100c510340c01f6164010f080c003071419442000ca9600701c0d40724131044411840428001001c1d6101103520307100b165510003400e1400482c07510050010034607500944682c1c240310540141381100007821495035021a551003045469691001c0c003003010300807081002680c0c1a1800606500c1001948254840d580d0079201c1c0014134a50070003100c1070600c9044000d132400748044098810f61040c3d0b03060401e4050300107004500c036041c02c58 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 443756285 1250 443755035 443755073
    0x1207030215070c1106090112020310170109050c061b01061203020d08060102070506091909241508040f140105010f061409190317040509060d02210a 65
    0x804031011011041c4660740c01050401000906107006001ca800c00c81d44c0c089000703040d80c6a03503440a0303010050303c8814140302031101e0305200000300910030b510040c00030255413080e82c08a1004d01d00c0c160b010f00380d0310681800f230415000000e00e001c0d02c0c607000005203030303081009444203120b4a100c10701c0b5003103682946c0a0110f02c0e0b5131450400030503906100640842da000c3c02c20049a003000030000703688000601905028080001e441901540d4040328000340250500302084010f071990600b03009081c80c4180c5602c40e03480603082054005614045100342d0700364a0f2101803a9010080480303983d01c02602c16918505481000b2004c40d010661a001c40c0b21420000b00303040d40343c0396841c1040300251b44943c0400c41424050404c02c140b500444420000407628289501c0c40491046a10243c070340c0000c04c69001d5407045449000034002502c21034104403442961a6981000d0001a10309002c00030f5100c4e28000078600e00454890001c4182c82c001341c02c540ca608403a58402e0803944103000651 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 443757535 1250 443756285 443756293
    0x10090905010203160302030f180106031e02210303040b061309060b0a1208030a1109030613050114010e04060c02010b180103060b12120f09040603060219030213030305070512070302 79
    0x440c012001190191307050342c5140c21840c61130b00010720102000d02600c1560b402203030802c10700442c0425006403000d1900080c40d40188a45209221000c00d0090012402420b2224290076125510003060041403503003c041c0d032443d036480d134610722a0200203001960213001d003000c103080310950744035101849100741400240c2c4840340c8108000003446034000c40d1210803044c80c82c1f0014101100741d81d040300c0d901c080400c0300c280b1444075180c640281c003502030701803150000300800415015080b12446000c1e400811140c11701d02c003d041419000d00070302d40c800c40c0c14000320780091440e03070024861035107030300c000224020048000741030030b503801e0340f515406100e40c8010b100340401da225451400c00300b1980c01130102e401a00507034480c00c01603580d002125001c190040302c0001e403400c94106c21002402013100c2038413480c0000080d004001d0f90743c0c000e90b820030b0101046020348201c80040362101c5840c1d101500d107a404948543c0142c2d401c581d80e0003800b40059900000c0b030301070041e00d03200c4e030054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 443758785 1250 443757535 443757541
    0x41b0324060509010e09011d090a170406082a1b100614030118031b0c060824010e040b06070c0e07270e0402030c1002060a0c0306051810090905010203 66
    0x40a05d19040681d41c41003c0d2900100004c64001d8412000c00d0711000c0f0300311840d6203102125052048042d80070300411411054940d0401d0090010302c1500c0d4140c0b1503014a480e01c0c03940040c0c1641c10304031042c04003005400c0701e402260780c102400300e44294101e0240404600400c0d6400c00c031207521840c02003910f403a001e105d4205240c3e460b0941c5201a0020424020070501e00314280a03020710107414005c0752040401044c6d8201001094160042145200c843c2e4910f0003d00c0090110740a440740914241e102e080c3c911030142800d1200c9059541100d140d5580080000420300025160b500000c00c00210000540c400d20440041026000303048039850204030141400402000488040814943c0c3d5203000e1684020f64080e6101c01100445075a12440401d1920044c680707103a601c2011100482b601c0d660000c1c45600c194003100c420f200380700b00400c0a40940d0128040c040d8003c1c0201411143e04515144103580700e480c0c47c640001c2c80c3e90342e400c0042143d00c80303501928507035000010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 443760035 1250 443758785 443758787
    0x516051b0111160e060d0b04030c110f011709150406090c08070b120703060b120402032806020306030307290609042301020903010204060306080606041b032406050901 73
    0x181a00044980001c1c1403d030b01c100782c1d03032943e00300b19008480151010070040342290f12032800d842403069221004840a0400d0b0401504030b441d0314a0403100d0450307046200c0d07400d04185038040000e40044e103c1e4900c014200d40140021790f4000c01d005018410f6201d80b07005048040b20b0030380254000c520020381d00110b424403400d18600358004401c15804148104400100501110140310349645e480302c56460754803040f001b42c140c1350300408140001148805d4038100c29071314140103d1086044076403000c000200354008a071825205413609000340701c22800312b00140c005540c0020300600381e81c0342214a03614003c041c8050300d69000b07403403035038000510f504412007000c2d50004c0e411101d030350175454290381e43c068601c1c4014070f030303502a101081481c1e560355007501510301d41c00c0020001d5454540310307a0010000e1003503101d2140988500c1011803036505041c0f00c2c101200420301e43c0544000300c1da1400703034060f0414100040f1341d046011604d9102044000c07200014150a03a5201d58072101c20300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 443761285 1250 443760035 443760047
    0x30c090a2915030118090809040908180405072a0803040f05102901030b0604120309120b04030f0c02061b06092b03020d0212040b0a020405030a030516051b01 69
    0x3000c200b0350740100014008010480340c5a0315056041c0030200319070358a483c15082c64081c1c4068103400a04012001d41040031031005402d00c10102a040c2d4150344070030b000c11059540c180c03034890101316000c0321542e424459500390540301c20490001d206a0f041c598070348800350b200f04c2d02520541100a1420104001403110312211410000140a10b85404900c40c0c034a081c2d00070412040c885c076100030030341d41e4001d0304021060072000346540e031220381d01d80040300f034000b051800320b0009100510114002145004030b01c0a03a4101032300306100e82c1c55650a88250411440312801c1c440e0001200c40180d66071401030030a042d100842030b41122421048901d0400007402e8401c064000034ad45c0c00049400c400d65042c0e42c2d030702c20342c5814400c24017801079000f80b00300c0401c22800782c0000307000899050341c20903c90117240700e68400d18040d41c1d01e101d404100d01a500403ea80341d00801d845901180c800c1c80902481d135249910040c0d141c83c1940d40b186080c2401d401c424a014159828820942c5c1001e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 443762535 1250 443761285 443761309
    0x3080402032b03091b090f0c14030a150e070c0209090f100209010504231c050303012c0a0b0f041509020a020717072102030c090a29 58
    0x11421000305a11002851520300a80041c02e04160340d80031010705003d01c2d4007140d50420b1403072980d40c0407580c41d0718a4001801f46103030000025400d0506403410544501c5103c4020b01c1403000352402d68542d4040e50f006001e04107800e04480000101c0816a401359551540c06040661905000c0000c244144048801c0c001c01c214110342000082aa41900c082224141081c02d03040c0186c0d40e1680b580140da4900031600300380b040d11600020822903481c15503042e03008080499600703a1894114002049621103500c0c014410f41040c40104092611403040036004600d4403c10300750141482d581303011030842121655807041d292042c401e9503040c0308400d000301030004d450078010400d2460303103130f4250385c03451003180200360380014070709200c2d4800d21110b00541100b40d50341910314810155145c1c0c0b83c0076800740108150240040044001090176500210359000d006007104203c80d20401484507401044550741070348800004d07512601c2447d4544020004031510080d5007103000500c24507688013 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 443763785 1250 443762535 443762563
    0x1c05030313050c0a08101517011e0b060d02070501230601080f0915040510020f0c16230103150f1e060e0d140d030605120a030813110a030308040203 65
    0x11803018400038401241002c10841446d50100b40c01d42c400325950039260305130384194a1001c4c3d540b0359004944040d000070442d19050b844c252000001d00b40141c00301c51f00704c554540d0102c4100910002a4041e0f00130f0040140508000600d4016401e01d0101c1c495842c0051140000070740c0030400c583d07800011311a0020019040b914161a042d40c000360b450131000300c0d0655252a081c00a01040000c100b0004010300d131510640d00c0d14880c1d00441442e802802500c201409003041100c00749140c9851042202e8008090040c5031140500c2c01e00c0c1401c401000504150b00c42171202605e5403070f07190010082c0303440b00c0c00410f5207240c0b4080482d05047c0091102c86c21030104400c01020ba0f03c4082d45084c100101c4010701200e02c00d00e820b0070307460b19828000d85c0358003800e070320125000d81549c458011140103490200d800d58000c0d00941c2c0351100000c00801143c02c0d440030500e0151015200c00c205440342c1d808503101e031001e8000030713003401e102e03801140014200703003c00085060a0054407658030030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 443765035 1250 443763785 443763799
    0x1020d0618150e06060c010612120f050306090c1b07080f070501110c041e0606021e0f060c0901030e12030a110a020c10030204031407060311181c05030313050c 70
    0x30f10707000800c1c440d0094411480b42801040b11265980d0a600090003010201700404844440f0714290381c1201e00303a074180c40030072440f52041c0103040c000c9086921803c0c4c003d1036013001e42d40303080d0100140d81244401500007103020b000980c0e550b20802c0001d020300003210040140d00d8004811600e4890309420160420082411031400710100040c0148405802ca901103120aa0030709610608240c0842c0e1190303560401000140454020600ca4102070761401260056480d8001c51559420f011145120980c840400030700600c21140c050903114505140200d51409003103209031501c075031224040c01c0ad80340042808079090341b0303101d02c4e04240c0c15101d00905200140c070020307460f0b220313181c0d406015649049403060349a02c0b982c1140c0c05940d000899503420031469000c913944520710b0158030013003441c05224207007020380d0030256256520f030000d08804480c050424819040102c07072030f003407204c41c2001003a400912f0600c0038502c20b040c1565130360140c080c40d050540c038cc900b00c008045c1c06003035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 443766285 1250 443765035 443765039
    0x30f140f041403070237090b0102010507050a17060111070e010512153c0711070f0b13080f0f071d011e08031c050a0e0705011101020d061815 62
    0x1d030f80d09085110881504640d111540880f452071b140800d03281c42d001661390140f00815100015031012540c100283d000b008681e41d003440955103481428040742c0403036840d410f001c6040e10f10200444c0d2046062500105442400c04220314021041c0c00104681003403030700500140c20b092403032008481c40140101422800b80d140d8111249028107030055a010503200c0c1c200b80e03215403c011102c0f103000942d000b0074840d0444415030342201603500900107420b5442500844400148010680b03805080203181145003064940140e4424407c9a504040080c000250f0403000d0287c600c440d03482c400542403004074141502c2c20004103400a802e110311103114038900340e9516014a040d1160600c0541d06191a2103001e0180e185030740c480100c41c88002000c0f12610300c8814001d4203501c90080902058444c03003910020364a40c0041041a0f0b800840200140e6200f2203820228403140d00c001803405100380d07045015959281c209012170541c0754003444941c4a07920626070608810304050308442c1c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 443767535 1250 443766285 443766289
    0x40f0909150507030c033207090803070f1a060303030a0c030f020c0c0307090c0203120a09140705120c0d0809010512071e0e0a03030509150301030b0402090609130201030f140f0414030702 82
    0x40c0c65a098610700c904c40c0000203900c8e900440c80040a011300074200c030303200c481ca49011204403024402c112905034584100c2c100551110281c940500c10050165085556440c941c80003850320b003141c801099180d8481c800509601d2004104214030017014049010401d82494504010f81e4051036035203103004d03201c40b5015404816159103020b84282010162a20f4201101a1a24035005030040301400c2c0300da003820800140401c00c65a081e0789842c050380e21102a551110084100c603034105085a0f0507200007600071000382042c0105040c180e013040d070003c0020440d407408945a00214140789112006080100f242c1d48255440c1c1c036082c000761658801042c80c40741184001014008045100c0071103544140b0490145100540030a450750380d2420181d82421060728280e0141c240c0d00c5c04203a0909140c840300d88940d00c401c0421091880690044008000c00405107600307a6442d50211032010004400d14029070808601342600e081c00c2c01e00400b8220304a049845560041000800603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 443768785 1250 443767535 443767601
    0xd1e05042915060910020709150b071e0804140f27040c08030d02040302040c090602030a1b02040c11010b01030c0c0b09010e06010f06090506040f0909150507030c03 72
    0x400d16112849029240b0400800c8076030080d00d0300294081e4990420368501540000c2c200112403990344180a040d03411100a480e4818500480502000c10040480840d0440c901324030060000c0d505407a5400c4591511101600030b500071480407408001c0580117445d141c140d034090860100c584102101e0711041d01b5894011140f80000c1c418424400034061000c18850040108060019030340e50703548041c2c100d4025407081c00101c1c800e40c542484a1070480c81090441d0580f8420b40080d40b51504485054a0881c00c104208600340901e4100100607110390280e041d1119803519003031114841c05030080d0030744680a00c00e40c101351405d15050752032548040007601c0142c0044540320b040d01c65840d1b0a025040c60b006402040c81120000511683da141c4454220b03141d5684104925480300c0801c0348512480c40307080300580c2c403c002440710035103070fa001007000c80c4108107510711190040c8140c41910422030708140803c4c0e48499001c3d62a405004849840040c0108035504806001d0070f0000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 443770035 1250 443768785 443768791
    0x40e0406050405010b0901120302070906030b0f0c0405100503070e030604030f030c0507060603050303090f06061014130303030b030705011e03200301030b0106091211060d1e050429 79
    0x200c680c9803004181881001e512a0b40a00d2029100140725a11030002144408503200101c00522a40c42c0010300315003644140b000b500d03440b00040300543c03251070b4001010715020704000c0d5410030030440000c0b0b0380d0380d0107039501d54551982c481c117480740303898280980f82451405105000f0741060040000003030b401800604643c00d1410b0002d918524400304a40c103004041c0c000304000e103030460100c14090008061031081d6140302c1185c40301c80b01c007242551901d03003c2ea28140c010100080030600e96002d004c01c110b0401d00c0c81040c07400c240c2400040580c04140354415030100b81d07141c03404109402d0502c60307000640380a081411860a1013070749518401c15049011080640d29007403100700035001b58980d460603540b001c0307003512541c417410944070180081c0308240100b1850080050b1280000380e0070314041c1d401111100c41880000207210065003d04071b0011002e541e402e051040c96070341c03140e0300c01001003918001001c2c503283c58200382d0099180c00c2c0049070384034034145442c0c01c1303a80c000c180c0d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 443771285 1250 443770035 443770043
    0x40c0e010f140c070b1b0d0207050d03140d0519021218010b0604090b0406410a08070305071a04090e0c060d0b18090a0b2d0417040e04 59
    0x14490400b40340409000e41490115140034070840018189aa080906019820f050302c190401039901103441e60b40c00840102c4015820a100070441032400c0300850341c00b207000e0304000c1c000004180c611401c56000c8089146c000381e8820072b200070155074031300e014034095214004618003822000d517a00881c600400d10003001c2c4448601c0840004290000009040e0246c006070b00d840d01d42940c0d4021306a03005015000320700c0d00b02c0002c2d0300c02d2450341c0140310124020181c6100070709140c8114000007032403003144130b85040f40c00d096050b8a86080364002014100e010341105420351508a003810ba05501240304140000d901e80f10a603412000c5400f10360304c040c400240910904480341c240380c0c3c0d0051547d4084404103802e003801c1201e4204204050b400ca07847c9a4000b451f00851040c184140e48401c0a6803080c400d600c0020841c0c12804d4004004002e009070305c2c0755031420104050684001004900409018807040042d01030700410000045510542481d0800203100182c81c0c1c020000381c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 443772535 1250 443771285 443771297
    0x201200f070b040b042a05090402030f07140909070b0912070906030f02030c030d0e0607020d0c0303050415021b10030f05010e09070503060c0328090c05040c0e010f 72
    0xc510121290120791440e40c0c00405840c4030315160030510701d0b0103400c803000d50b410203c44030709901100313110402d1203000c1d468081990140e81000280841200020412a01403043c040703020b11401c02044010f0007002c2d0300040e030910700c520605011030004060412a49517000b0351051151584120544810141c1590b0101c01640c115003243d1a100071507100f07681303080c94061b010040c444131458494003140242c003100d840b59a04001c1c90b07960820541075200003040c50780c94046501d0301c4e400820495000a0048021011380e4486a5004032503920032804260001801c2002400391030786540c640701a03001903c3e801c036600d511007858904100e401e900c00d041c4e02c0c914207a4035010382d1001c2140102c04004218641c0c4941004460702c40541d6001b20902c0b07203050006482ca40011698424502140d070f95065031182080c44185039810303984c00c3c04100000f041c604040c2114405d07480707228064001c50044515000c18002201c840482140802142c48105000c3c5d91300944040340814091401c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 443773785 1250 443772535 443772547
    0x70203070e07020715030c0306080606090712020d020d09020a0e0106050409020f191d0303040315050408071e031805061e0f0a02100605012d05071202060f010501020120 74
    0x1241440301c1c68105005984810780d59405c0340380d0503803101031001001d450070083c1540b40c510040c0e99040490701d1503131102a4000188a4a22510481c11031809510b005400d00a190200384180e070494510001c1e000e42d01e5910009524011405000410341100300c0d01a55041000040c200d114174028103500c5a0009289204080c0300d004070740290032001800300e071f51001d86900910aa180700c0410030020b640e10013200451038007000f12411254045a40300c094002d59a6a1001e080b00a1040c0c1301c0c0306050002001058909070f441c5000040080ba9500001542c500903016040807076158141144601c020701c0192541812984030800940c1460700840c003400c00005944070b042615440c403540420443c05003a000501c8036400002c1c0c420504c21283c9410044030004103102c2203441c20160608040d41003c1c0d8600d04110740e83d0a80f82080c640750840d00d4407480501c0355000440141c0c00744003002894030129803050302420003480240100d41003048114040e10300c603c00d100d00482c0001350 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 443775035 1250 443773785 443773787
    0xa0b03010501080c070309050406030503030609070203090a05120f0111040905010609180b03070315060303030e1219090b030126120301090b06280f0c020d0b0718090c0e0402070203070e07 82
    0x87c98000303280c003c100740001900c92038400d031a504295041030044004038040b031041c5001109481c12441e0161400c072180e4076002c2040390f40c8184803818038680c0201c0d400000407000038010300790300b901d0049040b65581c0c03804010340210350f8140e111204004160300d0900c0211148441020502801c84000c030f08403903c540024241000341d8002880f0aa8161403c000d1182c0e54000c2c0c01228005d4404009050b011900703191145040800d0064040040003007401c5038040c0d55642219003060301d0040d41c59500d0b2111240164400c0e08414018014843c0c841d0030503c0c2c460031080b0000c00f076405810b410844943d9804103000c1800b035880c64507100ca4207003003a500c52a05075240181c5403003410300c40c541810080c4809203226180d82c0c3c0003405001000c0250307402102611100b40c0d025003c1d003000281e9450b14541c03d403020b0040010004200214002d25101100d400b01520108800280340821030b54050100307041c0d440211301030381c0148404005031740d02013002004c07600e07104003207c815524600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 443776285 1250 443775035 443775047
    0x10603170d0e0d020f0c120d0302130e130b070e090105040c050903030d0c11060c0a05160204020a030e010606090509040f06090b070905012d1101020c0304030f020a0b03010501080c0703 81
    0xb101c04000c0c820214812402a40040c2d1000b1070001709003541e043c0d1303030807100384078420714911607100c0d850b8000194400040c1c0300fa0700030311142d5a64100103070019121403448802010a5803c0c00740b107200d45070030320140450462041c0c0c202e07450f410449400184034002c64000b45052180c14800c642d500c2d200c0486500400440d41111401416a55150700340001d2800820410b070b284c0001800c0da080c0c517840003400080b094026500c00900307a0800da200c100440d9940e12a0009046081d140122080140c84a00241542e4141a1000300744c0440d80c0048070b084444a50050f010030051141c10041c82e12103404170754020307411001c0049411210708084000d0001250000d00766458182004034055002645800b915426038070381100003003410001080381003418611540d403c018810790109406186c0c560306507060354002600701243d00014a0940e04503500c240c441700f001407002001c500d06181030f800038003120f920040c25941030500080a00c0e00003080e5030794503040000c044051601501c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 443777535 1250 443776285 443776301
    0xc030605041503120e031e070f1203030b090118050a0b06131403011109010c05070f09201207080c090418020f090f070c020604030b070203030612010603170d 69
    0x180091090404030010030122107124801540d1400440360541c07403085c4900311564100c4001401080d19105618150407560b16070b00c0442c0140c4603942000440c018544120b40c000d0442e8a01d02540011909019007600e407070303400003482548103000502c0340d018000030104001c0f4000c0e0000030207503640011341008003400c02609500100214803000e100c00c0c00380410059461140b0740108075140c05080c9800d80d00c281514480c034800500c000030072548280100b85455001703404230b40c81c1b00d56804040c0c18a440c80e0b00580f846680310035600b01c5080100b642420f5895501c05600e01c0c020340390384603405011010b003202d42004660404101c96018580c19a0b49484009200704450110781c0042c5803030b4038054204038003483d6240c41081d824901041060f03c00c4501406000086d41c83c544110345c0301d0381c04034080741c0c040814800403011407681d00c51076108000703a4009560340e040c88001c000c011342401c0c00c0b50030541e0400700306000090400c0c07032641a2803450401151a6040130300d81c200900074003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 443778785 1250 443777535 443777539
    0x28030203090d1101120501030b130317090c040b0a03021003020f1905030a0c110c01030b040f0509060615180904030e13060f090c08010b090402070507060810150806040c030605 77
    0x2102c40000d1010307075000840015001d803103111502085000303490039030308240b0015101f2101940022030421100c0d1a0614452007481c0c64080c0b500ba12002104880003a076142c0255800313070b05840c02e2402d051107000941074013200e011b083c0d18038581c001080e1030b0403403000340205a008207078a00207502d10800d0b184510003c44181000ea0f000002c000c009810031107044003101d00f003041038070382140900c848401143e0307000042c0011205040056014000100701c02c2d801c40e17a644c005042d10310790351240c0d60040890401030072140c20400c0402040b80701074000c2300d2440f4020480c00003400702c5490107103200c0d2000d8030740618641c1d03030742800e88040d4600b2154a8010500fa610003940c5001c0b45e1040d01590700504c19030681c140c8071000c25040700c41c4c800d0144041a42c02d0010b000c1c07a8550405030440c40740040c40545422038940d03c4500b048510340c885030129a9104c284152038070f100b4440c10107482610501d00e10722011150083c8058000f0702420300039036843c00c8018140b842900000d024080c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 443780035 1250 443778785 443778799
    0x60d051b030c060d0c020105100302010c060e160b03010e071701150e12100f020903191104150e1510050901020a050111210108071a071a0601112803020309 68
    0xc071203405026040c120320a17401035203040001a0070607250224902500e4040e0340745107051980e955000c000701300e91088801c1d207100d0807001d1005015411001400751101c1140c0d40d481c1d501d803141d9001800030140001003401151031003c84610802070149045070ba405da00c9612444480d0401d485407480650480d422400854080c0074200c1d0018070231685801010040050342041e05c601000ca005416401e40d064001c84010042c880b20a0003040c1400d0040e249100000e02241c00a000c80303114140341c80800322846001c1051103800100180d03c01e0502d115994078007004800143e09804005c0902d051103004582c94081c1c3c0d02c20041c0c01c0315590b101300200b1200b04a02c014003019089400400d01c0c008140c400103941c100750070681812240d4103030080004be4200100d65100500c103440c0b100f20700c0c6091105001140803001455490b40346035009440c10308207400010302808101141c000c441c1e00507280b0310f100f85403540e0340e001c00c886002621031040c1030701d1404908600c40c8642580d48110707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 443781285 1250 443780035 443780047
    0xe0423100902180702030319020d090308010617040206041206150305010e192d0b0c031012170f0706090b060a08060c0a0f0c29060d051b030c06 63
    0x40c0301d90046044900031503a281c00403060f161030800560f8111090303070060b0018070104e001000e11b500e1a45400740003510140c10f003841140550b003180e60100d070075400030300900d0041001c650841442030001c42050380581403031a160b004150b031880f8500c1800081380740c0d8080035007800703160b5010041c1c511139490980c83c200e40d2801c2580c060b14001c8000c5d1030a00500d0380c0003503014000103465195550001f0307035204c21000c00c0c1c0e1900e088099000c0c0103440c603a2200907440024403c84105104034000248552607083c00400090030200c142c07c142c04d4040100e07822004200b210500c051100007000710a030752196011200d20150003010001084641080721100800c0300000e401d07885200e05568a4825982d40ca404076900c0a050b544140c000b402048403003400c52180214001c0c058003401c00b020b0200180e91915664500c030070b1066202c002440420f00e0b2801d0b000c20190300314900322140d400e0342b440b503110039442c0c120305407003240082007051051800d5101402002072015004010030b407a08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 443782535 1250 443781285 443781313
    0x1c0e063c10030507140a05190503060c030f06010e0f150c1618020304020d1502130801021308120d05130204050705070c0801180b040302010f05090705030c0402040e0423 74
    0x740c00c078042107560b4060740d4404220284d0100302c0440e804002020f01302c4031860001405140843c0c0540140058205e503001304170303610204102401211101080e541d64542108401080280900581e0400046140b940900d5664200300c6072015000c45041c040d100f040103007019244038084a51000c0c0c00f401c005507000d05041e050724011582100481b81906801c81701010881c48110340003980103190208000100d0f1b8900b080072071051202900500d0003518000046840c04150b101e00b101d42c3d0000380d949540c51032200c581e001010080b000301580f41038000000c070315008011502d80101e82c1e45000503d2041c1d002e4540e1080754003c0e10400c02130900c000010002da00105082e103184444039800540b21700144030b15000c0c981280804684158aa6118002d07030314081c1042d01150749803418128007104a10800d40158102c02c0281102c0c1d150509160078201c0c0494074600c142d00c1400108400301680429a501540c03103076448003403044d111040306c0518422640842607110b0f03159204104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 443783785 1250 443782535 443782561
    0x6130c0201020a08060609092a030112030e03010e0706111207080909180a02010305040305070515011d010503120f162301330b1c0e063c 60
    0x21281d95480d030709586505c184581d41c030038185520f40210f0244005207040d220612205042038000c1c40a038010a01c58003d007241d0340080c3c0041e0072090f400e1020b038040580100300381d1650031040d0300920900202007006510345c11507108403070074009900c01e168080002030001d01c5010403501095610f400325802c00c0800c54000c2c0c0040ca000e8408103002c5000e00c00c11441442154a41c0b40003040e002d2820f030300440103404017410407800e126061081c040003800034401a04050700c40e8400031100c0d89066401915180d1185203001c17400c41e8480140055100459142c0d44c0c0107045641079610026042051040e1141c01020007580c0704501c228402c12050b44200f00c891010f1070780714914103248007030281c00c075058100d0f80c0100d041c0719141915001900040340304480d41040e00d49540594480240c0c40b00d1784041d0b030b080b034023481540c264031555140e0f00c5a0304800d000c840c0104124507000c600301c0381c42011038504101c042d107468a1944c268507100302e0110303854549000724156003400a505400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 443785035 1250 443783785 443783797
    0xe010c0501020c0705090c0408030a050d06210201020c2b050a1203020c01060905070516080f0403050303040b160819150605280c0803060d3f080f06130c020102 70
    0x8071b070a1600c0401e040e08100c44c2034400b5900d156003d54030b0312080c202c0603141503002207500c2c654661034440c0028401c8501c00300484820282c2024413821045100080c280000c0c80815881003803d079030405444200302c1e10050f075480c4668010301424419060162170000301080060500c00000354104020f80e05401070411a10200001c5c005140c4595001007541d1080b10090001102440416070300054400005885409000044d01d0020341d14503c00c0c0c07075130250b00141c40350f42c0000240004c100700e440b001c56209101824800249408000c010003850025001024445010801d6032600302c055100390360600725000b4000301784d41c0e01c0c100a001a0840202d182c075070288044881040b05081c1c8862298400d140e440c805600c510759524201604040c20f0716030405105406200062041d10603c0741d01b0120384948080d2444401440d04a168500083d14000d120003c0070384045811104640e0420b841d4003040c238460392000041541400d0342c8130000c2a25007403144440c83c0d6a0194002c0c50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 443786285 1250 443785035 443785039
    0x203092e1d0c0301090803150409080c1609021213110d0c030302010507030e100f0e191e120e0409020310051f030213091719090909050d0e010c0501020c0705 69
    0x1034034207002d00403d0b00701c0e040800007514581e01040042c0d0306001954981440d008010400690480651540100b50700201c0c0b10304641c1e44a559a41000186841c01d0f90041485e004190301e041d580e50003500c8840b8014050344103010a19004100304042d64040c95103620001d840a95500d8007800d018040d2407082c8019400340d441c00000c504514030900032403524032010703c000e201c11151820303254020111a8110701d40c00d43d440752450007010017401854020b2201c0d5182c0307440d002042c2801401410b141612454050440d80104005810348146002181d22410865051100360b004140a0064104001e605000d01182480103070780c07550241e030055030f0010070440c14503100d8400710b84448490101941c000da2550204600d041e054100c454864410304040800003208142202d00e90000364844c0c07000705904180c500f44d00d5202000c14010312202000703101c1e10f0103e485994031802c00840c0c8804006c000b150080041e4000c1d401c0400d001c1c1d001000f19540d08113030801070307243c107440e005d124 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 443787535 1250 443786285 443786293
    0x60f05160219080a09090e010b0411070f080f0d020304030807032403140304080d050a120501031e060b0613030605060906031b0f062b0203092e1d 64
    0xc40803480000d260000020071040041e2425035a00c03100d0081d0000d0300328204100e1030040100d0a04402e00803120700f0131800001185202d01f400400041d00c0181c0c41050400d00300b03111071004224130309400c40f450394101c01c0325555030340342e520b074400f281c45080180c03007030940000144010150b00060443c881c404030f590030880b580751010b24504842003000c4143c0320f0400d014041c0701041d00802d00310303e40c9520100f200c0c941960307501d040d801c142d1325401030380c00700f04003107000e18140b6008565540315000d01001004558110744d58445050aa50b20441d0304d08018980241000a1a0301c030713000b000c100400e4180c0742c201c050901c2d0282c00b00303400105c40d1141010046800c0f0308116103180d025501c01405415403136040c84502c0507405640c200180c0c0725240c01c0b83c09805031120802032000002c1fa40d0072014102e5000c040294202d00322111514541c0304004100c04504042001484c4845481d0304401484107242002d25294000703075401009480d00c40c020b107907500c81e4002c1440c256641001d031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 443788785 1250 443787535 443787571
    0x703081908060415050402180a0b070309060305061f30141b0705070f0b07060e07180b0103020405090a050405060c07030e0409021206010e01090e0a080403060c0903060f05 75
    0x1000c10ba0344c1c1307003070311300785800144c4400d118518240d000361040d80000d00e001c0c0800700444000034040700f500d40c403440d400b01c0005a0038060650103502c0001030880c13810b051003141400008240c0c400b500307030030624042c00a105242c040c1449102031921540d43c01e612414926104d550011018104540381e04000f440c08078007040d4821300082d181d100707010384103240c4040c0484407042c0e0a9035024130303822103103401022000710b01c0c02141011040580000e14840f0303100c15031803501000f00c40701c4241144441d407051130b0401840d103046803040c041001100011690762041001a07020b4021340d001194403d078100c0401c4910303a55984070300d00c80c82c0a10304545aa0710342c1c82a124047c1b1550f4000303000a1402000000c40b8205600404049840070305055440c0c168540075a040500a030014014401d400d07004002040e4030f40240c00440c1080c102505040c8026501e5521030700ca188002843d0507224001c009039a801850711500030350b001441407004407004540d010040508540802c884126040d00d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 443790035 1250 443788785 443788789
    0x3060806010509130212010f090b090c09011523091c030e0405070504080d0e090105030c0102100509070b0409020901080f040803131403160c050411030109050702070308190806 77
    0x4080c0c100c500142640e03a49031244c690100ba0134900321001d80e000310552950440041c002d1180315045800c144c00020400715528041d202d282c1c0160200780341d54042d01030803045030364480308941113500d880111040307192124003d41301070601c0150b000c640c01240071411594081d01c8010220070b00120742c80c243d5041c1c20100803424621080000d400074030b210091034424182544425040005410114201a80d0300855450211108204800980e28041307459140c00c2c11400c09002d0407089002e0404d5100c00c5e00000c2d5507103900e60701c80d00b046446d5404510080c50601c00f00b4081c11a004000c0e40d01c9840e600d60324043d6000c0e05da1580020380050000302481c00040e00d142c0980d500190591a5490328107405403110003248003501c800204808071268075100700001e00c40c81d698800c1807610204281810503507945194000d502550a02059900b07640944084038151903880c42c0000b040d4403211412445c204441e00001c29000000440c460b08194241c0d80c081103003160360701d84c040d0383e882c242 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 443791285 1250 443790035 443790043
    0x210e071811070609020d06020a260106023f12090c0d0f1b090605040b180103120c05030d02030f09070509010b180603010e0919030914011101140106030608 68
    0x11410820400c103110320342c0002c000b60000034806000929010001e5415211041244d01111002010481141c5507061021150f800c800700b58210340600c04403980b521101070344030908070000400b001c0202031117401240c80015501022a5a8901d8020348000300c0c120340650703407103e0100c100d940c3c80000040c007800030004541d903c05074050441050300801c6d42c2c1d1074040051b615030071109030400d003044010041111082e48000d041c2c600c0c0128015140900740b00c00c80d042c030241c00380a48508884500001c0000d0340003170440358403010003285107a101108944250a0000043c5a400000b41a10102e02543c02950140d49d9803140d6401c03d840c1c034902c1c0380d9120080d104242e0080000001003025001c1c0030054011104a074a885200740104400544180c2c001d030842c642aa009805010b00031100700045280110300c90303551010a0b003942c9014000301e65611488104d84681340000c4a580d01c1000c22040b640c010030300034010f000355013002d4031071b00c0824062070f40040e142a0300040c00c00d600003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 443792535 1250 443791285 443791301
    0x1c0302070609120c150911270703021b07030c0302090612010905010218091003140307020a09050702060f0907090506011413060e06070317040218010806010515090102060601210e0718 80
    0x103018003c4103009041c001c40f45401c90230009001d03440c0103422100809a4030f8144510459500182e4448019601100071940000d0300016684002014000070f481031100c0c2d401c0d282c0480300540c1c43d40d00c0500086102c01c811a1070201381d42031001500401405401400d0540040c881580780c04520400740a83e00340100c480008c101d0216030104041040e00700c0d680324041206040d40d2404000d5008540ca81510f5400840e51664030410491a940d040c001a5040480c0085110003814007003c1161344a07518050303000490703520300104081d40c0c015500803840c100ca090350b0945032042005200107105d503a1094001254042d080c076074403480c1410840c3c25065143d00c40c0420541c040300e030040c08203c01001203800c504a04480c02c0d40c521900c0342c2c0c0c0d000345807800041c00d59605003000e000d440d800704205000311010a00c030410840e80c01091140e40040700380780400c1098140c0011103001c3e110310303134110b040518144810303000c0040441c1002c00d0f82c41c829032183c02c11026500003000c807440c0c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 443793785 1250 443792535 443792543
    0x1e040b060c060a0b120a05030c06071b111c0b060112020a12150506040803130b210a09120509010305060306090c060d11030a0515031c0302070609120c1509 68
    0x30b0001d40700d450aa40100c4c5402030103002100c20740c0c807004801e0315143c00c10505a07419800414100d650700d5081001a038441d145241441d0000150128013044d4000380000521029075030b40016440c7d182d5000e40800600080c00030f443d075100c03508060300f000b5021380300140042c0e014415030140c07142c58022614010007035030f0755401d03540c0940c403a000100700e481e14040b006a8000b40c009407a0341c5d5800a8030260000e04080e640c1c40f51003409074041d0f0781007688025150b40090021a102e440124103440100810081c5c0360030907660010f45e44010183c204c001004c20a0f800c4544107080d5100300035001900342a00c041189407aa41d0400d99104d41c119100c0c074181d480030740680c6950a03ca400303492001d05011000c40c80c070400d20810425500704407012141c80c6d54981c104120700d4241002015851130a0b4040e001c0c541c005264441480700442044c02856000104402004415400070008640110420314041e0b05809c00924418034004c043d2104542c20f104031554602074840c0b40303601544 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 443795035 1250 443793785 443793793
    0x2214190b0a0207081b03270108150418140705041407050a0c140c090a02070b01171009260c070501030b01110a12020609010b030613050c1e040b060c 65
    0x51540404083c1d80301c2e4400b140c4029090045081903005a0380214910042502564440c6000100700215582d0f281b40c80031505960a84141280d8210340a160490750100303400040c49620000700303000c1c084003102c04425000d01c50140c81445a10041d040d0390f640b04001303548041c0c1e6600104030079107012942c4241c40316408004600d0240c0118014510f0079110700300007411222a4542628561200465610980000000d03404034a440c000007944104000011030038241251140e15221205004007034003040007801d0500c1202c0c0030400c83c44800c0200006000f86004e07403805d049044410011009425a40048941d21030822000e5845100f881d000030046c0b2450301d0700460103800c048803101e05005440000c00c1c4000818400d0000c0e250184488000c5030036844002860503000400c02c2010780d1500c0264a016034021603901c1e001007072403801189210f420b0500d5414015030340b051551081c00f00d02a07000e00010640c0c80c4951200440e002c0020486880c28040740d440740e102d800c1c1d91b90300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 443796285 1250 443795035 443795041
    0x180b0a05060a0f0b2101090618092604090e100c090806070c02010c120c030806030607020a03110708160f05011b1407180b0406050f01020309092214190b 67
    0x30f05003d80204920440f080740c4c182e2241e050303000e08a0087e005048551b03120541403101f172109503542d1404034a00b903400c101c07404058540750071009401d5400400301c08010b034980005c1000d00240d8000e040411820040812500e050590b00d01461040c1c0040c58100b11469800c20701400c1c168003100c0c08078024054556403503500b11016030036210200e050104250514000c1040c1034480c201010280e00c03031010103a058240039242c0c0310003d188078807aa1081c41008291980800c0c8e02491680c5070600300e4250070285180c5061049039040348045200c4c1817090304142009828240454420800143c0103903112001140c0100c0207a4148400c665806c9540d0005110900c00c0c4540390703c0c270350035615082c0d226a503406002c01d08030a980002521f4600c800050b01d0b082c40b640f0018441240c0d9001d03500c0b9481c2c00170351030340200b5408038840c1c510400010b48031400d0800718000c581300b045001003482c9035885c040c0401d442146011000c1e11981e100c983d4000c0c0c40345d40151280307800c80100c2103c0d50b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 443797535 1250 443796285 443796299
    0xf06070c08031305100e0c0405100605071119050a090e06010e04060f0e0c040b030304080a0209040c1a07031103090906060c0a0c172a06030a180b0a05060a0f 69
    0x6031001c0d000400803c002a110404078006001000b08016415400700700045201c419514292140c4025881240b03880305000f04146160b010070300b01d4605042072511420a810400e1400202c41c50041c0c00000100d40c0a1004140c2e14150094681c102d41c00c14949403603402600468500210b04511035006000510100d15150130282c4d00511403071001c01c2d04040c4c4005142946c1c0c12010700c104a40c0040d10901c0b49140501404008403415001581010715051019903515040d1202134021840c00b40481c081c031510000280250100c040c030310203035079108440d00d050740e445070200307400040818910320340000d000b1040742e14140005298500c5611980308001c4103074003040c040a00f40c4614a00d240005803041340c080000e042c0706602007401e40740e08985504010803036440b141000c4200303a480303041c007031392048071981c00070140d03a00c94a994500642d84000d00c4030b514400e0140c0800f912190800c4154140c440c402c0f0f10001040c03090351282c10501c40c01540501441c481000078007801c1c000d86c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 443798785 1250 443797535 443797537
    0x50a0c020108061c0c0509010815161103040807031b031110020f0d0201021903090b151c061b11070306050a020f0c0d11070302011706030a050607110f06070c08 70
    0x100400810400c20003513641c80f454150b10f4105021110b1400c2d100d4100241c1c030384901003d004000b41e4001d0042860202d04210f0010300040040000d41804881070b42d00910a814058003004d40c10308603540c0e240c4030420b0554038052403000702c949a0f0a0460520141e80100711841200d5010512400a61040702040b041c00b10f100042c00c1140b1030307458000e45800702000328540d0100c007a000181e46001d81568241e172440070b8603070300007810f0030044010001810b091800307a1150a07600301600400c21900037480c0c0b04000111038041100800c40304081c46110351280c14050242d120402d400c05000900740d80e408052203001499802c100c4042000c1200c6410060380800a410700501d4840550a200c6054001d50b16110042d40070405601103180c1211240c2100035607240104185403961740001d001c0300503032036031101031120f40000c90041e442c204204a025503021080e62030398601940c00400c950908041d6420074072600c0c010521000700031803140c0c040d020700e43e43c0c2c25a52045131159005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 443800035 1250 443798785 443798791
    0x30c1d1015050913181a0f060118090204090c1e0509010c02060412050f0714030703020d060e1e39120f0703112d01030f090602030601030606050a0c020108 68
    0x20240d0454800180601340c410411000c2c400b50785a00c00d140c450a1102085148400c00b0420b50038120521400c44d11620105900c000c0903c1c141019070a44603070001d0f10030259000070a4540041000701788441d594000c051207207200d980c1c189500d520074030b10000d181c07020041040800c908118070391043d4403c9038a009414000b804140c0380c241d4030541240b010040203001e84058120b041580404141800f40d000240700c10f00c2403040700710607840025212481c51100a02c50000c0e11150030030801d0a40000d50318941501c00d990480d414000003e003095680000038480d80982445d0028007240843c18521090002c00941d003800032000100620101480001d40e00c411840307a02020005c042050948081401740900743c040d2070341c54880c49215400c0d050710300c00c0da000e2001c00780c41c1716250b45032101e03101c02c5617085801c0c1100000503002080020b0003c6812801c00b50031a0601c025900114042c82c1e085c0c0c0c00300074007582c90380212502c0c00380000880000301d10030b001c0405580304a400e190 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 443801285 1250 443800035 443800039
    0x8060f0a0812040501020f06092833020a0503010302040f0612060b01020d0c0f020d1103010e0c090f1b03072021030c040b030a06030c1d10150509 64
    0x580688554207140382a0211258050b00d0800240a2226590501c84a00041c000800400c04c508181030050344035001008050f9003030402004a108203100c2d07010fa03209180d0000120100d50700e0514640388507200391545541c10b20000e9099010040003071088510b11a4187d69071810350f4215030800018104d0020f5512001f901c4d58008610024105011101c50340b082c50005030000944c000a400c000c2020b56240510142e045c0c8000824213850b401480e140d8102e0b010016104107103060416aa561103000340c142d847e0076200d071140c800c0040c0740648614129204010f503a16074400d00d2907000116010a0b0a01c80d5184903090b080410015607003143c10b40c00c01a00200210f00308030905d0041c4140720240340d20000026104030114002e40c81e2181c261904149540390484480945125a00c6a201e070940c0000006071052002d0f484407000e15400035211a0844c1d484030719850443c030b000c25001d140c503a1000820020080402d1084c106c81007110142c500c510221020344030347d000110340c20303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 443802535 1250 443801285 443801299
    0x1412040510020a080415050411040209030f060117060f0601090b0715050c070614150105091c0b090f2a03030702130e010c021906090503070c030605240108060f 70
    0x100d5441c1c86400908101a601d55820340345151905045488226500210661514100c1440003052020b242001003c1080c0c60160307564600c0c401007840c3c00641c8160301c0c994064034002147c4001c82c1e4001c00d06102c0c035103003124003d4942c1620692001402d48065010a008200c1000382401c1c5c500504200746c05004038a00720790001c0300040680e6400c40708a030783c9420020301c034410480140700d411203644d000c6522000d5442c2001d52840510803c40790309040c032102042031900c80d0b035081440c0112511440101402d0300151401c11001d140c29902d040003802151510000c401c000518400d1400311140380040703500383c60b102084800070f0380600941500080083e0300260300e66200304500b20b410f180d000220b21205044c40b41c2140d03c82c04128003190000c40030740607116080f01c0082c02c1260000000a40c40c401e6203070042c9035204207100200061101f138000010f124580d40643d21942c21440181d000000c00790b010100000c4a009085c003050890001c0740036800c142c51300c202890000790640e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 443803785 1250 443802535 443802553
    0x51006180b0c16060807020619020d09060c0e030d0206130c080303181603031d03011b050a03050705210a02040503010f06080c01050c0d0c0809180709050114120405 72
    0x41c285034411082628681d1002200300003004a8051240051507103183c413170020308014200035215603002d040317050260340d010041480b2541a81c1201d10015000b00c5c2081002d01a14110000d0700b0f80704100004140300d1070b0707075103c1d90501181c40f01c10148103601a080035910805d4a2048440d59441076900c04000e15003c40c1500d400c10041d0301a40301102c880a5040f50000d6251802801d841d61101c1e0312545e00c000c03c000f940105140da2901c4918080c03803004005400400c2c01000310000314000b030540c1c0004150b00a070800003c040715001d42d03505100940d580d000581c0c4500c950750900b07102c2c100c51071055140b0841001d03000c2c2c0068400c03c026140c66a1100000d007507404210020780b040c0e40d604410000140c04000c0c20700e900c0310a080881c10206086100b644443c40803041c20b062000f01c0d06100100b11202040b1200683c0c0204400e03155102c0308064001309100f1500d45000c00c001c1c4030003141960041d121860881e0221905905d40316208810545150000e00100c0b4a4402c0e0800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 443805035 1250 443803785 443803799
    0x405100513060905060a0606050408280b0c03041a01120303090303060f084204060906090c05010f020f03030621071707090c020705150d1d1005100618 66
    0xd61a000780568001c1c40181080c0508201f15042d56228405000c0200b0040183e0800840e0030030000000c0390440c043d02d44a03004c0445894200e000040140c0c480400308a40883c100c80914040c5005141c2600d200a00b0487c00c0d140030428003030384895039a0100740f00000f030700c80d03000220319610a15000c907030b042c1d8a4451601c20400b9400200064004c1c0d15808001d1508150420300c4101d107081d804080300214a0f484580980d14001802c0c1441000c005002d10000350406002150b0202c01044046a681401e820401a034003410b80000d0f05110100e04040c40003070f000c0f10b00d0906901862031a10f031002080407161410900602448a030313544a0b80d81c110a102140041c03074020320f2004000429640c0508000064006180080c500200c40c030205070700060340000e0f914140c0301e0f41003447c0000310000d2180101110000383c80d0420710120510b9400c0305541108016400c122501c079900070a154040c0c1d40100c4104d6144045914100080b80c8512954100e02082c411484541a00c6c2c0f21 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 443806285 1250 443805035 443805041
    0x110612040302010c030b030a020609150c03160201080901020711090601031806060302090106170c0307030f0914061e060d1b09050708060406180902060d06060306090b09040510051306 80
    0x541900541d40d44c0c1c2e01d031400150140140101d8200c06c90280180d80815070009506002d120312403800f9144500202500c00d490800b12100780b0b10342d0b41180d440e200801e4035a04602d51a00d01240010f1b40000414042001402542c0c1c2c0c0c25400120200c0c02442d038410310555102c02040c00b41050b0300c0d2121100c50080300c600394004903000b100701040c4281540140b11f4003a42c10307403041003044110301d07000883d4188141e15035009400b81003450f50300c0d120000304501600ba190001c100041c40c29031080200140d082c078900c40c20344d520741650a0350383c130a46264601ca400451401c1030700c24840002e155454123170219400e03240f00e55041003085c40b502d600000204202c0d000680c5181d03959052050306d6821190f519401503040f1800e0040900305214018a080c144151042840d10b8007100c0c01107540da00252000ca19894108203c0240d45110090141103248520080c56241c04080003403800c10300940c1d0b104039040f00c000c050710085221302e0350041400505007803014441400301c0c030020741940 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 443807535 1250 443806285 443806291
    0x20d030e0a0f0510053c0f120f0106020d030207020307030605130618150c090503160f050315130c0308030c041d06031b0109030602040906030c0e01050d110612 70
    0x1d4502c0c1030890402003070080d203451014040b403d0141c144840c5080c14200c5070802d6805058110300e012003010b200d4001034a05040714000d013504004952400c1007d648400303003014100205500c0e030942ca682c0c652403000d5900780070341801a0000100145414001c1c1c00a20517188094101c0d8180c5a0f40e4036107400311141580c00141ea2030303900c0c01c8402809014010341104d040700541803413410203c0d9070f55070100341c551030741052080d444a00c0b0f030000c140030b034209000a000150a8032501c1e801d464524609030880d000789611138240c2000400c45050003d0000041e240140c03070a100c50311210002007510035904011035036081500c0d808030000e172110002d107005410f401c500e81c0e01c56040098030389641e080800210140c10119080008a5400045080c404506804001b80302c128a40048407000343c0c5400140443c2d00000c1d0010303003004560301903011a80556036000e031050b10350965103110f010a02c41c299004032007071414000f040c441300c20500d41c44001801145001103070034900c041c000c011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 443808785 1250 443807535 443807549
    0xa0903090e0c070b1f092307050d0e070302061813020409090b070305090715050c2a011d040b0a03051b040f0b010c11190e07021506030a020d030e0a 65
    0x4100c40b4104840340180d9500140d43c4408071124002000102000341c2d6648940c01c450303034451100034400541c940e40c01c142d03603607c0d10303a005043c60206c0014010742d010903401c10800d807030000701462100004c540002542c2d03006044914041c124070228141c42c0146c2d4445902c50140209400250442c1c401407004090103c40070a143c2e2203820301c440948001000441854142004c00c0030070080456a81c041e0fa5a600c0a9441081035800441c0c4c40e00031520058258031403c50014151107407400e4450300b046d40c100300f508114144a00450708882d0f0036070072850b0070920940505141c50070ba000014034020140810640680e280c450520f850003000003900219810f110240e03590400340118103904000030020300841842d003000a000541282c40581800c50704800c4a2460340d90b0418801000760001f0200c04c2c441e240c0d105d40c1e8540c5000e80d079803800352203140b0301d9105100c1c0650742203200d00d03030050160a44220940030b1140c4841800006c40030411411440110790717844c00c8580000d0448 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 443810035 1250 443808785 443808787
    0x160e030c040f1e090312020c030a0807030209060d0b03120708040603090201021906150614090402090f0405160e0102060114090604090b01080d0e030303280209040204060c0b070f05030a0903090e0c 86
    0x31810080d100c000d0b0002c00c901b0f824010025607100100000481c1c14100c66071928142942c0d603030400b24024001d0201c034a61007180041c4100082400740c20020300743c0b00442c251000401403230051400d92252074001001c0150034881000320a0182c2e104200d0280103005031551440c03110040d50091080802c126603040c0c0d6451450300c040244071521014220600b0715000e582e5007504c9140c039501620901d144143e400040f0200c003511041c08410001d04054828403081c101580d4802400c50003010410010f41d10b041215a00c0d072000503068102c1d041e0348401c04a605070b040900036a1000101440e40203504c0360368a074001210340c0d070900c2c020301e9494054080b41081c90b40040c60020f100c00601d2103540107009002c0c00420f00324101000e80d040044058200c02d040204030301900840b0740542d803051000c600000c489801900300907505100c0c080c0c0c2240c5580340071082d100c0c01c0c8810a030380d00048051000640000280d40301050140c01b901f8100718013680d41d0b44401c0c000004851000780d00f04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 443811285 1250 443810035 443810051
    0xa090f030503071b150c1b03020c0102190804090203070c0f0c081203040b0c0304020a0806010b04060e041503060c02100513050f030c2a0315160e030c040f1e 69
    0x54000081c050020440003030540003000790f03c2d441c12180c01c0a4000017080e66501c0044a400d00803203140042460103076012506048074100a034940d00341c0d050b0507015000d10303819820001c4400c44060501548005402c0c00e090501c0c5006000350030042076038050141c444011070100b0340209075081446d1241820385000303401c1c50803242c00c02e00c00b1031000e00c62110030310900c40003900c61031031290311402d415590340d141d03030b01c5000190745200345600c4200320f03000350000030a084046500130400e41d1440d890b80042a584401408100c0ea00c008042011207001401403000039400c0c0c01103030715801c03a4811500c11102d4140310300e0847c3c50681d140c1c2c0703c103480400c40c00108a800d0100d460b00700d4000303020714102400b00c500f09894640c00001da80b0703141c0c600c07420007050400120400031b1001c001390842e9030090f50921061816031045e16441c50698485440c821510710500b10914144805805407410b0f210010509c4080c0910001182c0c0558070b50038440c01a04e03d003441800d5051807140042a03000e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 443812535 1250 443811285 443811287
    0x90f020f1c0f14041118010f0509160206040b0c090604060806040f0b0d030f03020d0507030507020f0d0c020105030a090f051510050906090a1b0203130e010e0f0a090f03050307 77
    0x2641d210104046203040c8102101c00c000380c620601d82c00f54100800703258101700680040d14000e90300c0b10740e196407800c281c00403030081401e80c0c0501c1644e1058403100d1454a503c100606003091030340c1c54100503841403000800041e90100910342022003904954106145800000e10300e40090308000001100d400c1000300d50b02d4240504003903450204002c101180810020504400e621003001e0103100c2d048241024186c8250f0458034030803d6610b0400c545d05040740d004024110660301000180304030031141003202e601040100c580c1159803030740380114416500648094100802c4240010350f280a900086602490054525071041020785007080c10300000303c1d1509009441c40e002c0444408040c0410f0b00c8a9102c0c03034004004440000103551203090f1a8040c0c00710f50021214241071104e2140641e400101034003c0107507071031001020135291982010107440900c1401c40c040c0c3e980010542c11f444505a0340e0300110b1100c008504d103a103c0d00c3d00e012020035890100d0000c0c42c0082045001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 443813785 1250 443812535 443812541
    0x2121006090b1c050a0f030f1106010f1701110a08040308131115071209092018060c15040b011401020a080c010b0306090f0c0910090f020f1c 62
    0x140800050400100710144046900c02007814200c40d8403d40390190541482405c101e400c0c0c0b25548000035024403401c1c0d140042544082e19001d0700030820200c10b5820749203000ca241816030b414558418901868016602842c4400600070002550396609501030203000d840146502c102903280c00c0003606052030010501180100000101860103501c03800040346100240321101d41140c4a4100d00c1022440385218070413007800130300d021449003040c54015084159441154082c0104210f0300c10354005036003031043d80304481c02a081c4100036000707862a2900308452004c1e00509281e082010416a19140030208034044510a0024080004202218910707a0140081d207408c020082e8180d00080e55400c01040010048800400c800d002c071b11003588050720b114030080442c0c0f081c3c201619002c0e15544400d4960b0350034041c100ca050494106101900d018401e0a0007005160389488904002021191031300030300b140d002c0020840b1004200044c0058850030009059481e030351032101012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 443815035 1250 443813785 443813789
    0x708090316030308010b1305030a060b0306060a0e010b0d2903100c1211160b0405070801060b031306020f07060b040b040b0d0818120706020d051c0b030a02121006 71
    0x10458800c40140b00090340160840e045881e000802911401180c001c190780082e650406034151285c00c40766010701c51b00e50400c1004040039010f0343d1103a03d03200c040c04152003881c044d842c88106450010040340c4100d500501165040c03050001d0010411542c01c83c0c2c0c0a030200304840c1084403800005900d180074400c00c503007a80d0b5200100301120020074003030b02099030031031017246840c0da0b40b01c01d040080c18042125480d60328040c1500140d8800d00d85034150007016035003a40c85215004021801c5581407190f4429950460503143c1075968110703251512000030441200c0741502401108030000c08040640b030340320705c502c0c030102e10303165458280802c0359101c030b0708184103909144218605413034002d2003011840d005120a565003828808400c034540100c080c81d80c1082c03030f06100f4200344101007402c10940344280d00703950024016007405c03511805950031840106141c99440c01002d042540174940c0c0c20000303010703525103c0140c2c00182a03d514040f1401190300120702c403e200d070f20144180d0700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 443816285 1250 443815035 443815063
    0x3020601050d1e020f1201020d0e01021315020313060e04150509010504090204090f08040f06020c030c0f011e18050108130b0601021015050925140403060207080903 72
    0x82440311607224400c003180c4080380c1c0c084005038444083c2c2552603d07486007104040261041080864140d01d250007540700e40006501e41e8036243c40c0c152011018000ca5024480720b24021070580e091140301c2c1d02034013030f00003480154407081095402840c0b0200d1804028011074440c100218180c47c20b21095a1040c03114002d1030340385150a0110f40c0e100b03203115041d074a060380c0010301002c0d40d1020400401140d0000340500d007007820070340d0801c680003004105885611040055041e6641c0041e603852020020240e410f411032000361002d800c1107019581c41c22414074144045001c01840c0380c0750301039164102c000140500e41d50004064103000b01200900007840c1010841c03600d0010b002010806a50080a9041c80c001040040c0c3c420800e015a002c9074060410098103070200f03c04c01e1203c0d920480d4061442d110010300c04400c40411a8020001c0f8002181a5040f40b4005ca80310030761030a5111500384207100100204500b88060550513200d2000c4541c0c035001d01c8105440d011324014615 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 443817535 1250 443816285 443816299
    0x6071706060a170712020d0c0e010504030c09090c05060d0c0e031917130807030b0c0703170901110d0e070e04150f02090616030f0e0d0807050307060c020a0302060105 73
    0x24114541c4140d64024030341c0320184210072910b84200c112107003d800080c00240c18004124955400103e41c0044231a0ba45070f15111845c2d1605801541c641c040c510000d00f192840e0784040002034404e41194961503c2003402401e681e0315140010150f030000301c07094400b20f94800d454015180c01c0b0340e04070b8808038120010030381c103e50340d581c031400b0126440d0014400e007421003203400c0381c010307020507a0390300c03160040c0b1a041c0c1a100c01110380c0d203600f54071080d1800c102d0340c0003050007105202c3c221030046806544a05483c0c4149607102c40060001c2d0005007190350701d04c41660303195010406881c08840724007000c28421032000704c40340b614205800a0b54040f61210610002a184001e010001e003240c01c0007080d105030b0300140c4e40081c014070008641010340001c4101c009030000c80e07039002e035610a8444042030705030003404645451448000350381003c4440070701e002085c07508001e040755521a6084928010312940c2d1070341070b00c491004a0300907a100b92101e200b00740d0141b142d0390250034265425 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 443818785 1250 443817535 443817547
    0x4050105061821060412030f0c1e140301061101060e0919060b03100603060c080402060d1104030804030c1d04151a030708030423031c0504080607170606 67
    0x40c210800201c0e118500c201801e500102c0a00196055008030f1015030040d18040d290a040020380804202200c0d80003a01c2c00c0d01c00001050940b0684d030b81c10700746544966000c0e071604041c040d04181190500240031680c41c00c400c004468000550103030216594036801c4004404509094032581c0d00308a0380d80b40c4a104025217070700d0000d9040540d15000c1021001c050041c00c051009103510f140807605806a20411410303003030710307410100440748903030402c0000e40344907401181d01200981c1c0096015404100c03204e40e0400c1c94001e0b008900300300348454900b99503a519281d10354020b038030031185138112400411103c26080c824002403652a590307208503152568400d0029481c0b00100040d0f9540c850b49c659569124115074590780c00003400f218586038540d4180c0b03503250803610a40c0e100034108441c83d01042500740c140441448003400a0128102030000441c2141a101e202d1080090500000502c040200103203401543c0c651030b04515214160300445040c00020400741c06002c0c10000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 443820035 1250 443818785 443818807
    0x918020f04050c0c030307020a0311011a010302030c04080a0f1101090605030c07080c0a03020606040e030c07090209151303020102070504090503070236090d02010606140d0f06030b060405010506 85
    0x4240032011007210300040c10358410b034032000320380900e0350b140b469440040200020035400042c0c00c0c03030f0b5500031f8484006403010a1800c1e42a02e40c0c4090b8007040c114164452006035002c0e401a42e0003460f041301080c282030b2200c0d0003614015044a003621480090f2940405000d0b420011200b09003003840c00c001300e01d040c95809000c134880034099010100c400075040040c803a815040e1150f1840315002d6441c42c1c03d06040095944c007090b81c20038801c51500d5400c48084100100302c51914074100050001e140c6060032900094001c1220301d030300851900091001e008030b250041010100e0030035041c00c44c1d4103600009107083e42c00e400c11805286801044004600b0000030341d00215411546a10000c4c0580c184854101101103550413010840c2c117140e100a1041c6841031141460b001141c5403560b483c0320403401e0f134007984500008500741545501407500848010030008504100108075080140070400031034061303910581e50324551205108461030309000e01401450125001410130000c075070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 443821285 1250 443820035 443820049
    0x2103190305061011030706051f0b0301180b0f0907210b150307020c120d0201200a1b12030e1b090c090103181103121611130e07091802 59
    0x1844070305100c0501c000720b0301d800c0200700b03c501081d803145d000c0c06141010070001209c81a42000200400300b100c0c004a58030000c0e0050328102e602110040c48800b0110100100504500c001503400c403a03440780e288003e44403040d619000d100c040e5101c0c40303e48440032400c040d0041c600c2014000d14201350340300105588200390480049060002907590362500d2200f41d15207103903409510f030017900341811071500c0c0e440400d20700501e460780d8000340200d01105240e0084c0d400070307403240c50010200b40203142207503100301d80215441e0041c00300004010116102e00702414240910311002070b4070b4041c03040002d5030070f1001a242d040d0612507104003256180000300c061400900104401c01d002c101600c05170322139000124000104400b406c01c048850602c01941a40303104032901030b201d0151209440d0484400f01d0328031501040804811411507a00e5406640304841c103580d21450421001841d01d03964450301c0b4031380c0b0301c1900034900c5c1d03440c1952441c2928050100c1c58100d0900d02c200c0c80140c0c031041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 443822535 1250 443821285 443821309
    0x2a0807030f0803180d091a0f0403062705030405210a03081306020706020a03110c0a0602090607140619110f0c0f06040302060703050121030806210319030506 69
    0x2c0c1d03850b0b58440d40140c1089480211141e140d201700d2503080c8403260000d0426054425151211803e000c542d01580010304c10000780c1140c03504100802c2000c641d45a00041324400350892560341815080d254840d20f0070b8141090780c0ca60000039040180b03240511180020b01000c45c6030100c440148111035071260000b0302d010701800b80c1900024840f480d451002c100607640035030219100d400609280000707402408600340403034901203290120750091016911154904001000c50400d00d959640c080e40111003516005002801b035240040d603138826007507003031840500920041c50042c1800c07402010000e01002d100d0700e401142c21f50100100c0446221364202c0c40700c41d55407441010f1207490001d0700b084040141c0120020300c010140e010600d18010f50305540d0610140c0d0302c0c1d40b01c030f503210b000b0883e9a5405001e00300d0b0803000280140e41040d400400100010910443d030543c48114048083c00210700740c0002030403200c6950f5010582c1030b0140c0f44d10381048180380c80d0010901e145624 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 443823785 1250 443822535 443822543
    0x50103030e01110f0708070e0f0907060c06090204091412031003030c0212032106010f09050910090501060e03102016081912090507050103182a0807030f 67
    0x81c20880b0b2a8082048214180c0f200040364901760b502c404054444805005694116205101140b05221450b134460700a19805d0040c012040ca4440152420107412508980c1640c50300016000b507500c42c4280058680200c0000c9800b880c03041050707041c0903610080203041c00e0140280210381ca400382e00c113001d036545400e040000c0802c074000180e06190f104041030003484002800d210015048041c40103607a2420100004c90f11503000540306c0808000c0d0000004003803100400c41450110340d659003040360005080140740e2030300c2800301034a07400d8010b600410b11070400030010b800e080080340e06d01030078000100b000c1d0082c1a040314000c14482004800300401181e60600616105494a4280c3e44055680c0c0c0e6068000c50100002c3c01c000421b0012800c4884c0b025030104590085940b2103a02c01e0141080310f0400006400500d1245220f00028100840910020341c10808a00126500b031121340304411444480030402d00b03498000c20400d41011608000140c02088017071041540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 443825035 1250 443823785 443823797
    0x10507020d1211070203160e0c070f1e0c0605040f050105090d23060a060f08010e100c030605060c0c0a08070608160314100302031b0f040f0902030a1a0a050103030e01 73
    0xa00203c4400900031894040d5243c024264a070403e1303000c1e28149011103c0d100b9010794a80d4031030302008a01c1c01400409003540f40308090b010000b801c0c12500c12061000c800c2045800d001544801c98130380c1c03981e004070010420001d010302c14402000020b60050000f46001c5240c0300c0583c020880a18650780014072408026003501c040c0e094204c0e000075121650b004407049407a284102d140a003000c3d202d00889042c241d03002260717641040c01101315400076000145000d0140c2c034088001081070107086401c160341da4401054583c1c1e41401040c0c0d101c82080100101101030081001075202540211102c1c0e028040400c02c0b04d8201092503804a0b0446220030039241c02c11050703020b44655020144504446401c1080b02e00c078500350101a01d0080c0c089400700f107000d50b29105500511000258409911880c6021b585080e4200020f0503401c3e1b01d0104044034203901107480c100c19030310112000c6000d4502e4294144111040a900000e101c105020a52560b10007601181e1251155410054 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 443826285 1250 443825035 443825051
    0x1080d050418060b030a0c0f0e0f0f01050f0c031c0603020d0602030c070b0109020a1202090109120c1d040302010b0a0501050315180901022104020901050d150203070908010507020d12 80
    0x42c0d680607070700401641000607581e14100c0b81510040544120200c0403422950301c055441c3d2040040800444025081c1311041d105101013050b03d4050081c40c50400c08208450b20010401d10013400001408000940d15000d540c650034030b4089032008048844c501c0d0000400250707440d00c00d56040580c11450041c0e880d200c84030608003c0c8641080502604149c0c000026203003001c1d40100140f0b030b05503a0380164000c8803001a001da00c5040030840c0010340e20101841a410003201d030f0784066210b8200c0d00c154036030303c0c00880b42d105100c40d0000d1118203101304000500d5020301a500d0f5125040710800c102904000010b4424003010305401541c0302c00440322411621010a80c444d00a50340d1029041454851000340c040d6024a5543da61a1025030003c000249400d1102e4040c0e40d00410028850f0b081409005008000c2ca0094070981c0140d4420005142c2a200540c0540c081d50303581d0350300c0e40c02c0541a900f901c030094144411540080781c4406070680c440800307030441c1860100404c94003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 443827535 1250 443826285 443826329
    0x1808030c1602060412050c040509030406030f0f050a1410030302070902070204180803060a080102130b0304051009030503010f0618050118030501141501080103051510120609060501080d0504 83
    0x40003031002500902e0019012465084082c5200080d91099044174200203d08048c0003c1d03480c203544040c480e85c414030040c04114001d4012005460082200003000b6038900495020340d8000e075008241c666480492400a080054100f58051408208414454a10ba5000f59220118800c810400781e010580c81c1c11965580c01503140400603070b441952185090804003030b5139005030307842c038030807103114000148094041c000d4078020412604200d405920304080712419520040044446000e10409205014000c1c030804000c20300a95400d41c5a60412203003002140086e0840c0040c000007840f17000e82c019010715404140c48081c0703004148220400d4080b0311a07082500010b249500f8045101120024005110b2180481614171600c00581c0c2006451f121002c0c00080c101e900320045620340c0b000c00c4000c9076040810510307018402d61352150902200101038100301c0d261f41c1c4920311001031040901a450152040c6800b601c100d400d80103020300148a42d03c1184c0220004480c644010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 443828785 1250 443827535 443827567
    0x8031815090907020d030606090b070f020607050f0309040b0109030f1101140f07060609060b0301061b12030b1008160809101e14060a030b04050a050d02101808030c 72
    0xc1807010300505041d0803c007a01a40f02d1580d0028803000a25000000806500c02c42401040742e4441548500d4505a034a0307030031003125004d8099030030035010030a920002e01c0401c00310030310903800b6014548500c0c60398100403d40d840c1003200341c100002c0103401d201113407001c0180600d5950220100b140d20341c00c1001640c50034a55040c4044414011800c87c40d8049184014203406109040810000b0740f140c0c0c003441124101d01890a4080007032005208182c01101400c0c0c1e1440340a21001041c40d95960f0071002408804941001a44414202d90141404082d012038080c25040c01401c91a124407000c00b0710211184c90001c10101d103010a40170312080c40340c1c410090003c1028018074220070b4040085240216088041c28905540881050a6210307800c0c00703500010b200030686850b43d150956030200c013078800c0e03800b8040d001400c00003400c100042600380305940c01515040d10011281070882d039031024150410b0601401020014900c20304480d48000100071084d01c8100c410500051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 443830035 1250 443828785 443828797
    0x606071106040f08070b0c0c01050d02121006080a091203020a05070c06080603070605090a091a0406141e0907081305122a1b04020904060e0403030608031815 69
    0x80300009000c03c00c880310400c43d02c19142c4010803102140e65401c103203c05032148440191540d0045603c1c82c9896109000608646a01580250401030241542744400009035080301c112000c03440e0410620b6000300000c0d134803403e48070007000700d208103440320b501c140718503041c402c00c056000601c000b40394050415643d80c00d821011035601940c60301d8019018140c01d0f030b00e01e4420b1041c002e000405d14480c0c0202c0d003550001920380e03038803c1c3c80c141000300548a080b02080104102125075201616284501802840380921030030106a030700050043c0c00700c5c00300a088001c6144101c42080f621070341c0075150025840d00d811042540c4841c041100d524040c41d004109001c0c80078400c5c051880703500903013a240c000c040d4407a100580398501034052000b074004520b06412014043c0074400510400da02c0c0140094405445c2c03280e14000142120401d07008203414400c50028041403551510032240038141007002145480c070307240c00b02a10017120055440c0316020300500b41c1c2c12201034001383c1300c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 443831285 1250 443830035 443830039
    0xe1f15140414090138090a020f031f0603020403030e09040503040b0c01051e042424030c080604020105030a020703090314010207030212030709032003150106021203060906060711 78
    0x505000d141e503400f0b00000103080030304031109a401e80d00a001881543d078440740c5c0340c01c403c0e0000c1e200b006004404100920004007079a00b07028580d01c002240006620481d00c40b2400410010080180e007820701d401e03000341e000c0510511007407000a4000c81226610403007210100407603556490558594440c0da04a000c0190f070200b0303259800710381508414021040075017201880002c80c05a61002881194044c19014000b8440791010340d5184020868600800d008601449028003422007103e501841c1044004921020010300200c800d00710082e22200000d00780509064000030602e00003e4455140c640d4000b03006003c16000c2c1e421100156840804201c03403071101d0910078000d41103003000b50b01500801120500d600c00c004200ea20070355094980305c00841c00d40d2152104191401e034002c1c505200122002d005950030080300b00307a842501a2147c480d818604c0003420700000400c2d4518021081c030034010955112010070b40e0048040e2181501e0b50081c0c1005110003103000f400c15 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 443832535 1250 443831285 443831321
    0x1406030a020c1f06240c03020106090507020a060f0507020a02102709140103080a030c020a05030c010519050108030a0e06122703190c05100e1f151404 66
    0x20001c0700388a003045900e50200f0003003003c580e8900000448480701c849846440c09448000f10406000360761440800340248000030b10107886490420031a0020381d00840503a000c0c1e41a0303010007901d400b03130800612000300244a1030a0001d400f03551040000c000900c40c9852234040400c1d82d10420400c40c0150220003001582021a203001100e8441c50040c40102420508005040f042c0262414102c81d80803159518001c1c0f00c04044000b048c40207000c0045000f100124404648100701a00c0302c1c2e0071105c00003a0a0404100000c596a080f035254440c1c0390030000100100580031050390035400c010305001c0b60350741800000600620a0312000c000781d0b44030704144101c00062041d030700d901c615603408110000120200d5039903640211400300510b404d4003000c1c143d64901c200304203120b5620660881c0c03220b06103001100261140070410400561200580306102c1403202e21000000e11207640c1009504511f0f90350240307050780342c060b200c0080700c5034020442640b107690007008004140f46c002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 443833785 1250 443832535 443832553
    0x503090a3c0b01141c0b10050315070302030709090e0a02010206010504140402060903070e040809100e0310050c0c070e01091d070e090c0607030e090708011406030a020c 74
    0x100d0741058244080001d040c68480240c04200c400025004294100c0b0070342101e40c2c03030000109580c4841c2d290690301324a0b071240c0d1a40b05400148801d007a03900c06c0005004c5842c0c088648505034503a07902c0036102c0d030f01561400b15080145a00e01d500b046007440d0242c0c1da41c1e01c0c48426244900c05a02c08003c0d60328101e03204441034400710312281094800d900b50f840c580d03a43c10030403054451244100b00443d070440003082c0145041d40041240c03100103400d030b0304003c3e03942c0840c8213100303421034054603844030004500310145030110090250003071074105426211440008030365100a4041c142d025503580344041915a02a582900c010300a100200c8880d46d40390802c0710041e442c2031142805050034000c0c448000c11505080c0e0340714104a07001010740d00d01d00f01c582c02010201600f08455800780305c08240280d00e83e240107202d620702a456800d0541d5001040c400d100800902c168200521640184002c1000200d03198844000f222000d032a500e40311521002403055a0303184110b4410f0000c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 443835035 1250 443833785 443833823
    0x60e03040e18010e07060212161211010605062106010207052206080604030c080f040b07060203070206060904030206010909240b0102100915020d020702130f0e0f07060503090a 77
    0x1000342c82000c000024000c420140401580d101c00c01d01071200981c0240380128100000240034020307950800344169204c0900307465040c049819040c0000004410101e0550a444240030b404003e1406617580341c90050140c0300c1c00c08005410703400c410641e6200c40071808503842000390360050304000708280041c44c80c5d81c000007122070a402080e03078018107152001a001c1004035803144603c3c0c050f2100d01007805960b0b680b030320030341c010f901c594001c080510001c0b500880c050081c1c030506120b5540142d030307400e11000103850070500a204034898005801004002036000c1491811602240c20201340d41e992443c7c5a84440c400102080843c0c811000b044112400f82c0c010304903144080c2c0030f440c0b442c1151600e860a840a1160182592200144801c40d0600581c0141320448403e800141041641e07070000d560014448002829640c13103039000000c0200e0340c40380514801d410340c01800c0c1040540305440d1036078818031402d0180000031000610540090000d400c0c03481d4404188800c0c1d00220312 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 443836285 1250 443835035 443835061
    0x2100315060201090c053001060512030928050414070e09090303070e0a1d0417040e04021e031603030f08070512070e03191a0c0403060e03040e 63
    0x80c54000a9100300c0000340d99006105140136107802100c4203a030b10f401c01c011b010b103941101402c003a5035540d811080c1c4d90301c103817060440c00e015507000c008510945414204265201c51541e14122600204108031103559070485101d1341c407000546d00f001e01005040070741d003500c080d5444160491b003086500000710b28100300541c45550b440d2940c074840034442c0288109190101c4c0c000005038820008034000c0c40c090014402303501c9000b045c0034803258a4030070030007a410800c01883e2401a40400340803c0010a011010304040640c0180703080600c1e0440c104046040644040d00410f02000d900a484001e506840305141001c1d0440e03019400c1503101c055201c41a20099000403c1c00318160612485010900e01840142d0781c0c5038200105440000e20790880034142c02c00b4032113804507074441510240403d2000c042109005041d00c1000d0800d8611038181c2040402d90020708010040840400c0302900d0507240c00560000700408043c1c805840c500c51500903860140001c0100f00d54490509 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 443837535 1250 443836285 443836301
    0x10e0f03100b1003380a0306090311030c0a06051005061308010f0209010c06410a0e062a03010b040513060e0c0a020304030b09010606110c0d02010813021003 69
    0x511180c0d01610f81d01030850480340700d101a590041410704814110301e02e0351406110420071903000c902c000c104c410004004500d19482101d80a881d072440314107243d08120760001486018024600c0d045c50b061031552911400c41c0002e25903a0360b9800714103d0f030440d00041000c0c0c0000340c0419681e6903107000c51603030030400303200c0c03004198248008102d00001c40d0007607420548040c1c490104050155441d18042c214160489003640c044080c2800c6070b50058055a082c4410301010b8107040c2c202003a030200c2601d00030400d917035450a02041680701840050b02c80c0c0d00054405030701240000f0080012000c0c8012101e8440a54001c000402c1c20b6510400410499108071004504e64000c41c0001040d50500c2c4100700305a6048000130382003c0b0030400402d8024039500c152441d2a40b00e1b42c40c40140074040c0e441100b60f03036580e0001e010b466004486104425981d600510502a4a0002485078111640024100996000401d6400c1c01101c4c3e43c10003a5801082e0300d03120002c41c20f00400800c0c0032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 443838785 1250 443837535 443837539
    0x6010905042013150512062205180d0504080703060203100308070b24030a080d0f1407090806040507230607050a1b140616020904081c06060e010e0f03100b 68
    0x3040711341c2c105402603041740c441d01210000d0900d44e540e05070810100e2140700da1484059240250203103c4600c0c1ca20516101380780f0094500781c02c81c0d0110403c0e1400c0080320602c01400010801401039400c002a010112544040c1c05a90f0f990350608000107800c20b40e200810041010801c6002c000e41035079000c0c03140b1808101c0c0f00310043c08101c18207203142d075a41c6113501a000001140c0c04180032000402913070b00002d0010400421411028045403012001441c0001d461814441d4803540b1035482d40091050a00910080c01e10b80c5a15807680c103107120f1072007240a00d43d0110f1041909040c0000d034030000501e404d865411504203662500c4000200b100c1b12882da001c0010806600616281500c0a0703440f0307448440c103d6018011783da484030b091900f421010180c2c0c840181d99003807105200b580703c2d046240d1194019048030010140a0740c600c43c41c10f052900501009500044020b000740091078801407030207000e4086107080c2d03000380314645c260003400c900c0c80024035150080c003030311001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 443840035 1250 443838785 443838809
    0xc06030906160c030c110f0604080a120509033309010e120c0705040207150e07060e032814030f0a120209030606011206091d1506010905042013 63
    0x91410485103060748580040206455450401c04107030b0071b20503144071502c09005000b10000950004d01da541199021102e26409039204034100001c2821a1242d040c05051503030030858100300203500d82881b0f4003800512490700180740041d0018003000344010400300418200d03030821851690280c80d4600703c2c1c0e006032017400d54003800f0903503100855400c0f00070f00c070107481c0c40d904040411000c1e500102050392900a40e8140400103850b602c030b010340c00c0401d0b02c0107161040c074020015004401c121101c0780301c2d401c1600075075880d0752400743c07402580004410703003101c0e41c070031f860180300441c0000ea2180c001c0c400440d1002a001111000342008440d540f00d0303003c00d143c0480804180e1140340880d6800d600120040b580384c0d4091440a0300070a0003045c0800c4654843d1090302c12602c0110042415581c42520281c0d504018003601103045943c0b40700d183d40e85071160001c2c20a07980d40c400d681c091691180310003a030f0009602400d200300c07002c006d050780d50790700d4800384a407116841c0211088030103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 443841285 1250 443840035 443840071
    0x402120604150e010603020a0b0903101b0c0206070c0f1e15080c040e07020c0f04020c061506070b01170634030207150e0c040c200c06030906 62
    0x20009003144600d41c4403003900d25001c015910b00010b409240c40805041d0b48680002c40180c0da1b880008001e01480c0c07441382d49416441d41058038004540240c0603490f031030402d085003149040202d100305200d0a0415003240c81051002c01c42e24030412030301404113504090040f03218048254020308a4151507100070404084c07a104030311300740c0c442c41400380d0781ca130400c8040d45560062442c1540204c055032498201607680009a50102003242c4040060700f180d0f041b000b05242001500d031200206480440c10070702000403490361000080c14048103e20401c1020310700c7d40d115130460340c04951150380fa50182d650b500318805041c50f000415500c601514002401d00100300660f10700b551084412014442c607030582800741103444021110426408220300004100d886032a180f0012800800141c4041c10043c09828121390007103280c0700d64102003000040076805000b4910200c40300c68190030b814203040115291101c0603024a8005801004014240e0008a1f4184c42017400002c020f135104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 443842535 1250 443841285 443841319
    0xd020d0c0305010b09180402010507050a050c01090f150c060e01020c070305240705070c0b1602030114060a06051b010615020c0307030c090f0f11131e3b0402 69
    0x10040b60940c54000c14011822070b05248074940b01604203004ac1040340c902030a9841c3d4070705120141009941907030041c68149a0355030301c010710f03800510103201c0c40000303903041000c6020010b4200380100204500440100d06110340c1f54007211541c2c843c00000c40d80d480600d003256031124494402a41c003801100039400a070a00021541c0f004020144180e01a5440d40410f40d5690021034081c0c50040c40d101000c24840d032513000502d04442540c80c01c801000062042600b900c0c03400004038004440c0d201840040d849142c1c1401c19a9480d080540c0c880300701c5465600440003032842440c0640c28040b0006000400d40c0c6454903d410a80c2a91265000d42c0c080c140e49202c2440b00600380c0313103801c0c01005401d50591041142c0040100e0200b030b01e000c1041d1a0007070355600c03892410f0b81c00c40001c0f0004207452514050b8001d0454001200100c40c1d0781401122800a5115a00a01980c04001d44840580c00782c0328601e0f1000542d4030b08181c03180034209000f2141298102d001d2244143c03032803c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 443843785 1250 443842535 443842537
    0xd200d0b0f180115020a020a060801172a040b03420f06130c0504060323070513030503120f01121502090a0302030f0102190f0e01030209060d020d0c0305010b 69
    0x20040b4184201c034030b92809800f100204004600d28046004d0310707800d800180ea0b00da040c00d0042206640b00302c06941001c1d041483c0316482998a11143d20481402092800010b0300c6c40d10a141e03c200b604030001100c010402810000303a50503814041e03418401824042c1d031100f00000074031700b14904019440c0c03410004c014813903152602816004500003e580000003101164441c0000c3d02034402c0106000d000c400343c80e42d800e40040855004102885010b40c18454103041509440e03245c00c2d0300740c855050256022024108008000c000651140f1036108590140d00466220701100d80d00d95291011010b03258041c3d40c07040d0018800c0000180880c800709586003010b2304240c40e00c0980c5c0c4202c050320000d5101b4221030341c120000c140004096641403004840c1c85200200141e681e185640d0b08048415040d8100030178404c089441b08100d0380d1000e1a0070140000b820300680d51118880060494021000c551181c180000340e079018900c0701e5006000020020f8500f80b160b81d803548660462 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 443845035 1250 443843785 443843809
    0xf0a0b04090e0f0a060b0d06140f0c0a170403050c030a0903060c140a081015080a0b04051308030903091f03150b09150c0f0715020606060d200d0b0f 65
    0x701d90203002c40e50f020407416407084040020090136647d8444080c0d44900590301d4119030036880b100100100541900c003d1742e150341c0305502d2a400c918182e4590400340c8100c80155154075540750b80e030300081c00c0502070b4088883c00c00c42074007101e44400007441c000b00480e50b9400100c07141418540040305c254060041000380c460040c01c0c0305d05042c09031034201d4104070010300650f0b2445104500040101d0307034031400d010b61040d03551410b0042ca44056001e0540c0c940115490240345400b003006805001d410031042c615602c0141030740d07644c496001c00d620350b000b1209510342c00510410440c40030483c11020440300e0426841c140150f00e0403494082800300148202e4285001c204049500c40c50000f01c5000d00d030440a05080c1000e901055052510047c0c1c44040c403030340d2141401b07000c0d40681c0070603c062a100b91004001d58a0034a0202e40a401071901080321300386c942440c0d4850806400d505000741c8020f0480c507031240000011031000d8a00f11300650302910310300c20380b0100b034100800080c3c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 443846285 1250 443845035 443845063
    0x140d0e031b010c050709110d0b030c090f0a0b03061008011d1f0906180c0f0503030f0a030b09070f030b090c040308030601050d0603080a080106020a030e0108060f0a0b04090e 76
    0x1207950a04006607004000018201c40c9170080480100d03015510740324444040c240390341d48645414000c01114100c540c001d10710340c80780d4816021064280d03154404194004207002507040a61610401003000d050742c00e1410b94580244c004200903044c501684104580c03170200207211202c83e0820081032041d1801400446030080003200d01c1c00803101d084044075802c103480000b07081c4a41e0b1280070481e109031624440d6050f2808148090000130650702014003020740750400180d25000c0080c0c0e8910640f4224078224401044410301c2303600a9018008100740503203550340e903141c40d0000800d00100d030544240860700d40070580c0c0c80e0b0308150481510491182200614060660701d416a058100801c550b0400100308801a1850020b0080c040110310810300300b0b40b6696180e00181070301005070890380440d4800410b038804039601498079496081c080c213040380302303441d990b004c03400740b82d40d60b4246500320310007140c0007611034100c1d0300600c11203008002c03c00c0340700d401546103034456012003031400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 443847535 1250 443846285 443846323
    0x1e030b010605190f0f141c050411011d011805030f010e160305030f0c120712030605040b0616021c0b060f0607020108010603020a0c021005031f050d1e140d0e03 70
    0x1c0801c5001725205140c005140d60402c0c2080004005a03684c142803150447c0102d071104207210030480101c002001003602400c0012404039078840700e810000b11054540d0400000f01c02581c5a004241d03007100107000090250354003480b034550998043c00c59441c0a440c01c0c446d140802c07006621401d000c5043c1ea60100c041d500d49055180c0702105500501240c3e102401000d001c0e01595550300c008101c42d51047e8202110807020f804043e04654413a0310250041c2d01b4220181c9179607a5010803610091129103a040b076403d911300116039a0300411051149008603880a2020b10071349034a620301c00c1d00201e0344500c280901da0b05202c1940190032009000c1210030740140000d80c0a50051700c4141c030940340400099410303400160b02a60f403080180c011460020a0010700e881c00d846585401062222a45040c5d2610300810407940d60120080c000862103501c4820b4544e016007154180790300003401d00d1201058002450b11041e05082030b2012031040c501c1e070030076410049040e42450656118007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 443848785 1250 443847535 443847557
    0x5090c0909010b030a0309080105010e061f020f030d09050f070302010f05032e0905070807050901050a0215092a010c03030e030910020705040b030102040e011e030b010605190f 77
    0x805000c0e0406025460075540707520b40c45207141c40420050710054000c3c0d4404070742510f41400c15084031010380111a0031a0380c4010040f45031640086121030284000450000c0c0b002500300728182914050603503128080001c0703655250007250030801205001c0d0301622020000d000c2c80d181c0d00d00d42448024081403050714213503021406000516440840b000c1500c08a064040c4030100700c0006039451300a03000d6084051084440301e20445501c62100e09221200d4100380704003501c140114070742281085000911040224400d00203650380380c9404061840d03504100346a50f07291500c0061006404c07040c8184000c0090403115041c0201d98181c5070380c19008200c0d101100a4405541003900520080000f8061500d8060300b112581c0d049501400c0e100e81030001b08010740b00480100b52281c0e00500081c000c818000d02807504442c0d449190032111030400050b440c1069181d44060481c40a07007000041c00e41d004002002050111104850640d402c6101641c00d10807000a450000e030240c011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 443850035 1250 443848785 443848789
    0x7030e0a1104090f050f030a0816080a0c0504050303040b0c0606060f0405150417010b030c0d0b0a0e01060b07050a0308010e130609020301240f12121202120103030e010e0405090c 78
    0x807010324000e138400c100f01042d9440e107525118202082c0c035a154000110040100e0b404401c2039084440e40302013012a20640b0b00041c88140049c2400981070303541c0001415482c000c0080b10010403000d02600d0f101c95031201503182a03005402101c0e13107400b4007000a9041e00d0000e003203c00c8410840b1640b0b00341400e1805202d0a84841c91000135005402c01000ca1000580701450500850920012415203203c3c0240340c00e1a94241e1040c0c0904801c404100c009002403400da68400b80d031210010b900780d124074000e4013425003940100440040040c40205001010030740100c0e19000380c031a10300d9030741e9072000015480e5046501c5030f414003005080200040b46508880f060f540020008210070301641010071100d080e258030607140c0b20b00c0240401290304580d0070880100320000441c13400703040a4640c071040c3c2c0003030f001800c10032510741006840040c1135810780300345403202c06030b16106603160300c0c000c1c24449000012a01043c030010490070369161a02405100f40c050101510358008a601 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 443851285 1250 443850035 443850041
    0x19050903120f04180f020f030420030a2d08040905010e01050a05040c0309060219111615020f0106030605061f05190c0807060603031e1b052407030e0a1104 68
    0x2d072000c005a11044000a941490700140c4401c2501701c0d0304076030728100340ca00baa5618ac0d030b8540c3d1022098500403040c40d2039070b0100c2c603c10820b0304009550303074441ca903981001c20313078a582c44015005418000804140011000500151400b8907010003050b41c03180c83d0502c59610912802e541705414400a00c0a401c0c650064911038140741000b01c0c1c4142340341c0d500000e85c0c000c4024074180c2d01d0365010560409034000009220403c940011701001c50901c045d070f40019036140103006c03601d41d080740c2c00180a48200020500369a08030001c100361504c2e890564041e041c240c4110f4481e0306001c82d4410740080d600c414020700681d980f00d0f1440c0c0f0250420b05000030718100e00740014481070001d0b920104101d400140703e030314410070000446904501d0042c0036045412220203e00d181c0007100c00d40c40b070304990100903540b81c00da0300e408242e416207095440c110081c1d007007103201140f00300da880b0002c2c002c0d000c0c0c50041c070944d2001d00007040750b0b080203596001091300180003050606448601820194 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 443852535 1250 443851285 443851319
    0x31507080f06131a130b1c11150d090609020a1517090f01060f0801050c0f0f0f0d0c020c010212072f09040b01030b13020d0b060619050903120f04 64
    0xa2820701d80c11034200050304050791703596101d2019841e4a0190024500711950003400c04a42e00084213034250340d101e600018010380c400501481410020580d460f0941042c0c0f10b10b40c01015061080e14031070720b04038002e064084000c9014400c000000700f80d404484c40801c070014030070ba4072910461180e03014008510b40182101100313014480b609156032500f8018031015143c0d41c1d45110300e0300d07c3c00000c0c600310b800040c010b5886013400e000c0c10040c000508101c4460a0740401c4035902c5034251083d03103a56100d0072a214000529001c0300b00c41640d00401d50080844c400d0702990415030005010900601c2141d0700188000d40c0039640100703985041807600c60148018150000442e00384011800d40707101070310165540224100100100f10b840c40c54107030f001702480107025550981d6070104245c000e2205006001100070300c0098141e460b0007003501c0c1c214880d02e0504034a4004200064407991260306020b01a020341d06085020751044003c0310407482c10902400e1415103030000c20a400c45242e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 443853785 1250 443852535 443852561
    0x105030a09140307051e1c050a030612050604020a05010201050c040501140915030114030106050f01030f110a0f08090a111c0b010b09041407020304090f0902031507080f0613 76
    0x14400100000c003c00260126074403e0b40105203407108404110301c450f03100000186546c0c0300ca041300444000c10391074210030a0003418840d0722105030390400c0e4094186904103501c9901200c003200c05014002828034007440c002e03907050b000251910012401d89804035800c0c80078030070400007009594424900d02c03101d161040d014904041d000d400042d4a00d070084503009840c0d40100c01448503000310345045142c000214000c20840303143c100451000800284d40300d060582c2c030118148243c03d19040540441031665603243c0e11641060081d04801c454180d010014034001e0015000500008030005803e400c11a01c00311289804100030f9400c030580c10003c41240d682000c400054641641d89000c1c0c5440e90310740783ca6180040030b010841d07180d079540300b207842900d0090243e615000f00480d026035080c0c0c03c02240c441080d946030f001425000c10004c0d09849100300c001050401d90591702c0c020300040da1400304545811030b18265010040cac50f056880700c00000000070308545a44843c3d048000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 443855035 1250 443853785 443853803
    0x3111909022805160605180106080706021009051b030a0804060e091321020a02060f030609010e010312050d0f1a0907031404020f010e030a0f020a12020105030a09 71
    0x126141501a40c010380b00703950300d910700d01c0c1c503604141981c1500010030700030034640755081080d040c682050184103420003415403650b0f1804680c070100088403038000300360440300034091030341d8403440c3d01d5440c4458400c24006000e0401e420a0300492800385284450300305004101280d070780c200c00e0f58440f01c1d40d1452907040c480e803920800064a08030140c001040e280c2c0704c040c13200c90001e09201c60359400070034020f04480c100300f4500010746884100d12402d074501d1042c010090718218164680b010381040613601840115001c1c0307020980000862107030006032041551a60385904e2141501d0342804014940c010320130500c0c104500c41d40280c50039100010020517952000d0b181034080b91000d01003079811007a0680403200314100b024125800048600d0104089029000c884043d8940500001e03c2a410624140c0c200c2c1c0c880c620f80c1781054801025200c5580140c54103808000500200720b00980c001103000510391140d1441c003000c980c043e11958556552100e4050040014140855000c1c103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 443856285 1250 443855035 443855039
    0x3120a1503050c010906110d110709092004060f06080601140301080604120509010f0507080d02160507080a0f0803092803020c040507050a050304031b0f0b060109031119 74
    0x200c0311190000460042001e4003d03c0c0c0b02100040a242984c1c10100034007401805280346c038440011030380c1d1958400d00d000200a009401402d0504685a000102403418021805c0900c4505000030120504c0c2481e5140a92021024001941c0c605d1181d28040103c0d6041000b0250090040704d52106051500f6085454141c41c4a41c19030000c0e0096130b4158002c40c200810003004d005c0d0340b030001d001c1c0c0c101241000072290000700201d94a080e600100a8041400320800c091081940c215151880c1e0030364031030105048480603404005406d603130900c5008400540d000d00407070302840040c1c000c1c06041d0446e906407070f01079031031340050304080c040d104410100440140760600551060718580c03482080e001c942c00c00a18004a4843d81031045d8507210038440c0550700b00c01120820365090130016265038860030180d0340b024680c0c10100960312900b100304104041208c100c40b089108900c6031105840c1c0e403004444884450000506086a122521080d4500401d0007000c40c20740d240d190307145070b03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 443857535 1250 443856285 443856311
    0x415030b040c030504020f15040504020a020c120f07090516201c030f0204080c0f03030c010c021c0f0801052407060b09091b30100c09060203120a 64
    0x356a2280742e0380082d0782c4506200440c901a81840b42610b800c441100340c030044aa220f40fa203200d644501403007642d0009442d2543c43c002e0110041c0780c0d600410031084201d60540740c50722428410203000d5280a8842e000c0340c03c0c2140e228141c040c9a0b8141c14a00302e46201300165145041e00c0e00c90a0340310741c2550b9024000d9000c100e40d82420403007540040c80d80c1030640700031303060301d03904002040d5490041c00144a4403000007899a181002281d070a03443c607030300c500403034110301c902c1c14291800d50070000020f03c120380002d041511442d030454118107826003510111816080d208110380001c000600400440c60124030300984403d400c00d44031550104011800d4503544a160119411078070b405070200280b40045485501610304009030503518030408441c5102c00c0c01c7c6500a00c500c8002d8916022469400c00030200c1d040b000c0490b81c14003038250301c01031340c2e1840b60000710305281c107080003080802e101d0460a4104d64258006509041c844002000c188500400d11022a6503500c6034010031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 443858785 1250 443857535 443857541
    0x1c020301090c0608100e040b060a0b0a030c0813030206042402180f030609030409150e0106031a0f01020703020105210106050c0d020105010e2701020c15090d050415030b04 75
    0x1684200e42c4400c02918010f030140c048200208040c00c0e5540d0340400b00400503030010705d0760303000e03034000c032809003d0741c421000a40440140d04520180040422101d08041e09584000080b05080e06d036030300d9a179202d071401a4680d02c2858010b005030000004500055004041e07496003842890b02c2001143c42c810410049820490241100e4030300c1d110151520b06004411446166098000d0901403509180c03080e507a1040b4424020190354540d004561000c2c2c070084000500700c0420040f03c0c55179500d00003006450b5404c0c82d05204d0f5182440386e04035180818400f14030300340c10b030090b0040e2480e540056860750402c42c06c8500358030342c0380401c0f0612504095940c0c0a80f145488041c0c448480240b40c44c0b40910200020b4150fa26040050001c035044a510907030241c4980406100410070301140903280848002c107090641c00820484c400fa03d01040c6c1044038188031b441060103946942101c2c3c0d8a10002d00c0440c00308008010038024400c0c226030030802e0840034100400c1490400c0c01103811 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 443860035 1250 443858785 443858801
    0x150907021c26070f08090c0a1401110d12020d090f0308090706081015030b091519210f0503070f0c090c1d03010f060e010302040e030a0804021c020301 66
    0x104022140c80540c2c658602c4003082004120a014a0740307006980504030f80c0c07111040d1024058484009241810b08200c00020001c01902e4a048255280c030008002110001310501140d00010881074804000420a442d8440e40e500c85480c40c0e4924205402948628001c003120350300c0701045400720b01c1400f400f1752800d200c3d99443c03440e85400721029007070003502c0d085a010094640140412800200204010344003224084612070403e00000d0b00104050600305420003100410007150600707800d004455840c064500c0c2046180c404240807900b0308900130402c5c07600a083d400c15140116a90228001e881001c1c0d4545003203803074803000c0c17a5420142040b05c3c3c0094030040b800800c0700c00c0050000900b8004018804000c00b42d4005d008150409444142c9182c41d00000c1d02e00d550075040004a0140c1d00d40c02c100f0039413109140b001d04402404180d001c3c41c1400301d00d0004600020480c2d028002a94644044c0c1d1074603420400b50056401985c8049440d41141e400540d41c03e1040b005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 443861285 1250 443860035 443860037
    0x708070e0d0b1008011b080609011d1003050d031d010e06180c090f07030606030c0807080403090b0403081e0906030c090d0b0903031e13030e150708030109060509150907021c 76
    0x19240d42e0291008011f044e005001d28000e80c0c10b40010410f5000c0b80c00541007413072007030038010100c0e0b880c44503c25844115034400b40461082071003ca102942560141882d040c14040a007200407072150303440d00341e8030f184494580660110380001d4204091442ca100c000c0000c030f06a900741c940340300006603000342c15aa610a05410b074014000c415400d44202d0004240034102030110b08511708001e8804e50004100a061280400001b02054850850140038100300d031080f540b201e49a007060314007504070700e0039181c121444800220007068040d0a07a01c81380c000410301032850392a800c003040e2503044a0b44a40e008495560340400141c030001c2c0c560312840070b0000441e09d07440c083daa41102c0080e41c01601010306904020f00c0500803806524042d03064050a120301400c401c1d2012075000314101681003103003030300400e82408001409000314120b070200501071220702d031110300300100b1030000d45401005c0e82a01c0c4048049041c0384010681c008164019030b8040f095001103103819042010340300c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 443862535 1250 443861285 443861321
    0x9010f061e0806010b030a0509070e01060f0809060609011e0e0112050d0e1005090109350f07060c0503130305161418101d0708070e0d0b100801 63
    0x100c44400c41c480d1840080440000a0441e03500d0100503010300d10010b09030448441d00c440c00141c004000700555001401c20a0309510150381d20740c6c0040900074442c952100044120020440ca5100020f0150140c04e0052160f0016460040340d0346041144400f110036500503c00300142110450030800d00a010403c0b6542ca089101d10301103081003c3c0c60003d0b02840640c070303507142198803001e5103c10f0350111403c00664420a810040e54024281d41c40900d50b4102d400d081400c1114500301303080b04a28070000c2444c24010400d803da1910f014803c480d026502090302001068400c0070502401030144050320320f401c101280c044150581c5400c2540d95034044048000c216000542d4000101f0504000908011507800041e0704c01c0348034541c0c5050b0008640100d80003034041e00c260401400c507107400d461300c40402d90080c2109002241c421020074190400070301c1c41402000b000100c60b6005044040c030401d2a9541048280050407452060384034500208100b60b00740300d0502107844100e500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 443863785 1250 443862535 443862569
    0x30d0813051c030c030504150b06120115020d0f0c06020a03020909070c120e130b0a0803160c0e07020307060e010e0f031206060c0616120920041506050309010f06 71
    0x5002e88040f440755404151400301000f0102300840090f628620751010040b0b5100c4100c400101d1394041c06088a100e840138100000320b41c10a0907121040000d20b8090f00d0310040d64441c190760050000202030080341145010740d001441503401000c10031058100141003404010100e0310840301160850040303554891880280164094a409407411928000b0b1074000680089020700103005542507100b500c40c0103107400e41d541c91114001a14802040341d0300d5001caa90b8030320001c0520141038a000300c1c40d1a012550900f61062184550680d0b002149007582558403800107201c05608504695a240c6030100c0141043c48108120800d0b90011500e4000416083c0964000134040c0341c45040d042003034201c180000b00342c00e903000840c4001c0384201d0f000d103130042e505410301e206e00d11a0180340900b0f602c01c100c5040407406150401e40b28040802d0f4a10b03040c04100e46002c62080c101d08241e03502000300314829001181d102c2a518004900c44d58500461015142c9a400100e03c1c00d84c843c020f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 443865035 1250 443863785 443863787
    0x50d0803070507151d010501140a1202040917070c050f010c08070c080d020f1905120a0203040905180f06071b030e040509060708070507030509130212010608160c02030d0813051c 78
    0x240e6030140200070f090f1352100c1c0e00c01740051440120bc2c401e070508454146900000d65450b41d00540d091500440c008507640c2800003421f030300740e000600c02c0741c159100034030200d083d041c501c0c140141c81c001030315500d000071400c0d100d21003d9040b0355030440b21040c8046c004034109a042c013420713509003140e40080c0360075981d80705071078140303034030b0950000c0a02c003014038442c04144001101c85161000d80491a0f80e10000c3d001281184a146c2000440b1814181840810a6030703410f200210300082050308c41000080100c281c90f10816102c42001400d40c4d040d0500010580c062174650900c00d0810241003210100801d003600c40455020000d80c1001d000c024a868000409580c015000e1400501d4036459540141140c0038a40100d40a0360310302070f90001c014500e41c119988900e0b24000e000c0380f982d441a005000e11000c42c2d00f040c40800032021844064001d001c4040e4880e401000303800040c8400104942c0c080004051000700c5401020708800301c0c0041c40807102c449091100e41e22480b80d0200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 443866285 1250 443865035 443865041
    0x705010237081c1407030e070f030c030c080318042309010204030302010c08040305040b0d061d011a040b0315061902150f0f0f0402030f010f021201050d0803070507151d01 75
    0x100d03c20490401102a502c40d0b51001000c1d401850741c1000101c03900c0c0c03030707031024a00291504019024040c800001c0203004005036a0300032680318076544034000d82c40d40080d507109e0080740b11480a11003425800826407404c3c1d00505080240c402114142c0f8029429401d19038209582da10041d95002405009042d428081c50308240642d040410150416550007042803007180300e11810b192011401a00c84080c030303000036004000c10060524440c0d840b0b10505030701c00c004c0c03003a103000f8010841030010700e0f2074500644040307602072044681140e98903450130f980400d4410816600900400c60300c440500300c0c0080d4111060580e00910001d80303074020321a0050000340001c40342082490030400719030f98000a0700d038402032080389080c00352503030300c0401d1034420030748015000d5508007422403201429a074090b009148006000109030399981050049401001074041c180400c00c000081a0798096401013000500c24841c41c45040b0203104214115580314146100c4075241407207070b41c07115101340 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 443867535 1250 443866285 443866327
    0x23040b03100f1d071e03150603060506040e2a07050d081620060711010b0409110d14031b0f010b1e03070b0f0301080f070501023708 58
    0x5550010442c100f4044200b40141805403184041c0e10000152840d442810560128456801403620b00c20b03140f4009400391620341013212613400910310010b0494444c1c040c0c5000c456014000a20f80b0303050011017003034664009d001880b401c0003034111070400c1c0f20040c4c0c0112405100e00d4119100c0c011490424108000080c4130710411911340b0501c8012041016081c4130790b182c03814241b42d1515009018840011107200200d6140281020489003a81000c0544c9000803010020271429000314104401c49d40074140142040c820440c041d81d580c18040c0b045903a89008000158001604001c0c00c0d25660286011083c401c03c00c0d001c5240f61013040100005110f10f441c000e111591104020695100e902440d2071140c540c0360030710564585042c8480809820f03d030702010b5440c0d0b6641c020f945240e000b0300c6180d1441c420b40700e001d00ba49001282e890265407059010703001070002e220b4001c59075095002042550006080d104230107000ca9050004042d2244942030b490b11b000c03000e0607810301458 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 443868785 1250 443867535 443867549
    0x2150403021c0f0909021810020c01180b070b070c050304080102090a0e0f0f1302060c0a03020d1404050d031103030708010e0117031c0608150a110901020d23040b0310 73
    0x841000101c9642000181c019124072110041e00e8008000c81c0e0356407840d4002841d41c01403e51004030230000e42c0464030444980083c0ca445106140c2019080080d01043c4500591444140640400110704082c01034000703190f4546100e4a1040d80c45060855115510181840e0340c0040c9942c258100781d07619000500140856410500d0b0150410640c90310050525052448460002d2034107071014808885d8107802400e05511018007940240d034852000100342d002d4803c807035032901440d10601c0028051724412000508203441d000a00074601307680c81e000c40030b02190180b03821031000c00b08003451103400b0a564030049949804100010100c040c0c0000f0808000c940c2601c0207507600004441d0315080c10402117600d00c40c1843c01000a110503084030f0780034000c0c40c204c2412480421940c0e401001c1c0c5140401207840001c030381755107610400003190b015030011458411641e01548102c0101d00f41250140105510b182107400c0c294400c2c0c110303103c00c01001c0248040e003504001d540f0090a48 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 443870035 1250 443868785 443868797
    0xd1103191107051f180606030b090a03090303030b010e1e09100f1215060e0f060f013203010f06021002040f0b130803071109070905060406030c02150403021c 69
    0xb640d12015107441d400f1410242c80c007030000b0f807103080d10840d50045c2c03805410780750441e11490f5030b442c00102801d11031005880544031074011603c10700000c5200e0060710b91588595a8803451590705402030001454124103000c2c0700c6541850326107a80080150280c40d0a44034558891004104000500041d280004640d02818280102c000201450050b214400200c0268a0703003890b107007804c039a080c041001502d041110002d40091298002e40c01400ba07103003c40b03140e41c1d8000c207122480c4e141601c6a400200285010300c40001d50000101c3c100030100141005960080030b6034001d540b00303038429608125000f104020b0796034140036405840d070340400c0945c41d041c60700c408442c0450141c000c06110020024a039250203600c428000010300c1d0308410380381c035030006041114032061468031603400b404514000032586882075141c0c100742d51000709001c0c00c041c100381c0c085004011042400d0107610904680f955014245000c0701e01c82da1082e40203202e003188600b04000004010b580c50f10078084 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 443871285 1250 443870035 443870047
    0x20c0301020f04171c1206090c05120f0f0604091a0708010f050909070b131a0a090b03090d110118140d020f030f2503030b030105090309010c080d11031911 68
    0x924040e0030200e034401464115141b1358054480e90061855900661388549440c40505c402500316015103500384000001d04459510200300050031002100d0320581d41074810009038841c9010740c000001180200c0000c45000c41c24807110815a606540220118404c800100302441855105a002d4a419610806d407410000702042c1c0e1440680101c440443c00450400054800010030b4001030002e40201400309004048550581c0d0203020304400103403141c0d034082001400b0204a90154000700700030081c42d281c000048560564107009481195241e613072040102c4020b17911000039500480c100440f418104400501c0d10030300c05015019034004a60046403c00044141e5958200c1e00345440ea44001448111708120900c110010840b009407000c3c006140c0c2c158000305001c2c40980c02013149440e4070b010785a9070300a12500f42e00017051481a0000210520302410300a0400140414140900c44003800d41ea0021100c001c00c01d16441d940c1d40036160b160142210606000b181e580ca086 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 443872535 1250 443871285 443871313
    0x90a0b01060329031f0f0501050103141315020c1005070305091b010216090e0d050309100b0a030203010216111509400506030601060e0d03020c0301020f0417 69
    0x414a81076001d00041d52042c90700741a00c05001e0b40444200c24200140c40c00c4c01c5c0760320840202440d602c207919091404001040550082c40b0341107420f40161941146a590703140740342023200c00004112001059001190208100390001d0301800503004040c1c044181e07000246011180d004007280200b40c1080148480102e01082e28007030304410305a07058030300180c0c0c40103030300e444603609400a1201090100061151541c1c0c492641e01d01e00742d0640d80c09040365041200c1500080e075082d00c0c1c41c0c1008810362400e103805c5e0310400f400c07080075182d003030300d25030301e0b00028226088011111451801d8000303180410503110040304441070201d983d80c11fa0111a40780384070500072981214010303000c0f41400e0301080300303021409000407041207007030020604141c0d82290341203a440c402c0562504000201e0000d240118405043c0c1c2d44a603078150f620300600b420005035000620080d015401040284080c545080c00240041c40441680d02c1d80c2e40d2a0500b500071491940d1031441c810b420100d00b500d440d03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 443873785 1250 443872535 443872571
    0x230a0b0c1c180528030f020114130b06010c0b161709030a12060e010b03090c040e0c0111030f180a0e131502030601020a060b0f0604080a0b01122103090b090a0b010603 73
    0x42d0fa0186003030803a161b42100180e0051031100b0345102c3c81d046a4041041a101140004a005100c3c40c81d000c1c4030744425005651610305980d0050454123401300060340c10010800e580c1600ca07103841c10700c0d00c2c0408aaa00b140b4040c06894801c901d400008001ca80950000220903c10f98484401c00c900c51400041210119042c000c010442c080040410161304042000c071041c503400400c1040188550402d40d5520100400664041510b071084082c8130b0742c000c010b81d10b080c01c400541d41e1420f4465509150308410351054540d00c003100f58000701d095a2560f17103c074030403000003013410910442801c119170011b454403a000300352801002040f2059901040140784d8991103400490003684003c009019030903a0064150031100101e000181d8580019003040803078002d565501c1c499894440c40500e003900c6400c094800d03115030002e040d8507d1200c82e01a02d002c03107464000307581e826a50310140d0340c2100703685010503507002d401c00000780101000942e0060142d800c040048692071905647c072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 443875035 1250 443873785 443873863
    0xa1203050706061e18200703110706030204090b091e06030c060a030b09070c05150c09040606121a013207230a0b0c1c1805 54
    0x4129000c50748800300107541e04084094203142d8480948841154000e800000031071280c8150103507100c1c0444070705c9005105000004410042d403500b15034841850360350503400160304170100070582e500340c42d2580d020b00c1890b010702029a00560b07168685004001500c0001c0c1c00346200f070606205001445150224080d030a1000303041920141c2c0c1c800c00001c2c244150040e0f12a00b03c01c00041a010860f0701d43d1107100d5040080f42c0c0c800458890325001c890740c540980d00185668807003440c001d1441107141401d94403003001c0301064901400d000c045400e844641d0700902c045504140800c80c01c0030640a9068001100100c9248544190300004e040340c0b9031840c4042920a4021000e0a243c400c94580400e014170400d6181d6443d100e14049003000e45100c035080441507814000903140e240817034074001c0590000f003e01d8103a154480f84a11541c85451103940c0c811b42e003034940703a4280c03c0c0d0040c03082c3c0311880041d4142c5900d0a007400350034191241c425890550340710445c030031054440c2c40106a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 443876285 1250 443875035 443875037
    0x609060f0e100c080c07030201180e01120c030203010603080316080601020705191d06120c060a0503070309021f090509011208160807121418101704080d06050a1203 72
    0xb25541d080318054074507840c01400644039502c0014159481200024400c088074400c3e6510562150340b10000d107500c07080340c01500600c0765400c0041200b50301081510712040e000ba0301c070002c41c0b55071368002030841d1710951086690003004410003c1007040b020301864101103a06001115140180000751200089e000d80c521030f11030362265440c49030007019154060106541d02d006000c84c001700035010240115107852040b1003060000c403c8000114641001d00750280c50b4908012480c0d906941a400082c010070825036034007800b01c0075a82d42030756944050051010400700d03c24507507000300140c1c0390340c100078020707036440004000c01004a002040102c2c2c00108254603070040740301c0d41c42d4450302d0400103003202501113a2801808100d61035100c1807011625007407110f1070490101d8041d80941c001c28600014a41040900350812000403800d2030420714045d0f2410000d800c20202d0039409440075143e80802003165481c1c400c8520404000e004101d404134182460702a994540c19140302d0020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 443877535 1250 443876285 443876299
    0x4030e0f090601050c15191b140714150402031c020c04050a02090a0603020a0e090402011b11060c0601170609030a050f04030f0609030f030e0c0904051002130609060f0e 74
    0x3500680306001ba500d0411841c00421002c0c1003d004154050405503180042c81e45000c55600e0078034a4800c0483d0b07000e4040d29140082039500d103840d0000e42040500b80c070710385440b1a119843d5070782800f13108082c9182d1841001281401d00525240c040b101e00c182145e0784941084225130b540000b915200c0c2801106d010030b81e651880640d00c040c5c011541d81c01e410105104000c140c81d501b44d00a840102c0455850003c074203d00300412440d1344003650043c0c0811940c2500991130a119020040e1150250f03281c1c2400c00880c8002c03038503c1c0d001f070303116481c1c0760040001800710220344400700d0216002800100003500385482096124491003070300f44107120300018102c0d0340900f8607060ba0010b540103950300f0b0140b100c5041c5100500244d6a040f40041c40662003c07403054006d125000030323700300d00018414036001c4402d0203000940500300303458a00c90300744007030464010703030009050344500b0b0907006144501c1c10380050540d441982100702440140c0c80482e2030641c1c000125103d50348111448 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 443878785 1250 443877535 443877547
    0xc09092f061c0e0a0812101a0c010b3003072a030c1508060d120c050705060f0702011412060904030c050a0c26060a05040201091d04030e0f09060105 65
    0x100102440d5a040c01d09000e082c0c00741c81404480d402030102c2146e035815040321903844c42c03400d105000d0103004000405c000ca01d52400c2079440d800151400280b034000000790a14400d000510074000056841138466106800f040c0060300703c0c804e140c450940300700840c00c04541da03580f5814a0300b01854080040a40b8802641c40e240000f00180190382001c1d1030300380da588408105c14604802805032010806480228105040c403410303003401c05402c18980805034a000c80200c828040c1800203035114401c11801040540c0c13104024003040c004c002030144da0300303841d10001d030400055610079984050305202d0304a1040103035030040d500110444030484295035034a0103444041c8803060281c90f91182c4090502006552001c4a055480c40c1890008044450b00c1c40c4c14004a10781c80c10802d508090042803041426400582d000391050404040e07141d00d50b02000341c01c0c41102d8a00c02261500c0c010712080c541c112503030020150003038515404107025803000c42e011840c0505440e0402500281f1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 443880035 1250 443878785 443878837
    0x501030b0402270a0f03231605150c16061701060503220503030a09050601170304030605090a080a0206010f0b030108030a0e01020c060d0504110603041e0c09092f06 72
    0x803e401816540381013220086d00e031f0401141220400d20000400038080e09480c400d50030015298500b01192081e640000b4200b0003031000c405660b11070740d40745000620007943c00340341c24032403549002c0286424015103440c0c101c0003450842c8400fa9200740755400c10060015070742c03103c1160783c03003111a030f0304c600120a20316505850300721407140601705001c040141316000c003080d004055283d00900490ba00ba980703c6120324409500d03078140080941c8200010800104c854001c030390300c0300d038042c280c1c5c4140da41500c0d01d0b40c0d1079020162420042e00060f006000842c44150588c2c040c110342e494803421b5604203e0f005940b1b10610f0580428001c0203400314009070b02c00c000c0d603040c01401070708650b107911a9141400141c041900d00300c40c4074914248424050914900307807441150000007401180902550b04050103903440c005540010840002054419490007000141403040009285ca204e03030482e4030041e00301a201203c6080ba00a18500c7c15a641e0419200a400c0c0728400e4840c041c04861 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 443881285 1250 443880035 443880049
    0x80f0a0b2b050d050f1b1219030c0e01050a0e040f06090f05010509060f010f0203090a0b0a030b03120307030222060201061701050103030206070c0201020a0b010f0501030b040227 78
    0x3400742949040e0121107066211081180e0080d0744242c0031511919011402602e040c001c040071407039000700c14401014003901440c041d90143d021807059900b22084980e580d07200d60303c448031450740000c3c4082d486601c0f6901d842445503a000c1443d0442c006a403103c0002c025206072446c81c410043c00d5100303279040e5074860340045540c60784a001080709554418000e0041c1840c07003a8030280a24010000034181402c0d1486440f80b1401414110741c103500e440159a00000c5043c0c010461105004408640e02c80d00342c11400f50034015030b0710740c451460010007030603150001c03580381c041d4020402c1184481d0451050fa50850914107016071240340d0b48094030042c4000b200281940b4210340c6001410940660014050b19001ca4a40e690768071030400c554240c85083c480140160700004c00910100c1c8501603895100f0f00c144155241030180d902d5261550b9000e0304920682c00030344804000c103681600c111002d11405a0b810b505200c000040980886d8141038510240e0040700c95143c25641c0d079107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 443882535 1250 443881285 443881309
    0x30506190e01060311040b010224090a1b05151c0e1218010e011403011a07082107020a210516080d06171e0f011109030d080f0a0b 57
    0x18000c103c096641e0030981c000c0301c9040605800b0314501003c205440d403001c108100082d28000a12114841034244006c500600402100d200d02070440c0300000034000520324a940604440d411450368103000800440300d0781e001101c40070310410011008443c84a204401d4214907914000404c2140000d81f1410212200f62422510100062800d20050f900740c0940e82c1c0c0100b80c0e20101c2c034004600041d0b40704c41008141c60a0700c0e4040c40104000c84900c052515000e4050901c01d013460100e627a41000c5802c4003100d21507101c420741e0140341540c180382c1040d0344001b40784014502c5980c1611508541d04038003610180d03003243c610003d945036009208807540303840300802d250000f040301d06000c504e80c1c21003038806a03802c2c1030a5000821039110402c0e5400180319101070229400c040d80142c0003840e1000881c41c96004950048089600031703c6801e6106031151407290740c0d40300660405084c0280d1020810a03c02164144520f104107401e0440d44902da10000044142015000030f40c1c8020700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 443883785 1250 443882535 443882561
    0x301060e01060c0b070e220e010504020604030b0405010207081b01050601020c0a06080915070503180c0f0405130510020c01050a060303090b1612050d0c031a061602030f06060a0603050103050619 85
    0x1076401107c8001a030705240e8031412404000700a03001c600c40c0030750700341c460544000e940498184406c0c40030580c09860303140c1151040d0700052404031107544887c1540c12070b41c940d5001d00040030044298034001e0103125407101d404d00c0944100c0c0040c0d4000742e00c02609008060404c600c0f000000d100320030407c06440020030300c03800310b0760620f40080010090750040307400035419106101c0725507250f6000036002514100007041c0c11110a091001d0000900d80100a1200502844101c0d408601c0c1882000c40c442c250f484051313503c0607034441403801d464015000c855071314609101000807952110105064a100d40075035542c3e000054455a80c15203922005040d0003092a03125071610f800400500ca0305000c1c4c01c043c007040c2c01c51081a011a0024840c0b101130b0300129152039000e01d0f0203402460000c00c00f10555420400e10303002b0034501a050382648580c1d6208509010130ba141c10f0b12520001c091030300d0144401d40c1140e403119185c55000c1c0000c0300306800da810154010f103035900f10703442078041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 443884892 1107 443883785 443883799
    0x1020c0102071b0f060518061c05070320030412020f060109231009021e0f1b0d020c010c06090b0f0a0e0706141b1005060301060e01060c0b070e 63
    0x1003440b07d54001e00801c041242031b43ca03030034411909206080005400d1030546000b80480c1e40c10150381d901500f00e02ca12a0004800e102102e9100303500000c1c2e806c40031303203101c0142d19001f602c1030008203070302800d000070948500e1a48420081c8801007000e80b840320520b403030002108425070303070060300c9006040203100d501b21a0b0010a544001c00405203403005100c61000840c1e0017490b08844000c2e000505461700400c0258441c0c002114040a0102c0120400c006980c0300800007800e0306000090400304240081544034048054110744481000c0c9081c85140030004c200b2154048076520f8010741640c4010006070f620295001174031216101030301c003120f11100f03400011100d0021200101902c44080003803000080500c2c2c058004503041c1001800c0609407451038202801e01e0301801d0041181ca517100c20f013003c810f03800c0200780155844168003260140900340722140c012070707 = true := by decide +kernel

theorem cover : BRFrame.Cov 443705035 443884892 := by
  have h0 := BRFrame.cov_init 443705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 443705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 443705035 ≤ n) (h2 : n < 443884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
