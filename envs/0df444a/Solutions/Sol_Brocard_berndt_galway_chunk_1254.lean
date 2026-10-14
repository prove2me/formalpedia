-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1254
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:01:08.720952+00:00
-- url     : https://prove2.me/submissions/3bd570d4-4136-4e3b-b65d-c960a3fef00a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 225359712 ≤ n < 225539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 225360962 1250 225359712 225359749
    0x160e090c0105040518040f1403040f0b0310090509070f0909030e061c050c190206150303040b040b0d090b07030204090f14070809030f0412050c0102010b06070b06040204090204031104140c09 83
    0x1f01401503070354201e000400700007015240d1000c201008040d1581c44441d00400c0c036144200c1c0356082103c0210030009103405018001354070f440c00304160f11410230508004042c1c00080805072900e1301d120320094030f030105090b0005413007281303aa8842d1408a003152031810348011101500412910090003800f4001c0500c04140d500744002030b41c03980060b1826540368603e5018000c0c601c0c101c03105200c405800c0203080c0c080c1e8001c1c4411710020300c0c1c0c0e60460f01592400f00d00540c440c1c801211075005070164041c024600c221640a0146660b0542c01400550314019000e014104201464100700c51078103d00310244030b40600131490050040e8201030304030520b2000da038984007158402401660080e403100034802c400c04400c1c07040c0101401a84d11002092000f4440304070808000f48550142c8507014100711102d001045082c0d856a0440d402808000e100395151a5030b42000c0681c0c803088081d80b4001c50915041c441c42c0803c100076a031007011184a0681811101d8007170102c44401400d00c00311 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 225362212 1250 225360962 225360983
    0x21908010501120f1b03020c0105090610030b0612160f090209060313020103270311011b080709080a0303050624160201020c030a1212060f0b0903160e090c010504051804 74
    0x43c2440d00051484100025480c0542c0c1d50400d03248c02402c460004104405035004001802400790a4102c84004c580d00248121425100c1c6800a900500c4120400c4400d202c1c80076182c858150b16031303c039011984c68105d41180355654a43c260164443c1c680e03840c0e4098402c10000b501c500410b40d03900c071001c0c010f00d40081c035908030050038036808180f80c4107003005623401c04801041541c0201a9461b20048400900500d034541028000d5103403606d80c50000d0261220014003454420040c071002010f5800484482100908000d0014002a5080c6001c1e902e1a40c0c40c4072000440420030034144070b02c5110034903180c032916400b10510041071080b03046018604a15040d503904200c00108140070b0a00704207105820f000290000c4e1044040025032414a00c0030000f01940d05810f00072903000700070181c0c1d40d03d15040000d04110400741c1c0c0d55881c0e4401640443e40c00c0c02c5140315441000c40c0b0084601e04400c01006640c140114854254041c41d80210070300666880b80b20f903a0050f228240707114 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 225363462 1250 225362212 225362231
    0x70201050f0d360209070f020f030307091a0a02070e0a090c03050309010215010f0308070204060b0a09050f06070b060607080417030d0b040513020409030e06040801021908010501120f 80
    0x101a1910b00f030f00080f2140d0458500b00303040c07040710510fa008441483c8840815501940860300900700181000b06004800800359112402844403600202e030b0403007680d9480c646090302900c862040d00074510301602e030b5180780600c00d080100300c0d104021150002e002592900901d440d090b000100800c1400ea142c04a03640020400452180914842c20245803540c05d404002440c01104190b11584920300f94010012080c51840710b0040d01e4024050503500c806074000b00f406018140c1c4a1010200b00156074107c86900c00354510a0795811070300c0a00f214441d2041010a004540000e0203021009012030800d1030304da40104085442240e1003810b01d580e95220440c8190701041c602c401c0d404c00181074550504238401d00702e0f0410211000c0000d0708001519504107c45441c0c000c1c0901c0c1d8a440480070305000d0050440c103090000c1c0b00d03983d00c3e526009801d020350011040c90b1480404503030380b40c54080c003414180d416180b040c0d442448241d0480e5200f00a41b0850700150390059841c1134a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 225364712 1250 225363462 225363487
    0x8270708030c01020409110304020d060b04020f1603080c0a1b0c080a03050403150908030412020c0316050102100506090402190504020d020c0607020703050607120e0a0303050f1b070201050f 83
    0x24042c20505100041c2c03100d03d00006038050302d64455400f54611000c2003000010317620804140c950503084440050440741c0c91020800900c50101c2c0b10040b01000700c0c1d01000c17000010104e0207103900c41d5464100b6601d400d40b4100b5640107018041c3c02150fa0b00505103040c0076481c03041d908042c000d1040c1c03001030f5601d255460905092100640014030001002c0c010f00109071030851100358105003c221030b180c02c0c0ca81900c0340c000540700a0401d000da84281e5002c0c1d2013000115000762004050b21308600d101048090b40141520071540980100d8010280d5010b5500c146842000042d084440a0b51aa803c002d00b02602c202d010008a00721100031455458600c09000c41110b800f000598501c4030040440c03400a0040454045502612080c80020004628550014858200740d00d802030403e1030744024040c1d002034881c640c4502468030043c1a4160861405140e12580f04e14040c0c560b442262844408000f414400f12001c110443c0194032920003402c0c49910031349110304103201410072 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 225365962 1250 225364712 225364717
    0x90512040e061e0109060e060c101d0610060e010918060501110115050f060403020303030c07030e03120307140c06040f030e01030b011d0f1903120827070803 69
    0x307240030700810200a01030900d00340c01550903042c4107003070a00d40508400286030b55124058101000320340745400007143c17185000c0e00c0b019150101510205040e181100c0024102e2400d40071040c0b900070145044124046002809030380342e022000489801c140c010f40b6042e100b190b200d03040043c140400229151011952000c1e64201100800da20b8a0040010440301c0040c0d091301c3c09034501414904403062000610341288c5050350151907111013200010f2041c0a01d50020703405000010810461802c01801464240d200762102550240c000d003e0556540100340300f441e400c181000820303070180c004c0c0180f401c446401d4100501d0034003182d407010708000c01500c040351001c907400411000c058104415000000c42860200007000d40750300001c10010404000036100c0f014031f011001d1548038100d056092030300190040091080d1a0b204640c0c0b00c44511042d2903486000e0b03a050000b512540c04a0b014a0f05100000100c0f8881a160181052541c003103103090705c036418001510000a001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 225367212 1250 225365962 225365969
    0x1305210303071e0801150c150e0303060a0b090a0b030921091503090714030f010c1e030605060304021c0c1502010b030d141303170d0e01090201021009051204 69
    0x980003114506264010b00f074400c03c000c02024800d407040180f0040d440c0b801c8840b007070001c41c5070902c0990468104604605d1618500840207414100a45401d00c400402103004040c25140070340307015500c02108420340a03500020f0b512200b501d5042014580140296800c45800b2041d00c420010740344410201d00d06414240c54100f0020408017018601000940c800001110045282d4509012516200c8480b405103112401514505ca007403910700300100103016030103800030041080686030260501401e110f01c1890007200d07a1640b00c0f02c42c4240103034812904040c2110341181ca40c0e5080040402c865200203000f00702c600c0c04140030900341c60340040101901c0e040300e00c2d100540400207084d80c00c0d160741140294030100e8a13042046c1d00450f10f03000020000d401c0e540b1295130384c540006980710ba40c00984001c0307a5404812820035910001c14156140303141c10441c7d050080441c80c203841c0701c0080a0b0150b0030048080c5040c4500390004680c080c8500251205c5100080300200039030443d81 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 225368462 1250 225367212 225367217
    0xf020a0903060c0305070219060e0303010b090a1707030f08070606060305071b0209040305030403050412050d0809010c0816120f0b19080a330504110402130521030307 73
    0x950401c240003891242c0d10040005240034041031500b854042d540b28401140d0010329403800f01e0080a1110a034000030744800310405071b03903503947d4590085040c1c0d00030240303042c03080ba130031440040d55046910481e03840d6600c20014000c6d086c995160410840318410054907444e004115200014189100b00d0300030304590380380001c081c1071980c07004200c1e104140b960517130100c1e1000c000340903030303900101e40780c0c05641843c01350f60b40e40d140c1c86e00f12803502850307002c03586076812800080c00708003000c5544010039216a980810036510291901e090b0f8011100040104170000c020800a80030001c000d0a40c1c0240e00b410415122409a803200311400c0380c00c401559551580400b0182c038084460401081c1400035182c1c0842c102542942c94400100f402003e00b401e11072070b84101d070706900c0416400301c0a03034003001c809042d922000e00a04400c035802c5030308490740010b0074800c2c9000c0c0f09981c500c0384484203020810b41040184985c9140000055a4580e04c0743e840002080d000c100a40c483c01056 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 225369712 1250 225368462 225368477
    0x503030a0914040c080408070219080303160807050d0c090b120a180201051213171308073006020313140c0d0b13080c0c0310090b0402010f030f020a 65
    0xd500e80e41140700790311103640f040303051000040b2034951045545030400c1e0002d05055031911343e440010416071041c5031025882c99140e00005184602101440c40750040c45060300d880ba030484400c89202740c00b1200900429000e1002ca03070041b003c0d5102c03c1654586050032007085880d2403240255400005d020032a5902400c100b10450801e800740255610411810242d0404d02e0340c000b801500900080300c4010801d034000070780703941811144070b41e07554202004540c2960003403100c19480c0d1100c80750700d5180050340f1000600c03100014428044840a040d0b1408955420300a00e140050500d00f026140f08058038580205a0754030065000381035540c0091a0b100642c5010100c4500415041c410364108046074212a141e0360080551150710190254035075032800d41102c00103240c1400030700203840205400c0000c1000154641040c10300718203c55803819403c02800076101c40b901300078941d21f12040070800550240d204859035090904004c0b0b8000001c89407a0304a07000601c02d98002840c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 225370962 1250 225369712 225369719
    0x10b030603120d021b030c03041701110f070b15101101020c03030c04030213091709120a0602040f08030c150934121a1f08010b0a080a110d0c0503030a09 67
    0x2017402505010601c1d0041d500382454104901e03200e0181d84a161585d2182400404544400f9030141b00c2c440750030211291544a1501d0891306500400422200128140003140c00d4070b860700d48008050318020604500c02d482d2074001c81e0280c101c444402c0b00f542d0203000303c0002d100240059440f8a03010b20803039484501d18010041031651090441d10114640800c2c0f5000c180700074407410780b880000464a0381c8031a030101080320b5000070403150006000310368a0400f0484c03940c0040040b036a5424210040d00c0e04c44010310b8981c842c0d450700500661107101410b044112a800c03031640165200241c0b407130b0f43c000b452200000c841c02200520b8148100c403a064044c10034115110240128903a00c070380c46a44e940c4c98120a2842015113105c14000c180000c5520540b100001d00030200c0c5c130554410659100b00b0b084c0038107180d080c0380d44945280007001c42d55800010b442e000e595081802180c1c151031507420b0000c541000441929092400d680110f0251002c10080c00c44841680e10000114507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 225372212 1250 225370962 225370987
    0x150405060c0c06012705070c0224070f02030c150406020d0f0f081902070807050c0d02060a0e030a12020615010201061203140702030111040602150103020108010b030603120d02 77
    0x240140802607100c801d00075422580b400207803490545005d03003801c01250210301184201d61000201141c4c07050b003001e080186440e4804216400c1d02e109440d858444078002d0b0b00c800205042c000c440d40701483c2071000300041501542c003581c1041c00034060301e204e24100701c08540408030070702030000c0080c400501003000a5040041c141164524a80040040c802031070041480811100c008100134204000c038075210030750f40440200c011155030455503440140b800003800d400203003055a050081180b600b40d1414444812a0015402002c0c249050307554102602e4244c0c16004d81d91301131141408000000e60140303403440041042d50000c01503407801c04441e0391101e510b0390f039560440e41403510802203141412001004d960381410189020b1041c0021480240903c01029501d90308110300401d40858040c002d0054a207140c1c280c0d040381d10140008030319880c00f0310000780020212001000200c480c0b4000c0d6800010080c1644d080382a440d1101845802c0210400326040c1e001074615107181 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 225373462 1250 225372212 225372223
    0x13080c0f0d0207060f120b19050306010b041a0304050312040b0a0506150f0a0e0a060c1a1006080604020c1c0207050406030506010e0c0f030a0f0518100c020708150405 73
    0x900902c0202005400c1460040c12813800d4200326084c40440e200e406000031180d0003400c09014060301e10f50122442d08141c0103000481e1040074044c2c0144d42c00841c12440d00421503095170412610700b200001d44040078144d561000f00705803210301040c0221202d0550120b100c82c041c034021060f5165506040080308100d0740003600ea680300341c10415444400b240080c2c280c840e00507030084d0550310340d640c0d980141d801e01c416102c010f601c00f481502c08100a50071410203580340e0b01443e541824a9081006143e00e01c0c3c06440c9c40702d84600c20401008480d100c0e02d0025441007000d0409410306045c400403030314101980700003110680c02c88100c0c0e02e4559040003071900800e0b04440c18400340b80341d070b01c5550312400103000c2c5c4841c8007040d0000507401c800203c101c40c1c1280103500d0065980c5000505000140313005040e03419080d04142c003245004050782d21040d0485800d0000d80801002e41c1c0e001e034000c202e140744070415030058a00005081e142481410050807a420a60005107402d02c0c02c2c60409 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 225374712 1250 225373462 225373483
    0xb0c04030b06180c0c1213060806010c05070933080d0c0308010905060a0e04030905040606211a030102040305030309010e01151502010615111005090a020913080c0f 72
    0x103084400b4011080200005456008401358403542d03510075203200d009041054401c00d50b051400001821071032610901500800c0712029520701c03249444103001185d01d121070b46030182c06584940030900c40340312540d00c40e410070500e043d9013802020301c0008030501081644240440b0b801202010403440710309003c00c07444411540303414802070800d503070042e01c03820041c0507221406070ba5100040d1f41c0d450b48016407002d06140700241c1c000c0c0ca81460003c1c4208018012140503c4c2012000100107000301c03203240008180d0340032911310b8440c501e00f95004000a880c000c07028420800147c01341d450038402007028502981c003459070391030407030110b6094880c81c012410b2a07a1605d6024040701c02e40e40303800802d0b50f01c122014101c41000c46002ca01414198100700054140b00801d14180d64001c2562000f00c01c809084d80c0c07246c44a1180c1104807071080f112213005402c216002801441d0002c0324a51004407062503000141c107545400d501600155400c900642c06091000350700101002004140c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 225375962 1250 225374712 225374719
    0x1309050d030b011d03030f0310031a0708010303050a0e06160605100b04060f0e090f070e12100902150a050a140306061b0c0d05031306021b0609010207030b0c04030b06 73
    0x20841d4000000b80413441c13450340700203010041c00070028a9a028421100c101c5041d20003152241001400020700a8192208449410482c00182501e10b01030000307910803056515800361607841e40c0c409076503540c0f144900008201d01c0a0744005c4507600e50f80900100034009401044400a40c5010740c2110f01c003a2030b00c0078105c1d040d0401c00544650700c048a081d01e100d482c0409a40000300b03c01d80f00c0800030000258403c24030420040740c0085560881d01c0b44d04907a60b03504800030240207010804950040c045620f800c6840d0340f0308982415002098501e01c054068480d260500481856903003105030848001400060440950f03540140b41044081b815a5131503c0d5082c51000034085114a80f2454a000403224082840a409000d407103040c5030060140d44200026141c816100d0b40840c841905600d41b6142c04225a0720019985500c0314100c20a946451303071803010880b1681150143c10304611842002200048401101d80e0084c400342036500c1e2541c2c194075001040700c8004120230301 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 225377212 1250 225375962 225375971
    0x1080f01150506090d020a170604020103061d16050c1506090705040e0604050a060e04050a0b0c40090203011a030601020c0910050d03051801210e0106051309050d03 72
    0x1c82e5210000c50341208401c5a6408906505e440440d4404007990b2164180140e140c0030180000400710311544140d201740c0c0c04001d0b1513111980448212858241d042000741c802000402400750610300c4070041d406420300b9824014107d8900f85001040348101c242602d07810240800c50601d28280c0350000348900b0810704150918401b807508a600500140c812925000420082d514a50042018042030741c900c01803441e040c103026641d017040030400c0310022400701c00204170b0700188003034403403804445458800e00c0708140c000040142104510040c1c006038620203203d8600408000c03070081c5800c11015880e07614100320320011039a00c07944e10006480400801601e41c0e40403540741c0380c255040b190090031f0f48030040300c08000e50032a00103640026282014009254100d0068500c4140c0f04116940700c40d03041004542143c1000c80d031064019a00e514810524040d030050000310f090807000103041c48e601c00000c1c0c90540ba40d154800202e0303840440e20188a024031100c030080405050034031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 225378462 1250 225377212 225377219
    0xb010332010509040b0f06061c0516111917040e011401032307021204080a0b16020a2a1701051807060f05070210050405190806040201050706090b01080f0115 69
    0x1100f500c4003d156000400d51b20380041c3c0503944400940d20321407510055000f1101d01c4100041c01024180c0e444d003030340c03031105004514a51240306204214440c1c0320180c0b201e1144504210550b94409200f03c0341c25034203170072501600e211200a0700040900c483c00101c294500b04491758a2044000c2c0581098100040080b52450140140e00740e0440516036845665642c030049050005040c0310310881000000d0010702d1000c00510020600d000d1642d00c4c0782c03601c460070104840c131043e070110005031b0004640788000c82d49101c09400804250340144d80800d0107403480e0001c0000c141c111400100d2160f8003603451050900c1501d03800b0a454140000051015520903a20211846040d040282c010958880c2c03074465016900101d0b8040c1032480e0312007620401600c1600706014490240b0b03540080c0301c803181684030b00c000c2100c0c0c03000090401c42c7c413150011078295220b9013060b25007949802d9170000045c4001649402801e00d180a0300c411307440a1401c5080d0745a01c2c414100420400d402032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 225379712 1250 225378462 225378473
    0x90e04050309011b0f03110c01030204050d110d1a0703110c0a0b1f0f03170f07020603100806040605090d020c0f1e060f0c0106050d150b01033201050904 67
    0xe03a142c10003401d180038410340410440b90b6003090518018800100041e6100070150000700c05c0c0810b4416074103030745128a98400440032070103548545544548084544004200004038070310041102400450982c0050b0f01c2e01a00800f1030590420b0462000c0e00304990660316201d030650400240702d40c240b9010300c1040e07065035044000f6000d4036401c403240201d4002514140400d129528030840307514200c0e44c40b84032101c8041d0718801038621b0200c1a508110399070204046030080001c8081407800c000f120b4003840043d820040500409008169010811010802a00f80302d1882114081202c0c41c00c80622414910100c110509642c01110000350a80c0c5141b00e0748500c0344103454841a010300230381c074207081300f04072804680c1040c00000e9880c0741016030002003032001e04a40003481041d030703290103101c003c1005010290194a0b49588800404c015420069269805160214170101800d029542410000601072203101e1480c1c0c09242c540c8030040c03518010301d022107030005a403420b9106d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 225380962 1250 225379712 225379717
    0x111030618090f010e2407121104271a18090c04060308130812070f0c050a121403090d030c06150e0403031a100f020a0215040501090e040503 62
    0x290720341c0412000016021402c1004038841100c0d009000744800b004800015845052101000c83c000349902a607000b0361400c106064000c030442c5d40d500040c0c040e0f1031040300c0280880441d01d0300b070200402c80014810581c6c01412170442114016181000c0e8030104c0d44115420710303150100d541d4100e45a031807140c1d0380f20015910000c07002e01d1400d19a981200344c5040140441069a1040c40c0c2070001c010310074001c01801c0842503000180400985400215940c0c412044200224010170824240040c5240300f5100616200c0c0c1c1c5440d44081c0c0f250000341103161941c001c4085241851004000d2008021180ca40442d1800140d4540381341c401c00300e541070361100e401500348407101321030208002c05940104103494640c0070480f00d0741e8039102107064041e0155815000242030500305203007400360010340005228000c01d011070a1102080c1030b030301307000f01902560660280240e2000561242031348945641c2040400035074031400d0034005404100150001c6c00c00c030171424200000160300004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 225382212 1250 225380962 225380989
    0x9060806090703031d06040302030d0503010503060702031611010c0b09030a180f050d170c0c040644060103060603050609060112020f0d060207150b0d0803010b030703180302060901110306 82
    0x5c2600420310f940012600c00c2c861540001d40601c035090120200079801806107040e03d00032004d8a18940f9900c100701e030399000f0003203d000004501c82c01400010182c540d8000b10000604011240ca9103548480070f0407042110421940d400000307041e0b002590000711001101192002d10001d07500f0900310140a0030742c0c0c014140280400106241440070091051a20b007035010015941da0780400d8030715403141039501a80340500e0400c1c10100342171140107040b08071064a540102010000c00c802c010584019100700ea8159004c3c0c0d001005031042805100e020354090b80740410752a14500d842854580000c00554064000d440140205c0034403c1001071400d40490f011503075203000100207020f000340380400402040c400141c0104100440b503090412540d407280c2007180501c042c062001880b41408010301280d020001032154402240185800400c10300d00024250341918049413080f0f22800150007507030041080101c8102d00340112141000300641603801d5042502c04034607550740500703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 225383462 1250 225382212 225382247
    0xe030405090612100f0f0504050606090a1d0f0d051303030e150703080405070837050d050c0105070f050409020c010f0510060305150916050d02040906080609070303 72
    0x40208585680d602d40e070b40003402c0d50f0015104004601003980c4010200c608000000ea41048030841240080e88603040c442c035002006010141d4985041000f41c410050184581e03a0f0f9800c81d881c05c030310600313003c0848101d06800400340c80c484081c800b442d020030f12501e80d042240c10070003441c040c042034444004036945428250480030b89100040e145600c10748401c108680089503410a050b401403203280940d00540035151669140d6040c2501c0d28080b0700241103c038240b4441e03002c8126440040f180e800c250224206040720700c2d5442e1418810240c0c980d80018034003088080c1d44440038400d8139040200ca04000d0244101e250026246010718412884c81550214019102140c00e401c031140801c0280000c000c90329141b24401d4403074065004250000c0d20709400500f084000c2c0780c004803484401003010b03440f07580350340300c00d1481541c0d49140780030040305121b0403400700e03180e0016001a01460f440801c03501c0c1483c1c2c2d2280382c80001889804c1c1d40c1d2043c0c004201190300454101038501c41032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 225384712 1250 225383462 225383479
    0xf0b3708042f010f030507020607110a12031b09060206011203230406020705030606060417030706050f04022e050c0a080c0105010f0e01030503040b1e030a0615030e030405 75
    0xb801d2000502d0841c0750500c920380c280207180703091100b0b182c0d0400007880c0240c032820048a101e11048045070300880b0344801680c481c0300403d2030103004060801d18000341c00201d9520840a5603038111114004078184082a00d9005110001d07010640e503459031401417400702440c0f49040c2009540703c4040c4500305881c0c082190720b4040c90f1060441441d43c00c1e2070702000c080c2010031041440164010320640006000c0c82c0c201240da80340100320140034a900600040c20241040c1301c0f11910f20100c42c620200f440200401d000085003809401c0c031502c2d4040c50015a481c0a0050006110110145106440c010358043e0070048400100380d000149a240598444050403071441c82c00c051720300003508264006c202001e0280f030541199043e21400e880b12004690f5505205c001e200c02800010910b03041400140700e0380c081c1ca4007030100e40c0c110300844c100c00980254020007a81c004d58002c032000c0d480d400c0a0080e01085c4010f03201d4100c0d1881c080104403481d04809480b401039004a0344948102c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 225385962 1250 225384712 225384721
    0xd0302090d05010915050c0f0301180b0d0c080d08090303070305150d0501050a14060a1e030c170708120d05090304030c060206090d0c08040302060307090f0b3708 71
    0x11264041d0500d9444802045481640c0c10300702590081100103010445c10040010302c0c552072207007076418414800a103507045908200007030b104030710f407640c25400c0300760754511036030103903944403070400855010b2102d04424600b080051800d01c222b40341307031000344080c2d0790902640e0300001040b40d920400034a4009029103803898001c0000000c80ca84644c13002e1181d14690510006501050080358194400c000c1070080c00c2c090300c44484121045030f8451860300041000030441500841000641c0486101c0e0f207032283e555460141d4070f6006001d005030b503081c02c451118410000c007000780140900800382c1e12004603000140c1d03c540303488199100e498002140201c9401c00036100030310f074000804c10040b40c440f0802951040b040f20360030b4491040d04e0064801600403c0fa40c041903400030b0000e45850b00310b4090154540c00900b0300c2c030411000f50030002e0071400d006001405050648202652108003c003038551015050004511202040120380b0740030100d020702820f801d07054104050740340d4a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 225387212 1250 225385962 225385969
    0x901050f1203030a0e0f07030309030b040c0803130302030d090b0306040c0306180e060f0f010603111612020d05210405160f0f060309050705040f0605040f06090605060c0d030209 78
    0x5410121205807102106004842c501d85c1c20a850849041c0d00725403411120000856913640203100c0a00450103000051010130b0103404c11543c0705d4003d10850b859142c0d1008a40d145500805003c0d1200c403004000f8821454203200703030201c0040502e00086240d0502001c0104ea00c000390049204d20395908002140034000d03044070008021001000c0920920284a0130181c960f0004006c010702840c800641c0325402e9480d024052a14045000c0b01a802e018065009151860410b500d4840034000032021190040111503000d00c6030007650400c10700001c0207460b11035403141407000d220b0305000c100106d021000c8902e1903003158400c5030055480b2420024203100d0400c41100d642810300c0d001203081c2c03134081803110403100c43c4100e6140031543c8140441c100c841c4514010147d41100900704098507094002c400e0408594400041c280d55903400030f03040b100c40314940c2600c0c50b140e0008028855441c1300d10300081c0401da481c1031401680c2003010343c9030114820b010003419408920100c3d00c1d103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 225388462 1250 225387212 225387229
    0x6030c040c030f2306010f0c150935310e09060919031205060f0604090b0a0602010903050a14042c060a140919060e070e040207020901050f 61
    0x2201c0e65010440f0604018500d84c00741c441d20205648042d560000c251554407a40c8003508005103551080e01c600019514004c0314081c1c3d079010b01803592100070550104840901c020840340010300d00d0007850020382c0c2c4d6840d2045044a202d01c17110014081000c00d03000e20422000e43d0581d2540015120201160f5890b10840030b03080040443c800804005000f4000101c3c00d00070300e0705600b21994001e414201c08040107040f080240000c52803a03800c00d40c00071b070b5042150001c200601d003003040d201030008204181c01c181c0c8000718058035540c0c1200c01b4101510441c01600382440240308191032900c3c0580f0340e1041c10009400c0044941c02c518600007000e080c0d402400d5840c2c0c5500030058170310781820240000c1c2200007489a00038000c54003c0c6042d06841c000c80c1c100d502c0f5220310280708000c200000308001c100756900c501c4502880b40290591003410040e081e90200c1000a0a02c900000d188c11203480c07195004a204002c0000035035240c0ca0309504640d011500003440da0400da010a6090 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 225389712 1250 225388462 225388481
    0x150f180e01080a030801120c030803040f05120a180501140d0e071706130506060103020906160506090d03020a080c030c130b03151f0e0a08060103030504030b090606030c040c03 77
    0x5040050020031002c2e4041101c5603854004d6480b41c4981c1d032078102d0500302d030180400003000701c0c2c010f20042001030800c401039544940100070a04259200b80c41d500e0070704201e100e042500c200001501004280c00c0254900c0d520341201103007a80d00c0c204030000e021501d80d04c005c414940c4000c500c11a4034845600041070b1101140c05450784213a40719544a41c041001403180e84e240200b00000d01c43d640c81100d0100c01c03030b40000081003180c407044010742c000d601c0302016541261080003001c680584610301d09824920070340003882c2034034102110a06022103802c85100b0140100141d0220b075a004100a804c03000e00740312a540c03078450341e0b100705680c13080c10780900420203038900004013141e45c000610311560340c2c0800340004600d03101c20000c126490303121078040e18107031b40e0326404054030400a030011018007800d154042c60b01e4819203850104c00340d20407400214001000e20401c0010980c59802c00405001010b903802d001c40040e131030700030141c9510702030380d41d0320780301d400c050f12a42043c80d45 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 225390962 1250 225389712 225389729
    0x209030a0503190e0618011d04020319110f0406080601050d15051203090d0f030306030f060e120306030a12090b0a0c17030403020307110303040504020a08060406150f18 74
    0x40340c00f8403a02041003035000d2400070201d00c1d000941040c40c00c00034205c80031040d0301750f03108035036000a100640e010305020b001e645520243c130710390b91940e850b684001c5029451004c1803201818401d440e02054615101070722125100a0100b1030000c0d16840a5406603030050a00188517510000100d605004c2d4400c038145060030000324051211308008a0016a0390968454003220704d51881c440d41ea110b22040980c01c0404145c0001c0410224070000507024868030b808907000355a07071124850700311411030595074550f0700c00040110890810030300c0004503114495a08520f00000020b4559400c560003a003000b03051000c0c01c0040c0c1c0b0440084015146124110362100710710440180f18418120040364807240002c01120f40c2a2441d0036203101e298958011071810110340c0d24180025040003d040d090700c8180404901656180007401e40302400782d40780d070b0141c40d10204100075620340c1e43c0f1480c0085968152042d415a02080e0810103d0003800e0042d41040e100e9114045088d460f408a00b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 225392212 1250 225390962 225390967
    0x6020307030207150b010e2205060f03030a020616080f0c0306041b02010b0109080703120c05190303092f0613030b1008210405010f031829040b07030209030a0503 71
    0x70200e0540c0c030110302100e0a90f60002c0404440d024030000c1103012003075041c041480c00c0e008d016030205030000b40c0e21010113410003941c000e0503404207241d03410007043c51025030040010450b1515295600c0080365445103441307221800c3c0300c10888a120b002404041c0401c1d00000000c9154a681c1c01104603401c0e5148070f60040c0700300d104024002c20104150900195000c030000940000000302c0e04141c030741224480461400920040e20035412401c1c040742c0600411580d2a2520aa0f40c200510302f8040d880c04643c0500314a40f22088402e28000540700801e4124901c441811000b451202d045c400d8030f42541c0c031580b84c07058440a02640d44010704010164040124000c2600903101c2100c44c0302e411101c00c445921004541c122148491240c0d8000c20320080140e58031980c0c4105881aa90400040180d0f10741500b840d50071442d04195003085da401080c92190742075403101c00760307440d10b00b11904460816507220241407002605100800d5000300740d8200960b0140701d1400f40705d42c003000710380d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 225393462 1250 225392212 225392243
    0x20304031205280507020106060c02031504020a0806011805010501050a080c0a030209031212061014090d060e0105070e0d0b13020f0307031401140c0a12320601020307020d06020307030207 82
    0x143c01c04991040041d4208423000814500803691800e1442d4000c006e88100341c10010f85009500c0014400d0380d000815520020f692030041c440c8074060030485002d001012103040c074000c190785040e48403d0402c60208081d081655002003030580046410314030300e40d601c000c080704401034050402c0c02a414010140c0441c140a0740c0001800011004c94600f562aa40e460811070800d0303141300c40c0000b003095450414101c1100c40000c00390310500424441a806150300d03158211940c4403d0052280e41d036105000006400024a024110080345c484040c5101907442c83c0256074081d0400020a070590141402c554404c0c000000c0745001034215070b119070740e80c14401030400390100c20b40490f51922442c0201c001c006944648070301e40e6218180e1402400c1c0608464030180025850328450303031050034202041c00401c602c001c604070f21f00a030400380800007e40f02e081e40080e180d241998030402c4040d00689a1413203134030032590480e030011f03181d035140c1d034040c0d029101350940101030000800035071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 225394712 1250 225393462 225393541
    0x1002030d1a190807060305010308030c0901032a1709120c0309280906060c140a020910080f030301050a061d041107140f100c2105070f03020304031205 66
    0x201159400c3c01114425603a5040541c22904280809850080c0030400200301740707003002c000c0000c090185000190010a4401c1055414031507844e40c05001e20082c5605080d942f19a4407202c600c414091240d50341080d013082035403043c440d04000d10b0000c001c24901d0300c00405006880543c03801801843e107075581d0500550400660030900c6121001d07060303011840c2d030a24800c59058030f03030300e0b2900a517480710340d103505001a00007846440c0c42e110340d2221000603120800c00c540a2004820a5040315007012034060130004854841c0c5604d610500040049941c0c1001c000200ca01710700340011840c0c4c4180b03013040c038071004008180c2c0007030070300c0629010308051b603000340f00d001d025248410418a02c412050703101c0606078101005644107100f50210303000c0d5507118a90341c030942d013400ca900c0f00440d0010b8400789220440740d130307072556180c1c10400440e801000340c2c10f82c40ca4500c2c046140d03103065900a40881e62540c4240c140d02c4c0d648001400015085c0184502c2e1800d5542c00411116900c1c0c1c45c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 225395962 1250 225394712 225394759
    0x70b04060e09090a020d151d011a040510050613080d050d060504020a020705040b030102160506160f050f0d1d16060504050a0e07030207021008151002030d1a 69
    0x20075000707245240c000344860701d0101ea00b900c2c03d40d000b8003290aa009949510038014205910440c0d40d554800e10400c0080d11164400c0d4050701c001c00108818801100d402e80544c10b90842c5401181480304000388058403405640c182e4800b10780258681e5000c1c049a00b034141582c2002c03c052241132815007601e038004000d00282c40800506000050315041400f0590084094103000b5910040091003503250a0300480c86c0c00c2400740c001424030ae00d20015030801c0f0305241041d5229007240c81401142d20750b40a04031301210031824488600744088070000c01c0c9104101c8044a0148082441d560b80001a0009081c0c2001003928049682081c0a12520351500d0300555031034805480c00010841d002ea005e4500700c41c03004000c2d079502403601ea065040044008c00c01020143c0c2004801c0050b51422105035a401d480e036a041c10030304d015500444282445450580b01d0024000d040b801c4a40c00400c40b1012801e240000ca6404001e01088155194001d504c80d40681c044400c0c0d0364030b0b00e07040e00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 225397212 1250 225395962 225395987
    0x10b090105181819111315030b090106170c010207080f07030311030d0908070c0b030c0702040921050706050f010b07080f070f0c030201020606010e0a1403070b0406 72
    0x2155001640e95108101070384549800000700c1c0b1800340001035642260400401601400d803040d03500c000080c4007030a05000c001da90031608101250720864041c1050040130140c240000020030280c400c1c22001c1800d03441ba440014050300c004400140c6402c000e4118000502c0b9810f0300101d0032a042e410b25450380d05400581c1c0c01445500c0001601410004024504030034403806480510705548040b50350310f440803144c1800788410040a819042148250420366010b03103e040d803250090304e0301400c10071082d44505000305c010301c24464480c0d8000c044408455044400160143c040e18007101020486480102d84101d205601000260054014020b0320321540d0100f18a6a490b6480c85460100b07005048015000f032150f40002208540100b0740b5448166002c0d0810350b0b940d44580210382049002c98034000d48032000c00071941c0422116420080908008400c8041c1d1004101d59201034441c0b1100340c06030040b4200d440d00c3c00e0042001800da400d481a5403030303840e103002030905040c0d0380c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 225398462 1250 225397212 225397219
    0x4030c05010f0504020a120303110c0c031902101d0a0902030a14010b04060c032d030605181609081005040302070509041709010e1215010603020c06040b07050705060405010b 76
    0xa69585841c0c007244201c911130b42c4d00030014840320b0706201543d034242c141c91204600340341da40e51031000c039810580b000c2e0018102031030081c01400054001d150910202c2921107201c0e0103245981c1c401030344c8501c51040d0405035440c0980e402e224680118420b02c3d044550705400c041a5800030892030019001540720741c00b03429052180422030803c420101d4000d00c980e6855050500060201d18811080707103c41a00900d00454050300305080b007007003030303020601c0c0040c00201c08051032007840e0140282001400200c50076840e0311001d00f560740c20307004000c00f514010040c06821072000c600844c480f4001e042490708840f92085e0001c030300c800411060300c2c203a015104524001440740342070122a403290368064450f49075510ba80902500c80d40281481174140080c4880111558554414440c0002c000320300821080461f490400702c2e168042e0491002c042c0104009440b02c60005240d40d00710303a000480300c005903a5100121001c2c014204018994000d03c4244001e0102c150060182e414041303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 225399712 1250 225398462 225398471
    0x1510020c010315140d0507051005030406150501020a110406090f24180203090a0b040302061b03090c0f0d021f020127030806131b02010f0902030312040309090504030c0501 75
    0x502006a0440c5119044c1c0d400c90400106a481c1800200983c2c002d20980469480540310000500c040040d8071015001810100401051184034090118150404c0d10030402d00c3e410800000d444080b404030280221000c1d4102082a4031190b10a100424038090300300a4030101154800160194a240e4400708030100c40181111112801c004100d07036500d4039007003894444000c3d081c040c1d080100b8180c0f4901400c41150046605554028030841c0b00340d01030300882c90500200b010602e0070180c1071095000074010024801400a00c1c40004401120703484921b94400c000200c0500700250002c0d0852481e200f062860828034940000308845500240041e0500c440f80c0c019440b01e0000200940c10030004c40c0c40402d003c1d40034190008030260005c0d04210380b00039601c041ea0060741c41c00c0c11142c5403070003090343c0b1542849040282d5440020070b012602c000d400090b41d900400840403590148940800c0426008070003208c0101120002031019182905003d080e44500141c00c1d2115400d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 225400962 1250 225399712 225399731
    0xd020309180105060301031e020603010303030c1d10030218060406030903080a0b06120406021b06180312010303031805070603020a0909090213020f07021306051002150f1510020c0103 80
    0x31204001d05031140a082e05003142c2c47d50700d40d01d00548030100307844298403000c109080540c40b2a030042d4040d5000c0d890206683d05903250091141040c0d00380851000e48032816010b140d9175000102074070210505d00940c8540e605c500c4031041400510b0b03c240d01800004000403034a4150f0094500c41e0301a4440307030015507c1e40c40c0203081e50183c06800e540060300700418a401c0c821010741070341290182200500346203075030b0400018581602c0303020f0115400b020402081c03851040d1454cc0301010301000e50b00f4212000d40c584112041804020141921102c042c10151a01c802c000803e540100c1159403140d40d40c00003030000d50000b01c140d070000386443c8011588070754500840030302ea580038007015001481034560302c00039000036064220581040005d42c0160f40c03103400380c00f05c0f41c040c448009041d51500381004003030146d0050f0101036411010180d10300340014000d950780001ca000411b4040e0b5078000081c403c09514040d910f9000558a40302d04000e030740003440c600d40c1c03c020780f0104109604c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 225402212 1250 225400962 225400999
    0x11103030f1f091b020f1609020706060e0709030c15140309160e01030c05060301142b08041503090503030a0c05130e0a0c050c030a03090f1a090d0504140603180d020309 74
    0x2075070a01c00e000d140c03c1410408c10700710301d5030050841502501000902c641c032200ca40b0284201130324583c00040b030f404400c0c020700090045101c0103003840410041c1035044604040c0c81c244140c024042804404400154140014004040c50032498400c8100303d50300c904e600100f1000c20301058840d80c02040002ca00c0f030410004503416104010412066610387c0020018240394000d10940c0070440889000d001080700300c508007096200d000b80645035420709200d10254030400c14004101030800c1c0540021801c048112900800c000c100030900f0304420000f513901d403003071445454481d400d40340f001030200941c0c1e004c0c2c2d0144640385401d00c1080c800d40d100300c030140941000b4003c15001000011240750003580b000d0001c6101d40400420f84005448610303e070110728004802c1110304c030742084001c400600c895140d90490f03040c49400c29007001e40001045805181c1640238100000206000e884d05c01181400040c0a9084030310568001000039126003150038050f020303030113580551a081c1c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 225403462 1250 225402212 225402223
    0x20406060c11031f0e280204180206041e0b0703171302060f0d0e1b1801080703031b0f11150403110f12060114011103030f1f091b020f 59
    0x100d410704a0884508602d00301c400408515160841920600c60340700c00040c01e100c43c1b03046205c5103029140c0001d040380103000076120304201d6040659007440d90b03040141d44240a03202a54480b150b00703015024403100d00300700d030012a0012500c552012442800700349d80300703008040420403400480c4d030a4449018840d101914400d000358844014801e40144828440291804038074041011075082c09202c40d1908001070005c4071800044450843c85240c1060011080541c0280861031711540c5002c1490303480d0209400001d0400c102181650090f0080103806504280c004103408010340d92450b00400f280001c0d04072601400941c0501c4007501141400e481c1140e4120010181601c864030405c4000c80041d016590f0141c3c0e81b42103d1a0400d080190328042d14020144e800060004030001d841d03070b41e005225008587c4100304002c40801c01381c04041d040003202001d101020400000d01c02c501358181c0000b400035180159844030a40c004070700901410b07840c1c00742d406041e01400900d803500d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 225404712 1250 225403462 225403483
    0xc1e2203020f04091230060306051f030308040f0b090d08060d030512040c08070905060a05060c0309150405130209360403020a2001141905070807020406060c1103 71
    0x10740e0004083c0145c14012013aa62200d2915404001c0f41c05a50759004c405901954000d0b01d581e58509081c003c00c0000c0c8103c50f0042441c0000c0d2a4100340c1d43c210045500c2d01b40001410881c40c0d90100d070800c5441e0381d002c4c001c5544820502840d141c00c40340310b039a44464502401c0000c40744000304599041401c400546d094041e0f440b80d1400e0000c0c84041c1a40c400034004441010150900180300e65084c00508058854001c0200f45401c0140807c040482d00d600894440d010801131020115400021120700000c141c818070b003402845100700046000e654012500900f5218191800c00381d554010036444908440740540c0d070342c00300b119841c41501c0c210b0407480d4103001404003001200c100c16044d4070500c00c0c41201c3e0b00c8225907441c00380802c20f0541607940e000d140040380b81b1668124000040c2c030000c04248505081000710604802c5419080040600000140020901401c901140e095580140c000d000762940d880e00180040d04140d406da4180030740d0b54030440d485c0f80215801d030f0708 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 225405962 1250 225404712 225404723
    0x60c1e0507140708031908010812030a0c030f0e01020d06090b0913060905011401051f050a05070203030903010e060103020a080a0b07030f0e060705030a060e0c1e2203020f0409 77
    0x14241d281e80e034440340101007145018580702d003400004194900300010903c0f5080300144040303c2c03d003824050034039001a00300d0385564000c02941d2800b99011404e0741e038400303a000f00120700b00d888520103400030001d2113850481c070703030800c134002c46220303415001170041032034040b030800110755607440c84070440f511003000641c40200c0ca0301048560782600c00d00e012080c00f070300002525200741c0d51a242100c80c1e007858840c400002d08c004201070b02c2c01440e070303642d2006001c04d481c0c0f4051540f04000c02500c0340720700e14410300c1030210310703a010340d00c0c100142c0c0d40e81b290160003004400700049203070b5901d060911040344200e40820000c103c19401040000d07525610000c3c10300141c50703c1400380c1c0541454604600141e9481c1124219080d041043c1d60103460f5a0315520355130308100300a2803e490340c98000c034002c64011002d00010b102880c04580b14965080c143c0c50740b905a9248424291080320f01d504200ca2044460544002d50111100100c901c01c50b08141601c55140600c016180854006001c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 225407212 1250 225405962 225405967
    0x8070e0f100309030216290703020c100e0d1401110c0c060d0b220b0406081e010207140309030c01090e0f060a0f06030e060106030b210c0409060c1e05 66
    0x740350080e0000c0074500d20900603264207500c484006d055100c0d15501440c000601030703a9010402c40500d01052007900c0d40c40001d858080f29440c041d54400c041c821890084841e01400c0030000d02c28880d4240302d0704000e00c09030101030307070341024a5040c0007a03140078115441c1c0a844038003111031004650458074410003a01c640c131100c0c0104441d54000f4080e070010750b503d424055105a0301c0107001810003101054449500300ca08808030700303c400e81b07032009010304d1500c403051001c058006010084945441c21079a001d60a42ea4218064001d04800030203010201d80c0102d0707032220210140105200503001c4034410b02a017801183c001c600c034401c0c00d250110f584080352115a8801d03201e03901c40c4020301619002a6500341b90152003500342c0c00200002da4512003503440304c4040c040341e80141441e00d8184000240307100014211845240d400b01c400041003110288014180004156014024000c008950076420302e50042d014804403a1700040c103610717010307140704030810260906411507a100c90 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 225408462 1250 225407212 225407239
    0x7060504050a14030a06020d090605070e060f0d02071b080f060f011503060509010602010c09090b03030a0c0f02041b03050703060812130b03011403060106050703020a121e08070e0f 79
    0x2d8200703010449540d0107004da61706040220302680000e2400884880300001c0c14602c1d0304004017203800c0640b0080c00c00141e5a0242025903584003510040d0b411800340550f40e0002d07840e208002c3c41404401040260049541201c2c00c410300c4442c2c0803a2802000e40709080303002c11246444103412501c4c95070001001005000c40c05120104021001c02c40c03e001030001c0e1284001800c48000360300c440c0040c0e4482401014055221907240d00400c1130f00c4089c0036200201001a0300c1340038124944080111502d00c410034481e62141144059401410400c030584200301d510000c14a12094035020034146000316807443c1c8684101400caa04c07500c01b40803015a01311404910f544950016520020301007004160140760200442c003c101c401000c10050030000c0502d42000016031024003448024400200030035004501c0c0041c1c15805a19407403140d40780030003582c1003102c4544100014400c00e001942c025044041d030b6010f400b0507100c600000002c0340800c96a1070003918096000201c00b00b852 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 225409712 1250 225408462 225408479
    0x403051602030c0904060203060a1202030307121b03050d0e060403020a1506030803011202010906140405010813050a0506040c080106051518060304060b010f050304030e240c01020c07060504050a 85
    0x3100144020141c602002c24000044c6481d00c00ba5003d48090743d00000348001da1811200c2140104044d100800000800d0b40009841e800f850f000a40800492030006c098a440f41c20fa054096450740000300e030400290174010019080b200c0040d6150346000301e02c40b400340c8001070b4140300d0f41d4554010080a40c03141c3e51a192000a01550403106460750004400100c0540146000c1c00105207000e80751980c81c00010484581a88003006020b841c0c9a00d1615098441c1254107540f42805c0c101055200c403401e04100744a9004040c00c0d9010342c2810030b0810034003050190081d40602040c008c000d480303d03013060886031030f0301c201ea42c801307001c030804801020480c025242000703040103c02ea11019281c0800d0003640102d030101c0f0b82c1c580d0380414007229a00900e620690048034034246040d8507060707801902d02803410050170f11884034029600c80c0517028a00d84c85c420030704881401e80f11032a08000034040e42107a00b00d000c141c05480d1001c80d84034400c9081c0d03011248000c01a90406140441c40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 225410962 1250 225409712 225409747
    0x60512180309060a020a05070e0c03010b0304110d060c03060b03150405060d0c080d031506050304062004140f1c08030703090b10080f010504020a060522030507051305040305 76
    0x41806800709004000450b40c448028100341451384d000f51080503a54030704607040c10001d412072100b0840c600103114814503200180ca054894450070070740e07640c81d03505106191400ca5030a05502007520b00d280020801c4a4104580d17003042c5407001e20481e0303107a400510050008640c4e510300300d802803d902c0c00a2803d40c000a030072501c050901040c080c51600c401181c194541c00081055004903800130340e2544c1841071190381d41e02d0010001c070460500c1802003407844040c0c006061a034407248402d05112007010b640e01548001d045880d40c0e69650005020321412000f20144180507550310f454407410804100f200079000307001074014044003a03440081c65000500000c08150751818800c0010784840460f0340600d1002e100c1c01e0b5070034540702c42030f0b00e044190764a83d103880c0d040c50184801071b01c8512800c8291307a9581025911825134181c00c82c512282105035000314492000c00205110b80411000705545003619040c91031405000c0d00e45c01d69400741c2e4000c002070010024610392a042c80e11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 225412212 1250 225410962 225411001
    0x1e0e0610050403050609070806070804020a17011407030c020d020f030904020304081c0b040b0111070e092812180e060d150e010b01090b040b030702070b04080303040b01060512 77
    0x901c0c1c0c0c206a00ca481d01842e00104562003420b41d4040a01071043c00340c201700d40c13a40640319141c503102e10f00d03081e404103c21548a100f02c00071407102c551491903045003034103e0000002c100445c00711501e44814010041c000c030f200c0c980054040c014410344007510114124034201600c200861030103040d1401e00c4029480140203030340b8480240941c0040b191413078080010f143d00f505c4045042185481000304617405250710034180014219441d02c1c140c0d01044000440e02d0240584002c1d81d202e043e00d5003886501001070300c016461548140c2d810048000f0307600e03442c1c000d90b031300741901d01c4490080d95100c0c071180080000e404c003424200600852902c00030b500120142150341009601c0e65441241107800c90802c25064984020380c00c102d0091058500000c401d20b08442500c1c54015022140d01c00c6d03000342a6613070f40c000300141c2003034000c020300b00040000c0b070003165442c1e58813882c0c50345a400649044900d83c01202c00002c40354429030954a0303054074507143c0013003030716028a0054496000e22 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 225413462 1250 225412212 225412217
    0xc0f080d020715050f04090b090a0b0f010804140106180c05040b030c0705010b041d0d03061206020d0902060a021b040c210b06030903040305060109140714070c0b041e0e0610 76
    0x204400e00031030545e0181c001004142d9002c035800c0a10400c02c02d840d0b40081000700d0052510b031402500750740f418042041d407402820407007605e8990f4209540e090b503080c10512590742c00c0000000350b01c05121028102084c1c00d580800001c42d100004031058800c610603441d0802050001c40c052482c0070009140e8580700300000248500d010001c90b003580c0d80749038892040c01c07203c404000d080e030040c00701002d0020903140800c0a0740c103010a400030b1b0500e591010342140e0340812441c202e01f086500001106070020191030306d5001d9024020755070030103ca888100030f40a55a110300e9800c01d40101080389096440c0c00c030749000007c0e416140360301c084400f0032034203440b800c83c181c0070340f20760b002540291451005150b0303582c19418954500041031f4401783c0e101d0b03d003007011107905075909111604079082d481d21141e400d240190116080c050143c0190912040403000540d4844080082044461000c4020446680f80a21130340044c02c80c441c0440d15041200003603030b00c0c504100303240b030342d0280390 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 225414712 1250 225413462 225413467
    0x10501141915050415080613200304051e06010302010e040e19030207051207031505060324071407020d0b06030307060f0204090506060408031912090c0f080d02071505 73
    0x85000101c03002c10300780c03440089203000030240040c00612418400041e07003410052a81d09000000c40c14090760041d0b8900c1181e41d42c010188080501c1d442034004500384c1003c5501e07800d0500300705071590388800d29245000481c600c0d0140c0c550300810118100c0340c058542441009507a800d01000c2d1611100580350741c0501c3e0088080104854441c0448502a5009080840c10007044c040c042c0c804d4600004607030704c907010400002d00c4c000e2b4035506156455001050b1074840310082071501d6074004121900c048040044500c43c0a649c032018442d0200346c0d0745110b28075001b03460400328842d655001c0c1d0803143c0844040302044440e440340703403c01c0e8081c0441349048a2501c60710304403400d545040380110380000d410440b0090742e02900760030000443c0d11520b010700d409c00031a40c034032540e41603210b0361180740b51044a440c0200e003c80c0454806500034450a04140f800945a421900074440e44415640e000319038288009107014400e80182c008100140c1000f030f50b541c003590171041440401008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 225415962 1250 225414712 225414719
    0x402031515091509210c04091515030b100806061203040b1612090308030403080405072607060206010815090a0b13031e050d0e0c12070e060d02130b13020412050f0105011419 76
    0x142d105081d05031001e20401c000c012f0461600b50040000541100c40044800380180809500401d03456080303031040360a166188814a201421806150301801142402048580c100c000f200281044244208149070400902070340c1601e08000e9804098502001480003d00290040c85610b420901460440e400256520b620307101800c400c00342001098030003105040380302c6c030030000c0c00040c02040c00074122540c1042039066513132142c08820b4401240076000720f4020354050109148142d0050b480d2603141c03805859464280303501c89070840c00140b5808482c0c0d0300d6130144859461100d40d60342d40c14600760f188481c80000c1c000503080c0c840240141900000142d03900720340e22510065142c042d00c83c45290803600c0104200c005c1100b40107401041c1c1d218016a50041e07001420b075000e4100003440c03d155030100e42000102c200c02c0c20203510014001c104001c1201c0440300c034a203e03004803804008004407507401d0b62000e210b904401061100d0190540c41d00c0e0081e0a210244001c44214082d82c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 225417212 1250 225415962 225416003
    0xb0106050310170a020307080109030806010f0e1c12080c0d0e03040810060e0906060303070b13020d030302091306051e010c080a1d0402031515091509210c0409 70
    0x41d101c0da410309981c0003804e440110b0800b1f021a40c01483d00741c0080084c8103440d10080d000305001080a4102300034040c8100c005e034050b0821901229004d001440301c2e43c40c0141030808040050025070b0100100f00b003081c2e035a885103220718466001d02a005060403189001d10010382420041001540070500c800708000d00c08000d048900e590171080451075519040d42e0b200018400b03888880a90054010400c0030380b000400c40b42030617401500000c141e81d4201002c9130f22800d500c0c00a5100e11a004060181640b5401600c841e590890352351245c440c0986c841300c00c450380ca11609410080360801031400c007502c0b412145040c60103060840c0807440d07a64610403168805008007003c80c0d00440d10450b8124034403c01d041a020030307201145107090087c400d002c01030088803000c0c810300f43c000151035051000d40075100b20402c007411141d042c10542c0903120315900041c07502406420000308440b444103141301030110080c920000303000070b0448034052001900500c081643d072428a030101e10b000b10b2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 225418462 1250 225417212 225417239
    0x16020f06040e1302240f07020f0d0515071803080306040b0612040b0c160f03020c0307060203030612030a0801140a0f08030a2d0c210504030507120b0106050310 70
    0x1109681c0c003c4011600c100840303940180491400810001940010224040c045802818081000c0742c1c42c0d0780c0e24400035141c50b05502c603a6810401d5401da00d001c00400058100c22a421607070150400c2d62101da0494401c001000138468070b40c0c400c0c5040001c07403020700046400801c0544081404181240031440c55480141c25a12550540c0704020074007040811503600b208401c0013040c600b03010400b50544180b25014090038092062401904240c000c014588140c14003034160b4080301c0c0d45100c042d4072a003041f25100c2c01105224814070302c1c0803000c02222008152522004240d03400c1001c1400c1c200c000b000079030741102c483e201c0410800c0c1003590f8907004280210041d0780d00d000d8141d0050042c15001c46405c0700920440000f40300180c017082241d040312946c80d0008101d029402c3c1181100311844102d08401041c54890800c13607403000040082d03074060b0b001c03511080d039120880e00d1044440403000c2c000c0c900880040c0071051103030000f941c201d0b44c1940c0c1030f59803a80300c42403140c016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 225419712 1250 225418462 225418471
    0xc09040203100608010509040b04080c070320210a080a030207050304120302010c030902030d030e03120702010e070f0b03062101050127020c120730030f0216020f06040e 74
    0x14a5102d00402040e684a4495400341c00161203010213030419a44968415074085c00c01040e6a00114201c0a09003007040107400039034000190350007100602044507020034812840c42c1c01540b801c0b100e02c40201507122003908400f4090028100c0410f55143e110803034200d0400300302010340070402070b00410000c00c0a1b10242c05400301c1244804d0440c60f000c0d08444140001806050030300d9490b4001d40c2d808a6100050303107507401c003c150101001c841f141036110313107450b403143c440c42001031003489941580085480858034040b1b4882c3c6403512045981c45409208405a42108000040d01030404403401a038001680c0901900000c1d8103003581c1c20348909812a1007542800b204207103402e000d1907100c02452070311210441c07601e0b1842000da40c5074145e8680f16451303103400241d15009c00510b01002202038401c11000303100c101210780318009800300605120700090810002603240f20b520300c200d40800d110703050020303407490460742809580b84081c8241d540c00f4409000010782241d10141c102e00c0f5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 225420962 1250 225419712 225419731
    0x3070c0c0f090f0c0c020d12020111120f0711030a0e0d060e010f050709030218070c020a0305461b060e0a0b040e01142403061002011a01080c09040203 66
    0xc1e03180040e180d00440c4d00000503141000026240790015807031b070304414a01d094200c24000c041121800b400c0e07024011402a101f0404e1000540129420140c00c0d031070b0050044c0c203004219516400c108503102403a2070034180e081d400400c0588901401341c2024140c0d0500071f0f240800d0f0840310b88443c0d0458103008488078499440b01c0d2400d00400540c0f14181d4003004504207041e02d10b0030764003c1004e07440c0c035844c1c0910400d8404046400a40110312040d5115070080c640f0740820740341c0c50165252240709541c0d02d401c2c00007801d440b02d00080c030402152404451050651140c4030040b4020346000c1904066800c8161b0249110011b4810211000600200d0700d034010391080800c00d0102d066582d42c0070007031a500911090004020440c810f504542c01030b4008110f0942140004d004000c1c01103a540d0390300c42011040010040c04000740d44656070884401e550801e180b0002d9090300c407084154000b045400429443e2036004111203904100032070b2140742420480000306040b60300940319004c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 225422212 1250 225420962 225420971
    0x1140a1211010306150f1209050a0309080d030902151c1802150304120507210c0218070509040906060801060602061602010e0304033503062403070c0c0f09 68
    0x1c10758041c01918000c0c02016240905424248001811800c0103101c02d4100030312000000c40c001307101c0d00f180d00450b4100084e2a400182490007600c2640d0314170134800140134040498121500074850105000e4015000b000c0d4040e005001007220341c01032041300c4e20014003a0344240200e00c075201d05c3c400040c3d801d105114020b214010020a07008002c40c00c95400c070708104010001e00c0e124042100ea0a0750308103240c4482d1145003002c00207400e4100305800001141c000c40416500c00505489240250760b030310a0080510130521076114111056804120f0411902c14075045c15400300320402d01a8400140c2030303072652030b0a402c1d030742d20b40c1c03003a00141d101c0303c14410003121a1591580134103040c0020003202480700001600c9010360b20015045100000802590468000307195403008003052080440d0b0f03080400c1c1114941080d40e0ac18020b020110f0505107809410110401042901c810182181c0d284e2104a840c0c0e000c0030b030b0072603612200203800910a40c95941d590060a0052000308 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 225423462 1250 225422212 225422243
    0x60108010b030f0309101101020a0815040209030a02011d0405250807020d051c0c0201050711070e06040f06050d080a0e04110d05090106080a030216091401140a12 71
    0x60948410414007880b81c0c21042c00b15211880000c00c44141c4034003943c11103880080c0d000256a14082d01c00707001c40c203500020b01d10204540c405002841805040d030b0f482c0000d02d8610030306c01240240d000a50701a409008003034050742c09a080450012000c80c2c40110201307c0001150503528187c862040300c040340411800c045202c4560a907425001d8541b444013481c0401c00256211119074500302480070000300700381901d854440616607620300140600a41b112140028000e2504917200400a03040c05554401080c0104241003100d0440100390384545440040100401e0b0b504c1d10082d445560320b1002a150b121800303841d03501d5009064054464910040141c1075406240c3c00910440c50010004c885450a0007070346e400d101c10b4100040c0a81c0c0d0448038500600a9400404e068414001c000d0201a0b002403004425180d14000300402079461200b8001d40d503680b2a00603041e0503e81c0140050b490030000f0003109800106420400d5965100d180746072000c00d0800c0c0c40d515040041e42 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 225424712 1250 225423462 225423479
    0xc0304110316091a0d150e160303020a050c04020406091404090b010b041806030803010b03180f1f02130302060c03040315050f0f01030308181f050709081b09040206070f050601 77
    0x4a4100d40191048050441780395964404888012005075840d0b6031440ca4031070200c0c0804c003040031080554444c0e5086612810040c1d074803003030004100e9451203920000074007810b044c0252012101251584109203050421046c1800f058407070081c0c010b5950b0a891020406850b089402003024903400c2c0c0d40c80d414034505030644d4804404400030181021010400600030f01c040302c4c1150210032440307451361103501e030010120355642031200480c41004102d00318100040b0700d81800444078805407990a540803003203800d81c0a10103071520002c00500c0100094242a0001c003240010441500d203450f4407503985214410b0701da0a61845d1503500e600304040070040074012034100038500000c51003585141d80c002c00c1c250f0002e00703207912010242c02400340903174200310541c8001d20a1240700134078404007040b580249022136089000401c04000002c45d60404102115182408034650440c1c04032201404410140507008070b8020804004002c00b08000c8101c0c0d482300ba200b02d0160096500d0304204 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 225425962 1250 225424712 225424751
    0x130906080d03110f03041b030b060127060c03020f030301060801030c060309150f0b0307121a040302060126060901060608010506040f0e0703092009010e0c030411031609 74
    0x82010b140c984030400c524222454261445030300300504040d500c5d40c5a10b812003411094030a0100c4219500c0404000c2280003c1c0c1184951400e9031402503070060303110f04605003008044e102c0002c0340c200505100d032038130072440c5405650007030041f0b0780324504030b036501483c5900c00d030f1260b80016500401441004401c12515000304100c2c0740510880c40300d87c58200401c5803428509450700d036100240a6100c4142d000007480200040554072602ea5400103101400070680f421030300b003140b400c40f00e0300010441000754025501503001748040ea0a00c0c4c0801198a0380450003106c88442c00b1511403101c0081208a2240441c0e40000c00c0b094980000540301c2001a00000c0c4a034805000500400302d51030241c0084a100d034104041545a690301600141002900038290031014071511404044481c016041f03104203441c01340300307aa40c03410180c1008005458030722440d2010804200825403140202e03e0101005080e1482d41884403030300c00002480794403040720395496144840d128840000c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 225427212 1250 225425962 225425983
    0x30806030613051b0a0504062903040b010e040f0c0303020d0906030c1b0c080105100e0f040221070b040f0602010b120c151e030a0f0b032113090608 65
    0x1010340b00d0445650724240c4481e01d02c459a202e90540c6150000c1a50700d00724040300400c0c02510402c05191116482c541c42c094a0b0290801c2aa0001d40700780e00c1c0080b541142d11480d080210b0440356402c2c8098075048200150094400c00d900111810204812641c124000c52090f001481035005500c409450604603520000034546816042e00b00300d0f030420304410b600751180303400c188e280f29140b400c1e0704418200e8000084640c17802041100c8141980b0480085c0ca000050f81ca0752a80c5000c40e5074803402c02181d000b074012414084072955042c508508480c10504c050988094984900c684045500301e41d001000407006080100042a02803145a20394001580c40e1085203042414055840380325610031402400c00e810024404130a100a0b1000b208040c0540c40747d142035a2a035041c10341088c0c0710710003030502e40451410489041e22600d4100040078000d802d18021440020740c4400c500f80060400840c1000a170281480e841902c0b00a031145c28800100c45040c07107038643c0b80c2049c010b0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 225428462 1250 225427212 225427231
    0x7020a26010c0e1c060c0c031205040302030406030906090209070e0a120804060810090609021c0b0d06020f040e0903030406140112150603061e0c0c0804140315040308060306 76
    0x1c50042c01684411004150074082d6044039954000c0e1040d2003205003a8a005400ea5103052003030031040707510518500542c0e000341e407102150400b00901d001150402d40b00100940d00070001001620f0203a0000e0030194040d040010715041d860300800d8070190100c503050b0004d03130780c07044895051401d6604a4042c03d2508a1500050400d9507000b070944107600504d810701107080c00251031050040c1a01c8060401c0a1007408510395032100040139401030160400203610911100e01030002074850440d0900c4000c062002c821541d8903020001d5100c2d4220205140c420040031901c804001e138038500600b200c07001944c0e680307018103042c1e003103441e640044c40c19608808010860306610501000c1d0481d00b10701940720710300780140c04070010440b6600041845040401d40d00c42d0740c5080d40089036504586005000d20a03c502d07003100c049000c000d005000710300070300c42405103030780310300d8640c00340380025007140c031103080011000e01e00f100116030403070001d5549020000302c3c1c01c0c1070022641044001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 225429712 1250 225428462 225428471
    0x7030b120109260c0c280f050a0b0f0a0c060b03030a08041205090112022d0705070b0406170907050a030b070215070903060b13050a02090a051503010b070807020a2601 73
    0x42c11943d4030b0700d01c1e2580c031601c07480881d07080b2200001e1040c202c2c45001d064111b0051455901c565040c0201d1300c5214191103201c001000091442029084440f58480210518602001c20702c00f030341e052103140e00c16280745030740b860482e0407920304000501015406031122803043c0b40910303150140c85c0702e0302031100400c2000e01c03102d0510f036003105221121008460001d07880341d101d1200d00c0f081d00d119144100d271a1449007541c9065504142c014130341580980141ea8041d5282e81e1941c2c7c4130f201d46d1240340d000507000c048240800796015942074008041c071080d00d0384a5078580011780000c40542055841405103400c0c004102d03010050000d01115425101c10315181400c0098440c85040c8400b510035911515980420390751079500510303010031508204554100301400000941280c810340307014000c1e1420118240c50114141240d2120000d01c151940e82840c160042c541c000c15021208040c0034410803006a50707460850014110410200043c2043e454144141071141440407090342d140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 225430962 1250 225429712 225429727
    0x708030a0206040803090a02030102030c030415050606030a0c03110a050a090e06090604020a11120406020f150a0b12150a06140904030e01110312010609050307060807030b12010926 79
    0x81142c942c000d4000680989a548106100c1d0a268000300000d606510020801c02c81040a20286004601401c80d80c2040030344e00c0300250884d1810350301035a00c50000c1c030001d201d03241d440d00035022188403440c1c0414102d4078401040f0761504554401c001180000c9030701c0311410703400225030009060036400303004c0500f030a101080c2e200d10044c2c1054040d07178001a00c0e4030301d28091854006400c0380c0300c048400420607600041c1071504180035200044c004d4404000c03040c03000003118000c2c926031100441290301c42c9200c54009142d140314007074021010f180c001140c2d01c0300340f20810b40640441070b02c6940e031130a105804100d0300a60082c02200300400140111911020055944540c2c1410700c0c0c3d000c50044801a2005180c0300440e40042c800021b001c1030141d00c00c3c1000e0304a40041e05e44e80061912502055250b24060040d080040c4136040002e460911a8120b44200c2a001c1c05a6041d11100103040e82903d541c103a0a562802d035001b0f0444a8041d00e10407600c011800c42201d0781007010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 225432212 1250 225430962 225430967
    0x8070614130f11030d08010503010605010302270a03050d1706120c22020c07090c020f0a2411120115050904050a1d0601080105060d12050c070305031b0708030a 70
    0x555440180030b5034001e048030303010810108075510380040010b041310090190b141c0300400c1c0b444c0900810b806035080440000c1c1c6c550103030007518032100c641801c047c05001c0b4a100e0582c40b820369042e0517800381ca098000004070b1030a00032144600107503030b107245401c2e160820060350100050503aa004100b9179100318420303603020403000018482107408141580041c0c4018094080c408c50001c1d0f2288000380c548a200c07000500d090496400910510a00510031b60aa8459908002111035504203e01080c001203400746000c89a403905c1680170a4154440350007011512130310040e00c2205800940071000d124581d252600412000090250548480800916901890700c4940c0126210b10105414102a420441000c501070307551464100d407a0880a658520078420303419103503e40400b003111802c0c08e01050b1030858014007140b64021110034212229400000c00d2522070091001c0032000400502c01404181c0c08400303c0b5107081101c4e10001d007040c1141d48007001680c41004000b070801d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 225433462 1250 225432212 225432241
    0xb1b010c1b021311030a060512010902150a0908010504060c030b0f01090b0f0714010b090f10050913020409030816030603110607080c01090609030e1c120e0d08070614 73
    0x240e0583d202da05500755803000801401040d00007444030000402001500da41c1c2c0c5d40007600311081102c140fa00ca480c2e400001d402c8174520703840690400b114400d101c00c1a41c9a0005081d45440c0d8540aa0030760f58501515003150002d41c1c04560054031a10921ba035660b15000d071500180b0100d0301ca01c0b04510300b0b0000b8112050758420107142013270120740707811302c0147c0d14141c4404035000900008800b071240221802018141e00c154420081c40000ca41b1203d1400e22441c03107000000c03807032140a8200401c0054440b0020041c2425611003000180141c449010382c2681c0c510945038400b00c2c0c2000043c820503040030001c0e080406140c690100301103000403030742c000403141c1940d500d0780d03d2100d42006034030f0740320b155a4086a0f41c200b1482c04100002c5030b101a220340c0c000d5840c8003a0344c036800200000302c01d008d8001c0c03200242d0300c03943d000428107100c02e541c18207030740e418000034241c4100b01042459200050585140c2d4000c64039406100c005c2c01103581590784508807110130700d42651100d4815 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 225434712 1250 225433462 225433517
    0x801090c03020a2411070305060406060f06090308040605070f080c06090d020307030503010909020f060403030207060e0409122106060c060b0909150c0706060902091f02030f0c070b1b010c 82
    0x10102c4c402e030607a05c00c0b05000c44409540c109007906c0da60300d401d00b8440083d02a62061141f01c0d80340c1c910001d6000d119918a01c16a9446020316240a18100003140c00703402140040c0c6104031440746000004059800901d0000600320243c0802e24180031064148100d420446083d5001080a8070010354014200ea05440d105a80040c4001cce160001c502036041c03446590341c00c014006008000d064000402c43c0440d8980d6507214608141001030000391014060004c1075248580c0302000840e0080c404c00003050b0a5035400543d681c180b0062906440ca9030707114201040003004e10b803040c0101e900031020507000903220041c2500700403466503035030540a125002240f407582c02280000d080310007103c01064102134280074154440e0500d0b4000e42c840c41c25240300d04092008803400841d0214241081c4003681c0146041103140c0720030015590020560b000300f4023601b000031a4250000c0040d0040c50b01c2400c0d84d001ca11200408207084030003100040741440003183c103074020200e00740c1000d80070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 225435962 1250 225434712 225434717
    0xd0b03161a03090f0f030c0105130321110a05091309050309010c050c04060e060907110c01110a080703090302012616020a0c0312020d08060913020a0801090c03020a24 73
    0x100c0d40c510840134105a01c0c0d228403803060080c04411a03428000002400c0024082e2008221580340c01c1a00c10410b004048020b0210710300d040b82628410f00300040c448071b01a074840c00f00d20650001340c9075080364000d900702c40c00301d00007081c01c6206040c0000008881c1d0078400040052205544400b5035034002e1010b00c50400c06440c682d081008001c1c440181c7c803900c094414070680d6145c03090341e51024012105107021742410000191700354032031440004500c1090307018110700c486c000011540d4031071400402000c3d1261559a50001d85c00d0030040c0140c038066641c0ca0071340f6040d880014074521304504010540d98100c2500881d90181c84031498020041d1150310048915080d01681801b506100180025003039a80000502047c610940904078140d800d8a244080844003501c040070280d9000e40c00100501c00a1529040b04030000410750005000306582c41d5100d082c40e0940d455460110b414810308002041107040010028000d0f06480701c91899440445140350841e00a10384036404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 225437212 1250 225435962 225435967
    0xc0201020405150901020a1a0f072d090302030f150601020a1e020117160e060a1b06020f16022103090108180106030f020f040902030d230d0b03161a 65
    0xaa80c4c000c0102001c4154001d0f05141d08180d00c1c40b01340480ea80c100c500c27015040d04040095045846082040d00700382c03001001100340c1000c1e240381080d4651007030080b000e00c01d44100100242e0f804004000e20906030800a05c00da04800341031607494800030b804d0380d0566001c8111803000810256220002c500d402842f03202a4006000489500341124485105000840d0074080d854407134105080403d039040d103540d80d540c0300d140c01b40600c034810206200c001800000100400b03071900c1040c4004a4080c07031015041c105245548185580500d600e140d59203201a4010700b14200813100004032046610b907058480342010710f0300d8981c4030b4031003d00e040003009030005401c0302012002442e10003c203402082043d03140d107041c1c50030410080307003a40305a5400f03032050a04e142c41c1c024040c1c00d0741d0140140100c10503401050790401d60b01200d41c0c1c450324840342e182c0070090390b01015004180700e600020071007501c050103260521800c980e0001d041c81070110140002d000c3c04030680d00c0d007003140b5503199 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 225438462 1250 225437212 225437227
    0xa0302030d030e0a080f030f012312010209040c0f0f02070e06061c0c030207140604020303251e06150602071a0c03041202031207030c06020912060f0106030c020102040515 75
    0x1c0c00c04e010a80c0041070b0300c4020507045a051104409144540140f038501039841e41c980501c03005481c00c6422001c8002914185046507007010a8485c00000c020800507052000b4000040c0545070390410f502e0000b076400070201281e5a21100c10101e20307155001500d00b017400c001758400744404c0248100d00450002549018600c40100702d1540700000000c20070004c0080d01008029600454003035804550b4501800c105410120f00030380036650080007540340440220100050724414003004a0690003070b042c40c1c000c602c03800f800c85c620100307403005954000e0542c07425008654007806801079540f00340e0401c0c400160001818400d03502c1003041d0100402e0a02c5420503d0f10580d2f51044060102040000381c2c0d8440c903c406104620072011380b10400ca0041052030a4024450050001650034650b400401c105900800c4654005018981800d80c8030700c0700c0d454000141c815480104440b070042203110350620440108520a200070b601d000d01d0040000c8003405040c0c005401301c0d80c0003803000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 225439712 1250 225438462 225438491
    0x1205060d0f02010e09070305060a1d04240c020106091413030806060c1c1b0825051507030509070f09020c031204030c02040b0402311a07110a0302030d03 67
    0x4c261800d4001c29411041c940741070018050302096466500481d035150300820501045130900000c000c4200c616251517031107803504500554000d03140c0b00c42401c0e004074000c0c034804030300030108408802d03000030401c1072600c0d800504554004003040f462505004c14170a6044005a048a440e034152170108001d44600c4005240381c8681c81c0c5010181c41525041e00000110f5100b6411b20703d141e884652010038003550041c50012549001000c640040002d40302c942d112a12280e8a00c80c004540d410031145956aa898034149540340320801c21507104100a031941401003a80c0310107614090030304149043d290307060729281e9028241c401c03500483d428002c1d450070801e0b0b8290780c158058994150030681006050940e00c030030140d0142d070500344000c000f802c1c5402242c5694680100b10501030300403120004840340801e0741d00c030502c10166000500e070310060480c040c00e14074080700d1a0b502e03012446c2040c0742038920750100340940310100c0304001580d0041101d5a200c034150801142c0715807040c514 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 225440962 1250 225439712 225439727
    0x909020f150c012d0203010317070305310506040b0702010e0d0b0c04060215190902040b040f0b04050108060603030a23031608180c190b030c0a1205060d0f0201 70
    0x40003076540c0384c00e10a01c940c450028004010007601450180c80c0070340700082c0d0081c0d100c24000034001c2d04180c0601c600c0e042001000300002070184c85c109007001451005ca840c0700c0341e1040301d800c0d101307118210221041c8808502e0001000f0807241246442e113420240340e41d41c01614006818400c4c41c031011201c54403980902c0900603840751045000340b8107020060425041406242c0041c402c500b021543e8005180082e4050055040101112000e001001001e0151040200c0c1c00c60b4440d10b48040702d49580c056540c51000006001c91342e0ba185a0600088800507031083c441c41e403041c0203001d626200030045401004447c64414281142d030070f980e0050b90b4044500d00000c01c400010000c10060b0310402051400259684c01c14a8481c4041000b0f50b130b1154007000700507081540c05078000c2c504542100c0070f414510003a4003545603506100000c68000b101d07500c07183c440000d80d2007202507208070940c0689051010401c21070601002092019021050051508111040b21015a8000d40c1ea = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 225442212 1250 225440962 225440977
    0x61902040b0a02060708090d08010b03040201180609091103010f03080c070e010617011205062a030c0d110a0804080f0c0f0a050d0f02060a2c070509010909020f15 71
    0x1110ba450038007900096550400310b071501d0010741d040d80410302c2c140b0013140c2801038519a0303407048016401c0034161042540050000c83c184007490f00c5d44d40c5803207525000c1600400a5031542020903250130320ba40140d80321400d40c248034010800050041005c0e210402c001d0301e400002c1551500b1801c2c07441d52801d28960840e000600303455000003802c90340700d4038424110207109140d24540e41d80d0000c1401c0083c40380e400070001c0e081840000c9443c007040d60b8101d10000710140003601c030400d440041c1c40c584e000381d0301e03610b000000140c0e07013070701007244d00410200080e501e80b00752414484a0b4003e1001304050301c0200b0005002402e4661542010160742e4000c040c0340503103d41c4003000080c990b41c0c00d603400c0116101c0c0959003580d04058001c01d404003811250340c020f041e6564900840c90010302204025440b6070b91040301d04421190403005404518401e03034002c002a5040008021620105030300802d07455082101640040c0c6511122001594094a080103425001001d100c9207001d00300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 225443462 1250 225442212 225442229
    0x90d08040f0f09050402010203070b060303040519090e07060f0c020102010207021003020d060b030114091b070b01030c050316050d020109051e091e0103260f030a050603010e06190204 80
    0xa0042598144480640c085070b0085a9000b01c00d40d580e41002c00351641141d029026030402c2c021000031991280c101c40d48030400405072858a52501d00141001d501303484c2e0600040c030019400d022441051150314080c07411312008242840c94a800144081c10102c414010440400d010204590003501a20403160b8010500600e4000e0190028001d40001210088007400c00c1c100003408803081040302e050341c401000300c01c6c5816480d818045003840280605c8071000742680401c00c00100380c80503000c2c0e00c0c40754003034030190b5243d800c050b50555072603004039100b508280840040700b018408074008641e0151803091a04e502400141e4950300203600032600080110100f06c0e041044c1001070700c1c028400c0b6000d80964541c4860311099007d1401c111980c45039400050001c034103c018240d00205140340c41c02c04c0f585030300a56001540201c80c159803031140c0401031011402d0136019943d070100c010ba0080140e24801c0312440c3c0d031818003800b9008506140322072034010040c1501114060b21950 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 225444712 1250 225443462 225443467
    0x2a030212010b1c14180307050a0f02090708010605030a0f021902030406110a0c09110403050a08071419060f02090319030e091320090708010509071403010b090d08 71
    0x81522010503802a22821081004000781c0d10f515102c0d4410082021003001341031401d56164001021a070300002d441811500c4280404000a40100070002c0c00510030150300e2011070032441441101c0001070f00c00410301034014014008a0ba019060b664446040340d4003240f01c02552802000a200d50b00c8080e000c0110b680010044c82e800000400c11100c80740c0e591448041c8030903606e0b445101d9060000c1c00c00303120640411001e04140c2000f4514088513000b149056903954039a444c013940b0f00800c0780c2d10280411910305202c4c207503e50b00400903006000e08242e21000307112410140401500502e002c0e51040074100406d11036060714807864000c1d08443c440c1540d250702503103600d00c90004400081c3c003800302d28441d06001007024000c01c0715250000181600f55a4070801c2e0901c500140c001c641d00b0340850219a82d900e003154090321054482000c2e550510b018045c203001d0090000d014041c0030b4208506a01c59541140e0448001c044629228210000000c218080b0480041c0191401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 225445962 1250 225444712 225444719
    0xc040510051e010210060803041406040807031b170309010f090f080a12030e1b06090d08030703051617060d0803010308030a0e07050906060a03090b0114132a03021201 73
    0x15984240742d068402d03003c079200140ca1301c541c54152070213402086950780040c40704201c40341c1d00c0703803a1181c071400041c01c29040c55100c114051906856610070756101122030810600700b042d1640403000b0f00140001240100d1741441282c1d9244241ca0500741000f840e0080500c200b40318064070000b40c601c02c3d1000c000c4950703842c003c69940c807142d0004e4070600b8400100c1c840c0700340244030b6030310711380c01320310143c601c80b0807403070141e3710310201d0b00842c83d046002080545036a588420f14045920720400c401a183d0405003401400c03114024022080285036000b00147c1a4100b51b441f1203035080c40c3c1528000356254800700300701e1a50424001c14481000c4004410024104080e62080241030001c0080c15050b81810b80d4401d030b24801c154021102d80003042d841c0c02c00701b00421031030441d801c0200f0400302c15640c0c110b0f0101d00364041040680c2d20005106645000188001c0a051201c07050110010483c48202803800521400070700d45100403d81c00c4860207501614005c41c1850a0080303150394 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 225447212 1250 225445962 225445999
    0x2091e0a03020a06111c230c0304030f060e0c010909020703020f01050a0507020f0316060e01090219060201140c040b03041b030c05090c0c06060f010203043f050c04051005 75
    0x2ca42844d580d010701c0040e0186d15011070443d5003050b5042d9125040703140000d00360b40750824130310b50710185a002000307000724050781080108002c601c41c8070304c5006094103060000c101d443d8070100c0c044903004680190b502e40e9100e0200d0040c0d0752910030069880d52549410b0b0700c1c08159100641c800c1d401c0c6400c02040d4213840d8803a40c8180196020788296102e0000559100c1c071460490000a540042e1001c008c142d181e4041a0407900e1a0000582c043c1282c0005004031010300010311044a40c034000c2c42580d84c28024840c29103110000009142000d010007482402107015002d4401d601200107070510000c486144084019440e0030142e90341c1700d0404840c41c449501580c0e0140c461035002c034030711408000031915900301c0352018000503107600c0e04124502440c6048541144401d22010552031503801d100c56152022081c5085548040d04803400070340d44440c000e00c9035042204c803a10100300b02007034a17051140c048900007074554507c8050070101c1110f40000b0740002c00651502c10210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 225448462 1250 225447212 225447227
    0xf0106180b0f221401050f16390504060302061b0a080304050a0c0b0f030a0c020708100f0b030f0d0f09030b0708061206010807060503040203010237020102091e0a03020a06 75
    0x70001c1c4131380000c05079004010358040c881d00a42ca9001c82c07007040700c40d2050200d43c204055407441500240c035030000b500a120007080c08468804030410180c10520188450062004007c0c9000d55043c00550b10356000242c09000e11500307000307841a42070144800c8030051002d0319440e40d204074a02c0d16800c003400c042c2c1d0b649082c80c00441e8101d414400c08a11900383d0740c1501c01c003100e400c150502c3c1d6a100441c1601402c5000c8070340081d440f4903180411950410711034005251020500083e0300101e2a602c40240d5180c140d0641c007070f40041e41c2060b44000c1c0440e90f00001013803804c1c5200c20035100360341203071198041d030300c0a40700b207420348140400aa4000b512a0042100f203408400146140c4036254943c1401c1c03003a6801c96000304c80c1000018010005075601600040005040c0070803410340c64a000080000341813100484101c1902d000c8540d12500c5641c5900d1008608002511003c90b0b0128854072594094034056000c400c2685d9800c50003c01844d406400f0400031740d03a801014080d0b2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 225449712 1250 225448462 225448469
    0x61809050910140f0c07021f02010f1113030b0c0f0a09180b09130206070204020309061b0a0801060c060f09030e0109080c0a03020105130e0f0f0106180b0f22 69
    0x10750a0161040c011900d488002c4c3c001d80010268491a0f152032046803003c1e0b0101c602260002548035850a0101c606040c1810440442d0000704911416004c10001c035a505c0700007000803881441500200c0000040318800c1d2640280400b026480c0c090803d070480c06007a0020b495014001600e501c4103500caa00501100c0410283c100038410400064041d00c0074050407941001203240003a201203540d03c0754184c0c190000e46054030300314054000c142a60300444113506c0b80e1703022000740328030040c4500850b644159080b60300b505051600030006c1a43c80184100c104104644100c0c9040c00340c56840f165100000110401051a040c0f41c0a004004821100c1c4e02044800100140e0781001041901802c0b000070044103155080d07500642e4031340c01c18070f040760340e211001c01e0200e001445118014080c500c52038400b059443c00e03130a00325582e00e05802c2641000b13046200220304201c548803003030984000744500f40e200c01c0204880703001c44c050702c0300114400040c21040128080d01f46080c1d0300741c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 225450962 1250 225449712 225449743
    0x180609060a0e0a0c0303120b0306070c0b0c04030b0916050102060f01120c050d06150504020708090d080c030f0c0d05040819020102030c03042c16110a06021207020d02160618090509 79
    0x58091002c252b1207040842e40000824103006004c00041e40ba01c210550040080c1e41d0741d400d241d22600d030004a810121000c5190358010603510038204503100b01c882c000d2000b407004240a10b81104014000c0106100340c544034510594034204007d4002d01f02c001502000d0044007005034a410000e01921000b11050003001d000000814542024002c641e400d07a048030490340b42c205080140110218250b0060350803c0040c000f800c0f10704010300042c54100040e90703a03251910484801c103420100c0c62640300c400d1100030002084058008902d01211140031400d0700c0203843c0c2400140e003076100b09458490710703001c00540484c040d00b008030254150000480c1c220704151840c00604d00c2208140c9038864504680030148541e21300c02c142d1a030b0102082001c3c0c810b003c0a503940c440590304503c425107917030180c800c10006225410408002c5003c141d100802900048040700c843d0b0b50103c3c09a001040704032640c0500100c011600d05005000c103041c204a079241ca859421f4070760f1f030200303114040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 225452212 1250 225450962 225450971
    0x1020a030b060309071a070c180b04050f012903130311010606081902070b010909140a26040e0c12010b18040e0a0b040b180609060a0e0a0c030312 64
    0x12402d0590940f0f00c5401c5620052001d54100030715400070065007001401c0b0020204407920008a90100074001000ba01c818003100560b014200e006035442c60200034042e13440c1c03200f00a80304001703001c40b80c1112038521006002800d06440b00010300d6103615104103488002040c408280c0080312080041c034042d0303403901050004501004d003612418800c2000145604001c15041c11085100140f01d42c840c20b401450300305183d6071541002026400703000e00542d9904403206003c500c6560a645003155806030090000c15590842203d040c0702029028100c80301c034654110820301c049401500c0300e52844000c0380f6003c1141c0c4d00300da010603205154490036000000d010f85035002920001e41b080e4004001c0412a5424040105401c00d01034000c0d205200c1020301003010b002500740558068403c402e00f5180031080402d10b400d0301e44400d40d0950002082155440b401f190098122541640109080300ba410010340b4242a401c0090602c0c10921400820544c10a1040b180c84600040520 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 225453462 1250 225452212 225452231
    0xb040b0409050f0f01021804050606070f081c09020901061d04050903090415030314030709030b090c12070e2a030f090d03050601020a14100614131107120e060c01020a03 74
    0x7801d07801071007401751f141c042c4030503104013510303148c1c1069901882c0904258100320071900c81003180c182011040d00c421070300103164240d00000e144141c1c0200c107062014080c0c01a6903001c1440050140f040104014062840032012007042c00000c40c0984014014811824840801c5884c0d0707010a0704244070381d2801880c01c48001c800452801202c0d096205c11281c480540f404510300d0340010012000c0054040c800320010f1204801580600081001000503403120400d001700d904036224070789699406a64100b000c541880a101c7c0e00c07004800c0c0e0030314103c8000070010318580300300300e1090b090000441080024808000c90701d106046c02c0d01110f2584040307100c2503045542c19a00c3c00d0050b08261070002c089014007181c0c4404007071a070205d800c0d800c9099840801c0b101950001004014003891000d400c0c41d020f0811048480c3c40748042003131600000d9007040c5807060142c000c2c05051000c0d0a0b512203801510607020010000d4500b5030740d603d441203450300039440344558a0100e0701d0041c044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 225454712 1250 225453462 225453493
    0xf120105190b0a060f210e0705040501180b030a0c0816050f0f040207020a0f1712040f03260301060504031b0819020f1f020f011107060b040b0409050f 66
    0x1005514003410f020a05402c10004454415100c07090a0038801c04c00c489480120190504002c01e90702d41c84c00040041116003a941058a954007203031080741414010305c14044040e541c0b0640304070704500041d0051800c40401c1c10489004805080181001400034001d04041888805201d031850b4230200c43c1d07150001c0011450501c5602d0350040c2003e80040c105041c2980104070042c0028008024166110040c3c2e540705040d0f000801c54040d904000146550104560300c854600703d04c055003002d0400a11804100c40361002401483c05900380040b132814242c1a6103000c03100400c483d540c0e40c2c4600300601241e00600c012181c01140311300e480354200918003000f042d516040c0c003811a44140352484003400512402c26644400f40101511035940c81d8141082c4207116045098200c40d5101406030034244804620f8032030341d0500024a61729250802242d208039400713500040d10003125030225004100e9811100c0e00a483d100004090000020340504041d440000f11707540031003482c400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 225455962 1250 225454712 225454721
    0x80705030a020609071a0a0c02120f1009020d080a14030c280806060d0b0301050108160608011202300c090c090d14011b0c11010804031d0f12010519 65
    0x400c6e00345500349910b540c038250044010100d000311880d0030020200580c00050b645a511000e446407a0302141014080f050140b024094000b14401e040099400b03030303000300326407103003007200180050000030700140b0b00c41c068070740055a81c0f001d09401c0d88a01d8401406821035001c5440384407803803a484460b081c129505102c503a2144c1c103036915000ca80d00c0b2a41172062680004040d00e5030700c0c5e16444101d42e1900c09100c2c45000340412001002c0e03200302c145503003c1c10f61072504a07034204050f000c01030080a804a8039514119410341d100010341d108002c4a020f5020610b001a040700300901401c081400700040601089000311403541c0b0a440e0782d890326005205a140d100d0304110306070918030106032038020398640030301c4503400800c0c034040340d0800f00219090303200600d000c20300c2c214a085c00c0c0100a121818140000c0c2402e8601d8140340c0c4015001030240708520445102000022016480358030601c20410700c080e1401c0e020265a2161034041c0c00101c0721208281e0086903580c0460689014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 225457212 1250 225455962 225455969
    0x60403030629120c1b100509011b08100e09060925060c0602070209010e010f05061602042c030424090509070c0206070f02100f1b03020a080705030a02060907 69
    0x180103103400c0c1c58400c0781c00f014400a01664000f0000c0c030400b0f51540e080d40540000491103400b409008400344007017030403180040c0c59200280c1c50300305903540c00d6802035100424074149007005542e40d5100001e0211205c11a00903210264800040c0064040002540b034080d50b2405e065aa40025001104101e06450300030f0310580e0519100801059005007041001f080c0140340152410382d298002c01c5495000b07900c608240228840100280c42ca100c8540000d130404680c0c4901d404c50f050300040200381c121070003078403c0340e039108a03009003400004460078503d82c002000b408000c1e6010075a4881c2c10500c6503101e004c010356491854140d819840c541655a207455400301c050400d0b0600403204e00051900f403d003c0030100c8240035a0300ca10207009650f00c1a100ba03586a040c0d031052051070012103c02d0300034490000034050050f500f00b1030f940100300c1400c011462038403840c02c0032450000824005090208006074600c2480f40101c002e1404440a4085407800c2c1c50f0148025500c4110f4032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 225458462 1250 225457212 225457289
    0x130608240610020d0e030715080702150402030726010906021314030a03080403021524010c0c0e06220c0207080319050a120c03050103020a05010c0c12140604030306 72
    0x8081c01300c040c0c01004260140c070409011200c02d1030b19802c1c01070300001c07248801030104c1c075918200110994100070b864400f030444540e8051a00742503000c640d481c01b0070301403468002c40c038041e00d041c140c00c2100c6c41584401c124000340100c80c83c504001d0b0003980540c4e82006031307040c485008500b0941c11401480c140d00d0150080200a004c3c0d2001c03140054094030850450082400164000d040c010310b0f40d01502c581c0e003060140c200c41070b04075240000e24180f0b65041c400c42000110102c2d912070031010407a1401044104a6550540050000d03400f405201000200c08002405980426405000300b10001d400300c64849885039103030365890040c815219841d64040c070707001d080d05116401428508445081143c0c80303041c2c2c1c2c2c00080036240380051010004e540c41c0c00400c01c2d881c041c03070488020102801c01d0556500943c83e6110401014000c3d50500510040641d040006c1c0c0c40801c022103c0d8101640c0b01d609162900402404d06442400340881400340051040d4034503034207544103001c404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 225459712 1250 225458462 225458473
    0xa030203030d0b03210a0906080702370f0b0601050705030d0c0e06361008040503040329070503060f040b0d020301050a0c0311090a030213060824061002 67
    0x100c8072024000083c029a050f0040d00c1200481d10600b0340508100100c810107540c941101d2500249035642540c0110708200410051207140341d000b048413242c08594030071000c3c140b14080307425200c01002c541000b2280001c0055031080c8400609c03c2c3c00780c503204202440b00380d00d4900c0115500c3c010035101038501d070001c02c02003240001e1030b40315404201d443d04154400000c201d001034007a810044010401603d600c680c806003449019840c0b00c1c6440003d85400100c008401113410a000c0005040502200b00c0228042c0302c010420744000350746c401d4011050380c21110b81c643e1103011744a080e814100404001c951034900400503680308001c050070080b21030b10340504020242841c03441caa50441c2c5000f4200026847c03c1c014a840303181042c030003280e0700091000080031542088804898a20240000881aa00c0d0034180341241d404854000d1141080c1c02c41100400343c0340e005200a03c20f02200086016895032441e000b8003a0324560039032036a5801c244554540801541c40058121 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 225460962 1250 225459712 225459727
    0x24050325170a0203060c090127150e19050108070201020301060c06020304081e04140105093a03080f130b01150c08040305070519030809090c0918040b060a03020303 72
    0x200d803040880c00314031a0482e8280d1103581c0100e400c090381650049601c80000440c0032080d42c200459107080e80b40107441815409031454040e2590742d55004032542000d0700f02118466522618180100b910f0082440300d00103001d000c1400c01070000e220761404030700c2c5000040d00460040c401d9034102c4040c0e0701e490035407044e6580c8400083d400144110390b881d1003030090fa00101e146200901e451200200d105503120b04041d81400f070414000000e90411404100c8100c050302c8403034004002e040c490184003440000c41d000d10704290400c00384900d030355003080c034814241507100c00b005008440710315147c080350302c445e02010402c007000030015005204420040001101415060b040d040192400000b0b004290b5241c1d4491345c0581e00c00c0d1030340d52000740180705903d0845444d868040c45c1d003200b0450186182e84e071640308d01a2011079445200284000349000105800300d0b040144000d001e0800e00351485400c110030344080e00d00741c500002c90f00000c0c94a00784040700c181501c0d0028011418501c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 225462212 1250 225460962 225460979
    0xe0903160327080c030102090d020f03010b190f12081821010609050109020c0a060b03070509070f02010c110a02040f020c01021c110a0e0108060424050325 68
    0x5002801c808005400500b011a0302030710030505007501c419007480007880c3c81c012040f443d2040c1d01d0f00c482d109034410003840d007450380c1d12685108915415120410308030b0408002034010b0050341c01d4960004014980755015000c80710709001501d0244812a0000d44c032004800b030740d031021000040041030100a400c21283c0c80b43c900c1014003034014501101c018200140174100100c442c81044540c0d101c040600444106000712400343c0342c40340c011400c211601c50032a40c4c5070b0040e40d001c0c05055440800e000d481d2010300100c0040d02c00030f0300000701400d00b07030381c01881c000c3c0c4007000d807005520f8a181050324910038200759081e6100c0c10014080c02c072194003013000030030030400c960304465420411034101d40c00a00103448080c00c80002c5c60100080100710000340e178810141a03c0380708042000b89215030b081504041586001e1030b2a003203964640d008138008084e00c034020215280b90300b22411140503030802e00416208160180d4115425900110050500c88400c84011546000c4c06000c1c100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 225463462 1250 225462212 225462247
    0xd02060f0c0d150906050901150c0b073e0a030504140126040c0611070b030606271503090607030905071208040e010b030f060613030b0108060604060e0903 68
    0x40c07160b0001a100c0310140440a0280c4a9121000309500c40b0b07003c026038078107001d020b80140594002c06404402003a001850104040c400810400c03006000c160101d1094691440a09400030130101d90074140000207002e06498403510b016a403401c0c0664000c1e4008a00f00052503803644030103003081c0c01d00c0d0300b0318046d01c69403502904001e5200100d828514206990442c20b04a40414030440d06040c140b458481c02e480d000350302441b12951660450110000b280000c0301c441b00366558482d107414000038480c0c460701810803113400720f4014001f0600c05062000c05c0b4500c040b42d03a83c5210001c42001c4501380400c6036a1a00d13078021000061819010f0b400c00c100461082d07064501c0780f0713280c0d40a00323001042d81d0f40c2030f9142c00000c1428050405144952030160510481d40ca0030351601084ca0113503410002c08c081c0c000ca8000c100000100c1059540344050b40c0d00c00d468811641e111001c442da980402c84000384640d0400c8000034403d20206041405070100324042c42c035228070b07459400780c0030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 225464712 1250 225463462 225463477
    0x1021801080a14010909030816020c0105070f06020c010b0405090109020a1a09060406080a0501090204082a03101418070605161202060a060f12030311040b03010e04050d02060f0c 78
    0x5a80790010f4030300209000c48818060019450b00045155060400400e06a070043c45070f1614500c0308103000107590005070703000d0000024a00665034101a10b40b00e949003061070001040240089403c010b102010b401410400f101981c2c20090f0344c0d14140c12a0a80c1da91000180d004032416005100325031a100070f2208146658404c18a05507100e03000c0b420a9101c1e90191000460400500500034244d010f054010b12031035209500341410302118a0721603886c0000c8500c20780039803540b240301c46451b0b000031035221801000d5031481000726000c04058034180000403105440c020005440d0030801c074115080491500060a110b41080c40070313102980048050100d12180c2034000002881405040038503800d10ba02401803420320400c0c00c004e9032700c5500300c0f4095400502d01403010541c0390102c03900503a014a400304038100781d00410551440b540d00704040c20a00040003103080c0c6298041c80b030080e031081086460a90340038a00704d03203030a800c0c1e41b01c00854440c28046104e10301c84c40007502d0607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 225465962 1250 225464712 225464731
    0xe0105150f0d17070b0f010e0106030b0d0c08010c02010b0a080a0f03110118030219050c100302070204020f1215030303070c140f10110906160804080615120102180108 73
    0x1489982c2d20781d02115411840861441d280006030b4004001041d240c91b80c010081c10703031501b4554142903640b01d03e040140501c5003015500ca1030b05815903a0107072000b040b241c02440d031000403901c036800c850282c0f152040440266081c511b40303101c10300707101c1104003c17110142d000e000840d00c07503620075000200c5504250f04105044c2c4044004810a2140c090504076100300e494100b0900d01d00a0305202c4180142d0160554407003501000c9100440c11555881048894400d142100e2406030002d003d2038902940092001c10200541c039400e500918402d0041e4892000e25500c00003511102c0b415071480a070980c009102041c1300a0184000800030352003003005901d03035403084d50728030b00e403107400949041030340d00064242885c070101e0301c52501a010905401807802c042e9a012501a01c500c159105048030180d841900f84040c10055902400e410030613504a4200401e4550004a942da1428030a01c00d8001415a03000c4c14800c449da10300d01d8225600010310084010368507d24001d06c1001c0e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 225467212 1250 225465962 225465979
    0x90b0607050705100504030b0f0411040c080402040b030a06050f091612060f02040b0711011107050f0904030c050d020c0a0e01122406030f1406040201080a020c0106050a06120e0105150f 81
    0x1480802818401c0c1909c800d040803500d01410606148030300380103014042c0f440c1c06a450304030740d80310030241c0c0d0040c0c050b100415a83d00b6400070918011584902602c130520340424010031510058244c1e0207858a401102d050168505400a01d0b200034410404030300840500f00000440035080006504046200141171580d248580003d5500034403040b80c0c600300b0700e10310390007a40c0c0100c4840240e5a04000038400c0906200104440c55801d2644901c500e00480c0040d0801d8030901d42e03a0b035815482010b55645806110020390741e40c0c0e40d807441500c034646621006c60085500400075048078542e03100031b0320980d40d43c0c4806201407884e0700d000e4060980008956410b6440c4d0007040c0007140721b000252a40c170b525041c03102040000b2a03c411040c1c0084040c880982c4c1c2c8210041e400240c6418010f0784d402003280172900520441d408560803a00380100018101d40014a49010110500c02030204d9603c0d0242c0e5400c0328421a90800880c08080c0c4060352400c00c0030301c0d03203003100e07004c0c000c0d88 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 225468462 1250 225467212 225467219
    0x4180e120a09210f03050a0201050703050c0a120f020703090e010b03070f03050403020f030313031b0b01030b10050319060c030501080d14070204060b1c05090d0e030a0c0b04090b0607050705100504 86
    0xc4044490510a0300801c90007d000c03038103242e0910a01c0c5e440f180619080025007417591620717510f4070500400004006502911140f0039010b07a100c0341e00039140c2da00c219901c800924024181010038419100751042c15400043c85008040c2145d00c070b0521640c0310112040c21010070340050402500a074110302c641110245e2a8904200450042841248050488605140041c0352240405080c07041650b45502100064401d40b141815640e100306050025500c013a5600120b01607544002e81c180b14074200941c0030310395840003502a0380650000d012100452074142c040c0da600384290105a8005c1c459500414807460014170440021455207150001e550006020760340f0340e1300880b229640004070f11500700c680d1400c1d444d00008240f000d203c9841d00c0d00125445410034000c0c131040c003490b040d50405a0750240b02810907580e0101c0c030460307920f031a9007a8626580084c0501c4050341d1030283c070301c6214a03080c400c0e501290350010041410fa07080c03400b8031000c24802c15912007031003420720010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 225469712 1250 225468462 225468473
    0xf0e04050705040f141c020117010b041403010b1f030905030408100c080c091e03150403180807090f02040512010c09140d1704180e120a0921 62
    0x6070188565554054685060044003886200d803a880042904441c0303611305c909071107441c1c06508048114110882e00100c40c0010384081c007171100c040c1010910080003107541d0500c240a401a507054000503243c030303450030341414200c40fa2050199031103d00001e154041041c544c0d42d00604050314640071400003c0c0303071380321840d64000360400030013074101c0d200084605d01d292003449140d03031051908042d2400d1074240300134107205869002d8050807488540941d41084543c4ca40f480765405411190390481080044c0c1402c0003e070317800c400103880030322090321426540001c81d00340c0342c0a070040d2088501e00382d8254010190900c00075042d40c0c092100040c19643e0207134100503501920000309040386100e400416601c03803900005600550389885840c030f5150444800e00d42a4010034a40303010368089203074003041c0160b602552648803c403050040312503c0382c011000310340f10701c021140000c030501e070780c0400c900070f06840070005899201d007080302401422078070740c989101d14039480300320000340c85d40c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 225470962 1250 225469712 225469721
    0x2011112360f0d020a03050d020a09030b010305010c090f052b0b0c220b04050103020a2c040e010c080f04030c0804030b070e030109050c151c0501061d030d0f0e04 71
    0x1c0401d800c0030840002d6010148142069014588040e0100c1405942c0142482c011a00d036001a15030201d00c00041034000c544440140d070b0001440140366079603103442e9000c0c0c11514040c50004540420004011100ca5244025100020820107800000c1c603050402501c8081840c500c0090049080001c80d1504010701d0090540440c004c3e99405000d03100c40483d84107042440140c41c1c00082003200484160956050312824030317001d0f0752402e6050040300d40c2c0400034480c841d214129040e04500003d03020743c408443e1000e0b501440307030211900e1a0f81c01c070307030446140001080300d56000408800302424601c0d80f09100c0d0803c6c40440140b070310f070001c1903082038004554524001e8103000d0029041030019a00000882c02408103042a903102c1d0348400e0000603a5000f06483d00d074400d07043c0074003810703244610000384a030205c42c182d00600d032010300401c0c855031000c207c694507000801c68a5185c20b4880c408050700601000c018410b040b56650080c11505d4204a0340341410041c9030303600d000c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 225472212 1250 225470962 225471061
    0x20a110d0f0c2f090702030307090b1b0d0305150102030c0a0201140c06150a05030a0201020c060f0d050a0903031103040b0105060a050f0c0c0306060303040810051512010c02011112 79
    0x121014107805890a01c00180f0010700038001b50741c028000c001801d640003000f031055a00a0001e1512204d280180068411075410000c44600646c26490201985503101d01c6c4240ca880300d942155083c088010ba0b144c0c0b0681d40c080442e070700301261050140d401140e1030342c01281c40c0303118136250a405c041800c1c18200140e880c82a40c040180c40c41000e890205030b282e020309011005440208402c0e40084d64981450301a9400361101103500c2030b1451034442528020b00c003103103003404185884404840208060a0210080303454400b160011501480c00c3e44e1149030b202241c40696428001040503941254944a040080c2080700c45174000ea640040c05410032400300400c0702d035841c00c0405003004c1008111902030b40c010701082169110009100e441450f000c840040d540d21303800c03008160000b14401d0f29170081d050a005000152056015400081145e070003002008410150101c4500c6000e60704100c4c90244030100308143e0200000d03500100643e180f8440c030f41251020806c0078101000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 225473462 1250 225472212 225472283
    0x6160303050a1d030901080406231801020327071d0402090a0b06090d06151d06040204150807090306110c0f0f19170409020a110d0f0c 59
    0x107005058042d400b88596203000310000712203d808110b0a1641e07401180d4078281040703103984c0814240000d5500c2400b90080c191911403c0240014090480d02402d0b1380209410700210001080b000041c82600c0c02401c6101403524200a5404102070184904c0c8107a880e90080c032500040400c000481d5100a5184442c01840d03441c06004000b001d203001001c0d04012400c01010020766035458088501c00c04003142c030039004203c1da05080000303000210700680440340e400001b042c4e0a00f01d407407072700c0c0304081c40d0300c0f04403546d0f00c5d5020300060340614440d00c0c601d440044410b440741350045400c03a40c040e180345000c500c482d903280c4440059403840101c1e1782e2500b2000401c684020818001010005016801404002c8501c01071315034408408018400c030700803035407540c41080702d40d00007290f0100030040c8103030b01c0c1d980342c00f11030009500940118000c11404402c010074004046501512000b41307450310314012183c8141681d00d4070403640101e607200c1290030740e100848100c9200e0000c441202 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 225474712 1250 225473462 225473471
    0x20c120f16051806061b1c02060405060106030e030915190e01020c04290d06020c03090a050d02030709020306010908070306020c0106120b161709250305100b06160303 73
    0x1000340540e081d4180c0140f41c010289108010712511948110307500d444005000045c888010704825040590140800308025100e000007100140e001070902c0c06140201d0070744e0980e91340d408094045400c50030742c44000350828040403120b4a44144420070802040006502d4a04200d800001942900d030494011030503030103201c0c0482d40e0400052600380026501045180c42040782c8904403102c102030400220351007000c1c1c5a19403030b50f0020030b0b0080c0c0d0200f015501c03640403513542c5031260402c1c11890b000d21a1080d00140c40c0c40c000084520054014000e088a40e05040c01000079600003024581400491040040e00c01c0701001400b000714021040180c940b05403106440c2900d80692108004c810003070b40c20340203d0201c01c56180c00c0311012800025450321040c06444501941c5403035620700150900f04488000081072066010500302c04038640242c04810180c0c4200d010301003d840c07a8086600460301400542c0009031000009041505000e580c0c01c0c1d503010303226140002c030700183c0c8030f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 225475962 1250 225474712 225474719
    0xe04200907090305061b07060209010e030601060c060f0b01120509070f03030c050106091b0f1808010203092503020108060d080307020f0c0d02010804030c030905060a0201020703140703020c120f16 86
    0x40c001341e0740140782c01140d200102c9094216141d103001f8100040c00c400d034000b8560409031b010700030b00c00406a001c0c05842c01c9680d6040040e0803030072609816205203080640076400740c4a45d02c03c5542403001615802c1e460418030ba650740080c4030091456103984648207001c42c00c10f460b0a2034900070740c4a6582e074042e000311807801f6400d4409507844214428185980420321181d011451a10101203140085007409038400854581d1581c120901e50346002c0c3d200031030304150640003944200440c10031555005d510043c201180807158402c4d6104401800040c001580b080c0000768124000605009000f40c1f540c6a01c03503d9401500ea490140c1d0003400e6814400307c0a0210070a420fa003110011000c0550f600060a2080c0c0248001c040025210b42d060805005035025409080040c050320f840d6500340c0d0020f4001d40c4584000d9001c01c40f1f45c80c280502942c0340d411107460b250b142d030140120030034490910800c40a480300d40b001601aa038554100000100403503954140e040c940503402d58074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 225477212 1250 225475962 225475973
    0x90608030a12050c0f030403140d0c02010b0109050616031106150a080607050304240e0123010302030304050616060c18150f0807120504050d0305100e042009070903 72
    0x100c0310b441c01d4002c0d06040c20001103005070b9040d144200380c91807580d42d807a030b00c500e01103541c098002c0c00f40c40d100e040464000c40c55440c690180c5100030b0203030001c0006180181c010356071034104c1d201c1c060b4440c60401003c003480c007800c1007010919200b0b0031310450303171400c0043c0d081c24910200e50141600400221050b030307902e4001e074024001e0006101500040c24541c500a0a5201c0100058490381340c03605e50700d1002c1c01402c1c2700d8506203070f0010104106042c8000650190502070684079400000c40d01080c1c4000d402410039048030303402001140b0b00352a01003800003642010f05020158020210f84101003078880c01071115104541c0d8030142030710100c40b505447c00c03015811850000140500400c0583e030401b4400c00c40d20800e041204040da01d1a1045070305048a00702c48030305505040510042090000300d030b402109480c0c4040c444c556030012400c80c828a1440781d51601602d070004a40032a20240320a0f800a030b450050f408220701201c0801c481143c140e44010000740301c42c03802c009220 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 225478462 1250 225477212 225477227
    0x1c1a03101a010504060203090409231507020d0e1201060f1512020705060703050603030f071b050301090302070308072d0209150d150e0609030a02070e0f070e0a090608030a 75
    0x700f401c0c000c0c1090304051000b0342d00d010740144180030f10742d5a0090410300c11910540494a07e1004420240c040d41800e41515428110000351040c2c00640109c0c25207400841d0144a001640c0e544003c020018020042c500005991540255580d000b001c50001c00a00904002d40034040c40d44c480307002c1e030450081181c1c689403204c0591510501070040010350200385950040b8280c6004185525564002070031441541003e6202c1d400004d0b00c1c800304842112020380c084400711124000d20703583d505142c00da800010f0018016001407074240000380d11a8058001e01c0d015042c100050540c4160f0117074800d9215007035004080340e080b8030344118500707550440da10079072038008011545049000310b00b801c010004004c260032540601c00121624540c02139210a29050480f0b0060401a071465184d5224550203001806104004110410795001c528041c0c002c1520b0766525944881b400c0715203000c20304003071398880007000b000901400240100c0b0003400511010350391300c0002034405003d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 225479712 1250 225478462 225478511
    0xc0406020607260601090b030a060e0c031e09010b1008010302030c1e01030209030118060c08090102030c040e0a020c0f0102031e0118020903100606020705010908031c1a0310 76
    0x480e00030302e501d00142d806203000c44183c0c400e01c822071941c0c43e0a00141ca10351a290400444100f000c03040280c04c00b415002901110741c0d0007141c04007911544c021026510003111013800c52420030707117a844502d840280042d40210703400000074014034100006441001008800e100113040f020061003035217401c1c024818084011103c0b8600d0130401d506820800c81018032440c14150f0128505c00a92400c0d00225001c0b03d2246820100410500d030410040500d0f5030000f002803840da0006103c500144201c0c0d000e400d40004190400b07161107105850074174000c0c41c0c0440c1603000d01c0700740079001c810003842280d840b80314000b503124035010f46c15110740c004400c0f240312040c5000004100005080358104420580e401c400f50b525034000c1c0c0841c5c6004944d04c44110704030300e0840300080380c44d8003103103090a692090382e8042d8100c2c2d44038600ca55900800d1a01d40d01d140c40c00c0240b2072000c6207a80076100003103405064402c10701011001a080600c010035841c0b0381c6403120b824a0203590107913181c2000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 225480962 1250 225479712 225479717
    0x5031617030f0a0c051806090a0504090501020304060c050f18010905030109060b010e06090a1e0b0304030504180b0f0904141207060b040204030305030a1808030109020c060601030501050d0314040801050c0406020607 94
    0x100444c000c10f16003191611600b0a0042c1f2002845050b0303a142e240c4041c006e408040c1090111358845d20340103000754021a000e807250340c9001d8036542c99501c900700702c40d002580011841c5c01c08040b9510b42c800000d40c50800c44c140103a0101c009241c0d1000e018041c10a402011b000454180003400036001c3c41091100c2442003904001000c503075a211905907042c2c50010301203409901002d410700b0105001900003403c40780001c001c220070598088001d1094814848500c02400711300c00300e0130140c80b50f815a05500102c050048915814822181a8064010904924a00c201044050801000540300711a20a0000710f6600340720b0607020304004090309a4045107030603c0c60f28020141d00000d00003000503071b19810115a0240e01c035801500003608440c10f41d50340d580d030360302c400300942c4144c0107400e00e40514000940c0d00c1d8000e115003412103a003d040600715400964086817001850130b280c1c0304101c4184404103d09501b4400c05d4800c21541454540d074600300840a441d001e00103003190304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 225482212 1250 225480962 225480967
    0xc0703140918060f030114010609091503020103090f02040c090303080603060f0c030c04030804060c0209090d0806010315080105070e03100e0304030206090105070204330305031617030f0a0c05 84
    0x340e4641801c601542010b2000c40c8210b0f480d01c60004606506000380036178150b080141851080400100c20b50403504203803141c0e03960541d56a918030940d1900f10340c071412880103240420155000f0b42002c0000b5105101d4183e80c0d20203a0300203800c80c1c400328402e500154030900e05000f015009401c082d00980210000e0403586401e10001c0d0990000510b048124074010002c0b600740b41d103540644000c0d56110341165207643d101c0030000e202100d80c00c0180e1044407250702050010705d01007240030340d15400380c2da040344075070300d060064014000090480d41c260280200c00600c0c20420710815000310780326030b1914400036221701018607040228454851891601c0a000540200003040b142100c0d41500d910b038407803550000503a403038000c9402c00380d0014148081c07201d0101011b000d60500100b140b2803108112192625050f0140450000410310fa000300700d0003038007030f4008100902c1907101d507013080442c031138518101080d41c00030390b00200b07050611410300c0744203142405060354420700c500e0410b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 225483462 1250 225482212 225482227
    0x10b030a05032a2a0402090f010e010903020915010f080106080f0c070813090c0c0f0b04080702060a0e041a0f120c030d091409040b04060507030f050c070314 69
    0x586a02c00c0740c1c549081c0c625001c1ca00e941c0742035071683d035001c40381a9030f0a550405028101d80850030401400d5400b503a944200403455514240c400d80e0300e900b2000e0714040310311440c4001920b4071000c050b80b10341880342c1d6800000069603803803081407043c6040010f40810b0341010001400485c070380128001404100c030014030a060b8031481a5a01120701a10151140c4406030140018400c00b4805460801d000840c10012001c41001400316082c0c00420000703038190003030071101400d0080c4000c18100c0c0114010011072142c48089411600440f5400d00d04031040d40041c0603980315004200200b03400081c00701c1c891400c1d100e103000e02c550810400381d408440000280c8055504098240700784022082214040000c00081082d200040d086441c00705061402501c0d0001602c1012080041890b800d07007a07081c28103000d4041ca500c034151203030680f42e40da50400901002440e040c101990f5840c2c2c060803544c6ea01440740074040010f5550f5880a8a0500800d41a100038048007013400412909 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 225484712 1250 225483462 225483473
    0x18030d2d23220f020a080607090b250203190302150105100903230d0905150406140f19050d0c0201091502090301090215210103110d32010b030a 63
    0x1610078000302c01c0e6444842040c50520740c62a40c04201a4126010740c41c085146c000018445000e21001d85480040b242e5070800f1810720306c0340b4032014000c8200603080c2d200380c0c035428008466040c8001d05603440c5200030405070805884451080d00142e00000001c00e00c25202842180900001d86096a42c0d0400c0c1c000917000120600c4010441d44007070200c8800440c0c1c80d01440c005035a0142519070b103c0740100700a200040600510b40708642c612003100075441000100e40032620341d81c890000e4149109600380040d0043d42c54101603d6003000740f882000f070040d02140b0210166154591180d01420065040710000c20a201c00d5a1604119201291351058140f4428505810150f40c401c3c200010034003410300040029008421120351401401d00b0301c000d05411015002c2d071302a110710a040c2844444000e00c40a4406060303d0f00300f000380d091a101d40c1c094039008480d400f551b03001600005e142002c2c1c580ba0718490b034200070340c0c0f501007500a00030f0b50400d01d07007140200000120703070721030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 225485962 1250 225484712 225484741
    0x120c07170307050903010603081c050f0711070314010204210c03060b0a170c0f090c070204110f03090a021207061d011b0b040b18030d2d23 61
    0x12844900c401000141800e8401c1003142e5800c10050020310113581c4d2441c108403941c12115014040500c000003480000030203101c3c8600c0386100d501031142c2c07a00c4092054598080d10b0074103100758007581c48040302040c10301c042921505507650005945524088e85035480035100190381c16a142d1140201d40815486240c0c10260f03504104009005404180000c41c000b02507481032491008200d403e012000020460030000d40003a240440440c20600402c110001e0407151110b1f506418091000982040e61024100180e81c0300c00c03500c0d01c02004905407481d081141c81c2c0c181903000d10120700840c02e01400200080001000410340d640c00c00c03c3c040c210800b40c500c054007009060f10400140ea114003403419486001240400512299040103a00c41c001202c064480960480204034500c944141c02044080c1e010003850a00c0ba042854038045c5c50080d101141c20a0a400005014010010042c81c03201244a0001d024984070940e06007144880840d100350148800c100001203405820303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 225487212 1250 225485962 225485993
    0x50109150e030c10030f05090102070203030315030118050d23040b180603012315030c070203010e031b1002090f0d0c030c03080705060f15040905120708120c07 70
    0x300381c180e220420000c02d291a007403040c51a446020440340c0e01086805502c64014040c4554040c090760351100159401c0c3d109407640290903500400000f01406900c803500f14000c00c2c024004120320064200307004901300401c40548481e0004000600b915810846a284070b00f5115a0710011070301c0c1e4241020940a030344079940901c0800294a5003403c8000141d2420f000018100343d1a56140c2035002c0116030140015100d19000f40c035140d805240550b515900c00004030000f600e56514410b80585a400c1500201d0701907480340301001340080148050a00081c800e083e001d100900c010000e0302c1c2040d8002c48403481032042001a8a54548030542c640300c01080c1c542496040040c5490710022241e5440170b44051120703e404820841e12038024006640500e0868102c0e4544a00b50940a007080d03401d000c400c0101007081540d81010340100030101d00602c151110b1100048200915502030141100c410800040000c6841141e403c19a00151240c6006040540030b588103585940c1410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 225488462 1250 225487212 225487217
    0x801050a060507150c180f0308071502070c060819060e040f1a07050901080106032a05040b130801060609060f032c060402090c0c0a020d230c0a05010915 67
    0x10f04a0306100040c3c090020800c0d0000e020028058643c00040c80400f0080c19007031403003405100010080c00341c1c10307048281d94001d009036191140c5503856081120491221005058092000c2c001154060044800410943c1c80e61415850031600c064420350070502c00303064580c82c2180502c410b60b440880c0c0c60f80a5800403c1004442041c18840703a1243c80d10a0355804000043c00c2014031076000000e0420b5441c03e89030000d103642c0b68002682500e64415283c0300018000c909880160130700c0446c42c04440f0b0303a0030080e01e8661254203001c85a030245059107180b0030350b81008c11640b402442480c1c0203222501c0e003000c85034100100101100080d04d056410181c640d15809000c02ca541e851040d4903054030000911010304000301a280c030300031075040e482180348600203004840e000c030403a1113030b020a00c0a8004202142d003044010710310038605a403441c03010b0154a02c9281c5414056500e0503e0000410040c183c2404100f40d035252038225074100a81c5100410580008102592110141c1d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 225489712 1250 225488462 225488467
    0x110313090218030a030512280c0315091a0907080a050615070f03030f0614011d090123030a020109050f240c070f03080f0d09050304090614010801050a0605 68
    0x145200b090341e9500106160716000360300c1002c04064001004003c01c00f01c45000141d07a80d5095a410000d2003074080440a10074007040c0881d0001140c0d20a40e010005410000b0390500d10065100c0140b10a402122680740c0d50104100842c0144104500b0204203d524175400d103007680340107120300f41c05809103000c61744078130128146540d20300341c55488040c003202494641142d41091b403c21000c070b6a041d40420b1816200281022044c000d504c192400c103248403030540e0404004480082e5204882c41d010300c011000140c29507078100880c0c2c02010902c0c140419113040c69400e000c0b07140081c0b101e5110790310032a602c50041c3d8110002d07000329034084480352081d54420001c910005420b941050a224015070300320030401000018100f5100b04d40200e40d22542c4030441309042281c5030101504c02c1c0000c0c448a0310160100c00100840103c5100201781182180c1d1110300d140c006800030382803143c880c5002d000c4d81c149403408150750700c1c4c01d20380b68405d5454407001c11000001130080c1410411700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 225490962 1250 225489712 225489727
    0x4050102040810020307030e0a0c060c2a1502030a120504021201051f05010c1515091119170c030a0e0709060806070819090c050306040b0103031103130902 68
    0x29415100240a0b00054980c001c40002c180b400960040340c0c070402281c501820349190b01c00004140c50103581c44034499040740e0510078280c40c1e1043c252000c40c2c020401180c584144149c010003a814840b01054011010703003000052140101110b40d807100315070042c440100130a6002100300c50544840c1310001d01d90b1214000b0809080d90151056a40c0d8282010b001010307020080090300f989101d40d0340c41c1c1c8140c40780011214202c20b440c010341001c0b04a400c11204000541c45034881465040c1c0d940d109680d280344410a607620a00400c02a840116105860703000484039481061200c0c0342c110180c240c40c251005000a0240c20501c3c014000310000300725a04a5111a10038002d030b00440f1405551030001c8400b030441c1c1d001c2d17022140a0f2101281c3c0050103000f095000f4a50f90f0103c608084510340341400a004080c02500c000c050050000340a48003408a1401a40a1481c13039403030358198200071781b0304c450001070042503920030068606100d0403140c00e0f209440e003517600960345190 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 225492212 1250 225490962 225490973
    0x605070f08061003020705010507081006030b01050f0a020f070f0311060903030d09050c1e03010f0c051204020102100608010b0118060c0b0c040b0c03030a0f02090109060809010e031b0c060a1704 85
    0x2c10340b00030019827804092282180e0004201803040e42e00741d0070f10b81c1c0305489100c210160781e0320b0406c550100b8002c0c442201421180380242c140c400c601d2049a8910a01c1490a4a041c1069100e0742c0c0e1442030a00a01c1071007011141c4400c408000d5400740d18219140b00401e60b0b134804c8001c2c044c00aa43c80e100a800c01c00184011380032050005c19001c1034601d60b02c04002c505c6043d465a500c01e602e0300351400751003031403170151140010079503c985d42421201310220518450052040781107010301004004110118821140a01583d1000068000040c800034204000e0800e100c1c0040790046420000b00754454090418260b22a0151106031a6102c0208450086411030f054402c40447c0100f90004004081e502c40c0030a01810b0150441020603c000c0b407080d04002130010f0035020b4180606402174440715045050724000003154500a41da0500350b40014015a054808a07503020314806010081001c0c6500129102c40c030700418444050030001c040010721485c40d40d5100001d0134000b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 225493462 1250 225492212 225492217
    0x5090402070512030c120f1b0f0405030312070305280e030d090503030f010b280c30140a0e0303040e090703031b0c0506030901090c0308070605070f0806100302 70
    0x9043d40c446503120f08021003000d155401000e14521101c42c80c0000590703820390100c4150182c00079a402c0c4060f007414600444080e40003401c84000e40c070302000009020340301000105401007034180700c26014101240020145d581c00381000d01692a410b8401c4516450807080034000e8051501c0010700c0c440a000c000e0540c0103522200c0720b4903280c08a840300344900070004500c10350030141030002076a2502e0682003140645100d0440511501d07107030005c0c500c507001380130308d402e6040d00341282c02c0340290746c0d2122541c0100428100340c07017420003840f20102c0305a0003030032403856504008222400f0303c00003442e240980a003030310400c01c800344a0001603e0074000c89014000340104c0705114a48516042e540d0b54040c03008800050440d4100124000031369403408080ba030055000c02030340c0c500020003041d078201401d00c1c03015550f1210144000761004000a0085106424194844003075040c020120742e40108440140221004034201069101c0c0b0156401041203a48100300644190101d0003030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 225494712 1250 225493462 225493483
    0x11b020f0f1203150d080f130e1510090f030c0614040b0702010309240c0305060105090616030c0503030c040608070c03050313022206080f010203010f031401021c1b0f02071412150403020c0d0201050904020705 91
    0x14035371002000f03201c02e0003141c0040d0368054135088050848018a11498450341c442d42071455030031b001d4500107601c207800c2110501e0103001c0c50030802c0b80c180010400c0d554207c00003460b059854416030141c517014002c2e030303910901c2402e001d418071211602040c2c551191020100721454026000c004250051800d8041c19402404898807890326a1010413242d0040c080c4c080031809860001d0301da00d210f180182e480c554180c3e2141c2c255140c01740c5510350050780c944120ba00280405807552440d0502000511117244482c2c040303040c2c5d01e002000b50400164082030310050b401040103019900c1280710b40c504076948010780c1c0c403000800e0f00400303009000c1d00c0c044d440c1301c40c009100031810703000a0b00041c50356044540090380d007113034004040c0c0d1006c3e4100707807a2001d84c02c086820003c0e40b1003098410303240d68024101c480d03204090384189003040148822060300888190511080c594100320030640300d00e0035201c08400e400c6640000c4d0035800317550301080c8100d400280d50410487d0074054109130 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 225495962 1250 225494712 225494729
    0x30f050a1e0b0108070f1806080f1b09010b12070210020301060806030606180115020705030d0503191a12011b020f0f1203150d080f130e151009 63
    0x3081881e9001604009955003611006010000820981ca012402000704c40c1e14a0b818501d1518280f5090410300d00074100c821420b544403000070362124241b00c810300703900c40c000c003500e4001081c8015010b49148625940d015040c046c1c01800503c000724100c6036a0b00007035900b0515035507820022854240e0100d404010319002100000d240c03074201010901640048040e603415503120f40038040168402701000303240c0c502c0c640040140402e48504001602e00710710656030800d40300e43c00b01c3c1c0b41c28218000b040003d00008100300d024082d02034868840c18200c2e030140b29035541c0c5590310341408500c078100d6119621708095500806000d6101004170300713204280762030f0215112000f945508030400030001c0c03400f03403c690030840c001c0070403000c0809901d004443d0a50301c1d06529011400762821501c2e0b0030140d00322120001c601c201016020055150920982e10710607035800242100240d4441c800004182c01400710312400145a29013802050b1091817000d0b9a82c3d00840d0050150b90000c141c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 225497212 1250 225495962 225495983
    0xf020a1206090c09090b04030f141b0105060a0317090f10020604060c0507020d1401090c090209150703051b030904060902191427130c03050a0510030f050a 68
    0x204041c80c1c00c4002014014030b100c00710260740785165400d03280d850780700504d99400a0300280002e401101005143c844170300d4450f030044081541e00c88603901030400000310030002038071048446024051194003400558107d280c41d860341d80d8000400341d5090101d5070317250300801c0681140d210241281d18a000003082418508010b0001a44424081c2d40545520f4280f0401c007100d81e00440490300c0c1140d001e04011454003040d11041008000a0000c8500e55216090613011582c41c02d00100030b4054502c005035501080b5007003144441422800d03114030300c1c041c069240420381041c11f6400800c20003d8a10480c440c3d00159829481800060381c1e0003442c001001c00c802c1c0041e40648100c080c018903030f0030750782d80c0c1c040c05695401400f07082030324252f010090310501c48207480010307044007591402400000325105c00211500c1c00560040c030615903031034002c0401035050141c950000542c070b00c200083d081208500381c2071802c0b800083c280510500c000303010031000f0000d4817540ca400060007030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 225498462 1250 225497212 225497249
    0x60b1302070b0a150f06051c0c021e01050114090907090e100b0319030f090306051905070905010503011214060a02031009110a030c020c031c02010c0206060307030f020a 74
    0xe0744540b0680d00c000036140b0300541d04860407507a1081900303a07004051080407003032405004803020352213401b00141401417200d0101040006002e602914070164000e0b040001c246055102c4074120004144071580c1041c004010b0441c02d070311600c40300442a2000f4200307540341c500b0185030906540c00305800601e80303031025503080004203880d00c07401c01c81c403030503c01d9a80c801c04050f600c1c5200410764054606220f0034200090084480540f82e0800e82041450647da0740c0301d41c0202c2d00d046034141d002d11000c00d126581d0000910800b41c1c00390b02070600c00481e070f06001c0021702500050048814000e040202d05080c81610b200c15035140207900115105482c0c00901480079420030780311f118008613524804507a42400340100802d9200c03071006903051010707041c411030241034407040e00c0c4c003903008030100d180c0562028007448040c207200091070b90306451a803e0081c21101040b5044085401003414082c942c2d401050080849401c0804503d54a80c1c500000d1210401d0707600c40380480c0284060103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 225499712 1250 225498462 225498473
    0x180b12011406040c110d02030d0b0301060b0909130602040801020301090e01090b040b130503032e080307020108061804143f0c1c0201050c1216020f0f0105090f031204060b130207 78
    0xa00071500524410f10055080c0d00524cc05e840c528010141e50100901403a40c80d4200007c038280d02c04490b490600015a142d00c03840200e030300c40d40119082da500040180501307101d03801448060504140200000b48042d12003801d84007010b00b00070019448000841c000503400e69060a180760010166a528286070000304003000c5000305030316a80b0314071080704012154400344c030011a8402c6004d180f03840a19801115003160091110b94001a00c40d1410b011406860f2645d12030382c0709901024078080d0145065192080201d00c00740c1c0d40000c5141d050002c0e0141c1590024980004404605c80a013000380c0758440c02080c0c1c00d603103613100c1c07065044100401d01c0502c15003900183c0007045075845e9003011508512602c451601480845c4000c5140c0c00d0f001044201c5855441c030640e0102204449824209520b00940da07440341c0d107650502150703010a208555400c0c220f01e00440ca4440d41c051500e01c147c0c0010070250180c0c0e5034000e50076154850b0b241c003a401203d558030031541c984d200d103400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 225500962 1250 225499712 225499717
    0xc040f06030b01060512161e0c11100c0f1103250b04060c020d050c0405150406170604020918100f0f0614040207030306180b12011406040c110d0203 65
    0x10380d088020580001074450003941180c00318104602c8001b041daa440e0b1000200c0809a16444100080c0f000100446a95864540082d4071076590302d901156580c1040b2825070308040344140b084115032300c032001c2c6039001900303201c041c0e500034050a45042d203070a280724100c548548803505130245060092484038542000182681001d0007000ca040e1225403440c103c0c00307203004410100f07002c9a107120141c17401007407070a00144a002100e42003500000414160780042e185803100e819901007200c07403072405001d00806403903140e4956030711040c0f0165a6580d103070042c0000c2e001e41c41c0e42e004101d245405020528482c0e009100b00c4420f02003500e483d4004010303404804442d00c1c60b05002a00145c6203001c0c480448031075840020601c0d03d16410030000758401c5074220241035881c980020709180551101030902044000068040c038540280094030081c500e90075011791405441d403482c000308400300c9801a80c150350004982c4080b01f400d488980c840440c80e490740c0b2440d03525284090f4000700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 225502212 1250 225500962 225500969
    0x801120615031a0f040b0c031314010e0c011106010506130801050130030206041202072c0606120a020f04080f0a060b030c010804060b010302040b120f010e090a140c040f06 75
    0x1214415580e160390811a410245d400070f081310402c4000c5417040c0d01e0803000d0b542003400c809000d810420b5982c0d07072808200c3c10f11600301040e515078a511500001c1400f851044060a0a205000e80f84919056880c0c18050140c0d03449a0408900130036403c4291181e030340503040c00030080100e940c6074002d6a00c100003503500030f04205030300e400b146400f0a050030140300c42d40d4150010140e0f902c0361758501c031500b0b46600f05001107214102c00041c40611141d00086038990039041e4010f0a80111000d440c00c0c04010a1140110300400000c00c10a070040780007540402080401621815800d1040030035100f0741c2e000801e184141c490342c11540e040801c0ca481602d209000420104201074181030b00c031031282800a011841c00000113000c14036030381044000038814035005160545403001751190fa080a400b0900303106407042000360f1004c1d05e070350035809050790034040c408629050310711a03614803d034000100703180045048c014031100104041c546815005005102e84254071100400401d6070f4132 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 225503462 1250 225502212 225502253
    0x70501140c04030b0f07051603090828080c0c0409060e1606050f0c01060e01030308040308151f020a06050c09040b040e030702010c0309050619021c080112061503 71
    0xc0401ca200503984110740c100c1c2c0c1d101e0003800c0c0641c2d0f1070b00e440000c42c00c000c045d042441070403c0740954410040c80e08140c0d89200e034444641007810142d8140c50001d4195890300d0b84070405400c460310320348080401c043c669002074915650315a001c0030908068440c10550b80243c04e108084042000300d4020843e08031900c81142c40301072104c0001000700031035100e010301044040000800000b4000c00030080b08c400e2074004580c0c250b6032081c040b80c11400764000d81c001501d080a2000301548489403c0d0440718001c50602c20343c060800241d2000000981072581010001516074a50700078403842c40480e0f0803610400c580c1c58510240d4060b0b6200840d600c8c400c42c0f4044a103d4945802c1c030840130310107111401503007000000d41c0113640070140d2510540a0108156000179241d0b5441e0007010007000502c000c0105078010500a80340c407410b0a4848030410b01141f00701d400d03e6100380c805045900704401c4205a0a1070b003000801032024580c0074820036002c280200c14081c460102500140700344 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 225504712 1250 225503462 225503501
    0x1503091a040209061c0f0302030a0206102615011e08120405040509030d050a0b010801050d020117070908070312021509070909140f0604110406060e060d060b070501 72
    0x656034100180c04540007540320f0b29140203e140707400c0541501c2e54081544c52681170b460810344a0349070080042c44114016032001400c0000c86070706008103900420b494260000c0310b400c010109003000814010720451094544000500c6081004080c0c1661880000c240302c0b561106003102c480c07540e0101b0401d054802080c00205000d00081c0420042c510450385800c29042c40204000381101420f02442d611003481003480c3c90f96940314603802070784d98500c0003c80a08030000508480310590080744100e10020031240542d070030890707440b80d400c140c248040b4141e45042050f40c60182e590000c002c1c912030f101000c02046010106070025034403503000c6032420103205120801e00441162440c10a4101038800c1260244035040a16281d2003070a0400b0080142c0b050b061809d400040f60512581c00341d41800709000f11040800d11080050780e0602c9454200b16001d44070188000941e400340e8800102c0b8907520f50903138095005081c00501072640d52070142411406008421a500b07095040c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 225505962 1250 225504712 225504743
    0x61a04051509010308090111070b071203050103150510120804140a05060d0218090910050601080705070b1504090b0f070203091e04060b040b07140c1c0309150309 71
    0x24801121094001025082c8603801c0d961a04820780090203400d06005100c42d1501c4070020510180b00030b0300c01d003420b00d500c41065061450f17400322012058424140740030014400704d086500313104009621030340085000d49820581c0c500205c100c1d482840001d12843d004001c010f1444024030490300080888541c2262080420005108078464964403000820440b00c02d070780650051300200502c81000f85000c035845000c00e29a0004a441070159000825a018030b001ca0f4030425401207401c0c42c01c0c510600d002070014104d842450360140c07016015000040e610010040801222080070700240209901403601c410f1002d001d40752380042134448000100743c60b100100350392144034003c2107508040c3c280c81210000e0f2042180158005444810100340d1405010050000301900341d00c0958424841c10714800441034210744811070b41107110051030a41d80e0211100c983c01c0080c0030748222000c00d10301aa0089916445020300c009000c402d034240d550103034090551140101d2030b10a4240c103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 225507212 1250 225505962 225505981
    0x1101060806070f1d0d060b010305090a1511091009210f081c1103090106050103020f0301051c140c090a0507080703020309030c12030411090f0604020702010903061a0405 74
    0x100b150144001200c003241c52a60b180b1400d00710500302c2a68468040411419001c6900200c0743c803015603030710b921042c0641b41c1e0759040c498940d0185001001d48110011039a940e9038a2140203002e5062503142c042410b0721032003000480c2d8164100074401d1000d82007a00c00600042c60b41d200322912805591174020250b1a01c0d4108854541c2c0041c0c500f880c0c04095403018410307000010009840707503950340040301c0c81c1c60301e03ca82e010b0307909542e11081e160b180c81940030b42035030b0b01d07600300c0350406006001400440b84090162410750383e00f11184905400140500c5400d110b08072070240c02e482c0c1e48800309560150200d03800c91035141c10b0700c4a0100f82d442d170b0300d200309440f03050f5200f2001403510400140024441d50281da0466102d4090740c0c03a0810310b0240c40d2074000b02c41c1c0a1024414000284020060041e031501201d00041d10100c1051820003569400e030200140668001c1d900001d504046a00c12011134020310f40c0076504200351080061000f580ca0051b1000714011880d00000c50385082 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 225508462 1250 225507212 225507223
    0x6010512030706180f060603060e01090206070b0705130b04030204060e071e1407030e0301051b0412021f05030f09010501150e03070b0307020325110105070f05010c11010608 76
    0x210300314019840c065583d6203401c0101204c0394200030028000004400103210103031610442d501400020070110300b9810404216044031950880c2c0da2b01d000c10b6040161a214141c6e900c85802540c6804d01c0e0762032500a4075140f04082140e065441c910300042220100304001d4401d8174001d0f5003c120050711921402da02c080143d9403440803400400d0020100c1035440d190301848079862401c1940c03480c850b0b04502c0c2d02d8001d80002c40100d0a01110902207041c24031540d907201c03404140844540000140c0c2504070711550060359500141d50164100395103452000d2110010021391100941811120044c8a03030420b803240c283d040c8400003c55450364050141c58181c4039451000c001400c00440266225424190a16094098508001990955400a50300c10441d94000e107a4a94684065506c03c0746030070480900c640c0903a4502002c108031808620f0050000e0810aa481155051105106c2c1040c00024215800c042d001c49219074011444103c5080c2200240051174030b0309180303516071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 225509712 1250 225508462 225508489
    0x1d030a1a0c040506030a0c0210051614090a061218060f0c030504020603161b03020105040c09020c0d030f2004090605120d0806060c01060e06090f10050103020c030c070e010305060105 80
    0x113101246e41700300303150310201200081b4011246100f9540c0b60031401e44a04071070b070080452082240070003054112aa46009080c183d45842c42e140a00e400510f1407803803801058200140d09481c0030051100798070203242c0c0100c0c4081c1150780989468840003a04102e0900c9041906240071007440300d01901610f4050350380240301e68210351300c00c0c81448503001000f40200421084100803015950f800704500040c50103540081050b14103410040c03143e01b01c1d030b071144e000548100108010b0300c0020541c1d403940c0542d0700c2c1c04118241000c1e1f810340601100080700c4401000c01e210300c1c0924003014020301c1240d25440050201554540812600042d8840788120b2a00700e81c1c810159940715001c103d44c8500300504407410f1103c481121070840c0d401e60000f881d0808644113010b43c03031030210010f03a8003442c403907070341540b511303101c140c001307003003040d8401c0314103054000c51401c80980c0d0920640d103020110008941001c0d65a00c00701921130800c6c407007514203004620000c146410b261b00005140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 225510962 1250 225509712 225509719
    0x2030304050c040e0102090a080d090b0a0c0308040f080c07080106060f0806040504141507030b1c151d0a292206060e09060f0105101d030a1a0c0405 65
    0x75030500010700003d81404c9090b207030b180d5820001400360740d841050300306c0900700a50040428101c814030142c0040301c2c542003101e29040a00c5030302050b40e44103452200740c0780e0525026001c0d4542c0d00e405105030680c144002c0903028080740781c84051400080300c0003100d070604006d01c080d035581c820548912815103c45400225000c0004502d42003c4c1c0140390881d00c103007102c5217140244404103040c110404840f401000210050110041e81401001e213109411240c40c4020120310788054040800c2200c000c1401d0003100d0004074031041a4810403950341c2c104484680e07002c101c000240c555101c003400f141c40f94a050007010140c1003520140d07000001c3d04141002d503840b0035542e80c2c01403100c1190600100656600b407400a5540c0c0074200041001c292841007e00f00801010b0a041d801803030600780c0d0a802004010b199150501640d0030714403410884542141e84102c01d050200300740841c3d405118079010f5008001d080c41083e01549580620b24041c4d854005d044401e600c22071140075803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 225512212 1250 225510962 225510973
    0x809060720010e03032506020c030a12020421060b09090705010809060903040509090703020301061401120506011b030302071a07120c0903021c020306040b0a1d101d1005070e010203030405 82
    0x86c61a04040103500c220808a42000f40340744039640c0100740d901c82c481c1c0c08540d0708040b4000b0716107070308045d90101c0741d003801100307500381810032034800d51440d60390744018101d405200e005010b00240d50300211907000050201281458803401403a074035143c9110b62400201e40d000010300709003010882602800a400245207400d04e000100300480a02601404160060342070000c0160340174814080204407000c45101912503020000d0003101403190314036002418242040601d81c0e0003013590240d0075107038801075810002814210024022030340300600900711001200c1d00200903801d0a07124540e1fa9496101303501e0842e4180c1d0a44e10007400e29408200c02078818001440c1103030f40320144007061a07071340e080320515400103468102c00780e5064401d4032040c0c0c18810b0384c50a90144128400c0c56030074044040406040556a810b02001c6a0903580c1c0c0d0742040d103543d000400034108140206070201c42e80094400390346070041005445080118030038820303608040d400071054030700c100d030068050b00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 225513462 1250 225512212 225512227
    0x23090f12061f0803030411040b040e0705010f03090b040b161706091308181507020f040f0204031203050702011a092a0a05041401020102030c0f070809060720010e0303 73
    0x2a1450085038042e02c1c207124001010500d030004102551149004005507848000100c0a04c07044440325801c3c1c074041c03828110311404a01c400124030302103c40a08c1d04540d40281208101e006000142c0020002c01c90305c0140014001c0343c1c1015400362184560001030589046025038802050304813015448405500183c1030b03151100c00c0719032108404d480d0000003c250b5031001800ea0110384a5400054001c08807116820902001441d0110140e5154601086500061380b1800d55031444c0344241d0726003180c1d01000c0c1d07058068400940c4d10a8980311501210040580a1304c41150910010340c6055904811003006020300c0c1484040a071a50381e25803541400c440c1580d10b8014604001c80c050140701d040061041c008085000b03083d59100d840d1070800d0080c0c105038036002c50381030441e030040c428007003070b02401301c00c1315824a03000700380a9030b652140c50907030114040c400b65242c1c0900d01044100501007000300d505240c6096500b81001040360100555900441c5040c00350176500500545 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 225514712 1250 225513462 225513481
    0x6030311011d0d03050406140115091e210203011b080c090105031306090c060f080108030310120f0c0303081e0906190605090c19030207051b0123090f1206 68
    0x246c001e40104000300c1e8051080c0298580320f5401e80c0401c40b456074000d00e03003206c20b03403162000d0f01410310040c9000090310032414210b031040c098010503003403c14070001c405581c4030746008036201135409802480305807009420190164002c40c48003000c5040703540062010f4045504803107080c41c058560a065448000621448c901e080c44210ba034140c0d10942240420464415400102007550f00d44000d0072107800d000b041c0e82810303400075200e64010300a000310707075101f2620305041d10491074200000c6400d80c1800d0452a41c03210000c0c0c0001074984021003030540c0a0891442403c07070700c5090a000d400c0c4014125003d504444440541d04440049034030034003454450303480b2121400b03000c0345158445000401c03040040e00c1e280d0a080c000525202d01e03521002d02004001c050741400c5041c800191a41c40d10760022401c6200100b88a43e09e60300a40e02850303000a84044000d400d00c0c10004031481c540b100d51080c28001c3c07244068030140b4106160504012100c800030b400500115112030360803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 225515962 1250 225514712 225514721
    0x6010f090608040308151203090f030304030b15010c06060b0307090e0424140a050609011a0403080a120903090311150f0c0f0a03090905060906010c030f0e0406030311011d0d03 77
    0x140c011b00211038496090302e640720390313800c141041028041c66403000c40f8002c100400c410308041902030b8001f84010000300b00c1d03d24070654081c10044040c1e07955660040100e95a28502d040200346524000f800706026030038601a62103000c2c90784560f44004e07151103021418100840e40104400003450020b04000360701c18498000d414125000319003c10300c661454142501120b01d0180c0b15651410800d00d8038090203540d0051001105400f181808003403280d03218841c0d808051300d02100000c10310400c03441800414601039161078100910206460300801310420b600c405d0f41c261008552681172454074003000380c01224074a8109144c1007020704042d901c0e4101180c007c24901403004100c0040d0000c0c88400142c074802d40c1d0340d44030142400035800440310042d040d00d02840300c0da401c200a9903048103d00c04030940508200440414200c41115810311000000c2d030050f01f00100081003603006030f10704212080041c0203003c0a075134040d0480c020381c0120349070012507005411000d00c00d40070790701 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 225517212 1250 225515962 225515971
    0x61b0c0c190b0f071a04050d050a05040f0b0310090204050f010e0307030b0403080f0106030c0e0108090c06041502070503010e031c090b0c0c0f011103180a170306010f090608040308 79
    0x5081200c941d40c801030000b0341c2150907102000e02e800640c410410400710301c0360210f050241c3c0783d0400ca04154803550703034404007200381c42d051142c005114a507103070207031050b1401800c120041c60311554843c01c40301002c2d0030903a000b0090003903a00010500c24540d0003928299000941030143c003c0e42c6c5801154900b4403a22100d07054041e0440101c045040b83c5d41861059020791030345126030500209441c02c200c4140e200a00305458030f422400030544c0300256001081003464800307410344540391017500f04400710030350681c0a40005400110702d020240140c00e143c0d6250260f8005546e030794207145c2a036134600c01c582143e82040040703e001188517600d01c3c100200c0281c0005030b0440320350700c2c0c480d000c5082d12010741a04010651000d80300f410020b0722040064440244001000041c900c4000d001c0940800540460304645210410b0108200d01d51141c02105c00c200c2010801140862a03005503510340c0015010101301f5000d40c0030f07103004021601181d41d81105079440380c9040b100d07401c000c1c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 225518462 1250 225517212 225517249
    0x21b15030709031203020f090f03100912031410050d050f030705030d1118041806021804051b030708060a271d030d0e0c090108061b0c0c 60
    0x10541a0161504055407040c0710548401c0d082c5800c5040590790310081e81090020140100031704c00e1200c0144c2c040d11049003050f03c05d000c07102800000a810200404400d52100d4545543c5006125851080d61240d400507201000050100144020400c0003122101c001c170f20a032200308042e0510391407040c2e40358040c40c1520550184040464150b90040409030740c00e90011400c074031511600e1140741140c54a900c0164508a00d450b080082e545030900154415581d4071003206030016a190b81d12500ba60241c021556100508403da14001c0350f100c80c0ca000e07918100010f01c46405890042846181c1d0b0310b0454190f59030100d00300e5000f00c0083c916038020041c0321001920400e5111302d05020780c41d44400508100080d04100e00b10303040c03074500a17100402e154025680c8000841154400c20220402003a49001218264500300c0c0c020342442e0804070381c40001615881c0443d10500510403501c4020051100714181440fa000c0c24450b18650f8100c1a90b03100b403842c01c0340200d004081035a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 225519712 1250 225518462 225518479
    0x40b031509100f06080105091302030705040204090f0b040e03270901230102010615030e01022101090507030207080a030506130c1d06160b0709080a0c06020d0f021b 72
    0x1903000c900d0012040d035071822a0707204014180301d9980000c010501401d45032414041561400700060b5411501500c4440800030058200003952014400c0f10040d013405042075603070b243d4a14000c4000c2c10400001e81125207018000612490b280c06290904c07514a070082d400c0000310310420421070140030b00c0c064003100c01810380034207403038402050340203040742e0b00c0355004060f100d407628181101864200e4110f915119040c0030404040040740e61000081c41c00107502415039010300d0081c810219100c42c4482000c0802c5442501c8040d224140c500c00d02062104d5101d2010540c00c0c1c2c0130340c15000706440c80900c2541034551107540b0441c0d201f40000c0c5942c07460b40e194402c82d82210718940d03445002920b8009507041c0c00440020440c0654400d941042c0791003a401c10440049001303840c000d04500140012400252041a1040c090f144000540300580501c1c5404001c1180c603100c1c040150040c0d9910100b41800307220702d0400d886664003d000740980c12070039841043c80c40c501084c0c0c4074034071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 225520962 1250 225519712 225519751
    0x6060108011a0904180204201c270c12080304060e1f02040f1a0406030e07080f010209011b0209040b0601031503050604112b111f0e0a0b040b03 63
    0x65014001040354045807003070440417103005020564500319010391074090140d0083c601459000211049111201c1c0c5d030504c0994002180c4018003c0304600426a4101e01914800451600700c1c0241d500d20851000c20000e41e1206c50840381150180c01a1007103109100003400310f40c0e03a8101587c3e0700c0345902903840320400007501600e00385800c0c0f85080700c0c5078045010b0006499203080440940500b00c4182e82564814004009900c114000c0c001019100c03c900b903060341c1c00304940380203002150141d4400000b81c9207003c2c000d40080080380c2c0002c89204906800c940c50011004409801030038181c003507a256100c0d00d400a01c0582203604156445415140452000507000c0c06548030380040d049504140c2444ac4440d41240c50f55889410284282040e89440d15094040d0b0040b00c0034510000c40582410801c5407a2000459003040103038a40324400c0e9013081c0d541400034500d032a540044841503090003140d0f0701e1030088100814080106100d20071400c005150f102e0f002e200d803095428072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 225522212 1250 225520962 225520969
    0x100f0c03050f0f03040311010c0c0203030d090c150f02070605030103150e0309061201090c0f1b08130303110f0c06090105090f03011415100806060a0909050106020a1406060108011a09 80
    0x41150700340c001424a40c0c0c586e4202c1c0707080c01a0301590201c0d1a00603e0759240c0c0e000252240b00c0e1101c0b5880107038fe1440b5032800c00c428522000d00900030002012190109020090f00d00c58100c020300d00103000325a408036207640220140c0741070300d03003100d44444002c032b8072066480182480c05c01540c1520050200300c6181e9202001040b2100c580300107010309516203030004080e205c0141c1600140010b00c85060310740307a0b201c941454a05019081845900c05600b003c1421707200c0c104011181c624100d9002c000d154102c18000003038441c400c21030b0560800c440c225621068000555a4485030803c002e10351781d0310400c080c1c100701200920440710388804c40c0001382140c90300c1c121419070840700f4082010190a00d284440d0070308083d620404100d0005400410040c4e0061200b4401d40b0701140d039aa80c14400c60a10300034080302c46c804c001950712660003a5031200401d2003181c2c0d0f510101c1d02070200702808180030740100c00603120901640d090039110074030500e518500d0b5180e1030080c81810007665 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 225523462 1250 225522212 225522217
    0x303140d140702070f0902040311060d020906131403120a0e060f04030501140a0b03060c160210081b070809040506061207030213080619050901060305011a100f0c03050f0f 75
    0x4543d800a01c40140f4007a807003902004c2560207880e0444c410700040006c0b60340100c4072030740c601040710600e42e2001c6004592000b80500c0004941040000c9010800018086e0400044c3c0340148900081400000100340c0c0e04e8040054101400f130b01840f2510215028044040346104000c100c06d0409601d05170301034041c0c10582c000d41c1c15a46541c4065408482c0405035a0000c1002205221580e074900c0400d98480c0302800d4008151400a01c496006210b061114031296000b040d401064425107002003002d80d080d03070030054480b280024030404c5001c18003114025980710540c1c0e424070b11091300304002003000401d01c41d00180b08002a421a044c1c14203054400c00c1240c0380181c03500800e0400c0109012690401078440d4025010300000d02d4602c601c02c00c1c0b210380c46d01301046a0b550f190307546014110940c0000c25a600f404400181c0c112080951942c020b02902c0c0c1504d01c44941d04102c07902e81d039004006010404e19203080d00441d110f50010040030307a0700e01240c0d01c0c02c001146c8489055 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 225524712 1250 225523462 225523471
    0x901110f0105040308100630020706090b01080d020a1103070e07030606020d09080606100e0d0b0a0c05070201091e030804060e010909050105100c06060b03090607030b0a0303140d14 79
    0x50b5901c1c410001010340080741039400c900f18030500c08110781454070190241e006180c40c0c1250880f49511600380b18455069229110000b100a640395000c274546000500410801220b031124800008034805030006029010070820340d005124003002c0381c8462246e0748404041035014040c08030081480b040046100340601c005a4001451710301c0d1000090030721030592805402c000709400d040104200024070160441d100311400e00d290015907030309550401d50380d21801d0b0040d0003030b00c4420a221440e0141803050b18034080900071032000200444440c41002d0340240410310128062040f00c03c1c40700381d5024500002c0f04860040e80300d0722804d15680141c0d11050008100120051642d40d110950400401d6044000c0c030140d414100010b1304280703070950340810049481140c80074000075400c60002400340d8103180741e480c200481516181e4000b100c9000120341003c0300c01c02a42403104010080300d8159a03816980100c60008403603641c400d066501c0c8694540b014041c00f2a80e550795907028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 225525962 1250 225524712 225524743
    0x13051003060b13020714060f060a0b13051c03030b060f031303021006032009101202010909090302060f010e09060403030c0c020306100807081207060c1407060b041b020d05090111 78
    0x142e1b20f00c0c001103181110040c10b00ca401c030b44050034080c05895541000090340d44810b142912818007007815011f01d0400d5010300d41c00b403100c203000001c2c1e074440d204003245503000395420f0004441c600c3c00e010f107920441c5401d04035010100006581080701350040c0505611a00c1542c04035043d000c2898140c030f9960b00b040da150b200045c62000c0d08201c45002588903a41510b22040c40d242612441c1c100203a144102c44070030061070348040c1103a2066030000040c00641c2000c0010040900f07009641c0c42c000c842d030442c064440c10001c170384100d00f1400b0301e1181000e44000c00c020781c1c80d960110007411018034144180503100c0020070040c2d0f001c0c801d180c800d100400300c5e076103c1d600d4038541600d092000c2d485588582c1150081001c0c03070003801d0403600d0301ca40046011944840ba14002c803081c41910310412004003000c600041004030540004210b800c4c00ca500f40702d49907203440813040c50011000c4071400b6034801081e640625000e1070152005090504050040c1c0030f03c108001c2c2005486c003c80c032003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 225527212 1250 225525962 225525983
    0x13030c080c0901120309050f0f0406090e160f09020d020d05070c0501110c0a0b040215030c070210050313060f1b020105040c1502031c060b0f0913051003060b130207 72
    0x115030070261102c600420000410404203101d54030060014507480c0140c031700407400c0808070703142071300c070305203600e58040014204108060b0360b030391007000900781401d0081603402a1120544844d2010501e4810b4500d20500700d05441c0c0b510b01038074000d6014429000c0c2454083c03003448103d582c02e2084500c94000d40c1c071207800350052032500900316180941305449183c4107115040c404200092201e190380d80c4510200b0240e143c500021340c054070711303042580503000d00100704400016010081c01070340d8403c8e20398040c06c3c140340c0c0003901c0601040b581a0006511034400a001c6000b51304221221001e10138000303603100540380c814110409480c0143c000d40e45800c02c2c0410820503203c03510040481c08520704080c50000c00c002c1d220b1041034440884c221041d00030900320700c03055000c803000740580040681d440c07035210f04040c4150003044025101f000e16030307503c0c00c00308003d00a13640306401090807c40464219690f0b64001c01c100c074911a0010818040c01e0b031605c800b44010704034a801020081f5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 225528462 1250 225527212 225527233
    0xe0d080a081005150706020306030f0105130b0a050c160f0c0f0f050d080406050a170f190506100c050c04050a0e0601060e0303030604020c01090c06050c011103010f030813030c08 78
    0x108046640e0340070b64000c4146084c983d080d450088181e40000340c0c07100001d41c0d00d85824001078544070605a0503002ca518050030710078160a4840044c404912414070f080084e9205e01d00d000c2250300845001040003010001103103c92500040121100e108601e40703208504140c0350781c0b942c0300183d080103028008020040c0900e008035801000280741c102c80d840802c1c6500e03690400320b40110f104030b00078494041a0842d0742c9005100741c0c10443c01641601c00b1601e04800e05c1490120141da0300c02100000e12000c640141e40c0e4001c640c81280081e00c0c01d1402d20b02c4040c02c54800b110064244c540d800b803044004001e82e0b4901609d8001e543c1c41c803022581c64000d0302c10900b4444182e02ca0000d001055000381c00c0b035140801035aa0150086500603100c60950b01d03054003604101c20010f00700354000d00701042c01c0b031308031018040ca01e41920081010039801d07085007005200c280140420070615280420010701880d0082012286107900c1c0c4500b41da60783d8403a12915000d812005040c2c12009581 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 225529712 1250 225528462 225528481
    0xa1505040b03030a0804080c0f0c010305090c1005090402040e1906060c200d0506040f0615050f040e0f060405030a0201111215030f0a1401110304020a060e0d080a08 72
    0x5402a02084408025a030406800281e5901c1004066400d100e101800102031020003003e488000009505843d1500320040708684c44412140342180482d103014045070b0100d0300020005c48130700e006002e030300181130540c10940d4650030048503103900c65000c003c04552081c10000c0c2901a00740150070070300040b01d02c0b55000589146802160030000044070b460080b8658581da40c8040042541c1070f000c0210701d1020030401400d00d4030151a078450142480100108411050b9165001da01c040141c0000d500b034582d842501481942d0f4029805031410016150035030180740c040110340d0840f14240504c3d501356082807011902034580c0d400210300070300060340a000d1003e402105505442ca8003500c04c03030090034120007400c3e00506200d6004100c43ca52402c0040400c146070761030884807200c00ea4a007400006200d02c00a8155509101000301c0c0c1d184500140c0c0c0c01164010710208076a410120101e4480b000884915405204000b103040800c810300020800c1101698412680749001c87d0302 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 225530962 1250 225529712 225529751
    0x305010b130c09060e0a030606030f060605060f070215041a070302010e0102040b0f0703030e060c0d0b090c090105030901150b0a0f0207180c0201110409140a05060f0d05150a 76
    0x1d0058803410042d910030043c1e807003403d01c4161001ca00301303660b48000e9580030402905c4142c10041c1541d1600340f010003071004083e1090902481450103106261b1034406211150140001156000038240140c0e401440c0c074410070b030308429040507914101a50b480441000840c10200444c860700001018001e0503828026008031001510080d4031305490014a400c1c1031103800c02080c510390001c25400c0415110340c201c90902c0802108484290400d0310320400d050780914030071080d0a04d040f5400d03206080102c001c0788503540c1c1d614018108040200152038503440100118215540c030039489d144100008c4045c1c2c00b51140c003076001d8803078410502c05002c1d40305071880d074000d541c0032110801190007807803160440300b5a4000086400c0f558881e06a01403c00010750405e041d5003c10003241c645610b51001804542c0c40740d144005484d20021034085079402e944d8941c1003c850140c4003182c5c01c2c210500d0312124490745c102c5012061481c1130700b045910035070350510003a80b00d007200305885619140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 225532212 1250 225530962 225530989
    0x607020a0306270c03030e1207080718140103020405040f0b04110f0d05070501030e100501080d18031a0c19020f0f0f15130f0606030501150311041d070305010b 70
    0x40c1c0c0000f031119110b0a48942c0144001003c1000307111122000761166160b4480180d4034070125003810741c03100c425503107603499400b41d190608040c501a0707068407014000da000e2000c20b510910101e90039174007403101403c40200207541c01c0d180d15443c0000a408450702500c541d01800300581c8030520141004130051040704018441d00c41d2141501c0401e101040e4041100c0b802d09000484009810b101c904000546070f4190b0102e00d010000030741c004000c40d80102140306642d800502056680c01100e1480b00c900000c2d20200307a0107140550038a00c0c0d10001d800800c00d00c1c1107030500604079941034141112140c61401a00019081200200704000c0c203110070001301c01400c4082c40c10015103984089200d1150368036140e201c0401d41300341c2c06008a11b01c5503002004000000849c0c240000940440d00c0102ca05600e401a05600c0310070001c0c100c4e05484d4883c00100ba0b01b1144000c2101600d0550303c400315001d84d204a2400345601044030500445c030680010500301003200400038115503004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 225533462 1250 225532212 225532271
    0x3030506060f090d050106091401050301060b0c061f1503020c01140c070b040204060308040e04050d0e0f121f09150c0e0d03120603060e06151c020607020a0306 70
    0x1002c2e01400881582c0f203d00341a125820032400500303200d40034101c2d5900c4510b980e071034140315604020a007507440341a20b00c190f0091221a0340d40705e40b452248031f0400d8032100d43e001040480c1d20785500240d41038401071183d4000072900d4035800d00a000301c0d00146500d003c66800505005a01130038090030007016040341e003824580c9000f0500d45124880d1322001408407420740002070071507032160b0182001d0758115802035211a00e410381c641803050152000d5805100718490b1010042c443c494800001030b01500082d00605c180301071200301c2c8201407030000140240c00e1a61004040b444e03441003900c407682e1003c21450050308100011070342c0c02001101840c1402025501d450300414440344d203d80541d02140c82441030305007140c140c400220002d103400e04080000040c001039421219603214414182c8043e0349139540a0103c80b0130407000290040082e00b58100a0041c0e590098900ca00140001e031500308107900046000104e0380044401a41e80c1241100001440c41c0c1c241c0b5194110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 225534712 1250 225533462 225533467
    0x1020421050118080a050903100204080102090a080613080c011e02090a1418040311010509070302120c13020a1103070803013b2d0103030f03060303120209030c03030c07030303050606 80
    0x1a283c104d42d80c4503440e034580c107015001447c0c0003a80c50400180e80600e0012000b10b442d0f6844640d058040d500c5400b17920700c6400c01d4000490084000b089050045501d144039028841c0c2e00da583c51215040246201e005544e10b030303e0114403032040c0704104a06000e240006940d070651904205484c0343e141c00c1108900d00310340540e41c041c0c03a21000300c06491030310b03880804280e45510f402c60b0806840c80c1440d00b0343d401c007000d1000b140400681982628401c075440401080f00c02c561940e1600001d001c254410404c400041d58040b42e58020080510a8640705000382005010750f440c550081d1421a0b440d4400001084070940c000018084140b00d00c0c090982c2950340c6006500c406002100c4a034004e00081c0071905840148520401003940103550000c0020402101c43e4203200903c4280c002c01d003896020600329110340302c3c3c58140d95060b00c0701001032020711003c10007900103034401601407040541d802040d5608001a000b07001050700101941c038154580101a604060405c9000301420b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 225535962 1250 225534712 225534761
    0x415050106020d12110c07060c0b0a14060d050106050a0b0301030b0112050d050a051608090108060603161103040b0705030d0b040207200a211e03091502010204210501 73
    0x381c0500d44c00740c1e044400320b9003c148600124062050300c400760320b284140100054040c0d04016203451242c090005c8944079aa06112072003075503599010181500d4010300082e4031840c01340180426580118000160705480d9030114650215503041806c00e110040010000c00101c0e860950141110100151080c070f02c0d690350603078035441c2034040c400307110010482c0c0c010f0340d100700243c0e232000f440d40342c1d2400d2150041c03c00300e00c5580000c02e000c0c0001d500e00005822401d01e20101c90080c02522035045882e004c440003100d4201d58080820581d0004010000307484a80c1000703010f500b4012000346540e045035101c14421205481303041c1b40524014001e00000c00c0009144ca407880b44021841c010000e403000000d500b4001d0758200d0401c5c0f090f411304c1c00c240004c40402c41d42c0304511505400c1501c03200041d0600408405800042c0010600801840080f07841551885060110300000d8100380d1034030b900c800348003002d8180c00e000d01090041da00c1880424013032040700d1541408842c99074441c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 225537212 1250 225535962 225535967
    0xd0803070c030e0402040b280e0409050a020303211b03010b0a121a010212030118020c0a0c0602011e02030f070305090a02030304030f110604060909230415050106020d 73
    0x1403903682400707200c920140c2458014a489008804010000c656664442c50460b150b500f041c05860300d024506010805183c0c44141e44038a128041e4482e805200700c070300c0412003d003541030000c035a10302a806590005860070009400309035006800420321807402402da07003040400504041050741c54150a61690016804980c107640c4012001560750340303048000e0f0307400441054000b4025141a0300001007291034076002640b020242d00b921240c1801520b000c4880c0000c0c02200c043c031010001030b4801032900e81c001c00c010300ca481c080d1190f040751038036444100080c1d58003540c0980d4603030540c2008402180500042070101810850840c24250988140c50318001c20090a0660f0307500414400346041000c200e981e51300804803a50b0765242c0c40d00300400445910120345500c2c2e06460381c102454108103031001c0e2505591203000807403902940c00050030f031400388405445120a072080344000000c50071441030340201c000349049003452074140b04454059001c28110741100e00031203d00c40c1d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 225538462 1250 225537212 225537217
    0x1608070e010c03170f09060109090201090e0603120c0c03011103370c12060605040e040809010302090d0f15022109070f0f0612060b090111011413110d08 67
    0x9001e1920040340b241500c1e0075503013084200e8031000340d0030789141006044150401090b204400407000e4135603d0741e880818900b0b903104040c000380130810041e800e0007100242151142d110000908580b16050802000d04040d4061455003103a500314000034091400c0c04d00a10110031001e00c0c8880c03075464014407010515a01c208265a401840401c44d110f80f480411713105845c6181e1842001051811403000d00308124450003090070301d041c0138000030040e000e14150742c1200c0d00c06150760000c1c2d846036074420659128200302814507070b0030700042c4490345814034080c581d18800c6240e200ca550301d50034281900c541315103d8505d56070042001006424070042600c0d41d640d4800d600150b2a2580e26180d42403d110303402c0f10304841440c62000072801c10444e0803104a607801e4a0b021000c40d8180901d50a541d1503000e5103030401c3c0c04008607a89544034100707800106103400000120b081012450f03204c0000c080c1e618580242100300082d041c8201c0c184103405504044601c22405410307640da006030b90 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 225539568 1106 225538462 225538487
    0x10306080607020a080d0f02070602040e0f04080a0e03100c08010f0608010614030603251a030f040201050906070f050a230a02100201021e03160807 65
    0x100890341e1402445654060018075a4a481e049410361201a201c2030141e520705c841d241001c21803015000c1c05126090160f5258645818000e1030b4001a01c2081d4803c440c2040c0000503820004440c80e0550380d04014142c203000000207802c05088442050000e802c152000c0c0d003299203c110076040c4c0b10020001201c1a80f102411603142c4024094540401d0b4540c050700d00115503c0c01850748100010211002c08690640e041c2071411581d281d0440c0c0c12075402e040c0078001071200313218151510000078178114035000090407090800580040c2c1402000111500c45403103010450300f540350491240c00c1e0a8010349031003581c41c0109002594000b280b110303100800c0c0c00e88146020000740000041c1240d64994003003003880c1c40662951003c1d50b602300141c3e015100591a80c054074440d801c0141e490f40f0f4807443c1c00c41064100701a90701045085c4080210142d000b10200541 = true := by decide +kernel

theorem cover : BRFrame.Cov 225359712 225539568 := by
  have h0 := BRFrame.cov_init 225359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 225359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 225359712 ≤ n) (h2 : n < 225539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
