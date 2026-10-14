-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3481
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:47:26.25667+00:00
-- url     : https://prove2.me/submissions/87ae98c0-940a-4e46-a8b9-c844554599aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 625899280 ≤ n < 626079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 625900530 1250 625899280 625899341
    0x6050f150703030207050f060708060103061d100f08030702030d08040503030c0f070b07031407030c141c0c0c1104110414030a0203030a020705280b030c09030111030901 74
    0x1410041aa0650001c1c549007014400e805442025a00a00b1200405078a501d001e40321201103c2840c001a000d40020758558030034001c500460381c15105885151040c241d00000a8100810601c0120b403000d20000c1c10162001c80e0314000c260702c8000c0c1d612441c1d0342c4101814240340fa1450002c00c001e400c2030001003a0080116504035034017070400390b5902d04081c2185240c0c01481c0300a041480390004112421740c141c2c10890900510444e841455601d40300700380c085815181107800014000410b45590040358001040442c0612051300c1909a2184481c001d8465a040040c0040c0c00441e0410400c03001d5507200402d444109d50900c0701c602c60800142c41d6028610400171400c2401e070b021b0607a40c42c14003141c44c1854012741981e5851400500207940c581313091180c980070304a810a440c0c50801c01a81100c02d100900039080705661616403d038050746c00207062030f10945001c101e0104960741c05d100c0c108512011240c1e486e2607180c9540c0305070849406002100c080c00448a240500305031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 625901780 1250 625900530 625900549
    0x2030306130e010f0605040e01050c0406050f07050a05030a0206010602030c0d0c081603030b0a0603090b06010807090e07081b070c062102070c092306040911030102030406060906050f 80
    0xc161201421600225603000252101000100241d4a40000d49120695540289003520b0042d0740c203100d503a942086084c201e550440da18441030b0020b11003448094801c1d8018075503100d82014250030074030703a0303150941452680e40c001c4400380d10006140c034003941c040c00b46900404050000d9402d1280c0304081d079482e021181606010841c00d0700700b4000b00325940c02a5a03031101380c0032440c040d641451501900a1603604500b0344a0310743d031400042d4240c868003c84003165400710401441d41c4494006480c47c0e14003a1624060040600c8003140c0c5584041a4501c9a0700c280e6a407083c0341407031000d40389000045141b840c0d407882c081018001140110f240f800898003d032401200b05d1091401c070f9068075003210b0450031800d000003880d00034444504160419180d16083c10080c1d0502440c14000340300c80c4c0340040240c0c0c112017000841c83c4c581075001d001c0b0b00780a41c2da0b14141403100320020f42243d00448003100d81581d0360005001c083c4862080310b020700700030340761400c65541d2000002c50108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 625903030 1250 625901780 625901791
    0x100905090a090501020a020c0a1a0f0c0703140309090109060501080f0c0f130f060207030201120e0106091b0e060c0312130c15080606120105040f1b02011a06030403020303 75
    0x395008241e8180203075028051994120b0000c54a0340300210000f5150180c8040d1203100e0b00a4900c041400c8a08615144524008880407450314440103600051900103000d064900d004050001005c110004000000110904007541d5100110403c0000000c0103801001c0b00d5481e1682c14009a40c0040c0410340206080c800d200c001e5842d002500f403544200f041074840b6160104d0464034441401c10b0780030588500158000c100354488030304aa58640512021380055441912816403801c20351062002002800010440c6500c1d4841a41a07a0500031001008403802e04d000003140da029268204900085070010714003005140d00b260b45e4003403808070b068101044070200300804030307030403542c12810781c49505610071607541c1c800820042c1c0710900c54004220000006181880c0c0001181d07504510150095074903424481400b0042070748192000c08940d42d180360105841ea215040403009825500204a4881058040c07400c0d080d07084920340201c00502c00c0c0b000098001c415281d218 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 625904280 1250 625903030 625903039
    0x20f01051c060b120a140412020307060603080d0e0105071e110f0303040b07050403020d1401021303050615030f0601031e0b070f111c0e06040315020d0b100905 70
    0xc08003a03003810841041e40e50803850051401600003a2102c09201800f03102c240d0009030f00c502e80d031307000101c003d03030740721440c151000c07403606000500244841c1c11320485101c4c00d03c1260b090004036907400048502a40046c0c51200c4040742405c000301c2107021700000c000700100280b04c01e0406400140c4030a11001c1c0e0940c0b881c00c029100e04100c0e00ca6070b01e0060040c080001c8031041107080c41d100da10fa42c800c0e142a210f0005100010345083d02600c1194100c0c0e502070b0041c0300d03111150701c900050407d01c0c03590b40c1c295502005200e000000d02d400920196024001400603030030302003080c2e41c01030547c407040b038083e411001410f0054080402d40a044036085001d0300354800b802c100e0400112040400248a00f2881043c0404103038070907a200c2c02d0000ca070310b6280300380c98030038106942c40703560181aa00b03c0d081d01c1c0002c41c0c0c40703100b0f84028004a802070003070307810030340c0340d1b40c41004c03d452810a2000390345d804110305051020a008080d20140240e45912050300b01c060000d01d030146500a06015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 625905530 1250 625904280 625904287
    0x5130209012a08030f1515031906121a091f0903020109050a030201090218060d03140405060c0c0405150607030311160605100501050a020717010e0703030203040f0e0103020f0105 78
    0x2146244081c040c52140d1000666950780385c030407290b01c0701e20002d9a4050b0029011030200109080c1426134100202108024034259a01e402d004a442c2d40c0b55403510004a071030b61070000714149018170201009214054414060565202074008038600501e08529903201100c8482e0804500c140c00e05c7c41d0100b04400700d00301100307040030307400740044c80c01c014410321a442d0a18103040d810741c04401c0c4c0d10703c01c40710a16581460540ca0703560340002e840032540075210080c40c9000a00070a02598411610760f005070600b40d4400c0082c015400c00710280c0003d40000c0a4105d241c94180b062550000460b00606980209034002c540c2d80c2c080c5c000001d050540e01c140008000c4440001c0e181d5a41103100c04503d00c0d603152900700080c00301502d51521444403458045a1503004400740e82c2e000d85d85500802442c0d00c0d00011840711080703481056000e5690701c80c0c1905000040c01180b000c0d43c041c2e002550b469152041d103040c04002c60344214132910941d4010b1005036140705003040e0a4000340707402500c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 625906780 1250 625905530 625905587
    0x30c0f0c0c150c06060f05090a02090a05060c01061a030103051c030b0402030a0c02010c020c2809050f0601110d050a0c061b02100f0b030c09071202030c03010513020901 74
    0x21140c0090700b003040404405041d240195034040548041103200e140309100159803410f0401100c1254002c03d907100b000f001c00103150038025030117000401e00050001818564590116031036901942905a460751038030018404406468081c21100c003a20740040e00d10761541c0c550607103c03040c0d021000f015003001c5501e680b07111f2007600310b5180e04000420455680c00c1040290340100110800e0801550030080703080c01e407074000324000792a001c0c0030b01520392120034070b110261550311106100f2060492000040b0b03c8003003900c541072007030010807600c280c2c1d4200f035070000d4070007100070304644410383c40108140c1841e58000240d5081c16510f0501400401280c07500310050a82072141142c1101d03032420240c9100c2c0e0000e840d60541d0500c107410400302060000000a407412002c1c4141c0561140d10707404924148500c0312a030181d45031500040d005261060b0300280d0340191810001d1013404001071182d840c7c8102c084210307000c0b40d0f104500d0310345594006000c030101040d910320a000e10351070a80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 625908030 1250 625906780 625906793
    0xa050d03081e0109060302041112061003020c1005010326041a07061e150b12040f05060a1b05040312210629040602060c0c01060e25030c0f0c 62
    0x82d5440365205003040c56864200500c0203101602c010b17841641408407603500000700f102150b0030403c494182032031036955841402039285841c100903080603800c006202800c041401810540c049103400400c0551650601826000350480441c10840407110111030390361a20b000c5400301c40c00c07402d1404222406000e6000103003e44080640b55608011040003020190b500040c00404002c1c0708012074a060041c1c05038481640c0901c542c0750400300503070b00c05095440da4480e070051040361040c045046036900d10303041c01c500f640e07156800c0da25607403003100303072030340c2c441980c003020514500b9505061030358851400101c0c054582005005070010822030384896200c80c56202c108021040c00080c1c0d0712080c0f0f0050149040c80d07410302200b40c0c0c6586400d50090011141220241ea0050100c1d0301c403d41030102070b034040600203520303640e0303500c00189080015800600c2100140c540c1e000744142c03401c42c0303410408004249003c041c03074603920b5211950440c00000782c00c01c480ca0118270085940c40c094 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 625909280 1250 625908030 625908061
    0x5010203030a0b041404060f0c02031303020d110a080a030e0402072a0519060207120506060907030216060b100e0a1e081b0a0602010b06070303021c060b180a050d0308 73
    0x4084005c0102040207200b4140c0180c030304402c0340c0500300541d41140c0c804a807a404bc1e20070344089141221410009854401d0000395054019603d030b4100309140d00001d440c0146030f1707000b203145030000d001c0301080c181c009070180c1112205030b03410f5143c0b110503a10140c4000f00300c4481d001601700902800b81d0100e42e0f0a1500191002a1124041e224901c655207a035075494410800180320300c220200300408041e00c00440c15921100914080c0c0701c80081041c001da00034040010540c0c24403000c190a058004107910b814001c0300005a5411040d003400100c801e030700c402d10280150740c10454120388030a0f0040081341d100c4070000088011120405041c1c0d00554009562440703844019032040020302e0740c213646007004888a0034003d99460040c0d0070f0b43c88401d0b01a6001109104901c0032078080d03002040b80e1101080e15100d856203c04410707045410941004820520100b04507052004850060241aa007100c07219140d500d4540092595621110700404100050300492402174500201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 625910530 1250 625909280 625909301
    0x2f130c17091f0b0a290c0a05071230200610080f1507121b08040b15060301050d080405030d020607030c0906020c15160c15020705010203030a0b04 64
    0x1824108020404410064030764050300381d10480896400040c4145c03074000b00103a03a05000c400883c0081d42c2200c01002d500000307028480d1307000700134558002134014000d8101402e4044000e0300108414241480c1a4007400909030710a40309444000c1c100190140c001c0c80d0140c0b52500b041d0b517083c4040c0300c8403400c0709800038201a10424080c0440089a0f0b803607401036a0700320045074a522035403d50666648904102c50a0f4031805001083e50a0720515058031110300d07101b004500c1d0310240f02c2030140040080405400202404240070400c008090340e182c11602951180d80320f00aa9000192076100621400303218504d0544020204040395007690001c11000f801c1d02c1030392050742c1020791a800b00321781d540c0000340b50080000080d402100321106507580c0750b005000e40d01c010780c140502441240c80340c118a013002c1c007e4200070b0743c2c4444400c2c60980300300840700c00c84c0d28200002c0105070741c4015440654000900a01c060b0f42d0010540b40d03c02910000070401c00102c00108008000701c800307 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 625911780 1250 625910530 625910563
    0x3030d0207140f06040c03060e120a030506030d020304180b150a020703140d1709100c0309020102100c05090108100819030e04091e2f130c1709 63
    0x1c0500c00d102204803200c080c81c500009582c59085404106620b4490440d40140040007a0704188042102ca500080e100c050b00000c450f064038448590740107079004084400000f03900c40c000c00100b42010700ca5808960950300065042509040e01d01d558001c3d5140388d5080d45d030707807401061401e60795610441e0002c800040c10960f20703500d6040080d10b0f00030a003c1030ba8500340414007906103420004a5219801c82d030380c1c54064000b1841c5440c5200f520103890300b611845842040200281d00e07110742c3d60141e21702d450004500d91180300282c10a080c004880d4415031400c1d681006481d048012104165030918041c80e1a90b640003003000e088040b908624124480d480c500d1818a030751021b9421410300a48801c030321020310000304020340360360060080034208110803245458413800d80340ca4046200c0c040e441d4620340803001604100c440341d020007140024401030317452982401070844c03680d03002402c0e05014803400358101070481a030039220064010003130340000b88951418029040c42e9804201c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 625913030 1250 625911780 625911787
    0xf180c060d1e0606050a080c0403050a0602090d02032a0411042606091b030105042d0b0405100c0215041e0b0711100b1e0415030f0c0510170603030d02 66
    0x60010465081101c6d4140800c442c00d002c681440c40800c29601165803001c014074440c1030698800d4040d4009105e0582c101d21a01c20180047e0b03001d00025880c483c510342c1600c940d00020300441d103024107404410b8081c0345002d040759498804041120240c8807440c5002c941800100e05119640355011043d5260340100d4081c4000c00b240804c15200a00102503c000207014000405003204c0c0240d50050150a0b0804040300f47e190b11542c000307144e0b00083c84d60200d01c109403903107110310718103c404403a60b80003e48a00c2003c0c40d28815507a17a014a840103060803071810282c804045000360001d081005405601c500340310000e0040700405138444682d0b03d035800d010320b014180d91841304205c03800307000310207040e61031290911803400c14080040031030800f40006100b2181c803031030300c0344010f0b00540c45042e1b44054010f40940c0e100258400c0c0d01c202c00b02d800c01d081c420182c0c245a00b203184181c1c1e4203451040790340e9100d29007102024060701004110303140c00700080d00e144104402d0b0f100072030010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 625914280 1250 625913030 625913039
    0x705060406050d0c050a1205061521090105090d0e0402130b0304050705040203062b020904150c0905010509060a0905040e15010906030321140f180c060d1e06 69
    0x10b405003000200240d028000700740c2e03880781580e241c0a40146030002505824054003032810680219400c10000b51900600c450400713160406a0b00040d000e01d00f01d1107481d403c0d041c078a5510400c07644420f4200c02004503040003600d03aa141c0400660580c104044a0210441c90f0b0ba10303030490304520601e84600d40b8450380c420043c007064004860549903409154000245420580226031103404000e04416001c10010030340503821050151003110b1041c12604500107880744180cd9000305e0040b1a409501c3d596102401c080e00c80019007002008021a00ac10691b6005415070703803046c004071895903d80c02c50314400c0759810810ba01150b4083d041501c403446103140483c1c040e12a03c1c0001115401d41c1c1c981c2c0c801d80540308540b00040008852140400e4080c1c140030080d500104100c0d40030a202044c01c02c0800400810f0300e00305140030018007408400b01207080e80d02402d040070b5000c1e00c64200080c00092090282403005804991580e40d80d02c5036450281c02c42c0b516400724603080000680300e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 625915530 1250 625914280 625914287
    0x10905010f23090709062616030b09040605040b100b04030201200a030e0312090d08070f05010f0b040f05070e040c0201060f0b030702010605031612020f2205060607051b030705060406 80
    0x984999004035101024140031880b108521004804441f80f4071001512a203003601035042035060203404040e91020707028869038480341014012400b07000041000c0c2010700b013a0141800c00750100f00c1d4008855801c21480c02190184d60480b502400e04168180c050301000d044d00e4105c282c01001c5000f07607000581015001203e00440840c25000c8960782540203014808500c1002c1550780d0201c8240380103400211801c0081102e40e100340e210201c0031456684290035103003903c92499440d42c5038a441c162606040c4074410030611590f40c18041400c00103001f078084c400f052051401b80d604c8002281486000b50800c60060180002103060b49640303c2520f85c0c1500151440d50055003010400581d524001440040540700740c0c03c2144814a001e44000c90b00800d80170481c0c002d0701d000e0306606169998081400b04524040c0416075521044090034101c0e040146154403603a01807240801150002400f12150302d401034184000045d1800080e00d0314040d507001e103074014030015000c50384950 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 625916780 1250 625915530 625915547
    0x7080403240b060a020c090a02070b01060c1110360b0d0e010e100e10061e05010201061206110904020f180a0e150d0c0603090506010905010f230907 65
    0x81c80c0402401400d102080194401c0200d10b800690154001600030b25044884c103422803a2217000514100e029540c0c02c0f0307401d000f43e11030000315804000075000d105000300342099070701c0201e03032280b054145400d0241603841168001303d1010500d0391034a0442400c90b0346105281c01c0482e1040c405d990b00c000500041d03000000b030020040c1010841181c01c0c41c1401060400c12040c00541146402c00c40e47d0340040455082c1c400240c401c02100e5401c0c039485120b100702030003100c0081e1601d02c0c0200d011000713024941c0d115504580c50484104007004400c2c5038100c0c6503900010114243e0204060829107005040426610603c0000c4259144000b040109102020a0740c02d440e4200d00303c042007103242d414030035256201d056100041485521282884400900410001c40c01e1103a4944800c440c82540040f00030a40e105003201c20721600b040060b00608000c0010701c043d60420f40f500c01040e41a20988192500703c811200450140e100d40d6440444c01030840d000516081e03000600c01300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 625918030 1250 625916780 625916843
    0xb0307200318040204060504120515100503010518060a0c0504090510050a0602191e0c1e051207140a0e090102030f09010c0c020108100e0a0b09060d05100207080403 72
    0x4403601c280102500f858000d680403600152034480c1040c1c5000380042d410071202008590b907000721703400c00d42084c44d019030241c00703582c150f0055204241088245821074801801c6c06000c40041d0036209103c0d0400603a00341d00111342c22001c80c0319010700c2c0042d641c074001c030f070412400c21b410901049031080310107800d00200c50048a00e2010141d03100f0040c4d03103401500c12032100310040010414049032649800c821a00320744114854000000c0e00c0b64035450b00f040e08103408404000e9103400c5070f15119103003a0302500080b65512150510740c1312031030341e48980740320348014946441c40548040d074403481130304018107044448030307030a14045220394001d40c0708483e150000700e85100410560f1005110b038070408a001e40300c01c2036030079460b001510054401420517401c12590600452540e9170701a00e10700079501003101040c0b40d407440003080705a6000400c884c1c000d03d44088841c010560006000312074090b42c01006030b5420700d90074901010300c01c94101a01c01880030328512a6501c451406a000c507 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 625919280 1250 625918030 625918057
    0x315080a031e0503040f11030d08070323041203110a03020a030c0c021309021315080f03090108040b0601020c04020a02030d0f021603031107061d06060d0c0b03072003 73
    0x19156065001100320b00c040c0c52000030701c0601c006000100c3c10040100224006d650f07810000751401c00003407824020301170104c00036034004107200c1499003600035402007991400341001135880c580800c50048200420140c85a00d0381c503080c0c401580294000c0c21150040311030a55141400780024002c1d50200c5001c400091500391403020651168403100d141c07560091104036540c400345001e001038181c44500383d900151884c4a8032034810360b40b02e04604140c2012a03072a1f490f1501c180981480190540034503150001c200144550380d00400c151350213644148807100540310140101d03c0c1c40d40b0343c2005500984001801050385030000007410381c01000d15400d001a807030300d8a65109901914441e111000d64440d1080b00090280c0c0100300d0001200d900d50341001e65a454120544401e407026104c60420800b42d020004810320007107922000c1502d60380c82c100e084d41d0700e000303034101c1328804c0d4903d842e00400451750151242503081607100c2c0c00c210388258a50101880780d00d80c2d1090700b034001391 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 625920530 1250 625919280 625919297
    0x20618010c080a1505030d0c110312030c0309250e070f0509010f02010917030118020a0503041101020c0901081006060918051e07080412030e0a11010315080a03 70
    0x28160140a402412405a078401015880c0e14140744060450b000070001c040c540c008001c10562010008545003151959881e6a82c04042c2801440b0070300c0e5429003070103070b00721600080c2c0303c00780d04007241d401685820070b181d544c2d90707020b05543c14403140b140109481350607100f0740f03030041250350340c0c7e4002ea4040070151020350311007103000c0d220460480d0680c00420014000a24150300600343d6410460050001180132015a500c080d0714801040c0202c051640110041c01000240c500301d030305296660204610b460400e160262203804000d10052a4000600740945a64070a103c08880301030003402299048d6114544a40c68844803a0301a1286281200005410b071113540010100c400c0010b6204144004542103806401c000740891f403090002e450301200c40034401c040500c92b68042c2d0b2041042d04080c64400300600301c0c02c080310101400e2804041a0b044045085107245511600002440c4c1c403100058014124424032810340c0d980403100010941c90104010040e20700c03959900c4039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 625921780 1250 625920530 625920571
    0x301050f01200d0f03050601110624031906050f0708060d06090605040c0e09030909011e03050a08090906012a032601030203060f16030b030c1509120d020a150f0c0206 73
    0x36080040d413112704860380400045008904004030200500e4407425020701440e0310381c3c020030714040c00c1e490f4401416080800342c5092100503c079242d000902020301000b14100244000d04815003e4202885100c50503903117002c00c501d6134081b8003282e0b406203007404a40f40c1414001c0a0f520584074824514280c10006008058044206d402091008044c0700c81d0380d0030444080910f02d4031138101d1410304005440807020440c00c10103000c4a41c8500c0d12142e1718038004c0140601e891000d02a40e060080d240a0b00185070219800c900c82c04201c02c558061095035414100e88040e0007411060405003558009014202c8200070325060700d00070380403035007503846440d01d12419003030444011401c5071020708206001c42c8280c11a0b003454000500700e490aa403954009404030fa0000601e1421520000d03d0003201c0c100b2107041411082000064005071540503c00780d00c5082c902c0004059045202803200c61004030341c07213000100070082082201c030183c50801b941c0d4a000ba541d40d169420120340804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 625923030 1250 625921780 625921787
    0x350a0b040b100c0c170304031b0609030b09150910060b0c0312041b0f08060a0b150f0d0f050402011b030c0f0f0506070203030712020301050f01200d0f03050601 70
    0x111004400b078410030384240144400c41d41c3da80808003c0f90200d4828000103071102807000d82000c1d6000c64806559220f1441c6481100b1641180c40c034083c0c00c030503204c1001000d40003501181100e03044201046140d41d80303c2090305201c4201d814421140d006418002c200600080c0c1102e04400140108205512000031100790b001c0c8544ca007031982e04c10409120f0308808410a0b0b500103208100d00d0050100120392482c40c4079041d0422032046112000c00c0103000e108215250300000c114404200800d01080411203004803400a54003c81c1e00003a0b40c202032440300110341c609862510100b059035160318200000d0301c029030b0180d00082124030003100c5070050000b410714240d41600d4045074056240d49184400b5800502a18024071200d41c500c00b05e80c050001e14400d8445601940c1c0c2c0c1d140c0040050260f01e00103200150301032060006000f19205d06883c144803c2090902c003001d5030249a022810a084140002040c0180c4820309501074011028900000003a2014000c40c0e88610045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 625924280 1250 625923030 625923041
    0xa0c05011d0a0302240d0203060418030c0b0c130803041e0807050d080705011410060207033518130b100f0203093d0f350a0b04 56
    0x40b607200742e405408100500d003544e0b8140041c503491007901042241c80e0044041a08042905900e9980002c02c0040f546820b1080a000101c2e10a049030f40090a4800400070180d2000080c8040c0106012070914003040041c3d0740041803899049480340d071242c45880e16a0070600c12901800394051000d501d00800c00c0d80c10040d80e0741c6900404410346001e040213200c034149041921a040200880404200c0030f000c1c410310040e900241c186075050801c180c610b00b0034540e011001715080050180002003401c10396501e009900d9040140480d162201a880941804160140d080d4002100d04a9418142c203c030514a0122405502c29008c00c6e00c40080ea1460201d00741d200320400036915001d4020b1540711454001403048a051048900210380180b80005a0031041c2d800c03c842c03020f800c0381107010781721410f0000c80c01c51303803400160501500002586040741c3c00c0c030101480c15034008822140014510b040601254080c0c00c603480b6901c08031a003519100407090505003280305504050041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 625925530 1250 625924280 625924337
    0x11e03020c060f071b0c1205161a0d050c0c060117010e0d0801290a0c050c030708060714071506170c1c0203010b0a030605060a1202090601050f09030a0c0501 69
    0x20315028a00405940c01c088912213012101d120706c2c1c1c200810010290202d4041462060000b4540c0228007408010221165401010101144544682c0c008621420346603181c11054010034141c0718800341220b18000c2c01384410b01440307030000001300e080100240d040c0310015100201b0000c000340008035143d0104905400200c0c180d41d0041003070205000c5110072000c44003c00201c4400300e811200d5082c0d1011400400244a1031a01020702074184066008101d0440060100c02d10f030003145a1101c038020104410701c400080321040c0d000007030080341e000030f600101058000f4481c02c0400c0042c82c04d030041c00460b18201200c000e1400d00010946600c81e030042c0a00243c0021180c01e0b0305018011070200e80554075002c072a01c10f505c070041684081d620420011500e85441e0341030003c0c01c0740c07179031145408003c0c01542e4000750f12507040054105100b840d0481c0e40c0d885690751440140704402c034494240c465050070006000e0805d01440540340242c0c0c03074400d0015041a064412041c0100c1c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 625926780 1250 625925530 625925537
    0x140703172e081c0201020c12040504111315020a050109210203130b0d23060f101e09080d17010807051e010e0604090f06062c011e03020c060f07 63
    0x310328010b5503d440e41480304000d8400035250611404d407841c1003084140c4000003400f004038083c055442c3c01d002d6044030140b40401a81003803207805140c81020302600c0fa442c00310281402d22004144244041001190880000d21031140c20703280c02181d503d1250046824104065030400c1c07800c2c404404ca170003030a01c102c503600c001400d22024030855805107400060b0316a917107030102101401d00c60000002c06003c6140c10a070b20b4050107206810055600462049090a000c5800750340c000540401c5a130495080001c1400144015241030b41183c00108030740c4a0f003104484200e50103880c8501072991012090309590340c8040c0c0550b280c0c0d8600503103034404020b905528072086200070306031102171b0524051509800c91800b0414640c420b40210b40c0168a0351481c0b05014248c1c003411000f8402854132024a8000300c101071400b810b140e880d04480703000e01d2140c0030141c2c414241c5e40e050071074503806150310f0260414054025400032291036400c2c0500c100041070003503041c0703e891103400d0548 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 625928030 1250 625926780 625926793
    0x613050c040c1809050109050c120115140705100b06160206030a09080c1c050301060f4d12030f0703060803030c0a030f0606140703172e08 61
    0x3030400c8050032a007400e1004004200d40030401c07400c421020380004003140f100c0010030b541002c0c1c50784103540340149040e0600c8010418403a40d000e0042802d41185c0300000700a1a01210007012910b02d04440c8926070f00100c0482c2c1e01c000c1c00b1001c03800c0450000c541d4810040c0021040070b104090081e0040c1e10010f15001280401500b4490010759201d10309400000c0e0090407690b6080041d0444412001940d0080314160016002107602820198003814514115854076034020001400d140f40d1500704620f50040304007c0000414031451f91140164608224408000402000389038000d000505402028001c40052010400d4803a40704401e511624698901220f1126250060000d0041603034403140045e10395014000340d4042d4140b07030020341c0d03100907080d00202034480d400c1003480c0391498008108030341034001d01c00d58014503c071140c02c1d40710300b82d9040a66440f8015130307040900300344105c00c10000c8200d0b03d000300e00d50601200301e82e403012000741290074003031124091000d043c1e0191 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 625929280 1250 625928030 625928053
    0x30b01080625122c0709110406030b041b02010c1403010e0a110c0d05040e0a1505040e0a020d08040e2503021e0d290d0b0c090a17061305 60
    0x80b12048904440f81c20041141462129082002400c403425503269103c100f00700c04034001d041c80100010b001204c03092044201c2e10700d003810248120310844081c1551010311b0940c41e01e5079000031031000c01b02c5d50044a0010040d502034040c04105800400051006031030008007002d0205503070503600300d2410181c29950b000c2d90b081c018154403800680c200418460018040c10401134442110f41640d04c1540342c070300d006400304001001402060405040c001100c403051000b40003442261400c45001c1884200c3c0d50040b0708012811101071740141d54080750b40148100c2c04010b0081300c0701c440e0400356560790300e2030800320341c100b140312041c6075010109444080792203900a082e40d01c01c42c0b0100400e01d0011960b03c4884d0703200e0044803072110b0700c810f0141c0e10585004140d600d122a00e403850308a544144001a0303011000d207000402d03070200d003404258400d0700c40317050b10b10001021b03150b5109107840e0322803000100d42c60f83c4482e03400d100700d9000a100c8804000b0990080da4010001e004183c05c8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 625930530 1250 625929280 625929287
    0x3040f2111060c03010303020a03080604020d0c0309050705011b030c02190305010c030605040b0a060315050307060c0b090d05030a02070611030c04050909060c04180b0406030b01080625 81
    0x800035519080d0000d11031030396258205058514080c140c50742805641c4001190b800c103035006000550b018070900042010a801054a014040d03051410f0000303580c6620004009000d40d05035240401d1408119000594041e804078800c00d00802c01c6590f0b1340c0d618030044522206202d00c002a00020107507440020380a00d028501441c4000c0c09114002c0c0e0460002c00100702076401560640e46401131110682d4140c41000b0180c9012343d03043c44071420b0040440c10041c0070784208000c2658502421900c5240300301080701074400281030b500e4055458070000e00d0b58124400640d05800e0070b0020030140300000070101d0240d03d140e103034039003155640c0504800940200c001618969140c1c0d036040e4001100c14011031003a1903242d0780c03986490802e410b000c1c61610040202c01030350303c6041031240d00d0b25000c040d00d08580003a00b07080280e11040152901520408003490742160505030b0200410030078001e51810788400504a42c015a1028154441c0a03680e02000b03c1c19080e412440a80611 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 625931780 1250 625930530 625930553
    0x90c0904030c05010c090e0a050603070506090a120302210a1b02010c021810060c110906220207150c0915030b09150a0e0411010c03090b130f05010908030304 69
    0x280c180000380e09582d40b6044c1c01e490440c0f04040008140060910101403401100c035041059880200b00c946004ca001c030b41c2c0ca00d803500403244103000c003050624990381d519078484060000c130358a040300d00c4400d1401a50701c04079082c44001c0452440001401031307850400740d85c41d1001540d52440c041d426110384d54002c0b401c1e4030099040000340e4040c0f03005030700ca4101d4000345a2407030542120320701c2c02d010524000c80b0590041e00c2000100d00105000c65413645005c1ea5809003101e0f0101c0c1a1540c0e00094500f6032009100c0035100f80c1c0f64805200b42e0324070360251911501800d5010100c980a00b04d09044540c019040c001081c14020280240e06400d0b800c00d032441624100000c1c420901c000007070301d10808a91070310342c2030145180e0701e649003490200040108042d00e1007034000e0410350f488850f0511001c08480c10003220f03405c140181480384801100034500388940b80d07500c04200c041c242c00e4150034050300072020f83c52403001600d54031803502c0500300c41d10fa40146065440d19074401070b1006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 625933030 1250 625931780 625931783
    0xd080901031b1706040f05090a0c080f060609091608010906230a0c1103270303041208030408070b040302030d050f0118020309100c09030302010c090e0a05070215010f06090509090c0904 81
    0x1d46c0c504040c001c14416114550044444030001c104ca0403891910340c020f10013030b400c038003c1600206e20b00c0390b4500e400680640c20480032620981c00307030b8032103d00e645442d00e546000c0440a0100c0400500075406503c41292076010b840700f4005508088146290382c403c1c01000c44054200c1c070009600142158407100c4500c1003450141e104070703500344455241d5040042c22142c5400c101c0480b10b9240e0300f10030b403d4030116054000e036041c9442c01828002d84051500050f182c488000300240420002c0b20480c0e070225070141c683c66560401d0f0030000d590ba00120450791040340b8003c04240c80d0120489418102e446000140f42180700e600b20640180d00017400c250180c4c484c440d10380c145600300c0e000d98084050180c2d01d101c606441d60400070b00790350301c00c000d480502003e0002480685040d88080340d2020b6510000704081e10b40c02c0080345843c0001c4ca1140c44c401d200700000c20181100c850000448009a41d8a0450380d203500030041d84080c00d907250880ea40c0030010003403007820450200c130340c8a1b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 625934280 1250 625933030 625933039
    0x60c020d0c0e0c090406090b010816050903100f0b1f0e010918050907091b0305041b091514032d03030f01170a110103020f07020d080901031b1706 64
    0xc0d9580807030404031041030382c1c0f80188a1011401c0e0500e41001d04c10300c801485840741c180072400b220400605000b0010f03040d107050b81001c00d02071421754046c2c000c03914002c501800319401d040505407500001d251691520b4501403d01c52902601c2c98012580c550600c6040380d803034401184441c5c140e504000007071401c3d0500443d094001400a0400702a03841c050b5950808106850034000d180d04206e12a00000d1030302c0d207000d0305030030450b602c00009004d220f05820002056116401d04034607407408400340c03582c1000c501d140411049201c0c0c11401201d41c0003210280016101d0781d190054105004160350154401582e003800340488142410b070300b008080d40481100461819103040d17600480b03800020b02120001004040240881c20060300b004801a0004d03010f56501c0041b80040c46c0d010a040607000300e00e00051205500c1140d26840d070040c10006648840e10740341d101500301000f6140807d00d0302201d031000b075001d007c004035280b00558030b90000fa200e241c4840d8a1030000703042540c20 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 625935530 1250 625934280 625934303
    0x50a0b0a091809200f030a0f12050405040e0a0b070e0904110d17031e092e0212060405070c1a0a090606031112120f0c0307050a200a060c020d 62
    0x12800d0b2522806801031311152000e0700d4001142403240b403030741e04000607009900c0090440701144c100c9008600c03295104024800790620602d08441d42d000301d4001a41c05850200001c0214500240da1000d00d4401e1111b00165030350104142c5081c5610400346c0d4100c4540301c00a4001707800355012a00c00c610082c52180c510295480d282000f0034268a10400c085001081c0000c0b402a8401b40c086000c1503000095980f421031003154070765a25101036190104402c07900f408407002d4030248020300101140841d1a8500f045101504200c10344695005602d03003404a04001c1c80f030901c02d07e04a402441e034900c00001d04030010281c070b01c010104841c40b50384290210001c3c5003030003840000c43c041c103400700e04984002d0400480111010980c0c4e92030b0700980302c1c100d03980d56007020764070785000c41d020041d201d500d00305e103441c110b01c41c000006086026803440082000041e806240c582c0790125200c0ca0508101810311044400c240185404101d40c078074040018a0485080e0003032a02c9810302c2c040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 625936780 1250 625935530 625935533
    0x50d02031203010303050414040612030804061407020a170a0e010c1704170606032d0f0f011e380d03081f1d09120c0601050a0b0a091809 60
    0x1c2035003080c2c008800003100058100440b8200012550368101e044500708011844c060b460500c0000c074072801020700c44d000f0700003400d0040c507520202000c40449103640c1e143c035000350001c0d00c50b82a40402c0307510342510740206048124a009032202e2174500d403110701d111710b090001550582400e80b0f040341c20340c10642154a00030280c0d4044c00c010812600c0001101d80320310145410100d00410a9019500c064201c200040d2104000241800302c507015060204440c0c40c2541040c40788160026035108000d060703440d0150551211190301107a034510030450360304990010a0b01d080501b01411004075080082c4140400805030300f1881074161900803000080021402c40c2d0301c0c00800b5004124900100030101076000080e4806202041c84102194105400b51a04080c0c242c00c0500d206580b40000300444401c0100c0100c440c2001040c50b290601d030418283c0e60b03d07090080301d004402000d0000b41d160407880c151400003a26480e01d20a00b030420440600d92040643c0c01e5041c60b484860640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 625938030 1250 625936780 625936813
    0x22d0f03041e03020709060503030307080604020c010b1e0a0803070305040b0a2109051b0303070f02030f060a0c09050604140d030201180503310303050f071a09070e060604050d0203 79
    0x341031280e0091701840785091541c40c211220b6910040c00f81c2c000b00700700142554091042c50303100000300c07001a2a0302120125600405240c1c00ca260010b00704540c0d1040079005800c01c5d16036020858580c0d00b001c0d11340209503164016100b000740454410300082c0000007800d4040c00c5000001d01c2d006401000c11a218010038440850180c2441c0d03840d40c0580c1444814818420399441b41c80741f0000b44c804100210740d41e0b2043c42005400140d4003030051085580038400080b65510100c00c584140c2402524000107122040100010900b09000042c0c1401e28105440840301c60346a600c1601000c502840703120704c1381ca0006c908555031014a440c098440d070b01c2c07118002d4000c030020740c0c85030040d003c800a00448020810b024410b5500303030b0740c0c610000c0c07000d520580b81d061410a0315000c0c071071440c0f0342e20700400f000103000490303006a00545034201e90f016407161041c001107510055545444c1d2080800907501c85412031070400040c022800c010381c070700c20705620150840b004180d4280008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 625939280 1250 625938030 625938083
    0x6370908070f06060b1804050a060e0c0a020709110307110709020c100506042a09030503030705090102060f01030203120702130c110706050406080a09110a0603022d0f0304 75
    0x2120300c104040501424488030380b00d05130207814903003180381c80c0c11a40700365103030b160000c80c443c98800d50b11580040c180e1402ca42081e0004c101c4c140c901034441c01c01d51420805508960b204070010b124050b400100c1d1103040c0544003441c0b0320644030900d15110700c03604076401e600f0442115480e01c00c000d40001e06a0140c801480b6102c5220301422080c00b01c030303004809880010341114480c078181106a5103c0c060342880318001074051406c0310026170303010415903402030968009000d600010003000b8410340c02000400710100241d099a179207990351550505519428007010750140d100060504200781c61600415400d40000c010080d5071003032424040c04c4d00d40480f581400110003248001460408000b880060002030078483d04247c1000801020103400928001e0300c0c030b894142c1ca4050092840c50b411102c840034105180b213544890020340a0343c031160080e41c414651944818400910395024160f040c840b0000f68a40b1a891030100c3c8030303400c050000c0e01c90081040c1c002c0002c42e00344560327 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 625940530 1250 625939280 625939283
    0x1303030b0d110a050d05071526070305060d051c11160f0e01080c040203060d020402030405060f010b041202100201180b10062115081009050637090807 66
    0xd18151684001409410549a80181c1c05038503034102d5013002640101c1c0500c12340310704004520320108121011100128040c8a406450000292000b600480d01c441c0c584108140e89003070065860340c8007401070101c2c8240e80688160090800083e180010340c40030048207100745440f6503001c540c1052217040450384402c5120403007134100e08114000041c15090010912540c84641d00e603d050b400b02d44804121100d81d20075a800000540c0f20780d00c0344148603000360090300440d101e1602d4030301a40e03200c50580b905965400b5441c000100b01c5203040407103040c0c52082000103080521982444011001e9010200555485900604085506440303030400540691080310b024102100c043c800803007250000c0f4200a0462401c17a4200580544201002a04070001880c42c80da182c4081d2280c00316003000d030aa01500300380c02c1d2604007903085200146d00950968540d6102e0440220a00b0256078203102c0289454100c611400d4046141321458950483c0c0440c2004281d5602c1032181d004480 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 625941780 1250 625940530 625940543
    0x2130905011706071e05070b0c1c060b070803060d080c15070c030f18031707060f05040209040b0a0209060a1718030306130e010e0102301303030b0d 65
    0x108142c000aa08500350441c0c55006003507541810100100225101c2c2030205c02800501000e2865a210780700b19a151500050301e07840d070b41030064400c00d10f40d0110002c03241a614210850500c004144074580450300c80e0884103240029655801d401074000800d01d580c48241c0c880c4060104507010010710003282e80c0d0024080e100001040b4a408800c082c003000100034041d03000700c000a401000c1c1000e403010f98100304c000c103013682d000006600c01607000100002c440b4071444001c1c2002c2809030103018410041481030b110741c1c0c0c1d02481215001c83c1c01035807164202000c600403d0071311041c01c1d000110030a000d86056030642c041030103540038407500c030006108070070760300f0448079092080d54002c1c0741c0e290062242c46040542c50ba07207000c0600341318030485c2c08001500c000d500c203500c95981c0c100701c000240458101c0701c0602d8003c0d0422041030725841100b80110380070320040755580d1452910001e8071350b89600c68034040d2600f4003100700210300381503440140212907583c020301c80303440c0e80c820030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 625943030 1250 625941780 625941791
    0x319020d0f08060d0206030402030118060b010909230705040e0405030301300602030c0702030f0c21060403030b010e060d0e070f080a0b091c08150a140f0103021309 72
    0x540c014040c1c0c00a0402404100020050002da6544c66086a049a404651240d129100c3d40000f0380185400f5150301d168100015084d4100030b40c81c0c00c8040595400d0f02c60362285a07803012410b050390031000308900b0508a100450740c900f0717030720704140b0307005041d17031034820f0615031503c180e846800819181030f11103038008801080100c1d0b540b0503011642d440d0015055a1620495440140d04410b420003000e040c2c0120000e1441443e680645287c04e800030220381c0600408642107844024204241d0700442400312240301780c0301203440e1441034000c9100285004d0b940e5840880c01003500340c15940c10040940380d100035580e00c1d0030280051403140040000e0880c1c900344c000e80341c04419444110500d038403d004101e4800042200c14141d900320083c00096511203140d2410003041c3d16000c51005040d2500b0380700c181d8130901c8035104010b600d0349001000c0c3e4003010484074034498030640300780030300c116400800d40c10500209006644181800750400c401c1c5400030032104081e4100c02c811036642d9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 625944280 1250 625943030 625943053
    0x90705060d0608121603030902042d050702010b01080705090607150b01030f18020609040209030105040b0906011e03080d143c16050c0316050d0206160f02031902 71
    0x44c007260320a18080c480c02443c1c4400030305424604100c484000d800d142e80d0380c1d090000c4d502c0e160001003d05080090160103a10901e46140c4001c260110103410b1904e02800203804a00503c180786a0810507110204a6a900102150076a11480415800c100c00780708180028401e280305901d05400524003148000c1c1c010300040172101c40107000d4a150341042041c2030140d1a800c1d20550b03054040d14070982d20050031001c034020f4400d1884041d015860b01040109110305102401e0203144184203503451640e8a40e010b074407082101c05c007030042903002c0d00c0400c001440c3d40014406007441d15008554030140d80c0d40f00d04010401c95990341184c0c40344410f4404030703507480300300d642d1008014001956007030000300251485400a10340703501c030301200342016100c60094082c1d8140c2d18181d400c8070307a40c44003066807a003290882c1c1800c4405100d443c0c4070118003400420500d11480ca520001d08841d040e101049401c1051403449905502082120a42d8113005042c80c2d55420101e800070b00c0c221524 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 625945530 1250 625944280 625944283
    0x90507020d03110d02091203030426120105220e06090d03060b030403030c02071206060f08011406270c0408060702030a120c1b05100608011104050405090705060d0608 73
    0x104540341e01054a000c80d04801864450280d802c01800c01c8001604ca01e101400720754181c1c541c03403005103140b101008100c200302d00c00c405407041c04020740d0b0100405141c5030040d001d83c010040f04c0611102c1c8800144150304101d030b0200d922510036410030440402c00d078044422162079000c8100707580c011030304010f4886070400c8014824401441c00b04062031402990143c9400701510082c201600c400040c1c1e9014800c00c0000090304005841c0500210b00c1d00e0180001d0040d407064a52401100c000000c22800600c98281650244910042c46550301d00400c44104d03001d43c1030708040b01d281402940180001e103512840b9407400280703540e03030f82d00303006c041441c00710f0003010001190300400051103507560000344286001c0500c0c501140c400c0024a042d54808a500d45101710031010b0507100007400b200182402759050041010449940c50b0aa841e0990340c8100a24a01e000100300402c0342e03040070b1b840140d104889600355003860f9255800220182d20010701c0c171007400d0322160107010000c070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 625946780 1250 625945530 625945543
    0x609060e0d061a09070f0801120c150203041505270406090e030309010605121e03190f0e0109060522050301090305040806060a03120509040b060a03020a1209020a0302090a0b060409050702 82
    0x2041c140101504540c40c0c0041159405010b03098122074a150030004024032500000050003a02070811b0f041740781d04e2f400039600e4100d4800c00364448203035045240724600a500300c54124403071034401000e649203444402640820300349203642281c0c1e44c65001800c1c1c0010b200e48a101490580034594a040c070455860960300d15802640c41500da103c80c108131868001604a4103100c20904a00d82d880508241c41c154024915986000c1d9900ca8034403401c15403219103145202d8803a03e44111090016004680040c4d445c09081c003c02c404100002e040800300e441c0003600b280103503e10f01583d403200046400c0d00e003080e0048000c1507001c54240500030b4240112a44a0802c2d556140c00d0307850b5886241030420301d01d440c0801e004000a1115058031103070440c0103101d0003d170001d5664a9100b00003002540a0071181c0002801100c41d0013650301d0b640104102d0a4004100506190542d000c1200e00c0c0000392460310b0700b85c0d840365030701011385465001c0c2000386084038000840d890098000303400c290 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 625948030 1250 625946780 625946791
    0x20a031a0f030a0209040c0f03150e070608220210030e06070c020609100c0f030923030307080a1b0501090b0f0f2d040c0603060f0609060e0d061a09 65
    0x180d00001c20340d480c001a030141c0350340c0444510b031040d184e07800c100d240220b19400a03a901c01d49800302000b403000002c0610004a000c0a01300403803a21a41030301c0d00d500d40b6014590004104c0c01c003143c605650040343d034a100e00c04002c03202c02d450141e030008100d038105200f820b01294440d5501c0c041d100041c001d05610032824182a50644d03060b9000441030301c40e010b8000e100d4410480c160b2600c500c42c542140c2d00350350241c84465008a103080240c9400d00c5407054210700340d80c56803202d2801d020f0414440c02c22101500650810106680701690340e0058007180081003004c03040d00b088440070000001e5001c0c06200000f80700d00c05814244005e0400070440300c405506070090020345d00391200301ca03500c40c84040410340ca41d001c0d140301131a00c0b01c0030084440c030f03200000b05000038405e1f114400c4046500715181080110359903002c5042001e9907100c0d0b040450886002003203c54001c00c950022810000e00355030300d1305220795540040350000c0180e050003103000408210b0f142000c4000e0794008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 625949280 1250 625948030 625948039
    0xc0f060105040e0a03050f0733050109090c030f031403070903020f0d23100c020c030c0904350c0a02010f0912080f07020325060306031e0213020a031a 66
    0x118981700030340a442070b05545c480903040040c15106003c07080f150003a0800d49214000c10b044c01c40f04100c04c203483c0c0c80d20307101503191400b000080c15618520603072800680c40081070b01d44500e15150304d1041050000c0540610040c2246010103050711402184a09115246c1c076011500f18010301c80152084440783c3e000c1c000c9444418045151500e1520314a007508108003081310760043c40609200940b0010300d411420607003012460303034001c1007a10440200340c08645c465498101044100081941c01600c646038400d45126604034024888424080c0140b003000108048828a0304546c07010940044035048800b00c2c5c81150380c0316890680c180f10a03d441006a42000d4003001d25004016006080d681d001404050718100e4005861510340c000301030f603210044d18441d0032810490040b040221250102010132000c0c024805c45044e6501b00c408442a225194a074113400a02d50070166800458510402c240040c00d0008211006650358080361000c501500f05810a8003850b065108 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 625950530 1250 625949280 625949293
    0x40911030c040b0d0608030a030605120303430306060f02010501181517070305121602210105010303030b240a03020306060706022808100312050c0f060105040e 70
    0x1030340340740400c0d5029070318a08820741e51800c41040600040c02c00d9408191107020114610190f25019130100003220402e035031210a03034074001c10310f076240d1004440350b10606000b13040c952015a94581c010420021500c920304041c07900e66180c040c1014800c0c12100040d40b285020301000b0340c010152190a5014002844654103040009a41004481d0020505940ca900381032180c2540401100100f4801e0710800042c40640c010b6501d07542140019100d0340f03d810409140b010140f011264410150a94261811705550801451040201c1c2100c101c0c1c80621807800310840a11070309000b11320035100007403002408001d00488003a41803540401002856250002c0080c45d070803240700e081c09140044c0e0302e13503480c000940c03540520304010701240c0c8081000d00c0400200d003991080380450031400c01e01c0b104441c5007100d800d84c00b155064142015040e04200207541c0700154560050f10703081107410000022140f41c50f000c01c0907004003465101000401290400344602800341001001030103e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 625951780 1250 625950530 625950541
    0xe030714060f01230d06021b071d0601030e100e1c0c06050c0408030a030609050f1608060111010f0b0f04020c070b09011e0c11060a0e0d140a0804091103 67
    0x500710051141d441c008000c4d0b55016503030ba80400112000702e100038815412a181820014000d40000300341c8a003c81100512480c984000145401101e410030160080188890307044030030b06501a00050505840340301134900d80c0c4051007d40d219440007400010400d00b4120403514010240880b00c0c001021102110959540084003c400a410a0001c40c050300c850310094103503c61603008510701d001c08945d400c1c00e41d0341900180100c41c80c19000340496140d1600c40925100b055540300003550003002c05011141c042d05886500400c141081300052020724005400c0d26603090f07510300034583c0c42c40c002d0220302d05050020ba10034801c1e2001c41c108840340b17140d5580c42e0821300400c0702d01070340420030001d642e2044444002680ba130300800c45d100411208003130141c1412000884121a1200d540066030410a0076540d1805155443d00040c031090f40a0107141d9490f11010b8032041400b0b8490300c0f204400700b00c0302c2030326849895266600c501d4058050100e0f85024a00703040721804109012 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 625953030 1250 625951780 625951801
    0x1a01050f090103090f02060c060702070b090d030e1305011203021504050730080301051c210e06121b0c0a030e060c1b010e0409020303030408090307090e03071406 71
    0x11422074081c00c0025440f001800d004003480e0340024002e60100d000034070308101380070200d80140945071350303002c440005880300c503846054061009d40071b400c08503451147e00440d2140d05d074001d03200c101401e0042600a400220b800b5240700b40c00c41d040b203c000c1c03499041015410440c001f6403d6200c000602e05041c656280c03030b210005c5209840500e94010005041014041d82c82018550250702904810005192000180c0c000b403040c02c0c0318120400c212640b55051001c4404455484001e6008422800740342c95100c11005401c6010490b02000b505e0443c2c480700700505194509840c00703100c0d4034260b090f141c40d12200c100000c05003e410301c01102900300000c0d40028499150070042c200f69500b80103e0064002c680090301c2d248100900b0300e244444800700441442c3c1c0070317610070031603580b02d100303000c2510300c1e0000094241c1d04c1040014045034560010b80003580004003980c03c401c2c1e4803021a4140d95400c0030301260703504001611410858281d482590b10396401000d0701d4039241022104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 625954280 1250 625953030 625953037
    0x3070806130b18030d06060311070b0109110f0d0f051008030d110c060f27150c0412050106090515011205071b050610080c060d0b0a181a01050f 63
    0x80201c40d01102041c03d01c061003449400c25407104040302c4e00c400c08800060003401e05071250801013444e21900b0301c642c59084085950807a00000d42080c031364a014004801050040401364800400340080094501d859000300501c2044075404184640341c43ca050086410141c404600d00a010b8400c101041c030200c15034880883c04000003e10192008005417a40b05405032204103006803400c210110b1912003000307000b40c02010220142031ba8400030403180703038032181c0006041e5000380c80301d1220680301c440865000d404a003060341481d03500c2400804c1404d0180c01242c059440741d00a014142042c0b00d40d544c0801c00c1c4035004000881c0c400082c00e0750822010b421520b81e02d8000056240b40140e4084030840700f00e003841000c40810b42002070b210790007951500f41d1581c0340c09001030a0000010300700e905100007070800c0e00d09003103412014010103150a0094003c1c0101c0400918105000d00f01c0e40310178501400840d41070248500c0160341180b554066043c04030134415406040b07980f8056 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 625955530 1250 625954280 625954283
    0xe0a09050d140409020c0d1d010c06050c0405040c120b060708070201230406020f0c0405010515130b3c1b100504030e09150112092a050307080613 64
    0x1580039100c0742011003040f8480d90b08000d901d1400000d440e11203280000e04840d0b4103426541b10804918900c0b6401d92060315050101d0004250312507640110300c041d84142d4000090f40701052400b59104003003029a0b0b05030036258045a422222030300969510300507800d4140040700d40d20301d021411358074642c950003217000c00390400c00c20a0058112080078800100c000c402181c0c1e0f55145e81d44c1e01e030001c2da1403560310100300381c500640390078030802e0038203001c0c45045c2d074401060a01149650440700505810100c03c001c0f09034040840081c1160000c3c004045001242046019a450061017500f0300031260314143d1621251035034010881e481e000075100000c4016500706e0941081400007407034004240c02d5281ca00b40303400103103c201504068110351000c0c043c3c3e80c4040a603a100640710210540e005140d0100d0042d00e0510a1910168004070495100d01c25982050841e04c0041d00c030400f0344510848504040070060101d0f1804020140003000c1d450700900c4249441d141003c06601400c50 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 625956780 1250 625955530 625955537
    0xc06021b060414240d0f0203010312081306060f1505070308060913150b1203040f03230d0c021e010509100311071a010e04030507030e120708070e0a09050d 68
    0x31020110398804002c1c0c0d1262130800410b400010305120100000d52003103840c1aa142d16040b4205080c48290094a04880c4c00c446c03440c44a034405882500e10303510081c02107144550410030040020541c1c41954090841060391603c2582090303410744400c641640c000303040c06800d202201c000383d03200f507485900100584a001031034032483d041001080000000911407003100c002034140c2c410b0b03035120400108003117070160880d42d6090049512803245000e4140280302c83c40e400c0c004200603850a510b01c407481c4a010103c0440c00000c7d41c00c2c00540115003001035410300c580815480d014444a000c401080d118038510201c07107001034113038440d0411242c01031307a031801e140c80403038082d9201082440c0e03030340034641c0e48501d075181844208456100c031100e07500301c0b2000450705450410607180b2580d4541c56552421000781c8040c0c03203040c000c00304594400b13500154100000003d01c4144010710000d8000c00d4414180b1140c4003a9000050200f00400e140903081030220300c0015110690745e5007400e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 625958030 1250 625956780 625956809
    0xd030905030c10050907050f010804060b0609060304050c03060a0b010c0320010e0d12090305030403080423010902010e04111605010b1f030b0a0506030c0d090b040c06021b0604 77
    0x80d2080c21405804444102ca0148021140100416800c454417880d0200706131139020703840d2410420002501c0c0c0419000802400000d40020060381c17107441c611800412007418020650001423450b03200300c8048842ea040301c0310104550604200441d009800800c042c041c00d84003030002820440b50340e03c050208071090010303501d414610500c10120500c020000c0c8540c03607040003e141d50300060482d9200180c64040c601c0308000c1c03684140ca5105034507964040c5542c4698a081300e9008011b04165001c4140c10b00b132459094414103031040722008000081406a0140005041c06040c0f200c0140600d0410024101890144084a1244125582c040410500e500f02a401000c21400403904488801212200c0000480b6001c1d0320003459541402050110341c18405402c070f0504c203540e00241e040c000b0a0000031010090404070481030b000056240b10364860b42c02203c000d94094462007030112051003a2541808a140c0f880030301c4002003126021100401d540b0b01c00d03442900c40103050031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 625959280 1250 625958030 625958033
    0x190f0e18072705040b220c030b010f080f06060411091008010f050301140105270405030d0c110d030b0102030d15050f0114030a0f0e0f07090c030b0a0902130506030a0f0507110d0309 79
    0x803600004487d08040214a182e40341c0c40c0c205145902800b4500701541c0c0c0280c00a0b1601c00001d890ac8014880009040c56884400611000d4800800c05141030003082c0702c0d410460f103404c403811030103c4c155690f80c5410751605020100510464001600a90404030449000e100c102416811180309841840841000404c0a8403819003103054010800b41a03041c00305004001003c1c00400003400b00800c0358242c507400c03d450800d0760300408030090700065040c1c0020f82c01399020411104c810700603a4604101d244002c801c48811150302d00080c203e214007841380342480d04809aa40200b03080009903000458905242408000c0520043c40c0d121340c010300c1841a15005042d092442e9000c64031565080a1503507151551401a140340c149001e685864051103401500c00498015281c1007049080c200c4500195020442405250070700900010b01911154011803241910600005041d00c4905041c819603402400315010003401080a16480e0800f0039801e41c5203949040024021005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 625960530 1250 625959280 625959331
    0xc1101031404060204061209120f02071e031a01050a090504060914030a0210180305030a1401080f100903050414130507050405190f0e18072705040b 65
    0x3080340c00350302044440240003c0003d2078002e007050782c5081d1076800150320740e5a0140c1c01c851000001518140030610422a864050300b4420301855661065924840d140d0a01411200050b080d01c040c10412100410500c01185800b05502c03c20045603455545403400280d88860580204001a5600d20109081000c60360102215540c0613190341c0d00f001044e107105840380c2020301c0100250280312464100ca1300d039445006040c0c524103120300e6000c2030985040b211307604001e181203480c039038a69081d101c02c060b46003814000c0000500414446200c805000e0603c882052407030001c03400c112013100081d8002d402d440981d81800c00c0c2a60149040c400203007818400c000d500810b0b490407051001d4940d02100610070340b101562101e07403840341d80700010b4a101403032140030303680640000d082c040e602c2380c820121381004101c054010304240c09142c8608000c403030f5210301c007600354062035142400d03ca030020301c502d4458080300700440d1078a902e880203003010003807040301088600d2500710f405059 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 625961780 1250 625960530 625960541
    0x150403080711150f0a0506030c01090b090f15091f08060103020a020309041d010e07030b06100207170a06050c070c061b230f1b040b0d21080a0902010c110103 69
    0x82c400d02d50301030341c04e0213940e030240c0e400c041e110815014200070004619043c0040e540c107800c1e4069442e03c00342442d1440b90303034203900000c0100d42e200d02e80858054843c0e90312070716039840e10060710040d5030700c5d0804400c0000054440802491002e49031403246a6075400003945503011b0821309000d070303a541480404034258070a06042c0e070390051602e40c2e800110010902c21091201e00c004c001c002ea0f02c555562503945803aa40300091440e0b007101c0010f0441e0409454005414516004555000340c9484042c500910802640401540030381400c1003804a40d0103a96000080300c040c082c94600c42d40ca8412029100740101ca0503c03145001c0c041c03541003662000c42d4100c0e0040d80c040d484a45805141c01c61040e501c4c2d145509204034420101d010902190702081440b12342102e0107100001c10520002e0300c0c0031501c0035400301c40d842c001c2020445440203511000c2044402c413403000e04c000c0028022080107802030280b9841c2ca0203d0700141d802542103100310342c01815911220800e400101c0c003405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 625963030 1250 625961780 625961803
    0x30916030c061b24111204110307080a050109060c0c0b0610300c0e0d11040912051902060603100506040f0c0c05011112010b07020117100602150403080711 68
    0x500582c2ca5034a0080e00d80840c0000813400810700c0400011130b0000c13140d02600d5290900000e1b444081780000e503624590050013100038040d00d40503a5200b11460410010303c400340c401340d444085850070458144a009503000740741c20104000b8013261a4400d0b80c4e00001c1c03107940101181e20801c0300f00d50007040300703007485c2e052003405054003224034403082c100b01c0c800c228200d010740c02c020b41441064000d401e14061208058082c009000309070b100d010240c01c202c1c080c0b42c1c00980d202c845102054140031b0210b407048031502c1d00b690b0743c510000d061074060000d010000440d0809424802d540c0e4010501a0b056521484c002ca001d468160008004042601821045034500401c403129560880303c1c011741240510020056498890550400c034410255001d19030381e80d00c0014810f0090b050040c04100c0c0c018074180b0038404805000c040740035401e42d980c0000b1008c00d04c0420007140e040180000c40e5111107283d0f07205050136034010702444000303000482406060240800c0041c010400c1c5440300b07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 625964280 1250 625963030 625963043
    0xc1008252c090106050901020f031810030e010612050c0307050f01030902040b09010f0f1a09060307180e06030d02010227130f0b090717010306050a02130b030916030c061b 75
    0x3d581d00d000142213035010680e62800341c01040800c900c107000120507140381c0716024007a08000840c150403c0b41340c490000400050503034a000100d00c0f07503004d03c1058094011554914050344142c113026180088000d021342c8640e11406048c022034640342c0c003100c18000c080c2030100384403001c0c0c4001406010559005908003028a0000901e1100c1284050446500035000420207403101c5112080c64140d05050842d1a8100405811410004000c591150051030580b01c17291522040301001221607001e8888461a4018441d03146801d00420f03083d030983d40021494204801d08805500c00d466001014442150906102640350b00c410154801d018540130000300c2c80342d411a10040c01c601028030300070000c0c1c100150302e00d805012004440d44d10084107014036031071981d510014000040181285079001c0c06000e01e82041c9a0022000d03040c012180c070703100c1c580300718114901590f5800a0507154440032081010403400d40c2808103840a51400116800704540f028807400d81c4000010800f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 625965530 1250 625964280 625964299
    0x100f18060c08130c1a040b18030f0c01120209060c0d0c0501060b090d150b04061712161119080d020705040e150402030c1008252c 57
    0x42003495880140d014000c2e0b2070b05551603d6581c0702c060342c4105198010303d058960b100511000e403103404d45010a08804208602d4140c4039070000d07103d504100302034001c0c8c046121140c0310303070302d418807201740004445d50062402501d018002450040e10030f9030813804a60000e4011040d4540308201c452003583e0f48220b901c03442182100038a40300c05e504041c0c40f55442d100c0c01086007000781e011182d108400400400510782541c41d04c0c8060a81c40d441d500426a40300e11045a0b034507140100001481d4610500106608202070181441e07201805100751000400a04d030105000407030722401c0c20703042416080700703011700004603a490030305e28030780303a000700384004005242040001c80c094049101d030700b900c40055442c030901003900d652205044080c2c000e0100c0d56a05000002c50030761250004084030a16000a40801c00281c00c80e2079243c005002d48041000740c011030500c000c01c0381043c01d80743c1803103002010001d01c5045030302c5120340c1c9064014620040c0100d00910780c00d80c080f00a002c0e505 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 625966780 1250 625965530 625965533
    0x60302061204051b01080601080a060305061906050609010c0b07050403240b030a02030c2701090c0f11030d0902120d030509150405070b0a020f1c03060512100f18 71
    0x201c0001118211001c1c07040b030321410407041038896426084001a103590b0002d440c0c41c8010f58401000609840400d56540e03800008204d08000e0b0501807510321703401c2594040b4076a48041586c2c0b494110300e02400301003041044d2640e2021000501c5504420031031803540303490501702c409110f41e40c00501074401d0007000600100c6040c1480d002038581c03081c200002042c0307200b419214081c500b8041d5054100124110082c14045100000b461010b03400686101c01c120384166013400c281c12180711580c0d140d0252900365041584202c03c0d460701c3c148a60b03003502014056549104440c01802e249489070423003411901da080c011102101c4001c10f440a00c00034a00007002840101c6840b03895205d00c184000201000800d59400b031604500a41019400c0010024050f13020b01d50000031485040e082203004e00c0c091000540c400c01407007502c00c0b08a056074004094035179a8010710b02c0785d031462206098408001545c504020001c00b40803401102035454080103003c0301e5014008446c0726042e060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 625968030 1250 625966780 625966807
    0xa1404111c0204051c03080a0e0a06050411011b0b01031101050403051005190614040e0c0d0501050613050c1c02041503391b1713060f09120606030206 66
    0x140ca209407512000c40170200d0303440c00020800003001d004030700b804c004034100318425045580020082c504a0303e40101a989250848104550a48080c203050310052655a400040c8402a400300d84051036218001c2c1c41d595a11801884010030402d065944010664040c005440043d5000820f89803401011504003001d09012510a4502038010300040f9612000d4801e850940e44000c50030030744e4184100901004242c80d1a40381803e1081c0c8810075802e0b40c03680540c0c07000b980704200100390350a148050094805825400e01c2c0c41030b003840204000c0f0001c001c02e0b500301e8500309680c11203480059006c07400901c202d4010700f0303060281c4109102c50702c1d0150807942c8440d03030640303050100e50304284c00d03000317074854400403001050b9160b5816060140b00341900d5071940e50b500c43d01c0e910b1800c140d0328811f404030f1404441042e20b00118000d51500000900d0382e00400660400088000404000801c504100d005807200303c41e40303910040c103001580c0c0c080d5014560150485541c0e10b030103503019 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 625969280 1250 625968030 625968037
    0x70513020a0801051005040b090a170a0c05180a090201090905240a15050f040e07090e0906040b1303030e0d020705120c010c0609050f070e0907050a1404111c02 70
    0x980842c0a078400050036080118131448000743c10f40d2500d05283c1088441401c5901106006621480300e51001c100c1c2803051540d510303a48035050082c403044807a480d008483d01c50035801701c1e114a407030000100726000340c924130341c2d4062602080042c00500030700c0161514480350b08131010317480c504001c1000b4200500c01c24505008561000291072390b18000f005008a440e00912005800c4040c2c419141406500900740300c80441c40c100e03003820740740c2904a500a030100d5200000902c840c00c204141e07044010101e4124103c1c3d0080c3c2400c1c500ba488001c401c0001421100381318448039044000d0520a03032019080141a0064460f59600341c54002c0d940c1440b07000d005c2c4510a10084504070704800200c075102c42c0c406031102000064143c403542c00401d0200d1702507500b8060046d10011501f42807000501814135080c6a001c0b50601c526400d14100383e603084180030364181a024801ca5160a2400f01880790071030b0041410000820584002d000701e4420030b107006803802c0b0036840800c458014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 625970530 1250 625969280 625969297
    0x10f110c0c03070f031716060c1b0b18010f0501030c03020a050904030f031802041803120605010e0d02061209033411040605130501031e022107051302 66
    0x480e00d00d10780304401c1580318412886242c0c00c881c2c440c03c041002803e500d01040300801c2c4041210b06120313400d91003d581500e52442103c0f01c960b19061582000e8001c03e8128449201c00c140340034802499840e9407101001515a025125198014810246003500001c000c009045010320035941d5914000da20302201e40012407007202c081401180d1400e0040d0164403894141d5107180009002c001e090f0000c0085014040d83e0300080080c2c0400b5880310b01a0140851040070032201c10403160800400e01650540304a1026040000422480c0c0c0e01400140105a04a13107401c00602c1502c0050030030310599103140c461003500b10400c40c2820300400641400c12800340036502084001c10410b20304030f03e03020036a04203c0c01003108408502041d0002c6030601d40504006159038481c4000b450400c556085580d05503240e40041c4100b0418075224100c1c0d158643c45080301c3d000c581e00144140c0c84911a0040b1000500124001d0210803c042001400041c021411800b80781401002940c0311440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 625971780 1250 625970530 625970533
    0x1d09010c080405030a0e0a030212031e16030509040219080702010c0203040302091512070801020c0c0906010f0c06060e01030f060b0108090607050c0f0607180e070801120302010f110c 80
    0x41010164000c1101c0351296503c540907504d8112240804d960b0005040781498201e2014500440141c03604500300003a50007141c021501c48441024050000e20180d030030150300581407100444a0440c0b00c1d07000c1d046585803c0068a4045160200d0b00901891300785000c0e100a80410ba094141c0002140707020314500da00a010203404000260f80e80e10031880020b404c090340300005000d45100d424041d080b004010040648084404078662401170785170004440360f580010600e20842041000a80311523042d01e5480b414a072840002c1c1c1402d4034070012a00b0f02c200070508004111580d4460805040d1030590a0101c3d6101c0c05e00e4282d120102e80c049551034946100024158007415030144540c088000a054940e203841c0300702c2e00c942180ba600340891140080c4801c94940c00c1c404940f180d01940c0e200c00b401c0800c031145048428282d03000380031003031032803080c4092540c2c0901d6460540b101c01e6840d00250540e46022401007070010016091035103480340c80150100504000c080380d01c0c0340030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 625973030 1250 625971780 625971791
    0x80f010906030b010b0304050c0916091a0d02090a0b0c010b04050108030705060a0c05091c06060605251a0f01080c180a0506030c19090f05010302010f03090204061d0901 74
    0x380850129111404041c20b030708031080040042c412840002e42d03200e40310b6810b442d2094500c4022500071441a902001c10701030380031490440d5648020090000c203800000d80100034071400d40141148102d0000107000350f00090340f20126200c1c0e903401c10080a0307030f1999a60700c13500ca803d061b00070042004001c0c4128140400000d01801c0007040e258220b8021019001e00c2d2111703514038000300070300301c2c0a0341800070074001c4a001d580c413417000c004004040305d180c80460901d460844115103140c2c1010782449801c0c0008804d0390441102c000089015002c1c03641020080c1c1000c01c184507040c410801705402031020045245c48849016048808541c00c0316000784030503041202e021000358082031200b07482800079600f8800303500000e0b040365014003510758802220300402c0350300511a0061900030036404042242d03811a120300d0701c0341d4065040402c450b505541c0002d04140c6001d41075000c05840e00034034025552241c0c07240000307140011040300300c66421030031741c005020101c0c0d40341615482c00703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 625974280 1250 625973030 625973039
    0xc070507030803070201051518040c0503151e04260403080c0d032009130b0d0503071401200a090f090b0901080109020d080d02120a06080d0e090117030c0a03080f01 72
    0x504d04035850024042c02c105104aa127440d41030100420540d800e03a00c407040050f00e61401e100050b104901541800f28501c5d1940c01c0782c0409980c10920341d001108403003000301140c24102d4a610782c0741c549170900c4082c401c2500f480d49900680d000134160120011740324584500000d449034484d90f4036101840b54940003205000384181100c070140e07038500100445542c52504a1031040c01b41001200001c040f800f600205d2268500540110707090743c00094540306001c051090122642000d070024000010310068080d62820001000c52a0f12804200c0510303407402400408050031071f5425118845030b136820307904050001048854081d4101074004118401c042c001d21810540240903284a0103982c0c0d2955441c0e80410303140f8110690900c805841c460701003107071a016060920300450400d042009280c00c181c610b098100c2400740d0000d076a040d50b1590001281118400603042c0d81c104a11b48103a41117129003000000c042c0120b003040c5040581200000d4001c08980400c07800c2e582e03c070f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 625975530 1250 625974280 625974301
    0x3290f09070e1002030f0a0f11030a020a141005040c091a0a061404030f0c1412150a0e0f06070807080114040203190513290a050c07050703080307020105 67
    0x6560580c0082c03600c200b00034003814566034940105460344122803410071a104141c000350486220340300010901f40c42d001c41203a000302020801001c0801542c0380280d00c0101942ea84901c03d03009107940700c3c201007051108028816030600101e4200c0c2070003a4980340ca4484e10718445070240149003031400e82e0844240da012820020000c00c080c4c105201c041c2040010b0790001807204070503142c0002048044005180c10106c0c803801442101300101e1641000700b0f501100c0e029071a4240180c0600300280b010030000600c00c0d03001e40541e00c20002c6919291904005054078a14440c6584101941c10500303041c0020040c1c450480b40c0e541d2041c0c0c0d00d9424080300c65040c20f2050384080700d504c01c141c030414909030380210b800488006c402010501002000000d480d400c98281c081c1c2d00d039404910050003c50000c000801d95a241c100220381501440104c00c01d05c0036003240d40d0b45030303a80001804501180100e4080075000300884400c50380d607240c00d802c1350340b003111042c006509140c007140e0105c09 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 625976780 1250 625975530 625975549
    0x70b100e0a0e0a0f0501110a05250506150619050d050a060501050d050702010615030e0d082404090813030c060f05070b070201060f080c15070b061003290f 68
    0x18401800901d40f07240c41d03281a08841030019a0f1035541d5180025054604a005003038491264948a131560710b01c0711064500440d25620103500707950700d41c01c60002007011034055401446202d1002105404d030b80031030110302400480c0c0407003020340c411309186640c002003c0d00e196030020f00240010398485000d442901c240d84106e5020910511194201e0121038100aa0011081c0300000d000b030b503103240280d140c4110a880c080800d6403214200314a85082c0003d900400c51820180014100300000c10030741d0102d401d2107160385010000184069036541c02800a00340c200c852a80c4565030031070840c450080d1071004442240c1048000a1a076021380e14200100410341c645a083c4007803616108134107000200000210b5580760000300c0d41c400840c6070a009442c03994000d14a6100c040c003072140140b04290004200407091155500003420407038160b502220a9030382d440c1e1682020b500360040e050101c1d20061046500d031260403038a46030250101c481c60111501c030380c00c1640206100c2c0640 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 625978030 1250 625976780 625976801
    0x61314060f070b07020f0616021b062205030615120f03090603060f090115030f050103080a050703120203150a060e03210c06150f0613030303090305070b100e0a 70
    0x8144140b00203e00c3c0707100b150758041620700645050b135004001a90902100b15071b581101c0074000710390100307281d040200315900c1031003c581100c00040d00707000a4050146880c28110020485407000e1701c0e0200e005608001d000180841f01d46003003100ca12107070880c081100d140128207064003404c0d0b00c1000100c0d40c0c03074609070b1409035140c81040e4042c0412944000d00060304540108005001d5441d008a058020101d40314000b048000c4100300070706560801149000300c506040061010808003012603260a0302030500c1560b03413500785000c2c0c400c840007001c03080c560b510100412001c03c55101018002000440c1e14103041500c6035400e660301807907100d10680540c82410070300c0b112220003455000708525401224106903e1840851500340111040031140510300194296410a403101920302c8500722841c43c205148410740000301c240c184005400c164032000035106050150017222682d80d005400c5000d07034a1308046099010b8500d00c9560654840c0c140000c01141c0c0038031400e01d144 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 625979280 1250 625978030 625978057
    0x100e011403010b0a0f0b0706021606090501150308030a0e160801020a0e0402120a0b0109090903030f050708010302010c080306061306051801030e0a0224040303481106131406 76
    0x5421b06906515a4200e82c1e41240d03045c0d42001901e144000c0040c1c141445441070001040c0703844503150440c00d40f41c80c000900c202a88025081c000241d084083c0c1e5805881070100107440e034560030915142c03c020301119569405600d00209030854103400600c00c1001c40d488140340e02c1016010f2108a100300300d1100750007501400030540310200c6401c040780c90001454507030340403034039000ca4008903a104007003140483e90303039221000108001d0203655880610390600030481c0d0301d0358002800ba01e601050080071a140000001c080d41c2e50318056900100707040300380c01d090300d40700c040c05403490b806419011002c41d032040f8000c140358424018803261100c014041d002407070780e60f801e002e000000c0d81c1c92100c104ca81d01a135900740054010180000b98041c0d924413860300c0c0138030b8801d0a085180100112401c0b01c640072500e40811701000f40ca8280c00c6440f540e0001003060070000c036850150340100e9400000060314110b00044403568809840000c00c0d031440400407881000032a205a04400390301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 625980530 1250 625979280 625979309
    0xb010b0306010e0f03390301020301050d3003050405151009090302070504150e090d0c1716200103091e030c050a0303050f0601050a1403100e011403010b0a 68
    0x280d06148408413215030f0302404a41e6640040d2624900082c40d28400d004294240c14941c00480100d400044860384151b00071407030355041c0700205840c29070840d406000d09110014441d0076a500c61382c201540c00300c805640c010714910320b40c020041c050640f0300740c45502c0f03140385c02032081d01c0380d8618501800342c0031400c1c5006842c04651002900ca8201c095055010310803002802d1703120350207080401040312440840352810200000c41d10240038000003080e50210b00c28104058010340b0700e015141c0c0290441304010010000755003d44200985603164003982803c440801c91250360f42d8402c7d4480c1c64580d0100514540110304641200c1c2c0007905101d541c0741008440d91284000b00c990f02e004c2d241c06402085181c0754980341c650090741c02c8000a6031001080001038001038001c0d0400007d02e091072800c82101001010300b00e0700400c22109850000108502c121808203100091020b08100d040d15030723403158440d10f422004450715000e5406d016450405160100702b031b400303603040145800803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 625981780 1250 625980530 625980557
    0x100e0c0702130b090712020c2b08190902040605030f0d0f020d0203030411010309050a0f02030d0e030c0f0105090d140c010513062712150501180f0902120a0b010b030601 74
    0x648060011b9001ca000c1e50800007a00c4a40c001c0c450062088207800c4801d03031f00000f0042c012451012964802c5c00c00203c041400240c905840c83d0300c80f103807c400340108400c00d540c00010010729540d40941c0c1d00d842200301400081c24041800182d041003502d9405841819400590b01d07030807038040031b10040c0c004000050009188000d040031242c818580000c101c1203607500c4929100010300103484800750b01e00c8080442c0b404001d02c04000c02646030180c3c0b45501840826580c0c1401c24040307120b0400d040303185229034420400d50b42c04180c020f00070800c608440c100840b900c110f074690b20782540070755243e80000754000c00442d90603040c404c50381316030a49030140448010b60f40d00c1072041c6850088801442c0d401c901ca10403405841c0c0c031035549400040c903182502030b505600382601c0740079080200401000b061060801942401014003003045148a5915801003854020095001002021406000e4000500c103075425201e80400d400d507980303455a2241501040b603480303002501f100d01280d0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 625983030 1250 625981780 625981787
    0x111f03090c12050604050115120b19110703020c06130608190207030806041d03220f060207150e030a020f04021923070c0e100e0c0702130b0907 63
    0x40300c54000c10325000c0d0305445842e50081020a03080503203d6901a8040c0014840d0030700c1004094500b06000f02c048501d461560f085c02c501d2810044d161301c05480c0019502e110103500400c50104001003000140400039400c9406d801000c0143d00600c03440c1c542c82c6081c01c2500440d000740c4c3c00c0e00d41101c002841d00700101c07800c44004083d4031104010709255850600c03180061320115200b62980d44a80c0352030024041103a05140e02035200c0c54100d40360420200c40842100c030340c0f000400c4048041036101fa504207189030236030310245a01030b02003c0042e080d6404903d032000d0703401c101005020450064411034071140d0720580e035549508218442e10051400c0300041e0654400a0300140c1005085081040500382c0881d840c03010840c10111580c0d4030030483c00100390180b4000c0510300b840351540302e11519800d58021086d081108d800401d4400d04c0040070a4001c040941d4440c0c01c500d44031403048015080860120302440800c400d8204031800341c0034904a0031000392186403a070b42c030b00000300c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 625984280 1250 625983030 625983041
    0x190f0614120f0307050303161803030e04060305030d020703090608221106030406060e0106031406060304172209060b0d0c1e080105090705090a030f050c06030403030504111f03 77
    0x6403140e00d280c901c2460b024405042c40c9401540135640364644864200420b6100301c070b0203401c00002c858002c030f407002c2c0b110800080c0d030380500d4034240c0c0c500c602c40810011305054101622038880850030102d400055002466214071940c5c68418142e900d440c292904817007621850140c181841c400341c04032030000e03000b407821400b4011440383d80300080c001ca425903000380c405803000c0d61640d5080c058105588542801800345140402469158244150700076101410851282c000040802c0138031007a0111041d920110f9401c00d9a03441d00901d681e680c1070040882075043c03004448001940f0b14281c4140f4044a010569551900315580340010040c00300341da0182c1842440d204a6541e410404030500700e90f0001d45070421613504140400c240c40100400d4201084070400661200da210002000304403603211500c0c07a1034600500c0c24a05019280b00c1c003642102c0003104200c14107a05410060069000301c1d00058440404402c0c0041c055800e22269681020340003c040610320a9000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 625985530 1250 625984280 625984309
    0x5071709010c080d02070b010e060307121502310308030a090f06050c0901120204050109050d0507080118140a05060105060f0d060b07050f070609090f020d05190f0614 73
    0x101e00a1079169a8180c82e43c0040d10901c02d0304c0e601046200402200c25425409070158950b843d24510744035000a640e881e007409442205158004d4500801040d828209030801d580300341517441d214020741c40e403086241062250a084894400445014150307003140c01569007162081c1c1c0b6503620607003154003500503030b08112032620b80502d40d8400b050749445503d01805c11510025904e003200000104814035041c0c2c07044242d48100400c102d680c1e00aa00300b01255070603260010880c80e5030030b10a041102e10b40c8454015401d080c83d000303000b8001046903032030314031403242401840e41d04c040950b0b0758801540c000300240d1118006025070315180300038150045013540c615160091000182c1c00b943c1da60361108040d0100030400c4010801e061017240da080c60786074002e00d07a00f85096002050030f2010301c0f5200c44980e844008550000c0c00f90101e42c0700c2c006116042c40981040c5c203051903214488030118a9003440c240640481c01100d000c1d08044482d07444001c12012543e40c00c1180d100c034070100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 625986780 1250 625985530 625985537
    0x6042102030a0e01020c0d0606080c0406080c010804080c0f0d090b030411060f2106040b060a0c080f0702031b090a02130b0c071509082803180b04090501080d0507170901 74
    0x460f407550344651110948510980e000b086044c5802cac0c100e45005d220740c42c1e85210700e0a1080034411040000b030804d1301c0345403d181462031070b00d07182044000c0340b0488044480c03c0c0505080d501c0104800200400084465a01c40c02890380d02e0060751260301007501c1c0205412842c90b074601c0c6903d008000b0745940d0680d28550761500c2d065442c01ca00341c44248108a0301704131500204072440c5401e1180f0308403c0701c16114903152609240b0000c00c0400b41e5000200a60b05c04141003100c0032018081e1119103a0140441d0740010000302c80110b0324402c0d0502034071030901d403000140c0000f03147c000e481003141c1600170110b0250500c005000c1c150852450803050744160000010b00083e400282140111035840d46030009050003061810040da00d1041445070054811055a28110890306018030344c06240415006003d2001250f182c0b8007640448144d480c00f24012a007100140d2140c1c2c1200c03890022142044c2129030b0640d964010350b100901020101105284c000105000601c4c02450515 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 625988030 1250 625986780 625986793
    0x120e100804081b0708060108010606020a0b040c0902032e060e1507061e060501031104051c12171302060403080f0408010501060302070b09150c0706020f030906042102030a0e0102 78
    0x110f0035090402c180001080541c07140a0070800c1840031302005000d01000c8000b84011800d02c0e001035a150600c03400108440301500001e4107114003911540c01821205000f50760b01d050480454400e10400300c82074a050495070107a40d401c486462601c070072154152140d95444000c141001021001c4410441e0348000411422001030102d21403640c00c460324003c1e1244601c5595510011980940c00c118189032400902c035144400ca070041d40c1c02c55104031a2059070103410b5800703000402030700320001c200603038002c1040074590b04210210106400d401c490090303542d41c58560720081c0e44281e006504040d08105c284080380084008200705003200409a180c569208601400c44609a201d200025400309142c003c1142c044000c9400170b1440005085004001e110070398400f4018215880902d4002050000c008542d011344003c0584502099220700d00b401c4125142c041c2100c0031100107000c010f180c0721002d507800d400b0340c0c03407040380e4000c500b06544800b042e110846030154540c154032400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 625989280 1250 625988030 625988047
    0x90207060f02210a0c020705131811130504020906100c0b04030203040e0c0c0607110a0b0c09100c030c0b0604180f060c030e100c0504030c0b0403120e10080408 70
    0xd00041044800090511690300c01e0304494030f440000140a819040c1d09001a91020f20350004d20601581d030304546c2c03030359a8541c02d4004801421540d144266408e04c86404606000040d82800c0500006a91100c0000d000c11180d038125281201d0080d48220014041116030812070344505d1001e009007040000c07096a6101c011138200126003c50060f80006818400c0d80b0b43c07022a10b0308600301e50035060034a0707040d6085903152603004046500b08034000d20800d030030243c1005025002034026510015500f051051a29603510061485008049052000345110320031110900120b42540e540001c00c00c543d50764030700c404005045c1c0c640c425100d003c143d54000c0c0d010441e211161140b0820010200286010400e680f40d8601407000d040c90003900b841290808552890f42d900b6100000500c005c055005440c01c0c091500040c0c03089504400c041580000c080080c000e6034040c04082030f110200d0301045400e10000aa003940000c2c24036014250f03d8082d400064200e03101e030b100d030f908010300e8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 625990530 1250 625989280 625989311
    0x100e060f1b0712020c180f100902040e0a0b011b170f04060c210c060207080f0c150a0203010b07020f0a051903060e0a050334060203010503010c08040c09020706 70
    0x80300070790b90030b51102071035240c01d84c0421038620050800d503030000006c0c260007031401c2d00d0900103003485151260075000074040d0b4250304510003e0721110404649840d140c411503a2207800031900c00d90000c2c03409411913529170160144038280c00d00504000c240c3e03100355035202c6000c0c08250b00191004420301002c00810121800f0b04090b05055a0740c19200e841c50500056505003090810000c50941c465556030581c40500110030540100c40582d58101c41d20f0034600c41d2040000505002030f010580311201d160100320502903440c0010400999141c000481049120070710035450544400c000110050400c8244410100f60080443d40300d9540c3e400820030b038464005682d8401035002d2000d10030803082e44540a084424040103090003041c0b45ea64507624441d8202c0c1e00e50b00d862940c1c0003107021070300800000c040c840e100b001303000311140361801e03030302a40007800b074280300e94281015000f21500c80c4102511072038000194101e06482c040c2101c000754401002501d5407501c0d8002144100d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 625991780 1250 625990530 625990537
    0x32402090402120601170906061e0406081f0b130e03130e1e1605160c09140114030d030b010c02041103040311030f070201030506010c12090503100e060f1b 68
    0x200f6a80204030780c51300c4d000050444008821074034400b040d10341445402c0b0400150254803003400d44400d0030f49010030034881214442c50301125402418400081040a00412410703142c0100070000803c0755005100182562011921550000c00400403a80305800c20381000c0c8000e880b110a591401c1000b030320b03940c40040b03650030100801c2c44c11418006511490600c2c400c0c0d48180440400342420251441100d03040702c02c4c119410030a01141c010048030159180244265002003c41d031901c0c0d0701c1030500090a0f01001c001c11a480c200000074140001040c000462003008010b0040384100312019030082000c40d40312410000c2d40e490032001030705e89106290484200e40011610f0789454680140014405c0100020307582003030215080154851059500390380c0d090034007040d40e0740c030100102d604a90011001d0818060301e040c804006800c02a10000d90318140d00f5036030746d8080d44140a0696040003040b100d160700440024501d0084444640e030402044400d00d10298a840070701c621980 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 625993030 1250 625991780 625991797
    0xd2406230712110c01090501050304140102161a060a080303060108090f07030303020c06133503040818220e01060506070506010f06030504080f07031707031d0601032402090402 77
    0x40040e01c0c841803c0310100305142000d0000d180c0300d14034500b0200021712500006d0f10040900000f084800c0e4940c000f90152413420000a0110480240314103128003e500380c0702e0304002c019406804901c1a092804011080e075140f0001180f4584808004603019800100400d245002d11482e0311528002440844001e600903900943c9a041ca82c1300f85080110203404038001820b40d02c080b030b00092400d00581180da107050a00703030521000d204c1100b10000d01c43e42586845200004102c00c001d07149000d052001d550b42c0381044c0c00c0d1204800d20111240404100980f09240c0e00301240101c4c503600000401007034000003081480ea684003160880c0c128000481c0d40d500f1020060200c40b11703409100e00100034515052125040130b4032000c01c02d200f41410001038140c00245d10007414002c10603641200024000c505403403034400e100a00814580c491a2001000c0c0500000313600340001d0b001741a6508901040c0980940300c8046240d880d2102c003000c13200e41c09000110503581e035072029142d42c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 625994280 1250 625993030 625993037
    0xb060f0a080d090e06100c080c0313180b0306150f0d0f03080901020304080d02070633060c0c141f5f0d2406230712 51
    0x2c6550300001d80a5100e94004400d40c2c0c80003401c001013691762a0100307a03111800d080560702d1000c181032599007442003440005481c44001060b10100e42418121411103201c40900d600c00000514250162030b040c1c0007003a4180d00c080c0224107168000f21a5101c1140c00500070310901201c0b0000c1804501d6494080c1d034040f92044001d410705070000015a0b03c800900c000714558502a59558000d01030040080c545030b9001c00c0810070041e855201c010b00c04e813088140a10807850382580c003c500035601030203140308a21800008c01600a10300050082e61111700c9110960500286840c6c95101840c0161321800106100c103200e48481c04140c4000e100c3d035607280741c2c0701301c1d08104880d0001022001d042e03903a4650405091200319080140240741d00c0401204420040000d10f0b80c50500100703100d0348540c0010003c440c4035040c7d02000c401c03c400c5044515100c000e180202e6200c00e94814070010485100407204803181d1550491003056a80240c00d04105598844420400701801502c020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 625995530 1250 625994280 625994293
    0x30708120304020901150207031209170d02010e01090b011a04240305010501051912020405040e0303010f0902090603073915020f09041d0a03020307030e090c070b060f0a08 75
    0x10b43c10b1090380c0714007403c0c501c0c21950103043d2141d0002c2d0f48c3d80ca10f11000e8030442c287c1c1c46146a503803154030000000e1120225001c25505460304241c1c41d4008885040055840c084400c48130810600030070094a800c849030780c07000e0380303400100c540107015201e283c05084410040850400c00c0d941c000c07510321080000c0401000ca60803000781c100d035010b8001c90f052040601402c905462010b0700d011042c80c446c9020a68130b400f0340360030f00181c09160011a803103030529050710170f00c40380000514102d407000000c2040060791030141e60100d1103a1094160030180c00c00008618074040c0103060519402ca5861400c81c030802113098a41d441040c84020003200520300300c1341881f900307000703c0440d281c21070011450458204081c0c8241d01c540c0000e54011911050041030404104006016000345201a200503442500e0001d41380e034400c00d411804100950349111050804c1000c0b24801c80c40f50b10104e292007620345401064030303001410b050340621011403c1c078190700c404034090024550710380142031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 625996780 1250 625995530 625995533
    0x6040e0d05090d320d02010501181d0f030703021606021905120d0606081605190c0b071e09080a0611071502090f010c020d0f0503040e0f0601090605180906030708120304 74
    0xc0074648201d03601168104801400461240442044c48ad6462000010300c0c58004840c107481c0c00032011848203e00580604111034a408002050554401d40c00d90307041c160740b21100c8002c0607081c0a01320050b88021a0003031003243c111b81840b0464019401c031104c1078000e81d00001658440c010019125450700c0d81042402c3e08211110342001e4174516a01144651800c01005405116503540b6641c446000c16403201e0b00481c045040c00e5082170880110b07103801d00300904040c00c000000f800c0b0b412000d00e19086030b44262854800e88100c0000b41044602c99146c80780680b01811100c0707c2004200040380c006240200344207400c80c1c0c81e50700540c4402c41d007000c10924809079681c0e00c0c14000386014040050b40c0d0301864a07130069021302080001d40e00e1b810140d1a42c003c607000290701104400c188080d040c240c0014910400c0300340da4040e902900c50008030b506000b030110302e0120b4851842c440c142e03031400304422603201038080d08885c42144e40f1a0030510748034956034184260b50002080c0f10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 625998030 1250 625996780 625996783
    0x618081c0e03030306090c09010507060e0f070f0605071106091906032d02030705160609120311161b03060b120c0a09020f0702090f06040e0d05090d32 66
    0x21a8100d01540c11858501d0201751104401400c04a81f81400151040968041d07402c1d2510140c014cc410041003840b50242d039501d00301108005410300c91030100180e000f5158442c00d0913211103a4a003030426141d951040c07460301c48801c150358810400c4c040010244ca0b0194150030304490703103c0e1003a00301c0c41c10802904032420708003281084e204015082030072080030808240249404600145d40c0e0b40c4903e812101401031700c41407045c0040044c550024041c280d0408408980100790b40d00c8010b4003554140e049814003124164031150500030034940c2c8600710680d00c0b10314051f0800b0440c010a84000f840c008640f0b401c01c40760265264440c0b43c09092480000791180070f104010300036482c10000140c803802d0303181f00d400c46650300010803c0c40030003000c040e0f900a07a07000d00528007504040e5140502141c049400d140a00d2820841110f50f00b0009246044001d05494072481d10920078203000c44002540307c1550b21040070201c1e042540c030410128444800b2500d01c034000301c0c012600b283d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 625999280 1250 625998030 625998047
    0x603020d062013030803150a0810060e042f0402030109020a11010b0f130603021503010302131b0e15030115170408031504090507090203090c0d0b010618081c 69
    0x604040018040b4110f0086005210410b59401c460026100c0d580c50b04018400100e042032580c100030041400140c00380c00040f05900d40c3d04a50041c8105901e418100390405411180074240c0c900042240b07010300d40d04100303c40d214080c9103081c04000300040108090342c0c0280e0280c900079034002100c1c040f40d6400700301c0740c000c001e240c4000d01030182c001000a1403500e021240a114545c0040d240104542e40c3c0d00400003140c1c050300a940035510f40040100c41d800c2440705900800c21682160060106031007144101c07001d10081450000020b4411a0b100141c10080764020480c00001c9500443c403c0145000b004030080102070f48200c448001c000c2c428031100a8820140c650a010018030f201c2c040e6580f200820b031010890040b904000341c05040c1125000d0942d0082078400300d41c181442e00214851030100045130045101c05040c4254101101070107002840d50710010301c0300c1c82c4540841207441c00c0408211307582980711120079040002c107240e02c81d20b1800300c1150030708450304403592 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 626000530 1250 625999280 625999331
    0xe0c031204050a141f0503010f0b03040b04080307021e010501210507050105032d07180308180d1a0708070836011109210a060f0603020d06 61
    0x24a4209803800340441c60032002c501809145910100b060801c98481118080c2c0480e07072600d000c81208a00794021b0900c4d8000c1c020700200d995450070104800715850704482c00380f54082c01e5070810359103036103501e00c00360009080001180260f84071031043c21540800500c061480c540001a2545048011810402141c820f440c540050307030043c001040c00851481c04940013801e140303540e90348220f01e44180103807c50031150440f050310884103c180d03040c81050300c00d51301134503000618050502e03a01303d45071240c4030080030250100f01950b001c400760b01c000703000b081e0060020340c0400303010b5503840d0b00407603011312001c07400038ac00c010460720507404204c0c2500b100607401e0651103802c0c022082400c42c107801d035640541071345d1468055030002190742080381c54440c0f01e000300040014140f000059502545103640b0600e0030042c520f8100001d0204501c1d00c800380c0c001401109140d07036807500a8034103440800c005607651540080561554111780500600c95000000c811810000d41005060780c03020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 626001780 1250 626000530 626000563
    0x30108011a130c090b0d0e1e070501180306020429040e01033c290105130204030b0705070302010c020a030f11100f09050601060c0f1709040e0c03 64
    0x20707003280c0d40d15000c20001c855551a20080b4104240c8041600c030400168850001004000342d0a4485507840d480315150744910300a807902e0741c1c1a408070714203282400c0c050303a15542100e041041550700824507090092205038007103a5207950b9032030302c4040f60003a601c01000303001131420001804060721061421030350a489040d00f401d003071805400d524201404010b00703400398100300c08241300c602084908074122146800d200820310b840c00e119240850b590031113481d6860041000c0d40000289100d4543d544a0508801a0310704020003003143c402c40c4090414581c00c10012000c20300c84030820b4840c0061751101b0350742d90b4007403800a0840e80b480c0300840454001e083e04400195000c605a100840640b60108207013518009a40c24010044d8800310031a20b00284600a0000307500500c242078010300c10303100c0a2f1703a50300703003075400c409450001081c01295040d940d0024444446554944104100190400a681000c0740c02c45410048000350307035004031261141031030f00700211144c03003c2c2c03041c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 626003030 1250 626001780 626001821
    0x108061f05040915061e0801061a1303050a030216090209030703061d060405070305120f0f0f36100c020f040908070b0403030506060304051e120f03010801 68
    0x340c180350aa0041c0140381c440d0f40c40d08414014000003c3d00540003500c1d20714100009039541180148088940c92000e50714030491200140c50380061080d00121501c02010108400d1001000c1c60325501c5064030b81e1100080900200c00b04204020581c031144c444d400401415803030551840740c4100b03075800503040303c0c0100700c500c18039140410040b045036840030003c034542003506984240c2c80c1400340b00d0075091052800304000d100e0009001c031300312401b901c242c17650604010019101485020801c10b465802044071b82c00319040b480060102203030700356200d0b0400700304020340d080311206030070b408a4030300034003a594004200c0e10040c1c0130350000c21101c617412401180c9004d080010403040c080c0c03107100004c5020b00d10752965040303a007959030700049055880001d031600c0100d0004c29601540020314203800244641003544c00c49002e83d80110080612404841c808000381030311b40e003640044d0050040c0107000c0301000c0040d00028041401080e10380d8105043c0794211215016540d9030140e001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 626004280 1250 626003030 626003071
    0x30203150604060c120521011409060d03050c0a4b17070204140a200412060f0606031d0a0807150204150c031112030712090503070b010806 61
    0x107130440c8900e5001040101c503140c09403080c1c3d214060809460340e030501c0580807188151000308824182c6098040c0c60381c2c01c185400c18410307492822254240c1000d05541c591010a001da0003030180c045451007110301c83c5140303613039010b0418110920744408810481c207840c60900800701071000d58108105500b0b008001010f50b02c403d821040c0c3c043c201880c3c9946101d0800060780c101c1c1c26541d0060303c103104180e081d0800c0582d07400c08139200320300305103003442082150300d001000b60703141c40050000904041c01d1080742c441401c14110115a069501c01c400c120a03c102e0040c0e00040c409034800244000e204c050301286040618160202c58212141c1d41000a40400c103030b429440e0400c01010710107611040900080c0b1554004002403410944200c000b10792103a41c4100091017035842c0000ca03074100e0078140d0340f1191601c040b805d10304248002250b01d03200d0700e2140c01c0704c4001100890b80c441c45455003811580441030a584550000c00140700f500c0c8104881ca800c0300c0f001c0106421240f94 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 626005530 1250 626004280 626004287
    0x1403160b3306070204020a0c0c270c020a1407090e010e190201020a050105041b061b060203060a0509040614010e041106030c1c060501020712050a06050c120703020315060406 76
    0xc01a2105589030070200307558580e101c1a06030340c9180c0e805001151744217240c8a000e44581d900301e000f1900c2d1040c404020070030748240c2c0c0454142c02c07502034503110f1a50750310083e40e01504001000354114411240d16101145080380d014038954810805040c2c11340c14007072038a00351100014804c680341e050400d00e0034a0b01001542c48000c20741030b9605490030b01c4610040341011031240c80a0090743c204402e100a000b00070b41e2180e000080e007d50114410b07035500040c1c40101c0301d4518150300501e10f40c24035001c42d400d40c0041d0303030040001717003d0003141d601d900000d680510183c1d07090b51801c1d0b0390320514880d0115a10014058020040f20701c3d21450b02c0d580d10408012048000c41c05508003002141d6007a10030010703030351620244200d01101c00d8030b442070800200031621540e4010f106403d8006990750100007906042c42d0024060501c0302d15a0302c1300c1d8003604002e020b201810100b00011589a07a000b003845014030101d03a405a60303810b1055046824500301d40b00984200300c10072041003a04c1c3c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 626006780 1250 626005530 626005591
    0x1d030a0803090109200406090507080f0907170f10061214010f0608010c03050c090109090504021c0c0f14010f0809070308040f05011b0b070c1403160b 66
    0xd00040c503659075a5801680e5014004840c80141044600064030750703503d01102d480c4480300400e4400300102907581c10b2000030743d40e082d00d5000c0441e4895000c22102001050410b80c0100d100048502c82a502c0d6403120f015100d41c840f6048982100511610030481131004518100c85200c05011582c241114a42d44a2118400400b20840c10520381480c2d2801e4100e07100c1c00350108000c1003210b0740d507070b02d442c043c0c8044440880000d01d004000b0301c211b100b1000f50f894000040e90360b004000e0070100c1510052601600680e03105a80c1c0805261006035141110010340c4107181541d84503180030401c1e07035807003c6030700b10540825489070907125a0364030006c1403014408902e084103ca80380c58124a042405982000d44480000180070480243d40c00ca0070084034400c1e40c801064402c0c011886c003d040b0f031118002d014201d2080841d20040c851400300c0c00c81405180341075100c45003170401030b186a111501c80340003400c01000020030701801d50072040d400a14460b12604a0b4800b09644c0c04c81030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 626008030 1250 626006780 626006783
    0x60a0f03061a120907050405011403061008060a020d020d0906020702031216020f040e0a03050417010501030c0302010e01091e032307270509060906160f0f2d1d030a 72
    0xa0703c5000145003400c0c10404200184005402005a940c40300c01d140c0b050b41d0203c0306103000e40302e103101003940080c4548a8500315220000500050307101e0710041c0000c3c0d40684607040c4200d400b405072010030b104c03510556098a02c100c5005941c8c0300c0520503d4100814810725054283c420b000300c1200030a034010b03ca00a0740d0484030018282d000d04001002046c502980720182d10405001030b00f01604071005005a0380390702d034640e000a9461000602341d840c2400028900705000c9000c00040d4015800c800d280c0c0310505007800420348495074003a619554203025802d508200310108103000d008000e03141c50f61448980c01d030140b82d00c442442d80d40e1140c0e1207440e032440703c10501046c07014240d8401c103a94004071081400346042040f6145d69a0f0020386e11240e49026280225a074035410a01050003454991141d0b00c409608440c281d9106a0000c60310042c010b50714103500c05059100080c040340394201ea803448610400341002051151000501c80340e0b0305014280c0c069582d0700040520605 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 626009280 1250 626008030 626008057
    0x221809020d0506040f0c1a090d1a190f020703080f040203071d1e092107080412030806012f0f0703030f0806030a030e010302130302060a0f03061a 64
    0x144040e10100e111400d150350003a20500501c014441003007001c1486045060041440003c51903c400c0744290000708007425030709400c8204903200c09410485103214030703d0301802c04905041c02e0030071001d9540e00115212401041c0705003000c5081d441511419004007040c00d021802c00d01542c0e0003412190001d0003107030034400800000340c210350701013045030701400001c3c40324110f2078403500d09500000c909541304803c0e211445032141303084071801141441104480010841840c3c2a400d043d100042004e05c039015040c01c003c010003190102c4000d0000380440c100c0b801c1615142d0400520303c001c00781c003640c1001690340b0502028075081008031b060b43c03840700c03d00740000382040300540b508401240e405614054441d00005140c0c200c103a10003800201d40f52010b1540e40c007402c1503161841c10700c0090101d05a010500c02951203030340544044880845940700054407034001403040d400078020303d4005203520100080103a03040c001c1d0401081c00341d0941c81c4103058070703035061014061400c0200a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 626010530 1250 626009280 626009291
    0x103030e0301091b050f100c12021228090602070b0a030b0a0e09100902010c030e011704110a0f05060328060902271012020d050c2218 59
    0x26941c00f0350000e0340c80c0354418510000305010700e80000090100d4030a00380308820500114005050282c400209a09250307034213100c1d210302e50b03201c0d1040c0c105440940214802c4d01c0c4580c0d60902d25100600c50800101840d00082400701900608100c444040070100685824104003d40d00040c1c010f056a0300c1e072a070143c03a007041c0c0104030010400c40a000d5802400000001810180c0c420041e000d00d111200b5606500206140d1500307495452500a00080b501c1007054003081c0f01c3c9143c00c8a494051409034401c0c04c00040003500c00c0e9050f6400c0d64082100380c401074045c41d00c000101c006180020040c13150524040009005010043c03840c45280c408000003048100c90f80b0040001848800003000442d855030403100082d00706a2481c80b0315500041d0801c00e911240022403244070b0000c02402d801c026115040364920101d180200d1566000d200307184161600e030144520412020307100c95100d802460000105411090100d48c500400c102d00340f011400100591400e100e40e604003046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 626011780 1250 626010530 626010557
    0x402040203091911030607020a031d040b04050a0e0d091a090d150506041503080a11030904060815060a08030a030507021903120b0405010506123c0a02040509010303 72
    0x400103d404940a020b2221500c00b003005540440c40300e201d54260b0807a14950345031001a6590710380b45401801154541d59030603150140300008204800300580f02044200c800000709085d254107032104910103445200ea0f94801904108151800340c181c030744020070601c1c0515200880310b10071001c0c190384100007600c12441e04c82c442e080c5445644410070085601d03404c0c1c2c02200074130054541c14840d50801c44215800c94102011005032600146641d20f030052100c0300392a02203840d101d60545010502010043d40c1c5d45204250007170004c203020780400303070075480c0903e002c000c0202124810120350106001192000017680c4900708907080024507601c03860300c103034039000314010010408510750801008140c0e0000340f0006980350311400703120841c0e48000b0001540e0302401f615400141c14040c0540600d001c101058101d104051a00401e0109400300c810031485d443c84444031144025001a003e600201429030000c1001e1007103003440d0620000601d928018440034003048000e03170303d240c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 626013030 1250 626011780 626011783
    0xb0901050d060806040b071d010f1209140a0218150d080f0301061e032f0909040b0103021002070e0714120106021b0f1c05030c030412060c17040204020309 68
    0x2c2c064240001254160301d0585404609048100c0b5000700145101482034103500e107090414030a100140c440403481e0319012000c94003200034110804840382c49042a4002c01d070015000390744941150041c000032421030051141d09002682c86801d0041d10500308050b01d440351a011280398030444000910100c20b0516150030b0058003100e40d0322100000000520a170400d039144011064115905904c1280303440c01c0c5c1c2265800d03660700240404a0f08001d00e01c101034000b2041e40012084101c0c1040094800308640741022941166907069a600500940ca05444481e01c1500f00748000c0c5081410a0510303240b00740043c00c1354050011845051410303140741000e503113440d607103003003002c040c0c1da5943d0000b50780c3c0f001d40717013004039220107100981c0e980e0800e4081611420400b502d071042c940c111840002c02042041000d607058001407007410b580c420240000c000404130f1076240c400f40d03200d5080203030440b80c590140c4420f000c200c503e9110703666811420301c1d52182e0100d0700140c03241e84250a4a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 626014280 1250 626013030 626013041
    0xd03120c0f0f021203040b13080a02010b10050c0a1106040b300108070e040807021008060a0b070c0b0c030c0303090601061b0218071101060e04050106060f02210405090109090611040b0901050d 84
    0xc00340c10703000c290720820075415403200700c0e040f604842071149102c4103b400e541900c210020001c00d82c100c0d844020218602d14000090340364040e0080389495078685108140780c1040d40800c6003c5010300201c6440c01e200c95a55110851640d0f40d018035502d05412559030350598481c00c440c0c090601c0014060000c041c055038144c41c1c02611044200d0100c06004183d0101126aa8401c0e4444000454000d105000360340c03540e03900030000c003142da0071700300c6210700ea4009490b80d42c19440308101c0d01030110340c180080d501070341d11140140b656505054001d00400d00c0c0d05811250380e501800c00d80c0140e558441c0d000301585a140302c082c110b031140e00e0704880800c424107000d81c1540c03c000c000900b00c454012414071450042008000c442d031148421200c02c83c40300d41d51001603000303210202c11754100c00b18600c0d902060302c802a2030555504003144d0a800260b0000a480ba40d078100702e41808804e000700c9400b03500308141c06180c03c0c03e008214010340248150305041103230110b81003400c0308259200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 626015530 1250 626014280 626014283
    0x20a110405160e0a0e0a0902090109020a050901030e0708070e090f0a030f0503100504180b130209010317070507090b03010b0a0b0d09240e10051003020d03120c0f0f021203040b13 78
    0x1000750706d845164030b0090520b00000300d020700000030001902000344d10076140700c1c02d903070750344c040c83c18900d1001140030340b451070100d41550044070000100035200f000840010112451240c00034548401d01d0343c108007207000794641b9038000911321030020390f001000036009500c80c18816240d840d00212821441d64079004180c1080c40d103007944040604004400c115940300d42502e102c155034110050f40034007996800207401c048070f00010700000b14135481c00c440c0000b20403a0a418001991680e40c90040f4980c030450361345668018580c00c5d81030070700406030840310641d101c40702c4515021001740140300c0d501d00642041d0351005450104203d0303403c81d0b14543c50b004480410780290f0300281c001001c0030900d400c200e01c01d00b8407640d10070380c107401680e01c50710440308070304280342c9150248121001c00d90300403010003100799a91100401c0c1c5108905c080282030750b0718002c1e44071607a00a07088014032140d180541d401400c01c0c1041c4a080d0341180e5005a002400b640c46442e000c0d43c030110801f0340c060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 626016780 1250 626015530 626015549
    0xa02090c161209081608030f07080d050114120307030f1d04050411040b0a0e06010507030302071e060501081911150a08060901050409080304260406020a110405160e0a 73
    0x18011582030380310f409030082c2c411110903522881880314001c038014282d441018000c2c0c2040c001c00b055121ba00f00a49096401242e1540c030b040750140c080c200302c5600360400e4002800f543e180c060103040945000c41a110088011351a001480c1ca018106100d607810306c00402c0300c5003910000440c481202d0780c0000102a04c10b1103642403d18140c041c0f14a01d64055001d00e146c013608108600c0d00d00304400480d282c00081410350348030f04004580543c42048244c05258080180400240c080b6050010700d40d41948100b0101e4840c0c50b0080c103442040e0b10180540d8061941070040b040022400555140d0259582209210700800b10b124211007290070500c404c3c011408038019a000040c661040074200c1c1c0382c540300c1c2e0b2107404000031200d0591016000c000c00340000f500050f502d9141041d00c8055500d80c10040300035513082c0d00550301076002000140c1200449400b00301e441c080341c0030280e1088a060015103000307003402e0300070810413080a0422070a00e4040c0c0c0c0075254007503140c02510b100c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 626018030 1250 626016780 626016803
    0xb060904030519080a0b010306030f11180403120e03090f01050d201b161404091e0501050a1b20100c0f09050616030908010504061d0a02090c16 63
    0x1102420985017100c2d4400d040c0e09100720860250310a01c01c501c02e80f0303482020351040d24078035140d0305c1d081111109200d40105401d41d002108000304511503200e90310030755880f100841200d18200644441d540d90460a43c0305004d818519521819580902d440c2843d2003500c0f120301d20344400103010350440e10050140c11041c9030800c000e0010042c42aa801841c0c02c0000038188505243c0c4c1d034000390725030120320212a00611114450b180030401d0001d004002103030030050f40d150010302891454407100c2142407960719070b00300882030040d50742c0081c40700002c200804090043d14031900414440104014000e11400c00b50045031480b01c0181040c0701c00c8410031170b101c426001c010300072240d8007004034045846104009100e3303100c200c161500a0000b80c240241010080408548800100e0502082e160301090001c4240f046500c40c9009000108566190071400c54200010072541c50747d40d0081490380025032034a07518160021860300031107660f407080181e000c4034205452802401d130b4003240d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 626019280 1250 626018030 626018077
    0x30c02011b0306080d0f02030a0806120607030c1b0807030c03090807151d0307030201030c02120313020f0109060807050a0c0506090a06150f0504020705010b0a09020c060a0203040b0609040305 84
    0x5900c40802c4e151260f044031040d690307100c01a01c20500703000d16000145e004000400011748200411074120a0151040c0003c804d000384542c00d1130350481d03007040041c0e038900f10305183c82c0e405036084020f920451411a007228658503800b25a11860301c014043c04000500602010311a0840b08018500d0a01750f500040e120050000b207510660761030800905d004081032100307200803c0ba200b40100040042c0001461a070042d030113403621046ca802980100002602c04404120040d840340b18403492521090b040e0344104403170601424030f2241040000c0b0000e020254202d10182c0d00031a080c10810703203403403081004480c07003d208200106035016010900c9000c40002a0401e040c5218000602085800082c1c0f0311518403a48561031201200180070070a0b420b05a0081184900610000c1000302d14940801c4004159078840007a5503030001d811849404140700c260b400c402380303120941c43d600306030301e0b00060141e002d82840d10400c040008201054042c0c01255040750604240c02c2d08486030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 626020530 1250 626019280 626019287
    0x20f1903120e0a0608060f040e0313050a0e10060804080f040305030a02010507020c0f04022d280c02040b01020c151b070608070f02010e161d1006030c02011b 69
    0x101e0581ca0003240c0202444401c924240200c5030960312581e584220a85d40d000c01c0140041045050f560810355136601b13035840e07a10900c0184a049010b1143c038034440d20744002c0c00304440066214449a801800174440c0cd254214511400c40c2c9007440c00d055140c40e41d0801c0d66052162500c91010980002030000070800044044d0210388180d0f00200002d5880220507038895040c200c58075404038011545c0302d902d00d416400351181d256a444420704230030710903280903000c80701014008013030030020074800c5c200e90b2410f10fa01c1e640c64451050442d000003501c00034000700a00034009105640342d071540002d03648208a0310040707202c01081e0282c8038a199898404a82c009100034038011190205080300000019420044492564481585950381d22044800c001c02000e400115501c0f910102ca00300c804005000c0010340343c80e4107e15640c541071448a525903d000510007902d010000c12940420899000c4100c6019080200b400e4110050807801007404035403401d10414641300e54016030381d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 626021780 1250 626020530 626020553
    0x21050f04060906080f09060c180a0e061e010206060d08070c1e0801060302061b151006110f0709050901060306050c0306091b0301060e060415031b0507030507020f1903 73
    0x1144d110602d0588510100d10030102045629101d19441007001c55031811840c80206032001c00d51000381c207150f0260000844142c459408480c1c025040414400b02c5d1070000d00119481d0001d4519040012107080080d4890b0700052640d0300c07595140100406200065044451481e804510900c0140d15103481080d580b030802c1c4117400102d0580408a01400d0512a51040ea60001c011070300340028000000080d404178070001c4118020300e403c204921440211840c003440c0d00000030100310f030910034000d001500d00f8801030440e03070129203050101c1c2e0380440e14030244c40c650301000c42e150f070714040310901400c03030750348000c1080e803400303040020248100c2c01550107403808442802c015102d810f0069038561018800c1c880d0020200010081140650700300e0101e0300b4090000c9040941e00c007045248051a0201c25011a40b0b480c4450204968a52820390301d900c607003081410114980c030000e006000d10400240100d1a0f0220100540e80300340c40c003400e0070780900d8160801c0341c5a24200081c0c0c0c0c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 626023030 1250 626021780 626021789
    0xc0c180606030e030f07020409020d02060d0218041815060b18090f0c221d060a1707090515030304060908060c03040b041e02100f11010921050f040609 66
    0x2d1034200300c40480304001c13040b190050780700341465040c40c0d074039020800200441402240d101c10f070b5202c0b13030b401601d07010080c00b400110398000507207032000408910700c2c18040c00011840f8900e0701b04802d03051408032204400094001045003a000c40d2a0304980c018041d981004000b520041009001400704403400100c0c0c1d07005488101c0305d9100c50340300004d00142910098103c00c024441a00310b070304504007d80386c41d04102645410707a580e03412400b2200000003446482c24500d0700800c500741c182142048020040c0308018010070301540b05c85510740b00769001309940951120041603007001c1c400340b1444030040060a8a60303840d52014080c10215107489080b082d0f00908000928035120907050b00e00c81c0c2e8001540303c0311036a03180c0e18403100d00e42d131603107400211301c0c40000c2c840962600b0494503040c000d01d46610406002101016003030b040502c030040c42aa041170302030300c0012001441c90310007042d0081d1204410982da50706440c1e03401094900e0750111008600054019805880c220440703 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 626024280 1250 626023030 626023037
    0x3010618150602030304031b0210050909060d05060a0f06050a080d09080d0e09040501021e180324060d1703060f01020115030809010e0a150215090d0c0c180606 70
    0x1015403000807007810748984506805a0020f10005002c203004644038406140804c03c0e0603450340c000d600107021200308002100003c1c0b000b065100950418158075a000181207580d00320b50381490303880703990b9642c0c0106800d100a4503403801241640068102d40b01804000b41703440341d180d03128001c00daa200540ba0400c07000800c0f04000058100c4040382c103c00d42441592608030b252444001d1010804010b841191150360800104540014620038220340e01709014016594800305030b030800241c41c0d196251442504550703010680000500c800d040442d54100b015540c1d0343e2560006000c0d40038551003e810317001c0f100c4008c0070b210100c800461248404450b45c0441b00032a5004901f281c0c080742c40c0074480c01a84005001142c030403405881e141c9814500580302c00c00342c0303000c6003081101c4e90009000090285080031074076014031401c102c02d40324601440c4e96190110403140c0c0d42a0b80d218440500402d6010b40c002d0003140e03038200300508440300c0040e080c1c40051a2000042ca614410300000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 626025530 1250 626024280 626024291
    0x2030a080c010e0a290f010b13052e05040e0a0c05040305060406090b1501022a040c03020d0b0402191110180b06100e0f0415120b0109110315040b03010618 68
    0x170060040b090082d44110201c081c6603003801529101c0c0d900c200b5203861080049000001e05940e8a59540d001f444602a4084014011012a9008040c82c0303888014840c3c02d000034001201400400c50f1302c200420340100e41580050320554030752240f50009481c0d4000e1a007000705011494110342060362041048074003035034820032750825007503a600401e40141c016a10ba200c41621400b9107070411852025841e4913001c00d100040c0c00c0381d9802e240c100110b0340200b02e003199801107101c0c410300d051040e2000d40c9041403d1400e01403113445207000000384190880b0307041c2c076034008010007041c09a103040100302c0c00703440d00061999000103900440717421613403000103a400d0400324402c1b031152210740c82d42541081a6030801c003407110b0340c01f01a83c02a0359609410f10f0811b060411800174902011016a14015401c02c00020541600020885030030903410604040901048a82c03114200700c0d82c20021035a21b00080151104102d0541e0642c00d1a0011611807000c60781c04404201d041c104018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 626026780 1250 626025530 626025593
    0x20706060b0c0c010801150c030e060c0a05010f09050a02060a020a08070c05040c0314132415080a02030d08040303021303152a14040f080c01170402030a080c010e0a 72
    0x140171109000f0440c1d085404a20700c90024003a076880ca0b1703100d00c20308040191003410004217000f0f8000491001c0703540d1244608000b448001c0c45030307001c911031b40c0d5401d0120079181d44402d0342d41e6100f080020301a0800240007003100d4800e00c51104055808140165200d030780341022840c020150080364130451801d41c5d0060391501a00c20a03121244086d240e440c40e07540c0314620204c3c03903289181034580394282441e08600050981044446c0840200000752640b80c004803030b11403502d01d0300304081640c8400405009130750000752868444450703191001180c0e0300c41c54214041d00410102d1203034100d01e050080f003002020118040200054542004210040d0074505200603004494601c10b10b4800030760310a02e032191100c8400307200d89001e0240780079510800d9564032a00c0c0d0388900125040407160004640c0c1c0410050480004c40f0300d00c06443c00c0a400094503403010000c0208511000241b6881010081d04081c1c1d00c500040240c6541c0005810b1003540075130a0528082d64225000b114007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 626028030 1250 626026780 626026787
    0x31b030c070c14090105090a0209090f0907123309030201090b130803061e0901060201050411061c330314032d0d090f03080115120f020706060b0c0c01 66
    0x841a601c004d00c040101d0b4030304404e1200214000d80000744084c3c0030040d40c6920b44800d4690b50041e03c0201100010749411401541400500c0e004926403280140c8a0004a00380308a02904e401080603028041200151007040301300c5905004260342c0e04000e05002419019800b00c0144c0c3d008a40c2c0805c0742d554640042001900c08000070061402440400d80c0f070700707003080c066066420f100d0003007041c480f61500086800780300743d0014005039110300400080000c0e5407801a0b9215050310780500b402d00c80c841d2500c0070200031810514090342c68180105840848040c1d0303c010030006d040c40702101d080c581801c2415051f000c00c0d1103201c0340083c0d00341c01140c00402c0f9006102c4040385240c0e1110700341c1c1c0400d0000310005003801c80110174003007184140150321901c0d139240d00c42c1d0040c6104030454580034080d680c050341b0618254168006030801c00c0e4004000580401c00e1440000c0d0500401003080002c0c050001c1c043e102c00c1c83c0003030204508041c18020080d03901a002142d042202120044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 626029280 1250 626028030 626028059
    0xc06010b030106170c090a0b0403060b0f18061323010821070f0c090c0e09010501020c241909080742020d0e010809060c031b030c070c 59
    0x82c000a003030030341c00c0381303c2455104a60360004443c010300c91800d102103001070002c89140c0c100050340180000e0820402a2501c50009001020f480c20410510804009a455100208141244c120940c0007502c036946a0f4503005880300d080100300328200c001c0c2c5072100c1340c02c030f0a050321000101040003c5081c01d000103c05800d520b203030400e03000d1611100c0044880e50842803040300c0d004440e894400008406442000250010360000200c1e16103081c0c2c0105540310705a00300c3c1c000d07040c2000502003642e0201307802030180e40030f81c0d40c010b01c1000602d055200002902214007014008503410010000e4824501020b40d540d41d61500d83ca5160000603803600003d120700314292512554940780300c5014151141010502510000c0d21820503104604041160340c90900503080b803080280f500303400c081c01c405904c02c00c0c03030302c1c401c140b4142103120743d5000041e051603005000800051500e8444e0034105000c0d80102e010300d41c482c1400c100204141d000b1220407a807010b44090086196440034556 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 626030530 1250 626029280 626029289
    0x306060804080f0903030c01020c160b03100504110c01020c01050907051f0305061309030f0311090604030807022709070914070f030f0c2c030307030e21030c06010b0301 74
    0x6070f20745441c0210b82c1c081540700700445509400140420110300b042031024117642c0441e50090100d06030304050700c1c1031340b584a41142404400500c01c0c080c4a61001e0403201c141e90341075400007249018129811458040e20304540309540c00060300d00450441904018025484401210f465503224420801043c08241828000860820780c900341d0724881d030042c940043e406000b48140c1001d1104203029140501002d038045004445949140c0303a0611510140031414148942840b680b000024024402ca01c000b8191550114810043d50366480c0c2d2044c00c1d203056801700080380b0480c0205a1041e10450f4000404c0c001c003c000500440540981000f140e00404140303007903034401c00155003003c00074240000f0181c0c0d40c1c0c004032001c2011b10841110302c902e81c68141100c00007044c0300f5094155203181c1c0104a80d6100840c0b0241c400000751502d072941401c2c017043d900d2802000c03820982c9540801000210f0074215006c7c10000440240010642001558803d03a02c031110100700344028400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 626031780 1250 626030530 626030543
    0xb0f090a06090318060203090325030f0c050a030507080607022e060b0a020a151a060d0b090a0203070e0a03080301171603081b0d08040602090315040c060306060804 72
    0x181040010341640c03250002030300c070742481e0088003881303106843c03500d007950071200140c0d10008240304c192508200c032030a14504c640c1c004010228000901054140c1440002d01918010191504005011031402d02512016040e488075070b40e24140303950340e180326100381c15590049101042d443d52021a90900700012000000303425503548400c40c00040111510810643d524200415801c0c0003400910100c81154010b00c61502c590030510303007038800050402e02c598a002000812108101d14508004e8400c40c0c1081d1102662080749018103454008503500c00341078000c202c48001e05e58007850240500380c0d07504101d1010341c81444441001400003420544060004000044080c600c41011a1050041d540103030402e01c42000040b8003074004488884001c03034408103185502d046509400343c1a001460110108480540340c48c13405030002e041150005803800c9562001c110300007841403924010025413609040403102d800880c06118000703400c180000811500c1100058042c580010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 626033030 1250 626031780 626031793
    0x8030714132303010504033b040203040203030c010501060f1106060a03020405090705122b050313020622150c02010219050705060f0d050a110702100203040b0d02070b0f09 75
    0x41d548080c581e52100103194224003600b440290380c800f03009260003540320342c40c3d01c508250349029101c150101404d4403e0300743c0320071074000362001007034030400030528003660010381e0f0f43c4560001ca030862048200005466003401c00004e096a4000f03007218207985599141d0141c1d41080441c592181c0f4243c03885070f401510018188054070f4aa44a0f98000024a04035542c050780c61f404140183d000001d0107071582c001c0341148441031180c140706c6003404003c004400d4503e06c814809031103800042c09568035004c14043c45011900e9503002c07603402c40c1c0d50f103d44c012580540700c1da072590070750180598106840640490701c0014001d00b00a2015a4140c01808485602c0102e1203841125114161800c0c443c001c1d0004076621208018800060a0340d241c0756504400e000c404c01b40ca201405080710070386000050080c4110704004d132060507504485a41d881c14070342404034550b000b00c2d0044404d050700040c424040c102d0540c0104900c2d4895154a030059072800110358020f541110785449a40048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 626034280 1250 626033030 626033039
    0xa02070b0f0c04050411180117010303050a03111c06051c1407120312051b040302060a1404080304060306150915110a1103061503100f0908070803071413 67
    0x100c048a6010010b051220b0030540e55500190a0720072a00303401c1d01a030342c000f580d150040c0501000409414083c00c0074800311303420741c0b900c81680b41c1c14403000e400c0203800b20301c90030810f100c0e800074912080715000719604c681031826070248030b9440c100c04594041c500b8100181a0400e0003902c039031034203104295221901180c84190804015110005540c086e1842c0403070009034108010000c14001d0340e81030b50b240d070007400c080d00302c0d0400b80c079401d00d41d800e0071400c503a50781c0c04400300c8003500e81c140d032002d80b10003240d04240c41c40505e01d42c050035090000f05000c2055007002000c0c2046955946d420300c20107580c0c40b0101c4541241d12001000155028018401807040c80303443e6190400d40c1c5003000500c4d400e4911281481c101e10b00803aa0440c0b0400c40880c1c500e420000c0320b41040181a01e4020f0910f0400005c4c1c1d109025680c60b4442c42c0c440e440810f48400c184d03c9441500d07000710345503a40d1007461500007041d500c06c55400d80462402816400c400c607003002500e40d000403c6000c07900c02400d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 626035530 1250 626034280 626034301
    0x7060801171207050304050913050a1e0b0708090111030c030109020a140304030909141314070b030a0f0c08010b040306050a060518010303020c0f03060105152106090a02070b 76
    0x2400c0300a200b48140e1154515001180c0010141e00b800b80780a9501c80f4144010041e0000d006006030940e01d4810300e00da008602c000c90350001403a40f0002041c3c00c0503286d184465030700016000600301482d520308003c1c0240d00004000d1260140390000c02003080f0600252080b030200340c03484146101d09000600100c00241d00802410307295091200340781015010703144003a0f104139030850000d40e001c0820046549103002c0c0082d481001194081d013441c2008046454030000d4502609100403000810083d24080c8540070242a8000034180d0b2450700028010190072061465207480e4a40000040c603544135a4409058600c000c5540303260074078545520020b0000600a1110990346060006090307a5101841120408001f5980c6c0c0da0741c510b040c003074104900c0c441854000c2000085141190f42c000c50f13158107554040301c21140d110444031003554039025030300100001c1008003888d606000c03000c9000c6407003140122444003a645d100c61911303041c0d014242c00100001d149001054001e1103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 626036780 1250 626035530 626035559
    0x209060117010b030603010e06131b06170406021c090c0501020a120c05030d020a030f0605040c1b23061602150411010c02270a0608060402010c1502130602060907060801 74
    0x11b0003c980064a2100a41440d1040e00e100600d40303405640308040124480803c1040a5142242404503140c5180540041e610798403d0399000c0081c1d0000d000c010301c0740d065441c64410340300403440d00009804a60014480503409403a10281a0000107041d1b20009001a0171030b0700a4421011081030f0000399440f0050800868a6000602401e851881640701034070074001c8664003c80e282880841010480741180c008034000c9003402c0008812582100300c260100c20031142ca203050b543c40e0304182521555648085094490b00c8100200c1c40200048080c056001c401903594000b10020043e41d42c0c07000c04080709180700e101e000007008034105840340c030058441070412402c80d80c81d680c0040e0f40481a069602d50078841e00c1d15403d00d030700401c00c016034002c06803401005828241003105541d0040240024100200c0c000c0e82d401308000300d0740b201819015082e0030354480941a503144448265405504c00502c540400200328400004008084400d40e8072002c42c242d09040d650f507208035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 626038030 1250 626036780 626036791
    0x609120a0306080a0309060305070905100c031106040b06130b03060a0911030f0303161b021005040b0708040914040f1707020d060605010201110f22030203060f040209060117010b03 79
    0x103076510b070002540c0c0f07814072407070000d40d100741d4807000f00794188140503044520103003401d410840301c0007041c8615200c040d003c0c3d00f03403412400c00e001c03070a10901e400c441d00720703501008803090301400061104100b08028218000c11044902c40c100d90b0030000c3c0c490440d6201000305030b056018038007081003d03c49070310064140740650842660030010130007080c0380412000442ca80740d44000b08100d40002d00e40002c00304407045140c50740c0000724803d030864110130f10700340282c40381c0ca0040c0004007803800340c02250f0040045c00003583d159011418039409d250440c2c403584032411f04221007481d0900070403007072034865a801029103060387d042e52100c000d12944100d10b5980008100002c50140e584d1000c0d0884aa00ca14030105109003008002400e541c050250382d0a4401c0900000f92031a4030042643c0d40749696513501b0074a11181003403039040b10350a40c40a5010b0003a40705000803040f526141d00d1045000362207039a03568881c20011150849581e001c03100c05050301005009a50200000b540c114 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 626039280 1250 626038030 626038037
    0x62710140f1e0a170709180507051303030c1b05012304080a05010203090c01080907060f020c060a0f03050c03010503030a45123207080c120609120a 65
    0xc2c65071000b002440d5100001d000d0200340010070400741d00d066005280e81c07203c00380c40c014514a01d01400c08840d04586405003030340b10f8440340051245486070082d21445050f00400314500341e6a410060143d045404054504c0d100302c0500301e11300d01454408034200c0f0300613901c126002040401c1c16024094040c010f400da91780c100030004191604021005180740038400060362801c0c0000d8561500d04500612818442990300b004007a54021541d201203c07050b007094400d600040004a0800c1649a03403180d2004021544410090703204c2c400c10401600758804100c1d44d100c0d03190244007070100348a801d074194010881c13190541e1003a4101c2910564403050311182020a0b911031410303450807640e80d20003981041082c003904031120901801851718040d10b40c29015140c940014003000740c590300c8860040d4903510041c10007840b1a060611035408190340d00281c03119211030b100c900c1490320901ca000c180c001d040000101049050255000c2d000501f8050000d80956020340c0142a02d038051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 626040530 1250 626039280 626039317
    0xa050d020903070302030d120501140f100c08160b0f160f141222050c010305060d170a03060906050d02100c06060905040204050705030403020a080306062710140f 71
    0x1038508000140c1c150b012600c42600108c0720300d6800c012200c0581c84403403280424031404044c2d0b111481181c0381401e00b5a80c0c800c3c14000ca850942e101181c140004110081c0016086090031034500f00c01c09540c0b0030455640d0644800208414048003a82e01003484000c0c01810b803171240c001d43e000504c40c40c2c41d04090510b1075192288007507607002200302c5c6240390181001c03c0310303642c4402e0f003100c5031a0740e01c506100500269202d0075078071503688086506059880c03010400d40d40d20703078848000d60b0360301540042c02e05603004900f0009030401d450010100e410582c0100b03083c4000e002d480b00703075500504102402e0700d03e80c0800c0b50200c0c0144810052120800095012031124010000a4941030402103140e04142c030600c07040b00c130024085d4082000510030b00c000241c0c0030500121480e04011601d071292240c0ec00641240318025925400c24200c7e48014230f030801405d0703207480602084444ca19410105401911301207004809441348100421201510000d01806400802c01e1140300601 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 626041780 1250 626040530 626040533
    0x1502151005090c0d061d0a1a040e0a060605030f10050606210601090e161215080a110a0b030f100909150605030718050603010b04150611030a050d0209030703 69
    0x700c18280c030100c102c3d14000400c0310b640301803030203298014003203445c80c0210241075a80c00300080d940a41070b40030315a2140c0c420160707200070300c00966031040d0040007000000e1003200746581ea01c9104004860341030800000040c20b00d40440c80340591030a56002d003d280840003185c100800b401406035902c21000e0200801114a44036203603040f4060341c40200c2541441000940b500c07001d03910030040841582c01304a00300048000c0d200300c2c03009604000c20b0b0505515030440181008070000c0b03c480e140704400103180c05002a00d0301480b03000d545011043c009090901034004011300801c56101d2040021071060b41d81500010b50001c4010000200c19490f0369018085d525480429520b08105110f00300c0030701d2079480340c4d100902e81280201f02d21486d14018906400c910310f007110701c0d1940c2d100001c032151070a4009400d0304000801c10060340300c0308078409003504079a0043d4000120310800c0519000400011228851016181c1c1403e200d0305007003000c0698050813000d03425000301c440000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 626043030 1250 626041780 626041789
    0x3070f0212060f0403080619030f0203280309152709020304060225170702011209030504080d03020306030705090a1508030417030304020a030b04020a0e130c1502151005 74
    0x1801030041a00100f45424541801040e0000103020144295015155504032840030749400c02200e030b01c101030506c06144c2d400040c0c1404034001c0310348542040d003521000c0910360707841503d503018420344800a09580701c50170b5848600250301d00f0f00104500341c521168000d6002c8803040c00491000c0b443c41d407940c1b079030680001e0340c00c01d55049413480d40104050840c459005182e92515039000001e000041561700c500e8580c10b19000740c684a030b18002000b0f015640304070012a80b13440d135050184032010151400801a5105110b0240680a003042d1003c2c03031482402100d0140700024000d0510740d0403d41000804407024102403001940d480b0010501038000340030000510005014548603890320f8802d04499640505002140c0c00400400006a841c0c0c0440c2007502d4100c48000b805907a14400b04a040e0120317080b10445035062020040304840d03580003400759511952005100b00c1c1d0369500c1c25001252085150b0150300004a40c521850407a80880ea019440b40b04080241d6502c00114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 626044280 1250 626043030 626043043
    0x61605030705010e0d08010605091f0315030b0a061205060a0b040f05180c101202030604060e0405100612261303030e0a150c081606020d0902090c0a0203070f0212 71
    0x1811717044040a821a5504003505d24018101c41c10310610b03100380e06001a00300c008d07101004143c08040f24802030001c3c440d07072050802c000001d0882c8617451302c0e800d21816040040300e40700191400d08c00e01003007251450300100703403080d0b10070000d1035549c0314205020f024208450b842ca4200740e690b40300c84040603860181b107000d00150705030341c4180b503100d00c0b50a0a04215550080c0125510100c0010b09a44200c8018001d82e903240010389079119078001034003810503a4842e5030303000c0d00c00c414442489004600329103404400001002411390b685940002d503848103102130114090034100c240130303000f0115550180145690054a13204184200864540072504140c00244240ca84040e0b1810041d6541024220348090810010381d02c2400030312a500c119802822a070700402c644a5a070030b8500e9031444594099019500d5210000f0414000c02d60040d00740d210300d4280000c113a034035403100201d9210f8800740d40a1440d0142645509005a200410490300540140d040032005181400315 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 626045530 1250 626044280 626044301
    0xc0c080a1b1110080709030f08070501060303050c0f070e010e19060b0405010219050c1011010612290106031a030712030801080d0f030e15100810060506160503070501 73
    0x2203104041c02c0c8414050440c5a010343c00c001d002104050190503500f012a040460741e000c00110141c0409291100d014025800000c04a60801d800401015004005480c008400200302c800c480003556050307948a82d6807080d86841c03612200140a5944c4000e410380d489030300c2e031081107445070303e0b0842d81040325050751086c069664041014040c0f9a4140f1400980010245d9480034110107900e07081e0721401c2607281ca074820001c001c402c840b981d0294440724040c2c2c46500082041656a66101c8115041c10320101c82c941034500c0341c808034101d0b260b060a40c51040d0f10130150943e00780315050380203140389070802425480c100540001c954040004a01070702c00700a8201d40c202d00c03440c0240005d00b040e0040310080e00107060340c0034041c1d48281c0b00c03090386446117404200182481815401c001c2900c00980c10b81041030108000c42c0700345040754045072004000c98150301c11081903042155118080c007544400108852510015080940d0f11034034028008d8915200c0d00307950ba0760031541207004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 626046780 1250 626045530 626045543
    0x120e030a0f110f120d050306130c090e0703020c0c09090111180f0303041d0a0216050c010210140109020c150a0b0a0b04081c140703210c0c080a1b 64
    0x42c146508000c0d1032080050f000b981c0410441c16081e0640b034a900302c071803503178040002c04000250141d440c0002150a48803812082081414086004100003810b0082c4001403000502091180740300344203d4099200003405400c90703100d680308200070400040c0203500c003592160784108030300208034010608204c060a5401036044204103210340d1655a6441c0c41c882c0c0c205200400c040c600c010300011a02301d4550400b44156104070b0514002d024851441209030848004881008000a421780b1b01c81c0098084950440704801402c0640c0c0003205105203d102c5a001045081c0164014008450f110401e440340c524040b58142d840c0c1d601228020842502c07a956114207042c1101030001400482c8075891902d4203017501c0c81d60b2803a0418858441a1001002481e080c0c0309180e041c0041604610843d130781c0c400c6050042c6041d4606005400f4200c122a994010415174412070707a5541e040e0b01ea144138400c450300c1d94011504003001c0d20040c0800000a00e40141100c030540c2c21180c403a18 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 626048030 1250 626046780 626046803
    0x6150510050d0506060f0a080601120507020307030305090601151b0803250309030c0213060e28150303080c0d0507030603060e1f0902030c030a0b011e03120e030a0f 72
    0x54520050f1034002d02164003a0000700000384070384100c04101c55400d480c5040000e03050f1a02001282c0361400507030803000c21071410040c8450f1a0303002c40281140e41c02903030144661740741c080405031603040c06e105400c0d140c2d4449440418683c0101c64640506540043d0381c2c1068405854490055008640d440c02e40940313110a00e041001c00300c101c03120035040d86820082901c42d0b41d006403607a021101c000c0c0c420100b030f10b28030402d401d2036085000604520049030a803420f181103d4000c80020740c41e00e4103480302512000a031a405031281d02d180c030100901040d80a072a545083c1c0300c1c0100035020402041040000c0c40b400d401c207001d03e5000340c07141da0b0001030540ca98206802101e00000801c2c9443d000350b40858a00c0140c0c104020132030b0801032000518415910004e440c002c040f85009405009410348402402a2124400c0c12601c1201c244030200701580e0281c4480411400000c3c030248482c54003281d400d104510702c800481c0090103c1d020314120742c5501411981c3c5580441e900340b00c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 626049280 1250 626048030 626048047
    0xf0429120d090509090f1513150c1d061905041a0307090b030609071d030105010e040b0907081b0d1e030e06090a140102160f090515030a0615051005 65
    0x100c0115803000313005020700082417003506529150514070103800007501c4180301281400c800740c407000c0d80903a0302c940e010500c2789008403418007500e504860035020800c02d0f40c444d041d00c0d0411403c0504ae02e0020035071031401080000c021041e115280c24201000b01c00d12020078214160280c1035040721082410907280e20340210024140702c0b10350424102081b00b80309115241d00c407001480d0b000040c84c109000754a04041401510b020203244d820790642c2007000000312500a2906180507a0052261048940d582004a035943d41c0e24494402e06501c1040126858030000302c000301599802083c6070044840ca0316140d40703039404600b004d10070f601c2800d0340404041c0c11030402002c2850986445013030402c00d030300041c00e030a80b5106800e95040b4201c2114000d078428419041c45880081242642c603456174004041004540100050249444003144200c85070000300c1c00a0700004005241005944c1c2e10361019007100c85142d911036802001c00b250301d85d01c0000017030080446948250302e032800c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 626050530 1250 626049280 626049289
    0x201020304060b040603120e0622090e0a03050318030915180a06020c090a02040e01120507050409080f0c07090219020610030503031b04090f02090f0429120d0905 71
    0x442844c0c4580d04d400301c200000b40d4010410091442d47d0b00b00748421000c560f01144c803c0c030407140c2842c1108030b480e4008a0342e010b000c101800b030350003012081000110307440c031139642c03543c02080c050089002800010550610343e040300d842140c441c000d46e801d09210f0404211025072030300e01c110301c440c000300c3c7c0c2070032081c0e84200204095208035441c441851404001949403100c0c410344034084c0407540c0c002a2020880c0d011200200403404a0500641c2e45005010800e031142034102c9150103a1038000a261a15000300c010064116515529148045ca007007600d9a00c0004206541d0040a0f400a10f200c454805030102140080070b031a60420304110003400d02e00000c00c040c8203082c03401b4050003c1030700041a607074414074440819a80f103440c8281040c072070140d544030075002030420351b001048401075005403c1000e0190303819104506454104410b9602042080034038a203840d1032040c80e111240c240c141e4010303024001c4109403102516080c01e2607005d42950011039032981040065040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 626051780 1250 626050530 626050541
    0x312060e040308100e060103230403050c07060302120c1b1006050415080d0302030601180312030509010504110402030a02160b04110d0503070201030515030f010c0306060905012c030d020102030406 86
    0x10035070001c000e42d41001244026200d000e41b4482c1056070352128151881c0071641c20701c40c90070303801080c2041e81c681031500426661010701d04040901841c800081e20300d00030f0081d40d81450700c045400516507207a028084181d000035100d034900145001c841404444103104d90154200d90308000325070f050400090000f0748a1141c2d10451070914a030040140c04800319080096100034580548e61b502d4100c01220381c19038042400f465030040640020070840c00d85280c103034983e8a900d0501c01640d600300d0f49400c1340d90842c1d000c1e00d14200b02600d01224074181e4002c40e800300031240b0060500780807000300240c040c04e42c0c038100c0e40700b03035108140002c1c070205010702d00d01200110341060200c0b18540d9525100c2c003507040000d05054031100460341640c2480d51102080030050101c503a041c43d07140c6078502034042841c0c1071012900c0c040d4041400c41c400c40e1010161041a140d80c00c41803039071405180c02020081e40c03451b40c06202c1560200c80d9805006154000846a0000d6200c0c103181c02e00c00e04464 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 626053030 1250 626051780 626051791
    0x210b1812090109050418150b01031407170a0f02073009032004020f130b03060a180902060705061b03150904030215090a030e1503010b070312060e040308 67
    0x103800d001c4001c440e030384031510720700ba00d40035500032455542d0381001c000d2540004900502240341141410f200040c82ea100c11605d400c240c1c0c05111850344d442c1c980d4503a490549103070000a18118000d6a0030820100f510b4120091480004040d04a44610390490304032000c212075510414148a005124142941740404250a00402580b00003500a014a80e440c40010059200c1d10201c0e41c40030502c01c0c6001007641301510966444203103500352815035100345420814000300d0300e000b1842001000540307200782c0d8084d1214040368140600342000d010380000b1404c01640f140141801130b2600d002401c044e9204000400060030414146400194507109164002505000f0440000c00600b540c081c4c00c903041d1090140b82d100c0b428101e04250302a01c000c0c3c2030403074441c107006807607000145041e425401b0369030f641b0200c00c1c1241000020ba14080440f60151000c1c40103000001c0311600400002e482801c009000c01141400101076034810b41c00140e0082691041009164000f2070032940b04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 626054280 1250 626053030 626053063
    0x9170307051501081f0908040b03091603122d170109020c030f0705030702041a041107050307020114130906090f1407030b040908040e01081c0801210b18 67
    0x1581041d040719aa001451350240c45d17199046140b4500068951000840c01d401c038003640d83e61602c80c04042016482690525903610991419482c80029802c000c1c050743c3c3e100c001c110a904c2c100a0444508500c50340c5400c09070002c400d506641d002400c0e1b1440075401c0ca403680440130740c1403c00110745540c1607222140660041003052101c140c003204450103008044e500945640b21410850305e9805801c034021b400c14941032501c41c82c1e2000c480311500301c2344111340c140441800000104043e00407202d005015501c1446590015809a400c0d1441d40c1c001c044d211b4149010820441200300031341d17003c001c40d240e9a2409100c0c1e04002d000d00615042d290b9402c1c4030f0b41100c922840e1003040000d09003400c259844845905542e00d642185405039048494207813165154006210305540a120308983d920030ba021240305051003641e10200c0001c1d0b611214141ea2801821511984030406003403121002201d48400085905c00b640b80076043d40300044442191070500e06142c14015441d01500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 626055530 1250 626054280 626054323
    0x40b07090806012103030605060c1006051009030b06040b0303070623010b071101140409021218030d020904112701080c09060903010b040912030501050a03020d02010e010917030705 79
    0x2015503000c42d109500186483c1301c400c8403690504400800060f006039074803880c001481c4120880c0019a0700496840f44002c00074030780d0322001c001c104c081e051046404220449000c10200d480e01100f40d6021402800c089904150540000c0c1140c1c0b1498080f580e0703a50b00c520320ba100035441d10b10019294260a407144d40c43d410403510740260700035035900070075245d207150184440da446181070a401120710580aa280c9442c1c10802001e9000060f24902e20703802c002c001098500420790b0782d001d00800b90040e41c0382102d6208802c02035444406000d81081d182d21084044844031801003131600c1c0d200d6480300000070070342c6a95068118207001c65040000800034050740c000d4003011100d0304d960458003141d64100090109003d01142c0440c80c0e40685482024030501443c000c1200781d1200560f400c04c4543c1c2c98100b0000d060406001c0a034214100f880d0060055024616220207080141844000c00b0f03521212168211150001c40c3c1054101103104000c020003001a2004a019031131071050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 626056780 1250 626055530 626055539
    0x81b06040f0e1501020604020f06070f021302120c040501090515090901090e0d110309010c0f08180a06050a0c0b1302090411100e15070f050303070504060f02010b090a02130509040b0709080601 84
    0x9d40306082e42094424000000c80404201101d040300c0342595000d0880b51009448044080094100c2c0e481d540682000c00001200044900202c400780e0740305840e501503043c00c2c8000d01c00001c1c1002711500480d041000381695503a030b61100340c2d0003040b001030b0116950007007914045c105034141c490602031040d0a21584003401c40030064418044080c6001440030103581010200e00c2c0c080b03500506010380000d2030b0710f643d206890304540c485900392145486595140340031140e17442426040800520031461890028080101a540041c0e241d80c02c44a100826000540d142c4070558080b9040d406d00d201e0b00041e414401c802d1619040c00c0d003404810f8a0012002c035032940e2418135910f49541c0002041c0041055614442212030707003005c11a6102d207030440d0f0103011030784540200b1001c02c0036900303441d02d240d00c140240240802c01400008240d21844062006034000104802c002c81600704003040c0c5880d80c103025031080c1c0c001e80843e400c50030720b45005000300c0c0045d0081000d0f608110014030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 626058030 1250 626056780 626056789
    0x3061509150b0d110d020702090106020a030926030a0c0605010b070b06040b1906080603211207052118010203060102071e030215071506081b06040f0e150102060402 72
    0x5049034000341055980c0c40c0300703403d0350000700b400d600c1d166038a240104900440c0d031000d501901c1c2041c42690840e41c2030362a860b003603030340e4141c4100c0100000d0200000b03201208121104800b12040280d6a40030b0b4108610600c0c2160480840b06002450220043d03040c0480360003000e0051101c3e020719445e22106031a803d004880090032030340903e450300c1002500741c85142002d5186c0e07404e40c8140020f640c6400c8014010300c0c1c180c4403d40f091252009001c66140451b03090410380100041840c42c0140c00e040d901b0b140d0030010b045c6030911a00344100341182103d4101c49040108144810700f0030f240075400302111b105a903030032040701d0784140304002c41039070002242416680f005a403980710a204007034000101402d41c000a400c85000d0302c170403100059402c0070f0000940701d0495030580782400300808084621500c100300242d80170341c3d002e55901c0d2000b0b00c07603540114040c101d18909500d510780c2030900340f02c6510044540740c01c030003000180313484e03452104201c5101340301601c0e45040940025 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 626059280 1250 626058030 626058071
    0x40308031909021026061e0612091c0e100f0c0b07050c07080708060118020c0a0f1109090c0607020a03060507020d12150b03270c0f0f03032b0603061509 67
    0x103010425a840c42e01c2c115694101664040608410b40c0b51103450954452911441403500305101c3c41902c00800c4bd105000c0c1d00a141414005007196101c98502881100d06032a010191000d2050304c035004008222145e43c214400c0c00d0705c0c1c4685a48400030b011f01880c00c3e0103588180c01c4c980080c070b03043c00399007004540b6504450004020004080300c03485850001d124401d0a003800703114204142c070410580c0d80010441c40e00440ca11040d01d4241c0d810700c815001d08446d40603103500000c2408215242003c0a41000c1d4005424505501d13140c0c3e44400803558241e80c11009031344814042110b4035071013084c0c2c01020704250024000d01481200722800d1306001c0c0200e003181070b80071002601e01400740040c0100c103074440b03031840c44e00464400a20340710132400600c140241c0e40004004500e0a18040c0e001000310301900440c603040c00c45443c5154880c0600b609141c0c0c40080d09154100c0c0030324082ca202a5020300d40015449041c13000351090000c040d840f020f1041c2c02c0030038958542c09081d041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 626060530 1250 626059280 626059309
    0x2090106050903190f020109050d020d0b091501030c0f1710020f0c061f08010204050315060117190c031a0d020a050a030804050a06020304030803190902102606 70
    0x40c5440ea1019000207003403522031504d142056801034010b5052024220b00c0f908541e001ba00c401d08a1500c5009200390707490002c5010b504224020000030000e0202c103810740c0d22010603002d8034a040392206194008250a9000b83c0b032403400d82c48180b2160540c26101b000804150b914126a40044544282c0b60034210309000c02d92680405c1c0c10010040d03a03400c40759089000300c140c81d01c900d000c10600340700c442c060009007000707100d1150124115a052084400340c81004008002c20380522840280142d0003d0045042010b0441d030400d0310092040414040d0384010348000c100041414540308490304150400101030800701156140c048190010340f44110646046c04252068008103a0695041d40701a80203c3c011000000380304812018109543c01207035040c10441c2c0d1241c0482e038a010340e00019000f00c40030400328180c070f00754000304403001ca058500032800303886940001c1d4050a00d00c0418000c6080940b101c03130b0002e591402414145400e840f083d4413814848085a11104500d08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 626061780 1250 626060530 626060537
    0xf081f18050916150504031a0912090d0204020d110708030412020c010e0d170307020c0102100515132309190b0106050f04091a1201051b0d0209100801060e0d02090106 73
    0x6000b131104e00c02c4c13084802031900090a00c810050590105080350f01c11101072240d0300820110342d40703180103141201e580c0c030802450003412560740c2c8c0821000394041c00602d41802d50300e03002804d04c038618070054a80a40a01c00b001d84901d86070914411110600550780d045412001721050b107a0b0f0058002c424400d003d17a1010010b50980c604a040c108010f141c543c0030441c08420084c41650000b4840c807032240a07400d803104514100902c00c2a24016612040c11210701c1c4104805030900e482034100f45020b0080c0850443d00300e0a2940c84011503240d0260640e0018040280c2a80200031b00301750342c5118288010020f1003500d4600d013011060080d00b081080000d810b48200070b11500b0380b0301408861401b082040c46c0350074901d44054414007039078001d1f280314258043c04c3d44103205031403007204002c1c0300700e41040f0003001c80c5105610401511880c01da0a0000e00b0061700c03071710751980041840752210000d550610314003511540c000d40256100341d1a503010f072030041c0c41e4840750504613610303400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 626063030 1250 626061780 626061809
    0xf0c1a04050115080d09051206060105030405100513030905030c0102100e0a050616080c120a0c0c06050f0f010f18050703110708190504060f081f18050916 68
    0x241c2180949a1014031903006069041c3c003051568001c105240a0a1251520101c00d81d440301031242000c25070708012010f401c0b92000407060f5000b4002168040c0c4140140e56280c2a4203c407030342103850a81e410b856a80c1450600d604048c0c0110400f00034000441c001c0010aa50b040000d503140300d042d10903a80c851300d50b00302d100820020490b94217481d07409810354246151825005107480d42c48a003040004040c51301180c5200342c2001264180214110b0700c212070b079105c40408010b440003045001c104007000b42c192000c07480700c3c41004d000e64544403000103030341401c4003441110b05043c0c000b401c1d81d03075401c0001c1160030910000071501a00a603070204655450940c2500140703030f160801c840c400000a4a04108040d030401440e000300501c07250441d14800309000c03a40c0303000ea4050400411822441031032081d0181030155401500b0055003810310103c206010120680350307100c1001700440580d81040c190850185651000c2c4101c01051001d00100d14180d0f003050342d21809003094181c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 626064280 1250 626063030 626063033
    0x101503020903062e0306050a1a0901030b070203270f1f080c040902030106110601120b0a050a0f06080106061112030402120a06090b16210f0e0109050d0f0c1a04 70
    0x1104c258a1a6100e40b403403a42d1503980c0c00c000020703040031a4103c09051601c42884030441d85001c400e01c00c48030161400002d41c2c2995a01c2903002401343c0b509003076200c240440f82c0840c1c03070601e003082d81d65100e1000060002a8900713100c0d174947c20700895403081e0380c46544d1141d80581c881400d0000d522034580b824840d101c6c0c00f980e010600c5180c11901c0010f0000002080c01508900c0020400e01090201e4201e6a038480e8000340890340108014007440d0f640001c5030540b0402d0308055040520103000262080340440d081044030203962102c022a512884100826078000c001101941d481c80d01411803540c540288992078440140003d108076011a01e95040000c00c10000c42c9841e8013410810041c542c44c18440e034014402c407030a02d4002120a961b500092160704000c2171030307641c40c482c4c001d0741c41e1030840200582180e800340400e165494070b80080c100c2090180002d014000d00250802c1c6a01800007000514200794000c20f0080c9841841c0011b50040c49000c1c402c1c1d8070000e01c0c1003c0d07c99 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 626065530 1250 626064280 626064331
    0x2a03060a0b09370204080f01060302180601021002030c0c0d20010b031207030504080a0609061b020d0503062704052b0507080412141e0c1c0b10150302090306 69
    0x156001620b03241f05600141407501e00560014064034000c5500c400200145040d4048840d812070b01e40d40140c0100700880445181e42e002b5580007030080c030400b4180700c0c180138840c2c80e01c28080300308400604200e0300e090340d032007a00c4c0c0c1002d086041440244003038215040460341e16000c035454501348100001d10807052502c580140c41c090210785060f42c0c400903103800c1103400350403010350556849160400c1081100d5103030600800580c001c0e00070300001e008400c0140c90980000340161f40264040c100e585011b09541c006c1204400c1204410186007443e060051400441d0029086003c0030715000415910304641c0081d0f41002c14030308540d803031100c1e00d0000e600e0300036940310820303580c060b42c1a00c0400c40700c0f00e00e44031070084010454001451004201c3c40c0301d038034490342408070340114401051a040c003d4803210091903d44a400304403203e80c0e140021a00c048918005840005030144450101c820341d540c0341d420685004d60506030814002600e511000d41044011001421030f400000f00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 626066780 1250 626065530 626065537
    0xa0e07050c030d091a06030c2b0807060515090a02071b030f0b0c0301060909090602190807030501050102031329160203010b060304052a03060a0b093702 67
    0x1040580e502c0704040320405029111050048800c07a41d40d00ca0819a107000317a507507611511006008085180f00c40050003492100b03651000c000c80c5c01d19403012282100ea5101d040d409215502503035884a0b070341131440803140302401d001352a1030700d94080b40165a0b4020180c2d080081000e00594034501d51914125400100240396100c07040b4101c0042808101d654032070010303016081140980d0b485210810070b41c4402d0042c4000301e0003110051294107403035480b1440c80f5104800040c5412700b000202480c40550789244000a03809008001d0300329858002c40b40104800e00042d400d09502000d408000d020601500d400503201c101e09034080c204480c40325a0800c54030600d60741c0c4051100000d002d40312840c0059000790308203070f100083c0b810100d0407248665040b201900358101c09400b58115020548134034100380d41a00136200c2c2c542e6042c06060b0041c2480c24000418419080034856255001810303e015a0500700700d010b0640002848502038041d10402c06802c208a845210000c1c003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 626068030 1250 626066780 626066797
    0xc03072a120b0f0c030c16021810150509040209030a0b0c03090705030601081c05130806010e0106030c0c0605130510050a180507050906011407030c0b090304050a0e0705 74
    0x20114200296107100c510103050118000e00c0c540c400303607560340188403081a096801685074081000021050f0107810003410540c410480440651420307900015100000c912066072901c00e00b0b01030000a016141c0d54a00400032070485401000d080c8002070898003d444445008036000100040196014001640300682c000444460307400c0410342841c0035001103550041038840e036180417a5514000842504a0341d69400400494590018541d405102d8200d8101440001c1c4920300110114a400c040640352000041002d585031a807920020034040c1e101c00181880c0c183c3c601525039000300c071012402c0c0c0018001c075581c0c0740c1d100c6491041c10034071806029030080c0e4520064181d460f0f000709000300014a418480a0b0751a20061460320001c08000c06951084a08000e00d05014810a9206005040401004c040000d40e03030090303440000110001414607000074104112046555003051499009508050034503000c12003203603850041003803040300d0784c00240b2840d201c2c00c2140e0004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 626069280 1250 626068030 626068103
    0xa03050706020436060e04120203040512010c030501060f0e091503010c081f0f0603111b0309151c1a101106091b0d060e0f0c01090504020c0307 63
    0x700c4c0280329055226007600022010b0550003414010f401c4d040c020b03141a00d420394000382e2592695620b0b4200000820107038015401300703101c009260759441c074101d4032550021001090150400c1c000508550058000741c051110700303e11300100303d80c00300e01d50003200002d555440c46070b03d440001900b103182200c03001c0c2c0c0c15803d0060700602e1590110000c1c0c000c003021015140c101540700d508049400c81d50007890490b45901d00c007000402d22030b40040100a280c2d0f00680d16204851040b0760041c040c0010b4440b160f440046c08540c981480c0e00e42c24480d11140c14294148410505400004085802b0100320f65494084a883d110390904602050000003803401c18075080119002c0c1a010074400c41e140d0038015080000d620410100398942442400c698002c01442d080c0c0402410001c000400d48036541d549c2e231510400750b000c0040440c01c400c00c20007001100211800103082c40c056070003c40c00b890043c000e110144600109803103150b50f0000e841444100722000c0c5100c8030583c045c1c405c0343c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 626070530 1250 626069280 626069309
    0xb0603070e13020a08040b04060e031b0c010201200c07123f0c1109040804050a060c0506010308090619050d0e01020c0703020f0102010e03120a0c0c050a030507060204 73
    0x4040d003149100d1040802982c601c142010749049040c03c0b40140140e000100b5403180c00940000d8480b20503550161040c3e0002850300c0b041174180d4075503088440c062840e00d0305441c0d44014088100401c00c0c6180091000b8882b0700300c46517412120303004442c0b60341045000800c5803001d400701402910080e0034841c041803502c85803400c04142c02004075040a0880189412802503000000c11050403240d0021441c07007141c8501904a411481000c2c058444c0110b11307048009039174a1a10040c003440c054010a61510300b84000c001c00c03803405500003c103004414520400140b80405c05504482cac0040006032070703280d628003107041485141d0f0880e84400c1c0300390841407819086030180201404180c81000392540d00d03240d003403c0f44113015483c0c203150f011a00070401450601d108a40b00241840042540304c00c200d034851075a0400c400b0751112904400402c5043ca440d803140030041c01c07a030b240108120304541c60f19600c88038940350150070054002400c00c18000e154046074001e016280c2031924 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 626071780 1250 626070530 626070541
    0x110c1027050a061a0a17071a1801021207110a0306050a0e0105100e0103080d0204030804030302100b060720031002401802040b070f0b15010f0509030a021504090c0302030112030c060b0603 82
    0x1000d80c0020030489e4107101c0301c02801d60319440000d8106d00c880d000403010b07241c03400d9510780c1b0901110b100d942d10360001c444100480018000d004480c060f030304500012615070850200f40d425180000c00e010a5440040300400c1001c0821080c58110781c2c120600359030361014207807034001a10443d0406041c2141c0000d001040550014000b0301c12003000c80308000d00e00c0924200036151081d0000500151081d4402142101c4680c8a040040c030f801000c4540d100051440ca03000d9800860f83c00e022030040e87c100c402004507062a0000d032104920040070303600da0944410300b4040312030190011744101c4003c485440171056040b180500306080285403038014529200a0350305c80e48904841e01d4086501049100c006d1042003186044161182184000710010840301c0f5044102d205038141309981424004d0303180c0d1414035440c214034101c00d0350781c1d81c100002e44040e41d070008202e40c00c0604c10001040024060a10b0490280c1d051400082c680c14504242c1c000e0071807407030390700e601401c00804e010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 626073030 1250 626071780 626071829
    0x907050d23010204030c0902090d0606080f010b0f280320030d0c020121090605100e070c050c0112020d0f060504110c1027050a061a0a1707 61
    0x803540410710406045a14500701400d00b42d015912009107200320b81c0c0d07030030701c20684c00e6000307050f49940140503100c4140d030588600e02035a01652210245402c5440040c0604500303016024010605840030a803d0003401d020880140312501c2a101001c00a8804060b0114140720000159008002d0115299080003150104412009500d200344590084034100e90b004d614a4021250140c4030854190800801c0510442c0e80c049406017030b03a503580c032580001e056885554001d90041d180d620032207040004912142e1f8001c0c1005041c030040301e41c040000380c4001901440e4810030b00e449024500d58220b840d001e80904500e482001f800c010305010188800c0d840fa90440e1030442d01030041152181d98518507218030b030060143c0b82c21401e8082010300440e0003030005000850600d0518189140101c260b0400050046070181c0049103104140445800ba00c0341701c140182c00b400b6001c44400004901701d045210f00702c40d040301401c0269140d0020f0295000070f0101d2100c100d01c01d5070751007008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 626074280 1250 626073030 626073053
    0x1205030a06060f090b1305060f19051224030307060b010f090303050f0c0f060106020304060306050906031902061b1c0503060109140402070606090f0c081e0907050d 72
    0xc18285150403000600c251052420051210380d50b00c50081590914103030700000e81c0511982c0200400b9038800141c04d894060040c06004d40e41081e040c4c1314100c00904611b5214048000c004001c01400b6142540440c002a02d8000500d0050008940000d04404050548201c00298580400b241001c1840f50f690403070302e600ca0090361080684442e600303041c1e42c42c0459001c041c002480500411305c00100600003410206e00c0b01c01110a003201229007545005026003011005030408607081001c036400d8002c0c2409800d00703c1e84e16a1601e4001e000c030b59141011400503a198507205580300641d115401201e80140481c40c400d0b00100c0e42000c490b9690a5054804200a0b0005801c3d110700d80702c0c1d002d40c1c2c01a1016954118401e03d0007005c20181000d80c80c2e00c552080c0d0801614000400910640c401050000c0c7c02003012581141c2c0001200e10307042408080c0700b000c6042015801c0b403d200f455074501c01c810003060356101e07058918900442e90300722540244190461006004089440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 626075530 1250 626074280 626074291
    0x1a04060e030a091208071202030c0c0a060c021e0a0f0513020307021f0204180903201020040816091109100e04090624031a060a03120503 60
    0x18000360038039505040e6039214400b03401c2c0c000b03400c1441c140214094120f00181090040c2040780c140b00c032907111122640f00a03c000e07400740c3c0c0001500902c42c0d0041c030441005030012642940c2c014a01400500007a0302c00100070321840302e196140c41600803140a80ba409103020f090341d5070f203076142d034203a60021080b030040741c3c4101d403610124001e01140380212446002240d0142c010b030082101d22501d0105c8081101c51004d8082c080070524070100f4108150024101d00d020840e8007036406c001e850b0b032080288034404507526006400035a00006962090300d04906070000e0004881501000c0c05d1500e1800841980d03c000760000d03410400049208041441c80c80818440780c0d500c203041d0841c4c44003502765100800030700000d012440d020070103404135546420040c0325040030ba030008044500b8014110350a40d56202c40e00c2d1101e103840010803011000c54070300c00c41c1c0d034210348278214041a42d200032445500320300005a42034480b143c21078021544540d6444084076006000741c21500121079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 626076780 1250 626075530 626075543
    0x21120c0819050c1b12030412080609040b1f1206201201061b1415180c120a0203031b12160f23010f05150312030a091a04 53
    0x481c0c50544662207514018490b800c0034030f10b00b221071040c2810804100d0780410560150340ca0800700700411100035031066201c1d4091407012005c800300a4a6414064002400740301813500b00000119021241d9400c58000b40340110114104c40d80b00140d00300e03d0b00b03c0700f019802029500100728440d000401e620700107902090209a41d10075190407400f402c94100384a921a00c01009100c0c00780b0b151041349190300002e0704800d80306448150040307800303c4440801d80c1c041c20910000c500851482500701082e0036801440c90f800c03681c080c0d650038050641c1480f8007041c000721584032200f00070008040e640034041c2d94131407151804400820000c502c20280078011240d00600d080701000c11200601e000407003031800a5403030349441c081c403110701e08110b50782d010035104020100c06100c00341c010074880c0e03400400c884608000d0182a6032002d0523070071101600d01d0030501583d801145502d80e40a02d00321254403540c940302100060620715101070060764642c0c0620084225560402e071040340501c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 626078030 1250 626076780 626076811
    0x80d061706070f1b020406090903260603070308091908030a02070803030c1606110c011a1005040b030c160311160e0a090c08011803140721120c08 64
    0x107000b50307a4841d0b9075162000184251052480c0030308444c4040d244107001800c00594151030f1014901210700c20340d4140e0102e480032401c0f0342400f918810101c510090962180e0103810310b400483e03650301950100511074100454a0402902c0b0080700c1c4040c18100f60b4107000c003035510802c1946a0380007101036070041c040c82030b0100c0c42d18400401c5a005040c842500c520f000c5011860240300d0001c141c0c202d0b2019207865810000319486000350044560003400007032403070b6416942d1049120800000b034010300e449010a400d50b50410165011244030119541e5a0b640d1040074403218803602545d0616000054040740600da0b001741170741c1c9401044002c407000c0640d1481210342043c01445490a00c4402074001544e144aa81001100c0c510030007440901c152a00c03403007030940320119080501c2c84c0301c880405040c1039100c0c2c00850400003152246142001540707441981210f054800303040b2607036441c0318001c2c0c10300c550050202101c241d8001c0180200c80000100011001d95820b0344109448 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 626079136 1106 626078030 626078041
    0xe070b0304050d0807030b03010c09061101060b07030f050d14010e07081b180a03080304110909280206070501060305060115050d050709030b1e0115020c0409080d061706 74
    0x15121101040c0c2084cc0c000c002e031140002010290381414001c01c10021401c0850300c0c0c0917010b00d001c541840400409603007e1240030064003545140900c000c01d003400d00180300d81a51508003518806031290103003251195002d5900d500e00040706203107421202c11080007040f580c0700c400130710024610301d03000041251511f907000b99800700300002080200002000703404c4074171504490242160400c1480c2640c0e8001c00c0c0c55024100c0b2107200d0049541104c580c071103450b268001e000c180e40b0003003858010302070111072004913840c0c440e075400801c1d2069a441c50080c21081039a445007400b40303844458001d05030290a07076040c400d0721100030010843c0f080c0441c1c4240141240e0090f0220b03030140300e40c01d215059005511025400d0907110304a5404600150030041c11540400d04943d5410320003524030520010301900c502d841c00000d401d4800040c860685031403030050301d401c1d9684 = true := by decide +kernel

theorem cover : BRFrame.Cov 625899280 626079136 := by
  have h0 := BRFrame.cov_init 625899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 625899280 ≤ n) (h2 : n < 626079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
