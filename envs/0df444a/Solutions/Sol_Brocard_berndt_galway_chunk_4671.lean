-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4671
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:21:40.768346+00:00
-- url     : https://prove2.me/submissions/fe19fc47-df34-4860-a207-4d25c17e8b4f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 839928057 ≤ n < 840107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 839929307 1250 839928057 839928101
    0x1020f07260304080d020715093005070602010c090b030105040902030316031d011403071d1009051c08181305010914091c0c0f0c030503070b060a060504030303 70
    0x2000d00c2c581c0700c2d60040000c0e602c00030304003034140d0381072000300040c1801d660718680000d0306140003031a10410380103d0468040b518007005c050301c0c1804441d42030b40c0081c0910900514142415529030180307105040255080c200d08400b0203102c2c00c119410f580710310030381c6800c5909000510005005140c4201d8061204016441b1907406020075405407900c030b80ea440c142e1451843e2800d00e440005240c090500500c0250244414650020340b40c1c800c107613150240d80000403c0c1284101001c5455043d0460481c18140005c2507110010009854041d120100c1c1e25401081310302c500c4e881c5040151580c1e03402e008a000e1201600040d240c0c01c400240702d0000b02c1c261091b840100c031020b9101c01a015a00da060444503901140ca10b0b500100500c00340090490000d0301040c212914180c2e40100700808c000101007160107080388440c1c64102c10340030052912458215581e5009807400c1c0d4400495000250312031828100c81d4080c1c980660f5000d041c00d240d0758060340680040f0385408044415071003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 839930557 1250 839929307 839929379
    0x2150901141b151501090320030a1202030a0e0303040819032717060609011202180708090f12180d020d060b01031a031b06040914040303060501020f07 66
    0x4a030400054066410316403d05203804e442040040241082e418030600c03a20030008100c3c80289483c2200c01500240e0039001c2c034200080c2004401c0c1e90003840c0c101001c802d48800760b4000098540c42d400346c3c4602030b02440d07940c101942c9002364410008560f005010001131154280d284000381e070b220381407003040000307101c5490601c02c82c66034554117000755840c0f041103001461021038a0781c1803488042c11150030080701295412a0500440a03402074074034031a800c64580d40196010208600e6aa22032030516040080c001901510340190601c900c81200202070070100d19001c00c84004a001c514103000f90b1854200400750f9200c50341e200103007813400e1001da140c440c0c000049034440c08000031a80031402c005822650000640791051902e00001d03070750740d280080c58501e0301e060700c01d0b00c0740a9002000010003603c02c7d07400c40f1f4001c2d4105000700642002e48100c040c059403080d1001d0012507240d100480c0d403920098034007249540400801c012514070540400303004986000140708207482c0740d1b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 839931807 1250 839930557 839930563
    0x708010204060c1208070c02061305090907060906181e09090b04170c03120a020c070906080d0f050a0c060608010207050303011703090907030b010e150702150901141b 73
    0x1610007804110000060b0003041101002c4180d0043c0b42d00b445c80c020304011400403c68071900304001d000c2c0782c0001d2450b003000141860a402020300501c01006440c0094002c0c0e01c440192148a000c601b80d1781c3c0129a0a000300d602580e8000e28494207003000f07180c506111545a0041040c10020030051404107048200d80a005c1c59180126201049403c05140400402040b090340d981441000e20907004505004000c9903d100c0c01c600091200740c46245641000b03106032208502c20740b14032100000c807000a0340250049481c0c000030340703c549001000c1a11441300003010000001c500700b051150041c0941044861030b40a4280000c0c40c90300c031115282281d0000205075000e0b8008401084036103180c8031064031084440cc0510701348200000414072800c800f030100310074141c444009440716407151115094440c3d00400c000100500e080c00080d6a40c0f050400303a000d164180603002e692110f60701182d0b555041a9180388041c40700d0412000d25030483c031108801c600524202240e80c0d9020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 839933057 1250 839931807 839931809
    0x706092402070507050a0f0e0901320a090209010312181413020a0203030f180a0f061b230f030c090a0603140601080901090f050d180b1b0708010204 65
    0x119801a5200c0e1903043c07051400074a80e005a10440941d80107204007404944010202d980801c402106600c640e4103003405451901ca01c452840000440b60030310b580490009a0020300c0c0ca8500000d40e1079040722003055440748000607401210a000420014a041103c42d18103042c1d4a490000a01e058400d6448161151b20052216498030020407080c82c28040c3c814013031401c40c0085140c448007000203526800000c10f4003200f0304810340051402250301040b6018901c41d0410349050120300d290146070b0f16040e00d02a01d00914052a81001c00031588800102c000244c5504401d07400ba4900e5903083c55604100325070400307061150f00310303618007040514002c800e000300c1d450301d41d020441408203120b000c0d80007000700b40c140125a08808500c80c40303c1c0d0001e00a1911030610341d03c60501d14090614500001c040141d840d0805048c810046a480d000c4800c594400003491200041d04c500040176000d410b00d03042d020005614080c0c00760100e600d40c4000c0009031042d036656150428226001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 839934307 1250 839933057 839933123
    0x90f1a03062d0a080304030506011406040b0a0203130b09030703110102011e051618120c0e070210061a0f0703020106050a03031e1103031627150c08070609 68
    0x18440c026215071900003c02d00c00341143d036000b1400d15245844155980382c040c803400d8a01140b070a404642a01d4007422200a80f880c0c054103590b548040c58002e640754005018900317402600900800d403001421700301d4180b0100140200042420742d21080980420000380d075041d0740d41d40300c1d40c4025440040d002c540102c0742c107000045507d000c1d405083e84046000000c41088612209008035100428140042c1c41410110485500c1e5a1a1403140c2a95540107494151400006c02c010940e00140440381c83c2c130074080c2400850780d80c0b08040ca102038a0280c0c101c4405e410b0002203118412040031b003030164000d100100e070311070365503001c41d01d0650182c2041d0005901d01c03a00b2210b0450340402520244003929080340d682c845401c0b9580c40380006007840c4001c003282030340240c03894440c1e000c106d40d005082c04030002040060388003c42c00c203414850316100e41500c1c140d0300c90150181031042c241641000515141c4140d50b690388000f86502d850807190580101500340311134072428150002540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 839935557 1250 839934307 839934379
    0xe0712060203060f1005070f050a170c0c0f01020304030305090a09020a08011a0a0f0c0f05012f040e040b0c04030605280606050a0f02011407050a090f1a0306 69
    0x2401d43c00c0c850084c40f406200c1303001d003600070309014899920108030742e101d9800c0381c480c0f043c82c0300c2450712a04000e02c105014103c0e0890381c881c0c0901c0041d0000a0442c07640880803242e20310000014010740010301e040d5a03001d40c00a00c000c00c0840e01841c0100818070006104014140e2101d00e12800c0fa0000f10440c03001a5000c070042c001070654003540321024016107000342c180600c1200003050f03182c030500c0c08420000d00344a6541001600714000d1050b50340840280403521401d002d0340520f42c0103482090810380003129007050f0f6a412801c840503a02000312018196407251520302010b50040c1c510890084200800801300b2850301c11036000380c40030060304010394007031201d9103103aa038001c0120b120a0314041041100c203800030200c2d159881075042c810100c000c090800c0c0c2c0100038152280ea10748cc0c44404000318540d0207002010b07200040d48902c004a911041e81c0f0074400c046018595140448a0700802c02850101c046c69002e20000d000840482400c01c40e213085c0c2642d130120b607481c04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 839936807 1250 839935557 839935561
    0x7030c060503040b070309080405040b030f0105010602010c0e0d050d050306150415140a08060919180c06020601060206130c12060912030902130b0307051203070302210d0e0712060203 80
    0x80700d07204c000c0c4c11403010b1070700340451982500c81e032807507224501ca014400d0b5520b01d10001b032520240981740c0d549410100801c07035907a451b9006030203007003181a0000014038201003c40207181c240c07d400e00068100c4010412802042003c0e00c00c1c0d400a0700c1143c2c45510380c601c0d003c40d180d0038001000500f901e040440c0448450050160a4030428400c0034010a0180b091600071a40001403551149080301d00d80d01035282d681da103031620500016040061030030b0074411280e03400380d1501440201c0c41418100d4001e59514000c90710f0340002c0c0102c038016003200d0b010820001c41c5030034038604280600d40010540e90340c0c2600c0b00c1401c002403400c0b45e28030384800004043c0f00c0c4c084040030340610281020321241d4801d174001240441d00c5840952030941c8e4081c3e0540f40c2e1401c00402025040161480000d00f01032000d10341e80e90044a400c4005200389482c200d040c1c501c41d00686040040c105080341011030344210308d005030500c01030020140c807458100107422580617600244a60007403100582da4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 839938057 1250 839936807 839936813
    0x512012d0f05100302181e0303041212020d140c03040b1c110301080703141908031008120a05031e0a020a03050f1003080d060302090a0b030d180b090307030c06050304 73
    0x1083c8800d8065040c1841440781210a2440410403d00c40c0000c5038070110445956201a19610203408001e8041c400401c0100e00c01400c00b11484c515030142c6107091000203007100c1260b40e092141c0f034500c00070b08075400381245a000b910103031400d2940c2e04156030070300f45c8600300c0d5801034100e5800207010404104105240c07000a22801882141c4200428031710340c1000c422558400c142c0c0b1000b0300c081e032042e560b80b1010a0034002540c4120800446503c050302606048049800c1942c10305420031001200040803840020010f12818800640070b04181d0700080035242600f004016642d210a1f000039000907070150150140b14403142000141ca030f101d0100c2c01400c94030024420b40d0407101041c24811a403680001d48000c0f82d07480301814bd81c42c0b0000c401c19002e0915640025000024a81402085401c5400c14141280e0a80480d501d82c6024081207814450603003040903200c10748070003030010440800c01410101c10103401c450140b6038079600c85208242d154010740020300040248410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 839939307 1250 839938057 839938069
    0xa03050612070305070501050a03020c0a0f140c0904030c02040219020f0706111902180703020301052e0e0109030203060f0702070f030305040510030908070b0105010f0512012d0f05 79
    0x100900900101451810769a40f5030355180d0031b0240d42c1c107019010038001007407032207a0102c50000c0c0000080d40c5c044445d61604813880d145841e4215100c8900c04800c1250301000100c3c0c0003d0724000303002001d2501c80d0f45095404865020301039801580030409500c4810340749504980c411090ba008141c420000c101c5182400c2c91a0091b00c10412040079103008410000703005001c4403500a040350070f81486100180703108030b03045128012070b4884410810380c05d40550103075041300c10aa034400000d508040351054624500f90b0000c42c802d00c94150500e031a4403030b170b0b2440740c08107060400d41d1115840e9000a880e02e18110340d00ca0844204504010b4800e0f030500c21500103050340c03a0441c4035941165070180690246000d1140070f0081c8500c0f159986200750098100c141d00071610f255500c001d420308004c10002400748a020800448504400d14848d0f4121540000c24095003402a4204208548821948003020091072a1300b46644810802d40c500700c4010000030351a000172034501014030003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 839940557 1250 839939307 839939329
    0x7080c0402090307030b061807030218010807051c0b03010608061e09072306041415040f12080408011506020705031c03021c0c170a090c030305030a110a030506 70
    0x30286006101c50001518001000340540741e00c490001c2c032650754030000c1070184280c804042c081c15841c4d0140211a41c1545c0101010a049480f446a1641c64001500c0b040c000340c50090000f4001c0000c014000141800a22002000c403004254805d940c0002401d40d8030035001001190804003d01640140ba9501c400e0481c4000c4050300061a101084980ba819944102c41400c03911201a001b06102500c84190003d001000d8a4803213480303091040c1c481189440240c060031450603003003030804104051b00d007242c1d100100000c01c41e0070035903c40740c0002280c00458400f0014440892248402e0180c1003210f004882d402c52010702e00007000340b82c10b51aa103c40d009070406224844008103c48042c1c00e03203140b0f030601503035861036003190091b03404c1c000c0c04000e00589001c002c0c141d00c6a0224010810807100174040c0780f140c5034000d183c1c0803110a450000c1401e54885001c0000901a101440c0d020040c4800018001c400c0c4502100b0366124015000000380c0c0c03030080140c1446d017025540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 839941807 1250 839940557 839940559
    0xd2a0f0f03081210120b010503100605060910050408010f090b071d01030903110f0708072103030c0c080d1b050c0c0121061401030605031c0c020d02030f07080c 70
    0x14400c01e2a41c1c490710100c0c0f084207121401010800d0016501610500081c002050714030b551840c03030180c034200000c44c400d0a0087c18420b006100a0b148002d03032a02420086e500700030681031603da2030038100a40c0c06001c4644005111050200041c403c400b0f01c0303401180b507031291010444040b01d20f000344280e200204284144078103104441c1007100300e9481005010000c0c00c0000300740032036080540b0300044040c0390f0a828842e0050380d00e00c0384004100b8804460b00e1108983d0380703544902c00c4d201803060180d5803c81d21345c070301c0c4800341c04207100c6e400c158103408003418050480d841d02c2d221107145900184211801e180ca43ca01d200c0c00c1e41c0d4008003051600c0300f501d002800c04030140d12a988600004800703904001c40780290750403a80b00c441c9050003030101c1500800855680fa00141c2c844501410001d0110b803510310006500e00f0081240d4100e0f51b00808102807082d807905054580001c01c40c41640c011a510b503e00006890070460400000034210040807a503240c59203491400d1003060880d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 839943057 1250 839941807 839941829
    0x8010501170313061d091609050a030203030706020a09080604031d0901050d06050a0b0301020c0f15010503060a0203130c08101a33040e0906090307110d2a0f 69
    0x20007000780d641a40d0100f95004c92801300104038040d215660002c1112120941c800c403c181802061460030901140c840643d0710b0740014160380d0020000710044500c4080d42580080101c20000381a41c0e0041241e0140740c00c000c500c03151105102e40c0351010454040380440d4007034a03008084642000380a6604000b2500800c46605110100303a8240c2a86001444241c0310f0001c030305c030141c080d0481e0740d030501c0240c021520b07030307514003001070356130341403105030909406040d840342600b0342d43c80c03503c60503140003400900103500d82000d050f0095100420101040d502d04031580001003040022000810802006180b1800c940c1130b544100c40036941c09035064840d00c040c0c6400c0d030712000c89080c0141003010142c1c0e040d050300f00221044044000302d00184907400940820f50300d290040cc0c80c040d103a010100c402695030390441942e20301c1089405071401c1c80c4020840114500010160401c0d03100d080c5428010042c2d20540310103201c445000d5500019081003031103043d0318944404024005d00002c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 839944307 1250 839943057 839943067
    0x5030a11010c1b11060a030f1404081209012309100603110609040605060313030915021e1618200301060806060c1207120804030906050a0c0507080105011703 69
    0x14007948210000703108140f003560004070921080020f2400d1081c0003604503641c1e01c04003078008005200350f0702da0a140c213240c48203e00c000100c12107a644a0356001501c6403078090350b40d13085610000000d2415940b1344d03d5a00c4150140c800350341800c09648045640c44050505000c1581402e000c0d0021044040c6030200030404071740002e100d101d03950000d46410381c1e103c1524001c43c1c0035000b6500b00039000708001061100b100003920b00719914038000e6441003d45511010408809440c0c1480341c0e00680c0700d541c0010049003411089540315445204940196150a4404c1c403441c1b02170707006c0803c58480b072014002c110031602900c0e41005101c1700300f01581c1c000c060381031140e000c18000c030740800010f00002011a2140001c0350401e003428012603014202050810a0580c49410704a800740c2c01100b240504900519013680100e600d03403070742400d1a0030500112101d400076a80c0d4001c02c0035032951400414030a000c0307032001d0501d40300017190545c1415401c210424040342807803119401008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 839945557 1250 839944307 839944331
    0x6020a1812050a240905030415140d0c121406152701021204030501020304021003060b03061003150602060f0603150f070207182c0a020904050f010905030a1101 70
    0x1440400f01d0340e001404a82001d182e80c06010040b20304c01020410350718081040051060001c0500111900d804400316000c450000c100d801000c00342000c0800b21061164076008141500b04a600d2291850524158034101e525401030329406440142e10415101c14407441e42459400d00c0c0902d4080c040d1540703400c12602c40c1c0980c0910030207402c000d6200c2c28110402030382c403e01445440103440c02c6401c0d121510703420218001d6105442c100d00c568252100024414002e0003082d0840e002c80022600799500d81c42407000e000301d24540481050790710000800b19070b14140340030000e03062503401481e8501e4602196a440c00001c1c087c030344240c2c05404502070403105a00b070194000000b2050040710b03154844c00707924000054024260310a03200040d03c2d000741859002181400c10300ca4218482ca01420b1000804100c120814185800c0000d5100150a2080c941d5030441d110340201c9400c1038802d580e00e42103c4015604880ba43c200180c1840449c6e4000c078008001208030b0000c0082c1c80d0844 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 839946807 1250 839945557 839945563
    0xe0c0105030115030e0c090421030c09060513030b1602010501091812090b0712121512030c02040603030206010e0a0606020606121c05041a03090a031b06020a181205 72
    0x1649640404d80c8640c40428400341c02d029000c400ca5015180e4115410945000a22942030841121500800400d42a84240b00c1d014442110585840b0350041c6402c2030821541a40b10700c003216440f200218000001440348040c440c0701c1d2102d40e0a044803100340400003401d40b081a44080b010a08000141900f0807401c070064030500e500c216010b142d01401e000c203549495407a408458106030124004040c012a01c50410310b207401a5200c01e0640c80b60212102111400c440c1c0f404611b200c00414840920038060341c103100c40c040d0924044000e4030354005001d0b24020b8004900581059004201c3c6084500c500d0b508100c00603000e000d00750511700002c1d99110300420b00d600c00c401400c040c160500c400c1c00204003100100c03200e0410b0503581d907401760280d4414880c04108403481c510042815602e00c054038041e6409078003909004006450840c0c011241030b81c000401c2c07039060a2100022070501c014410010b560719071128900c160380303c80100c1d000301d501440c6524000020540095004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 839948057 1250 839946807 839946839
    0x110f0105070b0a02250f12110d05030603160f0302041d060403030515061201030209070203040303091404240e010b160336051302360a090e0c01050301 66
    0x800f40c01600c1d510410444441da0340b894059450500000e2840300902c04038030281e40d822401484400d480c8000c000d4201c42c41d000c80b010741013040d0841841e100525200d02c0055410060040454a0b20284080104c0740b8003110b0b48900e81c584240603003001103003020300411508500c00c082c0180520b0000302a141c03210002400141016030351030003d090241014204006c081e005484180c55a1001207000840102808140d11034028100010030144c8000101e03801e40343d045d680c42c800c01d450982d00a00c003101083c1201c0d4401c1c0c4410002c040d008591003990f40300668a01030340c00641c030b0094001c6000d00117801143c4c1000003002071143c2070f0200f490056106038140b9081c042c1d9101d2111442e91111522501031b00200e08880d0b55501038640c0ca41202521421298235400241c40d001e0302040b4030858404500d512016032540004070705086040703040f40d024405c401c921648050001d50810400d030002135540d0f80d14a010700c05d4500800c00703408904420b080c051308d10350500c0d007200102648 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 839949307 1250 839948057 839948071
    0x908031b062a2506020307080108030913110408060c1e070b0c030a06032306090102090d0b0702030730090b180307091b0221030703050a18110f0105070b 67
    0x1002500f480070340040f05000040700c1c6018241070300d41c4001c1c078214019600c1952007000044480c000403c0d01c01c0302004452401c10020489404040c18410304006000c401324100c1300d6079000d1000044140701400b08510a40000c40c44550715244100042081e8004002890304604c060022000003194564500d40203113003025025203a0b41c03500320071005090b154100030600c44502001c11140c00c07a001001120b40d41940c29140159144128903080740a44609994003000c035011b22808982c828100540181c02803042d01c0c41d158150312484106500e0801261501c4c01c03881c00004003201442e051000108d681c03800000092400400d9848c6010b10202ca80c10410455007040c1140c1c1c0400c240310081c00c0f4118288101034107c441350300000c40040d00400940540c1100000f603020040900b8206800b1030411030071078469030300032401000300500021000b5a14201d50205402004600d002c2c0d0f4440c4042d2190200c47c00140300680c0200724590341440814800000000c40c1c02c03101a40c0000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 839950557 1250 839949307 839949391
    0x70b040b0313050109110f010302030c040905041a100510020f070509060f04090803060405180d050906281d0105030c0906070b0f010806060609130902010908031b06 72
    0x71071120502e4905220a03000740b1540c60108590100b01c0c40e003107902d4000d64212000b0740300030104801901a88422540842c206508001c02c0c454a05a0f03413201c0d4109026000040054003045d14200d55110103480d0500d03d10345400042149140940001d200811544054581d11b0f841c0000c1c7c55603428180a51445100d401c80001c80390b80b0380300207030354403464018018000a8600d041c11180d40d402a2001402181807a0028a5400301001c200c40301031210001010440c03d509000c546a42003000b45952002003005103648811891001d5020320402e81c000290100106a000c2d0403808084280402a01240c1e83d407410740e0307000f00030307284e0103504441c0380c540c1c9068007000030762036100710100181244031840c144003403810444080345c1030740c05140880d4801d0b00d81c4c2041107401d00803ca56280c0c01118201405240219504865403940c410b04126640c02c0c1c40f600154155085262408003e5492012820b4030400c2000381c540c1040ac10404614403107503010222034100075021000441103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 839951807 1250 839950557 839950561
    0xc1309090519051c090e09070312081306020a0e041512080d06081621020f06090310020d091b0f0e0c0c010f020c0d210903020a06020f0318070b040b03 66
    0x52249980310b8113501c4504041c07650703e090103028294a40600001003c100c000030f00002000500a001c0d00d070030040c0101003e0050300115040c80005244903602e040d044412170001c1e0b0103002500b050b00107a2983c2c8501c070b07452414841115000e50368000000010801004030310354410300d0760301c040d4000c00115038603000d0115a070082d02c490780c001541e51040035011000049560401016280c0e60310074004a0039903152401b11019881001952180529090b20b0841c0f6180c40100454400602500c4807642c10390418412a0400c1294180d032540b075034445401c1213581d426420000c09450940031469041070001020800c450042504010a10010581904000c01501c2c03035203d0800084c0084050314544902039040b02c130492075984074440c894011032b0700032460681243c88410007a0554140c0d40f651002418660340198154005c10300c2400110318280000d02c0031045015100703650307003030020f00500884001d00007005550008001484580078280858084640c2d403400b040e01c039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 839953057 1250 839951807 839951813
    0x7021315060c14100b1306030b0112140105070216120c0306090305040905010620060610180f030818030604050a230f0706030c050702030a1401140c1309090519 70
    0x24074000141054076205407400d03c00285200d800c480742e80b0206444030340000b1030541b610020303a641808018003d800f200b005000000684000018060141c0c24a240740300111103020708551059030250010f820030300d085011501c4100802c0014800c2034404c00440030142c80d00b40240700b10b400010001d0340c0b2242c803401803612480c280c5001d080701000800095075610800751642c0c4ad20794004442d000840c01c200b00d80d02c000716916108800241004103d6030079003100b150403807181680400030744204c6d0300c046030568010300c0702809940308118980e6502c0c82c0700d811521144420408911a91180040100003880800d1444010b94000c24202014295102d12161440c008111400c144910f0496601401c1700040c0b6008541482d20308118140c02000102d44070b12468102030f40545c0080c92480004240144005460b4601400081e000400054003881e000c000d0390f222160030008201d000019011705000c030020000d0403820080c0d4a5030343d40e82c54035100948168804900406041014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 839954307 1250 839953057 839953073
    0x601090f0909230a17040e04110126010521250e0c0306040509070f030807051c05040906080109030c150e1204141206041b0906090207021315060c 64
    0x24010000c00703c44907410b8054100e5965600d101d0195070360080070040000c0d000f402000c85040d181c150161a2180da01c9489920403c205900410304200360507506c00d01c0484404888442142d800c4950b0b011035145c00704000c805071110701070316030b20380391004105030320750307000a01981c507034607102d6201407203490780c03400b220054810350000944c045060700300000c0c00303400d10045105200403603040005840d041c0d20250b5424960080240c400c840301c0c8240301245100001d400128800c10407154800080c0400320040350801443e0808184081001e201c882414000c40000c1c056240c000c020300785a0313031402844080180d10182400c0503007001101840c156030002d0f040e50070b8000844020501040ca40e41d0075602900c101c45800b04800010300e114500070250800f02340404c1c00415440e2165110808030f060086c55004486640c1c0f0000144400c15002e503000802c800080142c5071b4200d401800f40c0011503889102115184c03600a000220405881034103486c054545411002420320740001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 839955557 1250 839954307 839954333
    0xf070e15040506040605030f0f07020304060c0204021905070b0a1b050f12010f050f0405131101110a03030617060709060e03190605070e090c161e11090601090f0909 72
    0x3811a00001d40410001e4001c0007d50040740c190a281c0c02c6d541e01d946800210141c1a1340340c80050304100700801070a4425004a540280010401850004c0c035118000d9844007080d100d101084010441d0700c00e00080d440002c2d40080601c0f41031290681803004030029405403102d0304103114000c00c861803480c0c0d2000550314180350301c088a02e8196101e000e805001e0800d48140c034810401303c0e20802d070a0909020301c0303024168400100c0061662682c85060340756a0101c42410884070607100b0344001b2040100c800c032507000b510001003036414080d031005400000c80040d8002d50002c000c0c040520781c06844402158524a0420b0720b4100c0c2c200000d0510191103000718003414001305000610580f940724900031025622120b0903809900288408554111540e01809030184148031802070302c0025119524031410b001c81c0f034000608000440344c12190003c0d9401c440c04154034240742001580b46805c0303102420001c4003d0f10300385040c007100c0c44500500d054a03032145882e008000011110344 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 839956807 1250 839955557 839955559
    0xb060d0506010b031e0a0510150801050d050a05060a14073612080c0c15041404020717030403170108071e03050304060f140301030b070804050c040609140f070e150405 73
    0x4007280c24910341400c00387c01c041c1c422401c96022881700154880e160419442148103039160401283c1c0f8100420000c888411800c0d01d40d07000d80302c40b000000308140489072180c00700c1c4800260b051240e900c10900944010706400c01e0100300300004881443d56813500c80b01d036095a140d144900e4410384451100c910319070107601d1441e0105040000c001e10b11002c1e12010700c0e02821190113480e48010840c2060b004907044069006c1000203120300b4030099000540800054005440c10410740e88803030180c0c040135902c00f0149070200602c030030590701c0100703100c2c4440304110401c00c03941014401a1210710a02c134500c02100040d2100d054500c1140201c030045170000f040d0f1380c54950b2050301505100442d0f0314200080c030400c1c0c0030060301900e1003d40b41038a41203945e42c450b6688005050725800000b81c4242ea0510030301001d01c8243d5250f018002c041c000a40c40400c0da00041c80400c40003036230182c00c012005c500502080001d6038812404001600100c8160a0f4202d840500e2841d030300c00c5801807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 839958057 1250 839956807 839956861
    0x105070b07031b0e03011104051f0e030a150b03010c2c0a27150302010507050c04060b09040e0606030d030921020d0f110607030c110105040f0b060d0506010b03 70
    0xc3e504a4005114484509040d8024420166040b1000c0403d100c1d0f40140c030740c800b041038403034980042c004106100e003820314140310204281c1a03001034034101640000b190010f001c0041c1e9003085040f80141d4485075403d038003d0203a802d02d8030015040c4107078510300b11400e040c074403258403049016000d10700507040003030801c0d0303150340e142e54420300c000310003800300940003c070890800e0000409214003101d2248184240c1c0e01b180c210303801140d40303911030b0200b65164810a040810300d50746920520000303054072013404d9643c8106d0030502040c0c61509012800b580c0041b0704001094602103280003100c0400d28000500554524000c400d06d0040060b041c0015041420310460f5a0002184800c003509511901440c280c040b004544158203000703806c007140c20800100d15064001c1d00419500c00d0541060108641c0e4403d00e01d00310389040710b003903d9420300d40711510103100c2122255074001806882c0318135001c2c0d440d143d040e80c7d480184210000a00008009114a40e00d20185407040d100c104075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 839959307 1250 839958057 839958101
    0x7080c1e04080102280e010f05281404030201080604050423030706060b0304020d03142502040b09090a0b0411090403020109020108010915060503130503030f10050f0105070b0703 78
    0x880b0b03000f50010000c2020804407014182030081100b903580340000550382e9840c0c05c2c001080011a484a100b12000c800e102044c440407182164145040b1244135026808000c0c518070403c0040c40274612041032151003400700030074009030340d00022032036004074280e801050b240c44a01d0111720b44501850100c0c607035100c0c0c0c11a900b0111003c0300910303805000381d000b0b104864498003c0ca01c54401030301c000f5880141d5401050010b03015110501003414000e003900d040520303c40d542013050303d200354018022640003103008110700d030034800d0441141090b52035040c0d42c075041c00c00e03981c0c0b02d24121014000b034104400207010000040d0b118440d40801a1069047e03050505d00a80a130124410403030105017028000318207081a486072680c856044466081e10910300700050701c07a0760018107400c0c00d42d4801130148000c81c6003000198000c61072070b4949010f620704455030241804550304614868080781402c105141e031720100340d40140742c2002e8039189a440d00c400550083c0300c503280c040c54032910049 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 839960557 1250 839959307 839959319
    0x50f0d060f150f050901110a0c06030915050c07171c1e09080316180e06100302070b0a0b040b030d091e051c050a08120402041407080c1e04 61
    0x14080102c0740c11100c07090724210311107003c0d50100854502c080026500b808505055803044800c00412402c1e0400e842555107241c45001a1020a4000001003921130000f0001c02210607103107180400f40c000f0030000740c14600e008046904c80d040024011180181404d0345100c0444219540d80c0084640c1d4031040c071200c0209000303082a5803103050310041110703010911850314041c0700c480303d0307010740d40c07602d56592402e000c0c0c0d0341080400c0d2601045200c1c4c100343d6107200030040300c00c0a0320a1419a42c450324180c004c101c1400e1540d40500b04041c01800352000080140a030107421402e071140202d50310342c40d04041030041554680d00c55040c4140341c414a800b0350820300e44804d13640040c2c809c2246000510364002e42180c14803490340c01a9140c4809501d1910941c02d260495101c0d43c20b5810b9215542c40f0440c080d0003a25081c2e50300e440078000c1c042140b40ca0b1180c000950b6251100012901d401070380904800c2c001400c104c1410700000b00040405220b9042c05c11700d41441d0b200d5911691944c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 839961807 1250 839960557 839960579
    0x21c050109090c060302130e09031e090a41060a03050a061413051b0a09060219050d030905030913060905150303030118090f0809090a0b010e01050f0d06 67
    0x2c01d00341ca400c4501c080c04034205202c0d0003150204807134080ba1603c2c0307074a08002c01d5400c0e0001051007045000502c030111800344001c0480e48401c105d80002030b1030326901010401c521507940e2000000c490720f0000c106e0b09600c003500c0d401c0d000c0e40e06143c9141031541c1c000540b480d60350286031154403c50000b001c0d1000c170b80581c0110301031050382908014050701e400c2d5148480d6070000d034296003c20310241b80c04694602d034025a078403503001500d03580c100d209a41418120b40000200d040400c03900d80090203000e0b0704001801c078549903220080c005c410780d612880d40710704510000c0c804061325079850f041484000c00c100c0740402c0e80070300307511007074402e41040a0090100303024454881d03007440d001c108480c0303148450926450004020354030716440c005043c0f1000418074031044900d80c4400e141000704000400418585008940d00d030b03903881c6050100007a5800051010105074900130310301d600d80e40c0c03000301520800c4082c2041550307000c0f043d854000f1400740280d4090382e070b0f0600c00f004c21944400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 839963057 1250 839961807 839961821
    0x100b031023070c06111809040f020d120e030a0b01091d07060201021e18101e09050f120c060703050c070b0a09060305010509040807080903101a0102061306021c050109 73
    0x40c8010000c0c1d102c5140c0e40e8109101d070400340090341406d036103495024a403d042e95a0054032a09240000c120141d011820400400c40c05a8005a03c00c1c80c001c02c054102a489404202c11005032186040c10b41d150044004180a4821207640d100700c0c80c640c1281220070307250b03c003840c0781c100c5607895a03440f002400707548101681c0d21424901403000000040c81801d99504955002880c0200904441030000500366204901c0402c82d0500b18911203020304000010200490341d19000b050341084103203c450348000c440c003405024152200d0580d010041003401c500b00c01192555943c54040c2811142c9000300a560041400b90329000a003c0368120000d11083d03049459954031240c2c5c40c3e2060701111001d00c18140c102c160400003500155090008060442c4100e14044c1454a608042854020006180301e05556510510140003080240003540c0f1034091000300130714079000d8102046040301110003040c1540100fa138146840304000caa039840014100200929079482d00328101038030b00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 839964307 1250 839963057 839963063
    0x9060d05130b161d061920010b0f0d020a0302090c0c1e0606060c071404090b09160801110f070302010b1503161b1704080706030e100b031023070c 64
    0x10181031031052910300c195041310290020459400c0c0000c00840700c420a01070f003e02400c00c4034811074a04000481501c011042c805c14000054408001c03042c00310301d4170410f031654072400e138a00c610030040e650741051030305880c3c3c15543c407105034980311703403200e1903018409202d05240280c84807a105809a880d40200c407a10140032118151039403030910845100701c00c1d5482c2c941c0c22000d03080c00410710300800b03000b60034405403001a5008603522080386110f42500c0340250354111818000d201300403440c81e2800ba0480030000c014011980003900d605100d00020750340c0d01da901251260074103000f0360142c0041000680a502c07180d05e5444042e24581c0210340d096a42080c104005c200b0a102c3c0140c04500c4a0034038403d2002409903c0d16240e90000900745601902c00f0400405d54040038040c050040c1404c2d10041000c100e0103607110304140544081c654940d252241300c03151942e0019100d081c2c82c154204c002001c41160600c104620b5030880c010001e040e014090202e0a80d01030080c850b1a40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 839965557 1250 839964307 839964317
    0x90c050d11150a0c1101120f0e0c0301110a031d030f0403060c080105010905010e04090c0801060302030f0c0f0603040f051b1f0e01031104080a03020304080f0309060d05130b16 77
    0x2404080c01d40d5800390f107032424000b40c400410040021400c01c141c0383e288405040c07801600e45000c2403002922580300803402c45944039a035004000c0020406c100040600720024021012217010005041c000c4407903c20425407510383e00c0d04842d281043c450410888403003629512182c01589850a600a1108840340d03864040f001e41154881c1c0300c03a41c10b942050390f4403403c65283c0401168904156942280c1c420796940031000022804181c1e000100503140c00401c1091650041508006107140c1e010703c9030708100f485080303e0b6100c0c800120382400465440f5101d85407403c0840080c1d415400040c04d40c80b5403000c03160300448900340400303010700481e1003107a00c0c0c0780c0220443c8040d210b041362102095190091940540c040e4200c018003551507981e1038201076441c2c80d4985020b64516069000da04002400e1041e41c001307000c9010b0320780303241f002189442c60a001044076440342c4c500368203130b81d90b8980102d0f00490045411304601c5030002d20741d1502e404e00b21210f51008070200c0400011030713 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 839966807 1250 839965557 839965579
    0x6070f05030402092706040b1803040e070305044b110120070b120c04080303011503020d090c09060501111009030207030804180f0e0a06090c050d11 65
    0x5100c0c0007120b10075540600030352800d444a0a0f114095a452101c0c15178081180104000c01c039001c101a51040d8001c2c3c1240d04039091031829090f22852049049a954100b000180284100b1014440e04244140b500254680c0c031070420400780c5981d500e010001995101000c090045c08086000303103182000d80440c2d5410303406403050000010b0300703070041904001c0b0082c0c0e021980103c5120065480d4840c190424201c803103803890030409540c00282c050040803d4000050300608642c0760311010008890f8a41400c0c41c0040c0c0d5070707010501c180b50315103495034003084059100b40c065404240c007401051046442c680f810f80d0085026006001166250901c001038a40c42002042c0703480340075a02900300c101e60201c0380e4000e841c48200c20750540c07158240000010301800002c0000b010241034654030702e03041c51024001d8440740c2c070142d00d617a410a081700400c408040340780c42904ae400030000480107000c2c50b2400d42184942e10066001c1000c01c2c0c0e50041c0511102801ca80a00c204c40840d604 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 839968057 1250 839966807 839966837
    0xc08100b060a08040b040c05060403050303040605060f0307170111031510020c010c0201030f1506050c10140105090702010b090108070e010e0106090e1504180318030503190c080c0607 80
    0x3400b0302440e038000690b50f0004540801d103290740321a005800740201032410340c0c0358000309626030b00075801212940d01c00000c100038088a032080a4015a08030342040d201a140c400081c0c0d1031081d4092401c00c40304210041500031000d520201c1840802e111098891411400d84401e9450224211f80181d400144070781105101003a2800890016100d19810035036580045006040c200c04e1960503d55a080480281c40c425007000004c019658400742c4c0c9004e2152000d06000384d903810b1810217070521044a45075071441e82403906542003610800115622401c0403805070043e420141c1d04250004004508504040b1b42d400980300c900e80703851196641c4154005c40c0200901c00e2800084210a0510546400030409178002e00744503481d50011a41c0c0c0e00203801c540303c08080e000e1210f0440582000c0680010500804401c01604c10005502d55240d0f59124826026170041c00d9055042c5900c0c0c1d680600d201341c0f80310342c101d01c81d50f4484a03044156903071100155031030303400704421260351546 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 839969307 1250 839968057 839968069
    0xf09081c1515230409090606050d0b220209040f11090c030714181002031e0d0b0f010806011101090c1d0906010b1c0609021306110a0309031e0c08100b 66
    0x3c2600341100145481d2401c150a0000c1a2442c0111800c1e17880e01000079040e91402c881c00441c501030a40c40c1d0080c205071200900c030204568040810704011119240981d4031369504d41d03885904140f000c0030400c03007440c0c0354518000340c03142c40790700040a0b820312400741e0141010b18441c916948403a03420340d07000c18080701c2a010786a940341c0c107408501c8094200c1e04100000341500c1c6018011641030080b090356025004d065281555422100881c865000c540b26019104590100380c0d64840004013950000703001d44c4c00209031505002c101101c948002c0310035030001c010b641e04100b043d0410303a298450840b00100741c1360100d0b41c4030400d1010580303240340424000d0480f42020303401890007080c01c080312011200c10342d9805049644480000f80000b99000622407020100441ca035094140b02d005000c0500944e40a0440d0b4040c2d10b4500c0000d4000c181d4006a030f40001d102c0c16500ca00102e09030b84800400c0740140140c0c00f07d04005a40100000e5403211500d40d148188442c030145028848 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 839970557 1250 839969307 839969357
    0x41103010b061e070309081b010e040203090d03050903040b071b15120c030b060c0c0109080c010e0d06020f0f0409050c070b0439090f09081c1515 64
    0x402d4124143d806010040303290041c40700c580f1a0070840311403581c5400b8a41440140c85112603a0754000040f20f1156034000081e03090501d04a40c114210b00344074200c1a9500484c06001c1e0a055a40c40884c400020030000c0e5030041c14000401607803140f030342c40c02007070700c001c00784000b030b89946128000300700341c50349540c03812102c41107590b03151900407a6080000030f050030040709014182d503152000c4107612014010281d60910070020820742030712000040010090380d00014094002581803c2c40380c1c1e220b07a000d034009000b19001074400041d410908000d01c46c9041401c0c110f2070029242d01d02503d0600940125020a04208001d55a04905008610803c0780081c0645400000940000d240d034804c8101840420400007a504850700b44107800d4400800c41e4060f2400b000c030800c803c454a0040c7d0844c070f403c0d0031091044940390765803c1390300c0c09101540711017a40301e00300d904004015580704002c11044105501451980c9000d6021040fa80c4481580040c41e0192100c0104503500c00d13000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 839971807 1250 839970557 839970577
    0xc080708062403070e040317090d1214010603090203060106031a010807020f0706020105160309080a0f271805060d06053408010f030506070804020a05030303041103010b06 75
    0x30740ea501d0701c0e858040200c070005850146000e4039030440840e00c0801418016002c680d1504445040c68200500f10441d01c2c4a040c0885a1050801c54500c0700800c144c14282c149042195103910307003801010241171915030000340c42400d00c000040301030741a045800c0f090300035000c1e192141d0329441d04030241c2d03a64016010481d181e1410715101948620784481e40000144151122014940000c504090050307004c240180e44920038001c0880440c10420920b401c40d0404000e41542551441e0090140780c00b10000d003e00d0008841d0301501400001500741c00000c003840c00c1180e140c00c1c01c2c44803002d034007413031070601c1c03010303940018840301c0b882071354060a07006112050040090359140040c0400605c0c0c0040c9900506008200001c1c581000d0346c5004030424441d200001400028400c510503401088602c410310810404201c0100d41107821440b9413610702c030745130303214004a59145c3d8564131898042c4000020002031004c1c40362440b0b40c282c001c600a02c0b100c0c4d440030410405000e401a00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 839973057 1250 839971807 839971813
    0x60c1902070e01140604090203090c03010b01230f042103080c090603040b070210091a0603030a1d06040b0c03072021010f09030f170f010b0c12040803070c080708 71
    0x6004c0132000448450130740100038000703845c081e16055004180c4c0c00c195001d02190b40040c41c010f609240a0140c14200002881c043d100d9500036100380780d080c842207070300008102000500b83c0380041190100d40207480380070b4001d034000e440d81043c05002811a202034000502000c040760a036040d0b0800c407030b04c0000c0244000e046807116150b002038050003510b4081548203100250225050500849026078080c42000c50003c40086180354440030003480c0d640309400800079003410700e411607411049504a0302b8584031519030403020800e0f070b01c102d8008080010010400c15943d0900200401d403161058284001000d41c1c042d201c0038001e14449100e45c000994513a00311005070180c4032000300002000003240c41d8010724a55400c0768119a01a4001029400c40b0070701d041d000420740d000c034079220581c00d0840c6040c415a4000c030070107001c1c90540c404002451200f20408004d89c0269039091011203a80e6581c4800300f9680354042401111803070404280060312420215040084800c00409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 839974307 1250 839973057 839973059
    0xd06060305163209040b0301090201020a0f0c050a090c030e06160c050a06050c070302190209070e24090114070c061809050f0406110c071e08060c1902070e01 69
    0x1990307018000c0340203c0b42542a40401d00312100303400100a407111007440440d5550321040c09000a40d070686c62014001d03810050980f00503680068102e07100d0303402c107070346910900061401004080155020340c0e44011880404120840c650b409580d4040303850b2001c0000e400401603180d19a40c044680b00d0400200f01405409580180a10b2200c24890410790340d01d406940e1740d0a04030ba40030341e8403801030354010a090007016010000c941106210001068442e0042e034005001040028801c9040000140c034000303032a00e900c4601c8480386217131180c0000d41600795070081c1582c0c0000240c503002810345986100000c4041d03080340d10b01a0880401c0780c4050909e04d041e42d0302129001145419041a04005a00140c0d84140e40c0200700305050080307281024103241c000d0710402240c062003844100001c44125500042c0403040307441d0030301d00c245420090011b52079030150a0780f0403d620300611040028141e5001c005110b0009180c08080c110704500701c040b40c0e6256a40074100e041c10030100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 839975557 1250 839974307 839974351
    0x1b020907051c0207080a0e010c0f110619022b02100e030712030903030c05040b120702010e0f0a12020d0f08060a030204020c030306150a090e1003170d06060305 70
    0x60960030b90050b0305050b0303022000000c20803039201003029110308002250504146030301281203866682c0918002d079907030000e1f03214500100030b5500b006100301804a40c3d807242d52140001d59500c000105902040380000400c065154414a031858000d0105020f00410110301358190000d060b00c0c039030040102d8217029140070f0091508542c0f40032144401d104280000c1d103100100600c1c64034030f0760f002c41e001140385400360584410b4038900f000c0c410705100034400021201c00b903e01c03104409481d00141e03154003401741e00410500704544100d0191035101c0c1d000481c00904c3c2d55005104245a140c4030f94402c2c8100d81b114060070f010703800a1641101d11385000e10440b100b036040003000707180b001145c1d40e03075000908aa0103109098581d40021040007032038584a41c9041d4488400d0344400d1070a21991002030040c2d03407038061180300203072110200741c1d03500d04540100c010b5580055100060300b00c81d003814009400c4071341c2040d48141050710104031140f003409014003d01c4440c00f100c454040c118 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 839976807 1250 839975557 839975567
    0x504080c0118050918060603060c0d02070303150f0e06030c090117030c1b040b0f0306070f1101090605041202010c020a03082d0106090806061c080c0601080d1b020907 73
    0x1c40580300200002d501140382c0c1d441101c2035000c0c485548034841c00c00307035240d1140d0811744003c11540c403940240d410024014240000c4412122409000503641c0d400f918080e00103183c921906400386030108000b1541d40d00c90b540d50803e44040c1d15000d00035584480825a4440010a000c7c0e00038030004010881e4425141c6045074900075141520b0404041111040c68801200440a500700800d50b00031124103292148030101001a10b940d81d082c5c120401080d51210701819000802c00c0c0140c44059840c0314500d06100410210001c0c4004101070404002520781030f00d050321b82850030340c003052906005103c0c2419220340c94000d00215501520107642041d00280189050036603c8508d40c24021038800c407088212030030204d000301c3c3d4188640240100800e41001c50f0341d50020080c0002995480c8040404902d85140c003032800e5a6454a03170414024800709040b58403446001040d031140110b4404070304105a500c1272481d024940d00c610010b4040c02c40a50401113400103d0300c224490 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 839978057 1250 839976807 839976827
    0x2906160f0302100207050c0414090703031b020d0f03031104080604060c050705010c030e1c02120a11030c0a151b031a0d05101103010510030b0d0c23010504080c01 71
    0x10740180e03207503401d0f1440100244d80c0100c0702255660012600900c240c50248103044111604801e0005a03142000740c0b60b96a450301d00000c2c00b40441c4607004c00007400044041da43d46540a080f10030702402078640190201c0712414103d012070704004080040000190907501100d4650780200500d0721140c83e01801080c0e20980c200c2000810496040410000d004a0802d900e03540d80019000400312030590401c0030b5459018031a6150300d0645498907400a03c88101ca03060440395943c0d1941913000b51011000329034100d040e80004039214401c8070001ca02100c44501810115195605482052045980307a11a100c01c500643c481c101c4854442d5001c0413104951036004100f1150510002e071860900c444202c4855000c1c1024403007408040c0030348015030071468903090440d4102400110964640841c0e1020542c0d10205944166680f20203c1c18068210b110000a01d855030b2031442084100014080140118440303101da551256040317504407206400030f02410f0303510f00011141d00c998 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 839979307 1250 839978057 839978063
    0x6120a080306040207020a030807061113060806030f16060809030708273604110108090304090f0506010f02120f0c0106030b090a0b0f04030c0f06020c012906160f 71
    0x8244021001a00c031f015030b03e80030314050100740d51102c48a2070035005690000342c018507071480a010800c5403000301201c181c02d90f045030502c00401d40e69080841e01e403040031110441d06214420700c083c81800300300036280584056035561401542e030644266034900c110310f4003c001480030031a451541c40302252160607074600c8020354401c21528000601c0a1350030725080790081c01d0300f40b8180d40145807045405083d14907981684620302c0c1c56182da88039605d1107105141400302440c0081e00854003401180c0240c40a200b04121801040e50030710000c1c14112000b41c040f13220a02003000113400020b884940e40c001c0c0b54002c0c07806c0031040d03101c401500300c444000c03555921803101100041017200d44c1413068003000b0040803040c001d810300342045071014200c200706003a0001440f0100754061103c1e59541e0300100020821034152425900030301c18040400c24551818a14074403820700c842d041100c0c07992070b01115002c01c29031001c0003601d21400300104640c82c01064480c0000c2c9465000818182c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 839980557 1250 839979307 839979311
    0x51b030402300f07080705010e0a06030b06070f0c030201080a02030f0a0e0c060f071106030709090213030f030e04050106020c03030306040e030421051006081504060b0d0b04050606120a08030604 85
    0x140ca0140b1901c1c141c000c0d080150550020101130002e00002c200300c400908091034154540c0d8050030100701010894084c06042503120f400f1890991110700c120b030581a400b480e0085c501c54141444060070401e800308030b00003001c640104416002e00c0c02500e020f01541007006241d074844250220050605040f480c049001c0c0c1404040503a17202c00283c107088030044111540d6034980c0ca0701c00c0d4003920240246100e004140144641c59070720022440549445110050b0b40b00c54980100c44c07850b41030b6200800301880340070b03a40d040542c0101c2d0340040c403805403004c1c020350362108000c0e030b1140142c80d01c964050b4400d20000d441c5240580210401510b00b0f030a480c505900c80a1001c10721350401c20040324501d14815010070400100281d40c00040e00c8134041200c2801d117004c05442d107004441104175420400042814840c0e50381c17107910340c2d8000a241c69240c880711315055040c1c0d20300300e03400d8805000e01c10020b800c0d410810044266440c1c81009086800340d142c0d10a090340c3c0000e003102c0d80040e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 839981807 1250 839980557 839980639
    0x100c03110a11100504030b0c07151d1006060f0c060f050f0712050601050d23070e01090e0105241e0c011505010806040207060915051b030402 62
    0x20020301a00030a070b8098a40c9021500074282031101e04040140300e0402c002041100b00301040c0300020568210303514184180e40c0740b200342840c030740f000c0701803030020013040c0703030140405a130355194145104150481080e41d465010600e02031003118450704c40c1c0d1001ca080320501e80f4626125407400000c591241c100040d80c806082c50010071160100c850f052074112040511440c40d40003c020f416000300c005081c800c0b490898002000d40c010340099400b4107441c0c5403403d80d001081182110195803804000c00149440c00d4001d00324103a020049005c150101000304140381d40601140c180c50f005048040880c1c801881005643da60301345c2065204824440e5620360510324201c101c94116644680740c923650400350560071102c80642c0300840300702c003840c2005166004016a603006008407001600c5841a041840281c040000d0080031146239030040903000302c01e40d120714012a601803948a0f40044403548101602c02610040d6004904283c1381500d1a8840390b06209082d002400709580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 839983057 1250 839981807 839981837
    0x140f040911062a0606120708070902070305070b070503310b19060b030a0c0f0f030e0a02030a0803011a030405060a051012032714090604020f0f0909011202100c03 71
    0x8401d015080c002a8008109203c517914150045900c20811078003d40602443c0c200090b40c0c43c800c610440b802250046405410b2600030400d43e04500e800441210340c070314180340010600c0d0320132038080b20039000180441040d1a9142c1000780354006031a00010094515142d40c40c00300070081000c800403030558200c020700c61444c01014010a07500007181c0d103901f04050200c060b20209402182040344021004130001c5c0d010414801e204402e0400081e000e14000105041060101000e905882030111181c204000140218100c0e0725104280c044019130280055a0344025100a07046a100c0030209840e5101a4071558008080361a07d2007507503513070141c1205200714000309070040341d40c0c80d080d407001d2140103105844502c2c4070850011041d0600b0701482180e0300c1d51401c036004000280014040c0e80301d40d4115603546040d0317105540c503a10202040c2003d58885442c4078050440c1c0e00001580d4541041c180340c0440d8020115440e080d9910707411200000206000d50801000c000c5c92001c0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 839984307 1250 839983057 839983117
    0xd020d020415030602091839040b0318010e10180f06050a0606140d0e03040521010b0103110304060c031e0603030809061003080a020115140f04091106 66
    0xe44c403c035800741e11141498204040708000703181400460b00c8503c1003003948014000003d180054001c100212080101e280514800008a03418148080018041000c1c1105000b0318410750090090780300101c1d0341c200d01402e9403c19644101c3c2503010b040850810040c2e90000541c1c030140400e520b500c4401a26900321000304001d064070140c2d920014082079681c64050381000c2c00203424041d0320760120038090b002900c070351641c4c005407903275400445200c8101401160020b100040c031950140030300000894464001c50900d41c01903103000700905040d40280104460000403071419400c50391552508805040d2820f902c100701640c800103102c0101421002c0787d20b031b0011410000c3d40714218075018140c00030280c00d5100e144c1c401d404000810410454000580780e010103019121340e100c40f001e13400341105000c0c55000e14207034040403e0664080e00000146d6200b10340e055220007610080c001154120700c000740040d000514000000c0c10034400a10820542d19120580341c0304200081071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 839985557 1250 839984307 839984309
    0x30f110d09110604032111070e01051e010905040903020c030d111c050a030c0c0f060501090c02060903030402010525061a010315231e0f010f09060f0e0915030d0306050d020d020415 79
    0xe803001c0054010300640c00d1103826a1034031140d491490324cd10400c4030020740001164410641706a4071130848004052007401003031484030700903003103c0014a40c200c000d0921500744075a41600d11607040141c0c491612a0340c044040d4071691101ea250a49654040f8060300c0c0d0b0640000500c54000280300008080c0b51014144a0190704000b440354108012801a00c034907007490030842d03115000380002d00b0f03004401c0703940203542420690740c1e48241030301050814190030108104400c2d1f40001c0c0c405d00103e9008105100341080406101020200040d804c035980403615400024207a10103104900701c0505190656000c1c0348607007004059140010955034000454103a0741282000d94044c0f420500f0034103096070024244403c000700a0903008049520034804c040800025000c1c5604c414010100004100b201400b000744600d44245022001c031241c00c3c002d03009200b40340501c00c44e98828841d078001e481c4000d1044184d000c11380c081054003040b00070b0070381c0e21660b1183d001c18071405200001d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 839986807 1250 839985557 839985569
    0x1406070908010e0f07050607170406020a02030d090e06090414120913023c07080705060105090709090525020d0f0314010303030f110d0911060403211107 67
    0x106035a003444011070a6890800f800401503202c9043e03040c100c040420342c4400c3c1c442c01d549050b22403040d800c1506401c409803921410503080000d020500683c0072a074140001d0083e81114040002d91404882114080c400e0381d91682910010401c1450000c40c49500305000c0c007a09032068a41005c007906100354250b0300c0041504c0081e0642050808210362051150389140840c00c00b01c04195050201480700c0116540901d040036091807811145000724541d10781c01d14950300c440481c0780110b8180e00c5043c0030b862038031800000094920b001c8c80b09031320500c1690340360714505280000407405405d0140442e0f0245084030010f00f1918141c0d43c0b086000340096000f090041107090003d0024200103030308404050820000340c02d0321454407a503d0440703034540b0b4000381701c81d184c0c0441402040803800031090942300081c10b00409415411103510940940d81252104d01c4440810455100e10b00c001001f481000405070320100d08411030321186001401c000030092000e2000701d0800820360024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 839988057 1250 839986807 839986817
    0x6040b060d061415130605030319090f091a12030d0f0e0d030c120b180c1209010b010f0228051f0615052b02070804030b0601110303070e010804140607 66
    0x4414a81204030417140c041128080008506100c007007600d905c9881890080ca51860080d5919144100f00340001020300c0f401804110f9101d411400180c44440321403c100d075000d070782c2c0c5c04403403034130f02500c0d0655441600154074001c1055010703005022000c0c4000031059641061044509050202d017041480c15580000d0191a120307010b0300844810b100916214640301ca080c1c0306441d040e441c0c940d180241c000411103541d481225200320310800100140b9080d0800a000ca01e0405412880044200740c03903510300d60100710070032683c84a00d0354031160441d0419131075440a00f40040c4151110740076005440241501442e080c1d1914001e8100d0140c02e81d885004001e071008040343c0e420a0445032a01a10704446905408020128003441480c03010348514100728001032641250302c0980d20400c09500c40d80ea07403e20b0a402c6070100c4056010a100061349400311502008480c482c03030060300c0e0341030406200001141c00140040044035050304101046041410070040d05214402d10f40d60 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 839989307 1250 839988057 839988091
    0x4060209040501120b1b220f14010e1e06030c070c0b0403020603070e011107031401050109051b0a14070605040c060f020c060d0204090504051b0306040b060d0614 71
    0xd001c01c0750300580c0300000b200c0b0707200012000504204038160700218100c021090075039405400810760322603180100f60041c4d0f401514803d03000e102d81d0400854400842140c01e03580e03607610140c9040141401c140c0001c0802100c940e442c6402d1401d0f00c074040c0c4442c04d28180001d40300c040340159005036428107036018089490410441c0c0c0858100140500050f0706082c075207560b010846501010707103508203109140c400202281d228401e025003030b0030000300300d481c071658900303101c0c441441400c0340309401e5003040008200d94031207001c2c90f4068401070820310a8600f40150346030719900800820700c100081429a2000d41c080ca43c098090280682000070b050700709403800b4034003294258030120600940980c4420004d40216080302450070907600c5076680c003542c4c41620020320517500300600140c50a810310060000c001000c2c2038411100745001c6460340c00d1020144d46030000c84000301203600c458009040c500300400e5652aa510582d00803036254140803030080342d41402c40c2e5074602260b400c0f40c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 839990557 1250 839989307 839989309
    0x12070b0a0c03020a0503150102120d1e05010305030a120f02070b0106020f0a150e0a0204021819140f010e0307030803190e1203100e010e0a0b100903111804060209 71
    0x1181025076030403401c08515090404078042d03c507001c0141301d411684081c0e410002164000e001c50745c0410103c0019698035440841c064004142c15424151668007404c08080411201d216643c140c030b400c51b00640c18140000012102580c0565480140d56101c18040041125a00203001c050740708034038400701581001c00003072500442c0d51141d40954480703c2040c0101e00391a0220f440d6043c41400410350480d0610300a140c030251800094016200041e04058052450420081d00100711048080080c0294008003080f10b54021210701e1030720904410f600f858040e26040c820401810312003401000308001070705044260f80241c0301d46a000013049000c0d050400c080c54512240700d8100881101e02c2706050b178401611424580780f0b0070000200798901c00f04a811401446001441500c1d0340e180c0c03503030888600064030000156428000c100e5010318000c0040740d9401c8465072a8510180f4684511303100080544a42d40c114400b0214404004610184c1380d1148ac0200e4001d60b80c0d80070030f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 839991807 1250 839990557 839990561
    0x1e07050705121501050603070e060c03090306010609030515190e0a060c050424050c1e070b0a1e1e1715061602010e100c030f050307091712070b0a 64
    0xc12005500000c2d0a03d002c41000c40100e41590420746103583c1329a6458000d0301c0c503c214030740c4164804000303c1d030f20604c04000402031503640302c1a81a01c10310799039420240c0b040590f90200030328940141040d0a03101c420441d10ba070780220344214030030700119034000742000c554070031072000c5240e0000894201400110700481c42c1107200c1d0f28100c0d2404d460403d0380c8100900d8600c240d10212000b401c48152184a107042d60603848420702511307011800c0b61001c008141100300c0d0070700d1a0003508000184882224107544040d02c598903640c044c1d00400f4942520403407500c0ea05000d0210010302200d9070040d40e22515146c03482d0f902c81c018440c01c85045409002d00051842c00c0c400045030300300c40e86449180130f4600e000f45502c1d01c0e4001022500c0141c81e210703285d180761074118040d0003140360321583c0702c00101c05003406602c449000d21005032041b03c0303d2008607010300105104403800c110f0281d03c017611100c0340b56408280c9190301030300061081650310020058030002c10390310a2103001e00c414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 839993057 1250 839991807 839991829
    0xb01210203090f0303010f0b1608030c0406020c04020913150305061609080a0c05010c06061e051c12051b060106020d120b010206060108130605091b01020c03060103081e07050705 78
    0x9100440c00c56146c03003c2401411814000c0104003c00410f4100d0300102220030a58514ad020241c0d985a2034841a41401900030340b24020040c45034401c2034050382494030844081c0350b400f5180c10200d5044070800e00103410507428500c09484004400800710380184100c5000d1001e010b1541d000c4801800020840c0903507410140741303034000300d40c1403000032481640340088480a090007080d01140c1d0505c4c0008005a81c0602d040220400001d07011001010303507141a600111050811000c412a1200c03c002c1580700c02400c49408011000c07103203004a01609421000c22458071915414486180c1089000c2c1e004402603070220384400c8000744c001d00410050612010108011150400000c1d41c80001415150500c11880d02140880c160400d00c801300c207401143c180403504003490541d0740d0320002000c02c541c1c112680300c001070640c404a003201000c000140104004d07402d5450300310032607110003c010800c07884108880031003418107020b444290301401c0940446840c01003440001006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 839994307 1250 839993057 839993083
    0x1602090702071a040e16020a080c1c1d041d100e060f190203041109070e040b030f0a0b07021504030c0515010e0406111318140c0304060b0121020309 65
    0x200340020f02540c06244c454030b50006c00318044035501080b50310142d007041383c0204040c0100798006548001c40b1030000c0c01c850012040c03200078054441000044841841c050a002e040300d4080901001902e803c0e0442103080c1003407800100c0c60030301109040d01d0200130b507841e0740103c0d48441003000001e10030700a540d4031007800d10440019150800014a01d4500140f1704c1ca40c0c0381c0d011021400b807100c00200048049000740c604400c3d41400301d005444034105803c0184a941040003440071403c01140c0881e15401500042909000c2550b41058007200142203808500c01d189800315000e03820303070000d4051030090301c464000012505141d0300703001c00c0c0a203581505e2003a41c0108180992901d049034002d4201c4800112041d1100450645100d4200c5842000b46900d81c080b509002c24002c0340301c0c000080c0300400c61828810b01100701903e0803203c0d0003094405000240101d501c94220103220141450030070700c19030003400b501c0c2040300d035452211130300c0d503021081094454082001c0009a24 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 839995557 1250 839994307 839994359
    0x20d0e0f0a0503030a052a1801020d0e1c2306070c1208130510061e0308030112080915030f060d210201200702010f0e060708160209070207 61
    0xd40b919566600e100141400e0170f00b40e42e510001e2000c491342c204015030307010800c0f600c00e04120200c4524025030400c405000b5407200c03c41c1d803419a9800080c001d080d891302925810b0024022504001c1020ba24021024124440c2414400059070030b1103d00852032070011001c4e082030300350498905d04000101301000b0320494100c80004104440034003808003003035103017005155952089110282c3c00352500100b4511442d58404070b450110f82101c0c003520090350321400c0342c0401b00618040342c0e4640c030003d040381705c04200522a14849440c00c4541e00d02403208249005090000b085030b2407001c21034260140790110500810281403e0840d4200404844143c10b5542a855484a12032400040c02241c0b44402012403958002e4000e440940740e0003199000f800456203080160b51700c104000c1b40000c00c42c03034811f2685d074051a0726460f03640c0e0107400581032542d07e945015031a0301a241d00300c0300110040140005a59a403100e0384a980c03641d0140200c1d03803070041e0f40f4503400300c44500645001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 839996807 1250 839995557 839995573
    0x100915030c0801150f0b030c032d091203010b030105010537080c1309051008070308220b07030c060f020706090209070905010c0f110a0b0c0607050301030f020f030709020d0e0f 77
    0x9401000303a030741160b05840b005682b504d403054021b04858107415032040c0c98108441d0302c0c101c1440640010322505541040d2008054856840e2103544800d0245900d024402c2c4014441948100040c10307065400040e101b241200d04000701540000d082541b0b0a0720030408581c510403a0f0140602d504140899151401d10201c51811a4071400c075006070f6003910382d2580043c0d0358500010010009015220540d0066612800d00c0005a4000310b0f414650003032034445142020114a41d40c0100c039003540d04107040035850340d001c49900d0800002503981c291101c50000100c41c0f00d2000b0440b03140300c0c2000284c455010310502109643c0140260280840c940d01048036036049414420040e901540303008010810340b0307107102501240590b480d003114020001040010041c801081b21060708001c8510b140c4d552a400c903002d1000b40001011071744403925510050500f513100300032580c03008080d20200f43c0c076881588126000002d0f92014180c03034244034401c3c0e48080c4560a481c05001002d04140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 839998057 1250 839996807 839996819
    0x50f0309300d0f020f0f0405031605180709240e040203060d0308060613060f0905040605010c02010f11010c03090c05030c0916110d050403020102010e06100915030c0801150f 76
    0x307400707402c00c1c400785035407182c511a4a0104950444105001800b01241c40c2c8210501030956074101d805942d0103882000206a68041010100401c071a0010241505510b440d0f51507240b6a60140000c006e0000300c1e100402d41d03c0c6800004000d1039030b40755003807440701d48a91b00200705d0100580b0071401581f040040c4903481d19074002c1c2040c0e031509030030070b85040d46514010802c0d601c02c079401da21001d4413034180070402a5000004600b4099607540e280030040d04c3d0400c120480e00544281c0740800da030825007000550081c041c44850307607424280200344986900c0d2103800e4074400303030803040007070350341c409071000c00407000ba03d40e01614080d03008020015143c1e020400f000000b400c1080b01c150011400e2203020b00c41d40d9030070b816002d018150740f28440d500d18094240c2d002400f00b01c1c00355003042e030707551000396001412510070f40016090300344452802000c2d40040809401015000c01c80d0000800410a1540d0050042010703400014440c08803003281c8001501c01e030800040700502440801c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 839999307 1250 839998057 839998153
    0x10090803130f050303090a14062401030b09010e01050111010e0c061b0d05270d0209130807050303151903021903150e06070509031903050f0309 63
    0x3201c1000c1d40040c4401e08035081c280d50301c410381c00c40100b041c8800420450b4403000030820f000088d03c54030000e407411150f804c0154131031104486500001004818900810310300c001d40340136000040c10b0018500384a00d0110301449801d0300110441025400104104d507404030101c8811039a000c000c010380d52f404505181c4442e1031154040c810000440e150034040c2c07002e02080740c051a8003045981401c4210f0015140703811800360b040c09400c070020006603900380c2c00584118118010b04070a0f0444040d070030001ca840018000e030990075265400840011211300003001c1c01801100159146c0c540341070380c2c04034505d40c040c0003402140032240c11351072100c603900c4000a42c2da040351410200054901c0e13209200000c1e07071000c2e003085103a01d101040038400703500c10109210201e09585030395858270750903035881c480c40c11601c1d096880300421404040f05030f0115100c440c801d00c3c00030f15100c428110802644c00036500b601c055017103c080f010341610704295008200c00160010710304200c8920b40c02d05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 840000557 1250 839999307 839999311
    0xf0a031b0f020d080c030d060602070905010312081015020f0d0207030503070312021315120b06040509090703080705030307110a02060315010309021002010b090f040b070c1104060306050910090803 86
    0x1000f40c480001c4882045901c00503203c4c580301c0042100d4a0b96061024032000e02030600c2280094003c2c164040b40003400da02903541601d800c074800c881407010030300d8100c58106004081125842c1000d5012985001c0b041052406c0d00741c130b5009010448072030b001541801e11517460350095600c0000108002040842034a2180780c06091450086240b03029900c0684503040b00d81000d051080004a800004443d08041500e90b0340e0b00c00c8115401503040008442c030703034644164018070501c8200500c0c504400f10035804017003817040d0758019950343d5480300d45400ca00c00455044e0004810403182551103e8a00d2502d03888070000d140c80e040344c0d0003042c51844054034031242c42e200f4140014141c1d001f508000005980070306081044040c3c448000e000741041e00c05548034601c1c1402042180102003441170140e0340005c1101c15640700c001080c1d0f00104a08002c5554807ca074500600c5990b4500c140002140642c201086034074180c0c0020b82490300c91520402514900540070000c00c5119058903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 840001807 1250 840000557 840000559
    0x40305061f05030105102c01092f09120304150f02010e0d020106080d021f38120102070302100509030c010f0c030c0c030f12020c0f0a031b0f02 63
    0x40140940c00d00c0d103410160450b0070440d003540c201024810714001c915001811580464a58115034a00d42090740d4103074141000f25110400280060200c1e0400307520501101c0321414005038620a02420061691200807d528003d03001041c1c107941804d088a06200030b010010103180340038200070b103100080310b94a5104007001301e094043e9036168000d5008600d012014003c0f208114100803000f80030384402c0c0500b0110740625440741c420345000150700c0220071150340031010078000d481000c0e0020505e07501c08103c1c9020481d01e8012000c2041414080010419401541542610103002002c0d1300c500c030700d201c2e6a20400c4014086075020400340c0c491071800c4130200b095107071507041306c1c03a500461a42100e00d51815408081e80340265025010b081071586052091007081c0c4400d94008102030f01c094040f650640c001400f1a101d081c0c4035084200d840740060911148075041032400203800d206204e40e50003001031400380758100ca4410442200c440d030b2003444002683d18000714180d042c1000b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 840003057 1250 840001807 840001831
    0x11010f050711040608100b0321030606031e04060c031a0105070b0a020c0118050c0a0501050307080709031e032a030507140609060f01060c0c150908030409060906080304030506 77
    0x900500d81d529007100005240c15403c546da4003c11440002c020000031b0030741c0b44030384640389010328100f092807010039030419217400090840e5512400d010050b44014802d014080c94003802d0b0418002c804101c900440c06008002a01a0201e5026007107400c0801a0402c074085983c4401e0203a901c0011200c46035801030018101c0c0d11000c241501a026a00d50000c16500300b9404010080c0040341207404a801201202c2c14465040248581040700340a841c2c0011010000140c0c0580a0304445410422501c0c0c4401703410780c1ca4035031b8949100c568020165002400d4420400d15620666504410206920001040b42d1744400d102c000c0c03244a100030306003c404a0740704184803c8038902c0454004503001c1c2c854130714107181001e442e040704480a0b44061101c4001050a40c0b0410000200980c0242240011820207140b142291000c6401008000c014000400e14400920280000744404000400c50f11b0500507c8405d0f5200ba40011240e90310600080000c1400002c0c6503401c05031400300703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 840004307 1250 840003057 840003083
    0x4082407230702042c06010b030f070c05190b041a10060f2003030103170f030a0e160e1801090203030d36020f1e150d050a050411010f0507 61
    0x400d0191000542030710740640317403541e4405c4010041503800043c0011030251026680c03528100061800140d4904104032034204c00904141c0c000c03c0031900c6076000380c0494605080800340d101007466444402c031406085201400200002e40380200020003203102d18041501d000102107810010a200c3c40d000c0084044401030341c94066030f440ca601e04282044000510090210250f03603620a04c0112850a00030703200c82d4010500000340e4000000d020305461454481c5602e80020303003191f0100411078050421040c00c240c003080345040c02400240c4440c82c082c90000003050030003554030405a816418020300100598022089990b024040c401c0010180402d80d6240b80e50b07144001c0d421301c0f6404500401002d01e0b01c0054000489208643d4960300c11a00380901014900404240340d51004290305400f00d468401001c84200082500b082e041c860354010200647c0d0056840040c16175681c0144070038044440300813900c0765001e003400745150401c400010024465418003a19108904103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 840005557 1250 840004307 840004309
    0x201080406200310030c05030a0c030213020f120106020105010506091f0e0d06020903060c0906071203270c06031e0b04021207051b01061202010305090304082407230702 74
    0x60000325100e6003490343d00c078a032404102d0391000d41c500007620f50502c0100009198640001c922490a1b40000e000300500d2039582482445034106104650858090040894640c0c19401901100001d42c102c4051075240074406804c503441a00000c2c000c0000f003081107881e071103140030350030000b904c0428000d962022142c110358541440c0070490740503000700c3c2d6040500c0f2058004d000c000004900350380740d50302d426580c1d10b56849004a800d401000901c05034000c2421800102110071560402080d00500000340c190003200c015540780f407404d01222120140503600c10302c00040e0103a420b04100c0070505040070b8690f4458103e500242d191203004080072034070f8940540d50b0f982d2100001101505041c107010303005422100e042c1107030504000c03a800180105000d15800c580b1a40e0400481752074a80044001e010000c2c40300c40c0e2480704000028103210208904a0360060b000b0310b1040881035002c802c040c03210081d06031010071003c0c0c012801e102160700070507400002c020380034542d40ca550748 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 840006807 1250 840005557 840005591
    0x916050913140705040305070e011404090201030605041b030f050f060907120903030c270b071707050307030f230a021c050c0c04060e0a02092b02040b09040201080406 73
    0x404000441e0303080c4018090080d400130041c3c8143c038440d4095811881d1180c4151081810900c03481100100030280c40940c0d0405500c03078085170740180341c04070f40c040c2c9807004101a00d01642c0d042201080000134917558039414880c41444440c4160144003904040d1600700306400050005031080c40380d800810803540c05007403200a008646c110501c850409420060004c0594400d10400700d9400d13900c61011625244410101c10366181d408039032a070030070180300e4050704a50b404481e219410f40c000038080102c5805032032424840c00c0110b64404031031a00422021504880501303105180280815526203941507460560000003056151821032000b280b400801d404007002c140302d880000c890765a4844010103451100c10100c4550700442d10503c03040700d22520940c0e01c18640e8001051403003409030000d1607503000007003440c602e0741d0307103111000d1084070b0007200c52501d96900c3c1c000900b141000d00401c40c11020032200315080780751a40011344030010007440246525602c604d400d0741c6018203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 840008057 1250 840006807 840006821
    0xc0d03052d041413091b05030d0f050c01022703120403080702010f0c2316060203090603040c031502030a050a090b040b0a1d070513020f0a0e031212060916050913 71
    0x441c0e800d005d406128105404c4200708098031100c48446034002040307504001a5182c010b001580e81c2d0509001c0031202121540c104c06908095550204002c001c001180b003401072224990110703107100e11214904052a15004110540a180040c0000c0001c03030111000d0356081c50702030900640f6032221210454481e218500000c1c0514010b20b020b89909501c4000c4090301000002118408944048840107044107485600010ba208104110382d50401c8805150011b00c034101241c041a01ea41e2040003c0c080c0e9400101c0ea241c0c080304103c1d4042c1c442c020b158010541c180c0c200001c41007034480d590081030081000d440d0380070350800320302d001a6030741c802204084002032142c00440803801741c80d00c410b201d01c22144507070711011078090801c0c1d0303502c2180c0ca40c1e804441e03510300c1c0a0b03104100783ca81c1d00d20325000b07560500688040500e9607042800030070b006c4442c80d00320366551401d5010091034410103481010515401180256001d811008541841c00100c0c3c00702101880c025044001d0194 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 840009307 1250 840008057 840008089
    0x4050405010305010f0b010305060f010c0c0f0b0a0210021201050d020a081902031002191412070e190b0a0513050604080618060f01090e0c0d03052d0414 67
    0x203440000400e0110643c000b50005203204003d00111318004011001c3d5841030f690241e00184428806030550b001c1c2202c0707110749114902d50100d4a036200600e0740c2d0500c440e4040030740a40d0003e6004801036043c4205c1c400314806084c114140b2042e00f00000540d00d05005060040784105118000d554603000020001d01119040380d00001c810104100100c1c82140e00301d00030300c0307582d2001405200301d0007601d0f401c2000909586862800c0101110b107603002d8099481c00d541c08100c1045110341c0455618412105030300d420785901400c006202e03000c0000d04015143c50340c3c0002c240003c0e201d102c12030384102514074203140c5a03041c112004500000c40e40c440340d401000060001131150000c50124030501041ca242e044902da02002c440d100d21007241c0503984441d6003c0148581c98640d40803064444030901240d5041c0040f401040166044100179408500c020850f6200c0c0c05c128103090150501d00036000704504035042c0498058000c5008000d009c548481c00e502c0d0f19103603e9a882c6080780 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 840010557 1250 840009307 840009311
    0x207033e041e06180b0609011b0503031005090c07110f0102030d020304050d110f07030f0f061a04110406080105040b0414010f03060605010504180e07080708030408060a05010b0d0f02040504 83
    0xb91200c002020688503140f0190b00095468000c00384521440c000b03640082e1540e4a400680b90044421440c10301c132100136103900d40144804584108051031182056041102225007450100f2244010003021881c40b04001c008184c0062100d07004118201e0003924800207500398000180d00303500481892803807140c0701100300001d20100003048404480e080d111007584000000410780c607044901c0e40e41540358401c1c0000c0000580b200110000c490203102c008609201d035a440034141e40c600070041b01248018445114180762501c0b0b40e051585807051994034103440c0c542e001c1c0600f54144201449079036103100f410030b507441d1074008100e00c0074000d460b541d00f0341c0c490300c3d4100c2e83d544600060b102d0615100300414994000d008450aa902c3d80c012040f4002c2201c0c0024040d2108186001060084060000303003091300300007083c06020500050341d115424030901c107290402c018210390f8003608203c01002108004401c480116000050200e04083d94103103c401a21039544110380240c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 840011807 1250 840010557 840010601
    0x512041110050d0b010903050d210606050909060901065c1902240409020d050f160f020319031406150313020a03120207033e04 56
    0xa540702d0000e1402e080c0000b800c10000c40f4000046554092a01009107690300840c04041c01c140034941401060240210461804114081e00800c0d680e0700e07409400401c0000c101c0e840076141c00002181e01a106450b00710381c640c07400100425828460400d800700b510105103466540d41d04841e08103600c0d00011501e21030f00b6100b035140c0c10183c01869609242000e50144040e90000482c008414000c100200c800c040d0701d58080100ea0381d4404407281d0300100801c0744010b2540040c02600003030500d028010b0300c4208220b50041660001004035010950035010450500c0f80407083d0b035900c46013840c000e41c0c64001c4803416869803060000396210050008190442c9a9154000c1206541e0a400980040d1100b809206075aa201c1070040c04107401400001d80c00d1032508154000039000800b021000c3da50790f00c900c4003110140030311f540160000e60342070081c8014900c03817101c204102e40255080641c904010a07501c17190111000b240080248003041580c1c40d50030546507115000310500c142 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 840013057 1250 840011807 840011839
    0x60304030207050a2c070507021201050601140c030a03020702030a0b01270203071d04091b05030c01050301080606061602100f02011505030a06091e0b060f040c05120411 74
    0x9a0940c400c02d84900c52200300861015170b0761942c0300d8140101601c3c0041d401854140040c1d102000344280100b080074404180540e0364110860840040b6100000351400e16000040041816201d034004016003003206200c0140004211003446a00c2d107001078445410744002030400d9100722000e00301004010012400b201041022429140707409000d20741448200c0d898426030204960500105a001c20308000824240031007650800e4018000a40c0078000d9a403010005040e8200a40d4070401000900048c10201302185141c402400c103103046615141704166109402001c0c00d0098101203444c5164180c0a4002c440c440c5e070003011040c4200c003260000b00b558040e841400015800c1480d0218450041d01c540400e82e04050081d01c514540da469030009450843d40449040420b80c000501c4078680307580c030000c3d50307100d03908a001c80d081040801540e03250320000144224a8000076001694004003220000b81c51042c0104081c0e9580c1000c1c864011090180d5030490070780407581400c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 840014307 1250 840013057 840013063
    0x4090b090625020c1002030d240807210602040b0f030f0f1303081902071401050a0605090411030705040f021b1504172203030e0405280b0603040302 65
    0x41402e006481602d505204104079000c1c00303036190044090f03000701c201a211401c101c001c1001c002d1090044914242502d4038160803150750140248145100c0201c07020800403e1121000515020b4020b0400508240d10441d100e40488403041c00b1440050070241000300940584c0c0007000c1c1141c1460711050454009a0580d104690400c24518444002111140051041401006c83e056566210022981e080e10310450142c0b40c1c1c8180180001080c1c611600d03400181950351060102401c1005409801404c0d640045d000442c003a00748030081c0207035121a5411544103400101070110701c0c51880100b814001550091030b003090406035241130540300340d00100088c80e000c00413185654049400385444007590b04503001090710300004640411255000103004684140c01c0d98901006890b41d000706100c060070781031034682008410010b0641010754500841010348040c40507180ca200e159100c2e481c071024070300509640175200c102d0900140c0c0140e0b500301004c0c140c5179903400d060038080e503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 840015557 1250 840014307 840014311
    0x1c180b0d090b0603010e030a030b0307120c030b0a0c0e0d02060c0a0813050618040507140d0501091b120c0909060f1517070c020607050d1d0a120b040204090b0906 71
    0xe50b1000040228410f41014858128055043c5003c1c1d82012443c3d00c2c120b003d0016811640e034140304a10300030942d090304901c250410380c42040e5550312036142d450308100c044402002c405040780fa00c4600400d0a401c2002c41c4101582252035072900780740b0b84006041d5026680340b0010303500c60f00580c0f4040125910040c03040030520701d0700d5110b0395583c000b0080305214002c0041540f00c011000ca44190406410540d04544941070000588000f19401705864001c005507103103040d120401005a0b800c0307481307802400303000d1503c071802081d0402c1c0d01502c3d81c040d40465031f201590741c02003019654070516901c0003910202c01c0c20f0125a0f0348a00f0000c0d400007e000d4080200400b19030300c0300e5213005480320340e000d4988140282c060b68804c0fa080e100c4e030880200580e00004104404000030b00184108108550f8a8861681014060240882102101b003000b40603100002040c010000400348192245074469145091941c481c408107010307214280c00103024216804c14095010070100f0424 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 840016807 1250 840015557 840015563
    0x1516090e07200d110a030203091507120c020108070f27171b010201050420030304050603130303060f05210c041401060f050304020d0305030702010e0d110f1c180b0d09 73
    0x1400410400c03031505d49a2110f088000d000d039100b001840c03510b0900740d0211154485829210341000302c0c0741c55009520300307000e905000007440904044110b603007003540c1c2600103800f4a00200c6c6400d4941000d009118048802005802c0b500e110031840c80140010307602030102d20550042c9048181c2605544040d01c4501c14044860200450000c0d44140705984c0301d183c2014074a0080c5000d60240012380e1545485260580010000811261a1480250300810700b4606200200c81c49050050841b04245c10038000069180d90402c9103698043c031a0300b0400982d141d4070908581c044140e498040c4840d0480e400c507040141034441c0409040f00d41d8100c81081e00e82e1304d92007148250890b110300c41283c1c000d50145000440d580464800c8000c1d6038804441d000004100c401110894035056035403000800190600185805c11030043c0019100c44080e200200b0070f00c88a940002d580042c4121608100700e007440c6980100c81d0a9040700009100526166644115821030305007d00303540f960603 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 840018057 1250 840016807 840016817
    0x3051c02010e0f070b0c0106030602070c15030e0c01050c0f120301031506030314030712060803040906051906140f0c060106030c050a09060e1801081516090e07200d 72
    0x82c0c06035011881d480c900b807000b800b40c1580340c24480b42c02101e800440c8281850340d6254400302c0002e00c1d9100820146001c1d0356007078402c3d8500004a001c601888180e00c0400d8206880745401680015400683c4042400d2860300c0d60035180b0000e02d400340c01a181a00b0f03104201c281c40021900034000c505031303402000f540b004106105010401d44081e0721008001811013000f207481880480c02070341d004100ca2070903a440b0391100c24908159165500612102d410016080000801a108243c0146002d4a000d800c4200203841030f05c1c40b107043c0c820340090001d4404030030680c40c1c00d50101c520807401e841d41031341c503081c480480c07560f540c80900842d40842e140c40c84402020f400b0b281618a01a03240c2c0c0ca680308a4108881180c45d20041c09169400038a900a820502c0c640311520501808010f4002c0540b06090f807a05025014041d21418150f410080a100c0c103940c0292500141c403032012640702c441d101c0c0d04080720f00082007080d4004c406840c0300c4444407400b022a07a81c00814241d43c038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 840019307 1250 840018057 840018071
    0x8090418110f100206010e041109040302010605030d02010b010e060a0e0904121409030a11030304050d030c05120304050a08090f0d030c0201020c0a0b0a231303260313050703051c0201 80
    0x1480f01c019410050000981e1000c1e00401c0003043c08802268054810807000701d0b811041808141d0409090700d00b140540d44a10042c03090341010000480800070901c0203101c24459400041c19041c2c018181500590000855948146c080c1f079942d603e4090240c200f540c03a00e01410003a01c003860030ad220000041c4441c418126481501054a40c6150010040c0c40b40028070340e04c1c0c4048042283c800b03034142c0414800004e0703c1d5128988002e00c1d030700036203d20380010400e1502c40e0401020001145120400340305000c0428400101c04c00c01e10740c0041607644e0303514800c00288420790103078043d5a01001554403035080545c400e48455100d07200b82c0031200f03045d000b4010041c5031025401990340e007003424029140c0c42c038070032610b01d1285c8020805001768281c0100e1034103059031141e01c0030700100c90345080800c10403c210b117001101c050b6501c05240042960036010f6010703c005071903c1c40304e5004941c0c00c400d00c5000e10503200110761043c00c0310380c0d00c1d00890401c0c00701a40300404a015501e0010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 840020557 1250 840019307 840019309
    0x5030906100317030a060503060903070311120a0804050a0c0f03060b040c0f0c02060705120a1107320901180e0303040b1f092a110a08090418110f 64
    0x1d00781007a2a4807950080c2a01054024000260801882036103c9a220140007901c0d407400c1c407041d4003500060004e1940e55495050103401e02c0da184500c094241e104c90251058540400140d4200780400d20301108140c03200d003003942ca00700e40701c88042c2c00814100300008800010310000d0080b24031070601800400a02400c2000300c17800f18482c5000302d024100d200401d28402d1922040b00c610046c00c407030511000f03803509851721890944518217601c0020354040030759004108071181e1840813000300b04007400c1c01001024484a0300400d0f0011000c2000d0f18070041815034100e80a00d406402c06060791f964020910780400f14000b21040070349026030748003068074003000b260b00c00ca401c02004d014580b150409150340484078100304181240e242800309881c0c0f0341d40035840404100e5542c82203144800444843c44904004001e8144440d030240c254900070046200740450b90842681c40c0c684c0c40900128000c1e001d4641e0040314102e20000c8281000100c502540c00400300703451000e08104850 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 840021807 1250 840020557 840020581
    0xe0f0d09090605011706060903154006050c0417011410050307050f1210050103030f031b030b0121060306270602030a0212010b0c06150109060e0f0a030305030906 71
    0x1e40c8490380c175161040082d502d410072100500c1c0020300602120b034600315891003040c2d80981540c8040c00c200c030030302035101e109410361030744668260301c0901d20318178860705001004119600c0c44020480350326000085c03807401503003050b28020328608800c21400b00003244414000d100243d41c45a852811002107024040c090304158103540020300204201e07130070b00d410011220026140e06078811f400c012402c0c5440400e000315001050403a5002c1003079415803030301901060748010003404061403c7c07004010702240c0c240840e144005414001002e1013118012500003850b9460b071003240a03060140d0403001c0103580102e041700d00407502040440409035803106806840f5840040e44202c810400001c0340091f4001d5410008141c03005290140c8494040540082640a08903504021800708102d1101340091a40054880c04000c0d240c0312820001e4a105014043c007001c0040000c801c401940f242c3c1f200320394600c4024030030350078a50781c9d240c010a079030300c21698400d140c090f4601040556900d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 840023057 1250 840021807 840021827
    0x5150105030a0b06030a020a080706030e0d0504062d110705031212100305010f0b0f01080601021b03010f0f05060a0b130501030905030d0912090e04020f040e0f0d0909060501 76
    0x801915804590f074403000d001c01c4000e441c081d4180501400000140d49526182d002820f0540c09404298078028015044a54001100304aa00214251800d480d1700c2030071074059404e10b082030f5110101c40b00a06610180d51112007143c80708051243d049560018079912039155440101c0b50015150010f05440d0341200240e01315001c4240300001010108103a8203600ca04000d4102a1481d82c1c1d80f200343c00d5845081840501980d500083da085080201c1d0286011100f800c081d111400c0c881c00003540d8680c400d0310440c10705103da10710344c1207541c2904501703102510420244401c001c0d10400030700400058a04500c5046c034850000788520142090751200c1a95513a40f00555250500550182086010480e400c3c00308000910306030f00319104806d01240101c820440036803983c3c20180109225402500b205d5512004020050350b4500744a6014071064a0104690380d01440c1c40740b80a500c1e540c1e0038081d0181d00001040a90310003050800c03206410b00030b01a15a960b00191410094 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 840024307 1250 840023057 840023059
    0xc100e03070608130510020a0e0f031f020d0501091b170f180d0c0c080f0303041b0f0b0a09090605060d0c0e0406170c040501060c031b1203020705150105 67
    0x101507800c0000c0c50140c03480e541c1c40391903504100c02818055a4403820000c07074040803c1420b5010a407260415030126107509880c3d000d91300351900b804032600080e03503400f500c0c00442d115011b50341c5116480059805a50382030240020034446561120060000313024044424601c7e42c480e900b00b0301480b8801c801655080c14155601c2c0d50589945800820841d0010000b94080880304414640f031401000307410446c2090340c0d1a8000200c0343d02d800b0b0400d14050740b200b80140c0c0102c800b8100e80c0e0f008000c0f80d4106e903109058070b100e00810b203800c0350395100d1588505031701e81070f0074400202c1101d08402013103050120f40d0b44c17580d29a1201d9207202168824020380fa04402d09128100700181c4507441000c058006080198001d0094400034042d00c80e03c0d0082c0c80180040501c815050004000c0f01c00d107018100c80c14481d07907041a01c0244141c00c0000c015041141c2c659030442c664241c2e0b00003043c00d43c0c02c10b502044081c80c901004d4040d50003d40e0481d4140f2039400f8483c81000f810340d626040e500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 840025557 1250 840024307 840024313
    0xe0906090a0b2a0c0c01021002040807140a09110c2b0c020a090519111603140408060a0506100c02030d0c0809040f091a1e090a0f03020c100e03 63
    0xe030001007032000c034000e00c0c05035a0580582e1443c51941941400307040752100000c0103000c80c0350f0f01c200090400300400c10440d0306900501080c0300050010801005441c00d82d00a000a00300302d02c002540d0445903440406060328048510400030b0604008003080626082101c46c400303c1e1b0340000f175464451440d0b0310700f0018a0000881c01510503411030700e506000600010205c6e49540303250342150820740d48480503015054040c003c900c2d06020381c8440a800c001540c0c00c01d500300c400b4078020390b80484001d0403c00e403815078002d1142c00e541520040c140c2d10b005c0341e210780340c0900558002c01d01542c58074230940c000c40300490441e1049106010180e409800340140440d40d5400f030301c07406140001100c0400c400d000a01094565100340b05004601c00343c0411303004403509221900071040501d4281d000d4951003000400d85181d00703940b000f4219004000040d0f95448606401e10084500c01852002020405414554000340c5101007401c21652102d074060015819103121f10800515a0507030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 840026807 1250 840025557 840025561
    0x1e080307110d050d030e0d14040b0306010212190e090709090b010309021e04290d020d1b08010b0307060e040b0f0a0306060602070e011404050606130e0906090a0b 71
    0xe00a011666150000949246810040c07a950301381042e0002c8890f400099440751100714001042198501144950809040340c8104041c00d0762584030345d0044621400c0000045044c0c1e0340300300f0117501081d440e0140c0d180c0b1039071034500c034000341d41405032980d0004100d00710440861401810b42c600543c495203550040320b1816030494060003910504606140d81c4204040141c1c443d00c05030300b41020015142d075030484c801c0f010001143c401d440c840c0d4143d00040341c0301400d0201400321900b000ca044908507003242591000170310126100d48c0050002c8146040385d0143d420456110b000d031218a03000f44000721955061699500d4130b44650400030320386a1040c3c25509043d4000c8182100c050f041c050300c0002c2e500461411062584101d884c2641c071901007041a0741440700c3c2c0043c09144a040c241949060a007603d0b0600b082c5a4520403565600810301e039559090407140f4200300b00e1301724040310756100152140c3c82c0c401c0758025500e001e0400020803401010410801003503220706000300036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 840028057 1250 840026807 840026813
    0x6300a0b150f041404241e050f04050619230403020f06060607150b1c030f08070e09070e040e030702130501060804231219080402060a030228091e080307 67
    0x1200640f44000c03c1b0031442401c0050707110b01c0340030700c0640d0340c480c0814910b4084480a403c0485100034500c0c1c01443d80407040c000012004161580c001d006050001601460580c605000381003078203102503006c2105003000c4048455000d224032580c0a602034941e242c110012680e1900300444569501180404c184000100c03e02503a20310010242380c0000c0004801c404291741103400c1c046030702d480f41040036601c201640000e264035100c841d80b40059260030015009429601d404042c14410300045e40014000c91148120501e8198014014802c2c0c2c031441d81c11940f01c1d4044402a8020090f032156001c694a90380030342c42c12540302e81c0c2c6800035642d560721220a41446500c003c00c440d48140c0e846500024104229032004008000e07155641d040f00820068954090800c80300740300070ba50400016903242c409488240d600c500380035030758400b040c034a200b20150020f1102c14560882900e80b07155603000003034a082d50580340d001e28030802a88411101810705100e41a41684104452400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 840029307 1250 840028057 840028073
    0x9130c090903110304032d032309030706050405041113060e06120a06140d0b0c30040507080a082508030f04030806300a0b150f041404 59
    0x429030003860081c0c03c0d85050350415007140c4c81640191429030401040500081c1001c424100c14881d0030b054960180c51640c6c051724030440c03003a46241d00c404201402182199071412101030442c01815a846661100e001070040c1d0844d0042c40d005900c1d14005070f1405a8200403104030104c1c81d140c4202e440c0c90301c00304840f5480024141c5410000078003001c045403051046041c000c0d505240041401030800c007070300c104980540c40d000c0c82049042030023030100724502451500031003030f45031455407428101c8403070240c407104690103030300805014625072600f981415801e000307621480c240e0324203903034030181d41d55101110f5401811090341080840000c4130103e4003d525114003000f550076010041c0c5480d4483d03002141c0c0e0101070b003e5a0104020180d1200034154403400c01c07110a41d03101192a84d070030149003078600e90040e841090703088a0420320100701c901e501ea60301c04036051052405414009918259030400e50242c2c5003002c01002c0c91410740502c0c4030754059000c2003201e9568648070451 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 840030557 1250 840029307 840029321
    0x70e0a0e06120109080a0203042907060f0b03030705060901060504060803040608100f03030f030f27080702031c09050d02010c121e051c02091c0503121509130c09 71
    0x10b2966844600301c0010310003001034108000d25802442e2903504e00039101c1c02140400c11981c07461101100c4044071140c501003a50320142c1c0045000800e2548954a18000c00e00e149020f9803505c00400e12134200b050018038140f28000c110300078840d050391001880140d501c40d008030308064105001c184511442007548170380c00801e01c82810303625540c170b410040145c15035410a40001d042c1d00f2110306041d800d809100c0030100035007000c21000c025290a1140b50072148800d03603804105501881c1485206001d69240a0300181903a02c514034044d2210300c10000303c4002c40c08140d0840c1d000400b0300d0200c40c0506204e070180c4030585140040e43d034401200010024a100307003c9440700301e48034a80301000411850005807a603e5a0b5a079044400c80605112200ba1002c00c1c01041442c2581d2140b0304070600400d000b03540344114000b5890054110300511441d60403e40e400000c1084440044034000c5a60400b51050b60745501c0394424400c441401000282c0810b00001c801c101541d25680616 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 840031807 1250 840030557 840030589
    0x3020d03030212041a07080603060703150b040b09090a051b07051e011505060c0307170d020c01020712050a0e22051501080c0c0a0f0f1a070e0a0e06 65
    0x1483c00302c88220241940d0000c4d03078183d60840302142e108818044018142e40c1080860404504914101c00080e03a0741c480100504101510b501e0f40e14801c07650302d03441300c02502e42103007020740352610340c040081c1035040000ca02c7d12451000021038070300d0b451032141902030403044200075502141e8070000c180503403214600712014402c040554005d10000075030300c2c6180201600101d202044050114814031158100c24443e003000c00100e101d404001088a8040380d201030490030031003080c1b2019078039010707204e21340c86900d00006648014010660080c50403038410a60148581c40064080f00ea50145124140100d13150820520040c50403244000c003d4240c02403502c01440280409000d8600c20350340301d024461522030300c0c511581c010b003c1070780c00004812481d08003200344100a03502e441202d00600603c0c0003581c2c40e4180070204552050064102e0740041a008080444e080201e0044a55000240144040301928034003091040210758107002d0100d1a80c89800400c0b056001c040141 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 840033057 1250 840031807 840031811
    0x3031a030303040605090609070806190b190602010615081f12081306050a091401050405041d120f04090b030a0b091b0307030b071101140916050a030b0103020d0303 72
    0x401903580800040d807086104070b00c0031034581014420140b500e8000740c800541d0b60444102401200380014550f41e101007509007604403100c400300c052004002002005402c0081d042c8552548116000c01100316101d941c0200800e542c0c62561181012000300300b600003654200114039640035094003070031030603100880c44900c15a544e48040301d00300c240c46c003280da0800c00301d1803c0849800c1e040d0000286454100249016803240f0014400c4405010300c4202d401114582030445c1d10078800e41e409850050020850840b155035144981e0040c424039226512510440038030454884050703681a00103410700c5400c0905001c611800b4003001401180c052064000074004502070a210740c2c024080f40e00034100c03100c21040e5600000481c500b003103019900010301000000c82c01000c0b80d92041c0213141640010062041e96400340a4410025481135a5501448858000414801d034240c0b080054021400c1c2d5600038401409854030001c0c02d0308804400400242c02d140128403540fa200f8900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 840034307 1250 840033057 840033101
    0x715050a140702132412111018060c060e0a020307050f04092307090e0a1e0b0411010906030b10080c040b030702070512010b09010312030e060a051605160303 69
    0x30f0003200c6150000f60142c140440303c14251515140c40300d0050240010140c1c3e2220751ba846945207011505e44240c003920500348002c408900c5481c5028404a00820b54620381e5952a0300803e4000300e82400d8035440d1810b5066824031500040c1029016400780c081c00b841032410080000d80c1211314240c58110f91900124000104007140d00e1f5108106154840c25045150307480d14a0002c036070304990295494202910464a0001001804d03141e000c1501c040d03a12150140e006110940840205800601800d01042061007482503c0c10f100a0b40d8a11109a88520843c203489425003104e802c0f00d41c1083c0c40240380e100c0c8601e9540504140862450b25668061140c0d0079402100e8080040c1c100e454180014a0500181304070019400300a0121f00035840c001381c00e02406210017042c1e46400c90000003040e0207900b10094a00800d01982d190f842c0902c508000f40104503007400240302a5248041c0756400307101030754114401e0f43c00345240c800c590754095000389000b2091030301102d06100f03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 840035557 1250 840034307 840034339
    0xa020c0102160308060306010b0904090c03240c0c0803011a07020607060f060b040533120618011805070314010303020a14122203050f0715050a140702 66
    0x400740c40b460024049a00c09035410000c0502034080c1c100d030b1007a0040030040001204d40f206071007440b030040714001011302c00b902e0300b044150300c107a0000b040c0011207170b814040c04841d00600344c0c1c0509801d000b449210202d00007242d40c003481d900020100e204c2400144540070614120344000004406504e02d8010640c00050ba190800c0e201110742a890f5218006501c4250180b08000c1a040e00503605060501c00003541c04a02d1201c034a50310000e012190940065150381003502c00c0c1001c40140d60780251031819100540203c504a000b600800109805926010002c50403920081c0340170744d00d51828000c0d50040c003400740200c0d08042d100ca8800d0105118101664000e600ca60020410150946055030307000c0c002c2d05030030501790484401208010448801c03100c1051070300c0448680000e110b20020084400c1d508050501e02c00c81000003000e032000902d0100741e0b40f44003405440c0c1001030200300d51034860310804100140d0601d03c000f41e04030400c1d01410310281b004103094180d2000d20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 840036807 1250 840035557 840035561
    0x90209010f03060b0105041d04150515121902091503010c050c0c030714042f04050102060a02071a06030f0607030b0f090906130f21030501210b0a020c01 67
    0x280009415184100082082082c00d1080204c9280300f82000d904180c6001e01013040340c00a13040c1011841e0115000500b00704048020b414100218075003008181000c41c2c05074075261810340314901422040714442c1e05c2d8031002a00e040c4220822512002c1d55101d43c0c02e100c0407400c00750808020390088964602282c4d802c3c020340714006150b99603580c86481100070a8901031075454902d009401c00341c000d01034206900340c040d00d0648103403004580e11050b0080c440304140385280c803d41ca480481c4542c00c034010303203000800c02c0700c400f60300704c80c0b0b42d4440b010010304138492442c008007504030340d00c18500201c0c200005180d005500506540c103821044c6043d40c180282180c2250000340d440b0360420051401002c140c2249500f540e07100c5030381c41e0810249075a0070020b40f460b100c86121041840800907555240940c142c3c1c402407428080c119130000007c5038003030344204030119040c4800441ca0341440c00414034040c80034468940b2503407090701d51864502e805825490680d40800c124180d4002c24 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 840038057 1250 840036807 840036809
    0x91006090621032a11060a021005090f0703063204020d020609031507080109060602030315030705032e0504080304110a090c020a02041a091b070b040f060c1b110409020901 75
    0x20404c07620345148203140800242c1d80300d070940c2d846914107006080c00d00f0f5001514400f0890f050400260356120481540d15281424a10708024440d01001200304941504604402c64440e020490307018009400340c0c002c8140d40c891040b81b100041b0000e009403414034054101680047c149a103081013010100e410f03e41c400342d031105a0101c410901007120340c8071620038010190349000b008144d06200000351613200c05805c031010f00c10612420070407540e050001d000103290003000c0312064034440e1030782516520400074030302d00a044040401540001809031034482c41d40100f025182d07a8440e0355141600c00300c0450380781c0082c0303200700200300034030548508111926682c0040c050b0280500c100300c01c1d9070f411202114284c040c042c88240c0c40d1154040a030b00429940c28000e0007810070341c000303140c90255200c0640180c510344103200512903840310741c84030036004400502c80b04400f5801038a0208000455903922010748442d600424101640c040703542038001c0c0701045030200390f00000c00c100c0382 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 840039307 1250 840038057 840038117
    0x15060309030901140c030909090715080108071505090105030a0f06290901020a02090405013b0723030c150306190602060109022109100609062103 64
    0x100c00c031082d82c000c506140d00132600010b05180c458400c04858480c0225081540034140c500b01003241c0c0c0c4070920101d400342001c100090341c544100e550041c480c000030301c03030076209020b142008507a0603001440703031330b551030360b91101441d00c045040115000ea000409002010f5034410441d00c0344411030040c40002c03c00800300f400c49108240542c4420751680309188505881045030381c650340d07000b00e0080401501100c92102aa0ba1810f0290242c444550410820100903101b2008204c92042c00c450700482c040c100c84d401c0500c0c000032942c1d03242a004080041c0110303000390754840405400381250001c0039007980c01045010300030542544282c17502400c1580c000c0200051402c0604500541c0d5610320b9012661614015000e91240390600503000340076000140018100e41c1c1c48c00c072400503510600010700300e14107403038501c3e2100440c1c0d08103111242003000c002449840b9000f95000e07203000c440301015181e0507041d0344018070761804045040c4034841e207a6040d01282909003210400c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 840040557 1250 840039307 840039313
    0x120114040b0d1b0501051305040504020d51050c040807080a1e0c03060b0105210703060f0e191b0801080c040612020d020a1a0c0d0f050a0815060309 65
    0x10b0100c510f049800b840b500000e0400c901803103c080c6400860740c031881210400e5800103041c0e2100e00200d00c1070040c05601501c51805000c0d8030030040f02c545400c4058018404040e1404251006c1446070500c03c0041219060440105a1442c50f8564030190304040ea980303009180541d1414828146807a55012151a40240c104a818051000b00c0c07000305064505103107000c0c15181c1d0b242d1040440310300010f02855652036126801d40d00030002c50700018032510940512982002c1ca00e90205002c5a100d000203081c001c00141140008810406880d01c0440c0e40d4400e41e16581640000004c4640215501e0388402500d000400c4003103000c4c4100b40d50b0360b1120900d43c10703c9090b40c603045024561030300880c44d012080110910319071000300110347c102c400301c02d0250b403400060f03101003091300040c1d0480180030030600d42100f00c074002c102c010205820b030390042e4901c040980f03100042151000100c0c1d8104034542c4518070078640158481211642440102c1c0340c0c40101d41141c00031070f52038400e54 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 840041807 1250 840040557 840040583
    0xe1806210304090c0201060e010603020f070803010b0d140919022403180c10030b24070606080111120408040902130504050a062421060e010b120114040b0d 68
    0x2959402560400d0f4000d00007441250b03e402c0b0030942d08c6005210b002c080640c0480c10103c201007183c02c60f83c040d03401075102c80e100e58550f40c5042403030307014203040280c841c034005c10003600d49800288684101000302c0500f0414540c58040b00c242c105400e0100d03844050030310060341c20705101c45181509042c1120094682c40c0c02041800d050750740c40000c038000d900c400740c21a000ea5456044100340c1030645030109046214101003006002d003d90702e0201c3c114240c4280c0719a112490141c003c850050a060009a40e03a5150700d007240d50400c4030794085d02042040100e28206c41d8401a04207114060701440d05a0350000d08040b600010340000400d61600d004106070b10b414080c040c0c000100780020816113140a0015440c1c591500d22104e01180035102509114002c01c00800a0040704038160480f8042402c400002d02e014021500350740f0100002189840180e0b05807082c1007244102100d4990030101c660411244029840d6840780e11051b2000707054a40c4030058050610480c0740031500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 840043057 1250 840041807 840041819
    0x7061d10080f0c0f25022d06070b0c0c070306050108031b2d01090c0e1b0a14070609050a0b0106020d0c08120709260d0e1806210304 58
    0x2240050681c090480d02440140304101c80041140e81d14000266180003002000a017090040b1210320040d500c1503641004210512407500500844c072404114241c00a50050420a85006040300a06080031181c002800c2a1007440144441d40c2c0001c12248043d5032036031088180d9100b6004040b040d0008502000e041e24841c184941d954dc1c200c0107001032080d42030045d0318a0300700181c0418840e524440050750010700398480c8101c16000140751380a552507901206905405580100407111201036000d0000e1750002070303c4800d1410b6503880c840e800d0b602031000158012040a0381c04550713500d280c50004404000303840355940b099003500c02a43c90108080c0c20100e40300594018400007921400c005181071080b1504241c240b40350b8208d684407144100c0700c0c0c2403950411943d0311211030400741d00c3d20b00f28030a58a50008001220101c2050100c00c84003586000e200d55040280408540740d0800d1036078509034020000f03007d03001501358801058540e842003126005103904005028001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 840044307 1250 840043057 840043081
    0x21e13150302160b0a1509060f0503010504022d0a090b0901050108070203070803180601030302070e0114130e10050717060a060f081b1201080d0c0507061d1008 70
    0xc000e00070300341182840590010841105201d4500410b0030100c40c0006580c201158040c0c50080303040ba400c000c0c0c654603407040d040207203ea4001c0d0202403400800010f00c5140500810f446141d0113403168032480f00440c403428032142d150391081096075a0fa003101d8216100c0810b02001098031250100301004000d041c441c0302c10068015904016169041000d166000011240580da010480d15521359415071340000e15a40c098042001c2d008420001042c164001038030000d60700110324401159a031040213000c11081c42160079000031140c1c200020310b00255001070885019002610200c40c0c0c0082140700310344044403c075010544002400fa54180c05a11a0350301032001d9440100040c24040007900051107200050200302c0d40e540050450607004601c081c1c6021410242030b120030303408110066285003401075401500c030700800010811310414041d1001500480907100d00c2e17060100031501c00c2450f800c00c09590006181500440e00c40c080a483c2c843d43c15030b20f00c50141401626460 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 840045557 1250 840044307 840044339
    0x80715020c1c06020f07350a09121b0806010e06100210051f0603110708090a120f0312020310060f090518010e0105012607170a0b0306010801020f0d021e13 68
    0x40a00c1400100c110074544211070341c207161042c00c5c407d51241100003045a21883c180c102c1702c14071072860001d80030041081c201c15181031049544880494070381350440d51b1130b10b091240b052035401e80808200d560400103c40005640c81d0b2061380c1005030fa034100c134401d132601503440c01942d1030f0301c0e03000319450003480002c140a4401881c09100b080b4280c2401e4445004404000c1c2071040b000400c0c4060303980710091003000f0840d0324460b105210300c82c105400315007a201006d401040820001582c02c105c0c41c406c0300e00c0b41094414401c0700e80e003800d4085507140011044103050215204000c1081d54072216100b04985401d564200d0310740c10030180100300324060344040d05026500c2020305c000c94800512400d144000d406460142d901d05200312903500c9094611080d0003000340c24017550320119003001e900800141d040b40c0c042c0c0d90300c41b422400c0b4401e90800403d0000c3c10310903925000e5084c0c0050600504100740b14449440140c0c0158295000c420000b44589440c1410803500c0640d101e100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 840046807 1250 840045557 840045593
    0x9210e0303070305030103061a0306161b030804030804080919080d050a080121060e06092e05064b06030a0216050d09080715020c1c06020f07 62
    0x360030b00d076040d507003d4010301040c040204007039100c084d071b000b0006c141d9070f61321002c0c0380090807104641808103000058512070a14000000e42005080108680c550080800585d055680704151782d03603a20101d8030450040c204450080003080003041c980d0311014050304201c00e07940070040b4507240c03840151400c41d1800300101404006d00c0701411894120035180e044945196203240301e03108038091200544801c61004183c00e00e014040014040001034076403107070a01c00122100c920110310b0901c240403000b0766154040c900d0098016403044a600100d4110704060300064030301101481a4000a4004141509128501860305010701400c00b0700700c1c01242c03840c000b000b040021b45c042000303840001c001d969150340010724010b1001002e401301e5001e6420000b580e800480e1114024000000c07449943e040c2d224898011444550a072101c00800c4907030340040c0400200d1109001500c0e80b865001000d91038181d2040b0003061213800100f0159100c100c001e943c43c0c50303a2a2120f00309420442036 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 840048057 1250 840046807 840046813
    0x60b03180a050619060f0e2a04121103060f0a1a030d032c030405100203120a0b0f2e050f0c0d032a1407020301020403060218031c0e0409210e03 63
    0x10030260603600107c1d9023001911010509036503d01111156400070000140c007901c60000d800618403d101c5aa440c42602c2032101d65403c4e1120f008240d60f68400307940c00803481105030086559036480350f01240c0310a80f000038860008107420006400c0c819803460000100b516030702d00c0701039480c2582e01d0341c0626146810b0a015034a080c400f15a40c0e0082c0d024050083d905c2c0102c20200500800a494404004988100c010f2030101c0c44040944480340c5414010300d2a81410382030751030030110052460b4040a149000c450304040c111492600d00580f507801d000341002840c040117010300040503100c91020007007102c2c050540c3c0040441c3c481c0c0701840310591905440d03106460030a407130410b4104003460011302000710f0002180480c8940c44009502d584005000010000d65401914041c202100030100c0041f21500b415110800c01c0c28032500010148e80e1440494080c148203c540c40300a00001070203a00796070380300a036400301040030810f00010880040642d074331a140f03552645046c1c000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 840049307 1250 840048057 840048059
    0xe0702030406050d0e0102030403031b0c080306060d090b07020d092c09010b031603050c04061a07080d0e0c1525020301020d020a180801060b03180a050619060f 70
    0x203480e07019500444003003040c0002c02c00c02c030070b186030410b0310321080e000001c65403400d1600d4042d0007070445007900d440803000d40503031100720350142c284081c9043d0840321441c61903480c80708000c59a801303480c5140c00075945814a1011034218100103210f0307070444d0000c001d490302100014264241c40d82c010800d04198501c09a040d07043e1451040540d140841490300076201e0114560240081e4061a82c040c80b50b52b031510b4040314804140400c0300c2c043c006480100300103200388800d07274060f400341410113009890714040040c0600001c20500340149145418a40143d00441c02c2d07420b0140034504541c46a0520021032901034501b0030031881d0021078503c0c2158040941ca18203814412080c020713041c562422080d91029012143c942c0c0003200119541c00c904131000c6c18001700501d0703140070689040d10201d0110030511912040e41e07030b403031091420b650380e111854041850490036030110340518002203000410401200340140e4000c858120300000380c0070301508680c0c203035100d0700c6203200100e8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 840050557 1250 840049307 840049321
    0x6121104140d022107030c0504020a090e040f0209040c2102090601031e140f010602030406080a0b0d050a0b060112092612070518060309070902181f02070e 68
    0xe007241503004140c510700444070321400000c250700c420801000c20000b02c0c000c0c1224021020580400340c07880b03004007882d01510341090000300e00079480c240c03001c1000320381c0c18031040040b15011684144940304144800e0360580c08940180000d4504959010010b00d0500030590344109203c0c2d0522480822541355000f030b0000380c2c2c2c1c4d4070080c02d441d040c5940e400e0024140c603040f900f010b0018510321030a00c42405400c18980318420111540d0701141440000401e21a1001c030132141161103540d1003160075220140004024504241c100b0f9200c620580300a0005800b440020704041c010900c004591030044005040c07544513007246400c003403a00d0650000100e201001c078650705075043e00207601c0c0412b400040114440e4000d9001d10409610070012242d0f0300600810113954080c402c400030301010ba0910000e80010b0f070380014103030003040052155807259400b4107203504010b1102c0020000c280040b0303c0b250000d0341c070202d02040041001041540401420380182282603d010051030100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 840051807 1250 840050557 840050579
    0x60905091005040c0e090903031501080f04060f270209072109020102011d0105090c1503060111030922061e030b061906020a0506070e010c030507170406121104 70
    0x80503082c81980e44640702c1c001c103417103288005807a140107044e00500341410580c1580c2ea401c1203880584225105011032201c0d4030800c0280e00448040d01114130301d455956911024001245d038110805641e451075031100c6a240200c90004411102401819902d60040c0095200014001001e21140c440c4105030050b001c4800b440b018a00c00700002c0c050050320040b805030a40f401c034034480c4120000301100891041d0b20807400344044108032544a60240d05100b030001f8015082042103c0078000101707694001c1100103010307250714054030301c0c0080010000798502c01c0040407580c0c0d1404040c41215203022841048082d203d200c0710000b094108592082440f0424000206030300d13880b0005c00c110341c07104030075140317866220039414003926110b44000f07646400605c0103603500c3c495100480d560038054803410f0105c0d04107a541c0b0700070f00443d4074151510362240c0c20480702444d001d00712400c0107807910054000350145656644800c582c010104042c0c3c2c0c3d00942e45542490200010415200c00c2c1e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 840053057 1250 840051807 840051809
    0x70317010b1e090f04020c060a0e0c09160c060609020901030608010902091609050d030c03030b01030501050a0b0f120106050a0f0206010602101a0301050108010f0f050609070c0512130609050910 85
    0x214010380c1e50f80114400300d0703003081030590380c0350b000741c0007044180c0307004004642c045c0304141e20788003001498041c000303a40d40da0080200a5410100b08008a141400c00a80309055070780e0710b0604540c1c0d240c0550b1007104840d069880306203200d6010401145560381806428000c2400a000340030721901d0ba00058900c64020304000070784080d10030200301142c01040044000d1000920f80d050100c070300e09018218602c148021400a85485280c00e6198013034440e550690303501802e0389813800d0074400c080000b603101c2455440400030500030501c1d01c0611502c3d0a001e0586541c446480d222070000c0984480c404c0b4075a101503420601c0180041a40020190000c0506982c041035400c0a0180c12041e10038038000c054042d400c0000100721488150888070507065200300c20072a0f10301d1039100c1c03012110140ea046034016501c001040109124008003001c0798022825a00303114800b1080320010750120a1380c80c174200c0c075004104855900244840b0044c41c043c6c60f0a99140340509981581c00c02e1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 840054307 1250 840053057 840053107
    0x4051021020a0c080a09030303050a200d0f15030b06241303050d0206011403030408070b0309010b1801082107060e1906051801140406090215070317010b 67
    0x400304284030304074070401c26000203942141318280c0d66004030100030a0303508140020f4020070705000200d2040030700c81c0300701500d541c00c1c03888601d000c090030540f140d0300f0f6200c80c005000d0207450b801c0380c030060001303031240100c0d0005445031001042c1c80c610300203103100801414584182201c1290204042d94203001102c648001120b0035030302d40384a00501e40607105034001400c0340c800c3c150320707000141e00040e500381602c074100c000290342082d08080550342d100314064140c45400c00041000305482406c0079541001084002159072409000401c805d1694200c4031505405804010403009506100f00d03001c0d070744543c2c2c895506804116203202c09204080e4024075540c1d960300400307034444040c007071040300551035070130071700c0801c0541806005460285c0311140011704842400d81581ca0500c969114003040780d95030240360f501d6440d0080201210350702a42c0100124600d800d00300c0500e8002c003041c92203505ca1640c0300010303513076201120310140c022591b0854100403814400444040314290b01c54 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 840055557 1250 840054307 840054311
    0x60f0301181512021503190f182009070c06051311060c011104091e150e0903040e071d01020f03190e061b060c0a0c0f0303020910030204051021 63
    0x182c0c4e10200726214200c9a058241c000e002c024003107140701c1c400e016414003003440000d20004544d101c0c44400c88188004030560005012289030010b0f5032040001802c04521400c1c1301ca40101902141d5550b104407481c100154442a0712402c20850348070b030542064040c600a00400550f03900e0300d014100b01010107108100104001c2a016425007014011400400d06103403515a907061490180255403c01c0300590b10503440d0307203255061840b40c0404205525a480c501c41e11341a0b00010400e8080c260800031301042101040080c11540e50b10b000d84003aa8411860b00c26100034205212003d90059045400c007042203000c080000040e03500320140c08440014141035480701303862660014801c140c000340b0114041c1d0390b21081ca150b00440b0f00c40a4150741c05903961944140c07031489801c212101040303c22030340c040401c00182181050a20a0400515105441000070402c010103003e0300c0000740c0004041c481805c081c40c26007124682d50922040881c49081200d2903c200b6100c8254096 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 840056807 1250 840055557 840055589
    0x30c06030a15080c0307050d120e01050408010606180e06090103030827030c060108070e13020f0d060e07060918090f140304061706100f02010b060f03011815 69
    0x1403059100c9440c102c1c2000302c500c032460340c4890f11074550f8a00c6900900c81d00a042000599017000184182000c1c0d000c000001c030000901c406070b0b0301100540e01c8a040120034000403030392403401d100f110054103050711403411132030000d40c9940316044550048414000c801c0305100440d04e4010000341500e82c1401d11030f0581d9100c005414110100d07400d045c001020383c0d40000d8131400007100400941808200351402a07880f4402c003030369214140b040410032184400055a1403050b0092550180d10003801d202c031400c071000009017091a0041e0541e106940c3d540c018240a000700b0100c00103111609010b103100d42380449264002400d045c10585a03070f224014181005030165604142d9a07100c01005520064200c103543d603034000d809140f01040351185241c1242c07035804500c4d031103900014540700505a08000454480f44200e101e441590b4a50341015119521755000d4155600c000e1140e5480307614040e4606a8400100407140310546032595242c1401d250f0b910110541d1034102c3c1c285482 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 840058057 1250 840056807 840056821
    0x2341a09120403050a061d1203040618050a142121010f06050d110f0703020f2d0705030d030b031b1c080904090305040305010b0f0604150c050a05010204050a0e0402030c0603 76
    0x3205101c00084817034026008030f0350100c81b04030f018501982c0620702c1044100802c01202ccd0f0101030081014001c3d52114140780c00203202055088006040941550300702091b09500c2d60801c8442855007e4035440410701c0c040c0d401510b0110420701003050f111000951504000c41561445400766001b00540005e01003140c0700c8a402200c1c400c61305259059a9040940041c2100d42003140214010f000304800007982000004011031081c200084903400300e0485000c40000140e090f02900c8030307000700c0c41c00080c191750601175488203880c00d0314041407000f01c0c2800c050038000301850140d03075610b507400028640c2e160302d207140150301c8030380c0600507000c5098148503045000307005456501c24207045800301010381c0000034000700c901c1600240f1034079403a40d0400c000503070246141c54100130180001c00c43c900c2200798041c80300d081428850721103181521001d040c1a152401512243e40000b07081049013000c01c00d0000030300c040c2480c0309050902d0b6002a07210000200b100340314980c0400400c000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 840059307 1250 840058057 840058091
    0x1090336030501020307080a06060503071b0204060602030331110109030b070c110102010b0915181303020d0809210918090c0402341a09120403050a06 66
    0xa0405100d5440026941da10b4000e004c2e61003161601c00050351200480d814800c24040c2d102034810f6511914150350b03809804840c4000c02420700d0f00e40900100e5040c0140c0c8551148801a0250780d002d581d50b440c10310f03600e1040c24020803040d03000341810707801d0f40c1c80300d50005564000a9406104818100c000300c0040314412101d0304081c10385c19122040c41840750304032604100661182c4130081c02280881c0040e400c17038540160083c1c0004a40300012085144996801044240107141c500041410780d10003400d100300b2171300911840d0510121509050f010400c40781130a080f480c004080349800000c02d511201c1e10401041c002c141d01541080300c9901600391404440c0242c100002e640101c1d66400d0500001d81d201111401010320704100f6003814000c560507180481c001103c0c0d42c7c142107030421000c500d102300609102c80342001000140031043c1700c01100c1c80d48081c1c0b0a4908001282c3c40c2051071980785450615000c200c1040029004911501c900f40c0081d07000505003066806900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 840060557 1250 840059307 840059387
    0x2f0a050609240702011704120e121911191a04091b0306060503060f090426031f03171815072a18090503042303010903 52
    0x40d1800c1000c242c0c00c0c04060840a806118000d0341c07140170001003182d91000201090360302074141080c241101381410300840c9525400c94000d00003103086900e4130300c10b50500c2d4409141d0621000c602808101744503071210f4509101c00300f200c0c0c4181d80744a020800b408510284180d01410b240141c40d80b590308505010390b030041c5070360107003031221010740e0319003000060b004142c0002003851300b0700204d041c0d441601640e214000103440d608460b005001084001c0a000307008481030f01c1c581c2c104803114034a12038600c0702e484401111070f07101d05081c2154241643c06d41e07a0316841496560003000813882040e010102d0107040e07141d142e5280750200118040000d204001500300000040807420b03801074400401400c0c1c0602d503a43e100c1c0d414605480c410780200f0040711072604480b403060205403803c103c210070f001310b426400180301045544403411354000b50300c914885d01081c103022407000c40008408010700021402002003003201d540c060507a062041400d11450318803000401004582c14030f41d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 840061807 1250 840060557 840060589
    0x41b1b05030c070e011706011503020c0715030615050c0a030302070f0b010f06020f011802060c07170a02131503030f0e03120a1107030f1b122f0a050609 67
    0x30f181d03181c480e203146011400030722442c1040060b5401c00b0116030b1000c81e140e41a0b5801e034804520307004506808501a4011908030b595a0056040c00690080540c0c9071100c0d81ca003d446c04500310b450018045005010700040030240321040001c1110302c02c0c04a40d6072102d69050a0040c0c40d5405400e00410050081c00010034441c0404004100d84c003004103c1030440d14203508490b00c0c1d25158031003e0a0310603441c64042409203c1074410010325015000d010700409882c2150400d03070791041c541404d0340071045070501541104400c03005504204031285c007048041c92341805185d041c0da030300c0581c4001510000e4104000244180303200d91080e41da01d007658100a0403600c070000004810f229641c000642903000c921000c1c000d0000f070b8000300e0f94200f12600f09040d48080c14450300c0720025007640b8503010410005800000c00d20442c50344590080d18026005030010042500800003000300742d100e420b0411032002c4016071140e859208240a450090f02c2894a51742c1140c0802d02e0448944440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 840063057 1250 840061807 840061813
    0x51c0605040b04020a050109290c0a0f02090f0f1902040924080a05030a030f110c010e0d0e06070201050c3d1e0513080c0705041b1b05030c 61
    0x102040c07002c0a201d00d409607008071070406a86a85e0001550440300511828880c580000f9000448680c120320420800c800a540750b854005d40040c80c03810568202c3e000c42e42112140c00c1c3c0002d40c00e0004809030700149c0d040e441e18039802c082610a602040080c90140c4044408058405041140d01510002c1c84d844d8010b100c50380c01c0000340710484000300314088056152100002d854400002c03c1c041c1c0603000303406107152980c0f0403011809042c80b0301c3c19590300c5495440c0045a0942c4000400c9400e000100020361401d04043c61414460100d02c003008001031510005c2c0240d481c00200e600003982401c00baa650745034484101d08041c43e03091280940050180450600d00b01100a0004240162021200c06010040103811180c06401c1031b4032501c0d42110b600d51214644d03001d0350f00700540030030420100900b95507c02441e8043d00d070424054110005c2000941064052140c01208030350300c42040a88210004000f03000c009500159552145048000e202e0103000f107904890703800d07050f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 840064307 1250 840063057 840063061
    0x1006081f05091302030c041b0521040305040e090a050304090e0a0204090605040209010e04030507022107030501150906030210081f0801020712020c01211d0601090b100801051c0605 79
    0x25180e80d0b81070f0042c142c0c060300604241c0b1816282520420b402c1d50500901d40761800e10007142180c0f02d4102d0258003010502d2820003a2124032404103142c8038611958803513035500d0905111030003410001d8040340d241e9110126180000c0c00100695058401c820000100c1051001c1000d10f00711031010042d40003880d0080b20300c24003426801040c0314500075500d40d00345903030741c144000c040c0078200c4019000500901c82d1000620308100821205100003007104144403040c903e2031f0501169500891b001e0795a180d072582513450200301031000345520302c010007940d85507401240c0100d180e002003c2c1042a101d00064041005151645801d1007441c0410000c0c0d44078041107000354402507054424440c00000b40d00494400145541003e5040c3e548140b080d4090540c0b828500040780002c0001e5121041c9100e18211a000700c90081c0a4600618440d4503040d445007c0310140600b5501a04140c40d0000c94203400c80310860440f401a540102c018248401c4452140052080242082e0070401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 840065557 1250 840064307 840064321
    0x8090a32090f010303050a02190c0608010e07050301230306130501060b09060f090402040807030510110c100c0e1008040b0132040b04020c1615020d0e12010519051006081f0509 77
    0x9168150bc070303592110041c2d40d0b2a072826001c04c040461320722000030390400040c45410342c01c0c1010f08240407200c0507000900c05000020342490002c8035200c004600c1440e0390002c0c044c090007a54000c240303400c8a5403403d103204002c60502e00c00c0001840b94000c00107000446a20b45504171001001074000742c41c81c003030b1686011500e4014002c440345a0a042a10b07a801640400302105e80d5204404014800ca01c0030465010162890340c7d40b2a0902001c4c1c8620710140d141c10040b080c000a4643da038106625003440c08021481041e00903000c0b421140f0a80c100c06c030400c0b40600305071600c1d8042e0f041404801000a0003615140c40140d41050002c1100d50b80400c0c0040c0410000454201000c072140c5c540500c1c0c1d000c01c40c001a45401a4801811003c1d0107005503041c1ca0b03c0c03000600796002d0300c80000140d50a6400548802040384d40c40f10356414800c0d087e200b40c40d0804240440210a68a41640101002000307030000008600101001c5109401480041c0042c50046e0140940d40780100c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 840066807 1250 840065557 840065573
    0x60d05060d121d0301021305040504030c020613030302060c030c0702090c0c10020d0b04150b090109030602031305240714190f030b09010f0308090a32090f010303050a0219 75
    0x1c0e8481025428003880203c2c2c078903043c02650320f4130f601c1040c40304020b40341008020203000c000d070041d03080c4000000450050307100c00e401499107064502580290919520f4002c1c5000401485106802d801b0f001380040b038a6010100c81c80c294048a0400c140d413100f0b01d000c0481c0c030070a60f81304803a01c54804010362000040d00984280380e204841001500101c0007804151840e05480308400c1c0c10320b440038014181400c0c0500340700389040c54165080c0b0340b20ba8400049a206645405a007602c044400007004410440e4015007680540d20303405050b60b004116022650151600061041c3c00300310a14200000c3c080d00c1071760241208103402518070440180c6400b4031180440002820501c0e11403040c201100918100c07078540701040038043c55030311405590f80210005562201c8020720001c6c91024070b403600c6802c03403c50300ca500502502d158030060f056907100002402071ba04002084a505641080340e411240c04d410080d90741c8041a0049043c00850132603d04028400d5581c101449009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 840068057 1250 840066807 840066827
    0x90b04062712031802030604060f0213030510061e030b0c250c0f0b090405280501180c0e0d02040f090b0105030d02070b0f0a0207090207060506030705010509060d05060d12 75
    0x3d842c204010181300080b80c1060110180203501544441c01103000102e06a010708120300c1c41001c0142040310404c6201111000f40e8402d5403da80441c07083c0845c1d0150303102d030030001d0090a44850b00c030020f070443c01246e40000d11003c1c18000c4c0c00e000191502403c0c0e000c941c0c480140f0141070304910301040c20325402c01c00c0a10103441c00c0301d8070403010640034031010966082d1021049000c1c2000000410000900700c020b0106003034005c0030780303e05007420310348003900300700c40460b10003091940c1046880a0307a00040c8022810300b500701402414020340105521914072016145490b4040d00307400403402901d1031025070010f55140581180901c200040c003503050f14000c8040c0c0b83e2000e2800c40c1282d41e0981402411211581080300b02401510705c0014405982a40141c400a65035580325030104c3c1c1044000f03031035480c0c403001081203625050200001a20b403d007825404e010041010850900801e1164440e8035a20400300d02c00340e8034901201400ca9001c00444048000400020300350046 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 840069307 1250 840068057 840068093
    0x201051303051b060903100e1c0801141504050405060f0a0b0c0118030f11120d020306013e010e0a032109110402071509060606020709090b040627 64
    0x700001d0220324190007240c0042c4001001890400245c0c04060f000303241d01582d030080c502c1005d4270b00110750500c809001e080c0034603855600c0c1c03070b61504042c2c640b038049404c00548910082c0030024030100c204000e84003544c1c003d84d4002400d5a916000c9000c8050303c83c1082d601101003640005c0000003200140010b201090007480b4100072504005014600018020302140764000f400c600a03204140103080c40541408035442100a10b5030030003503902c41c0030761030300c1103400008100f601c0d60042c1503900c21110481d0610441d2040000c0d03810015032440031043c103120b2070344d02c41c1445142500300c07402000d181019100c803a030180c94060300700036031026080301001904200e641d51250910407040e140d50000804803000513000c0400c0000d40c0001801c841016500c1c030241005207036440345140b124814440010100d0414001901e80b08440d804600d40310304011904000441c0c011040317420580c86000414010340142210015001601403c00690480e011841c10f01c80441500804006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 840070557 1250 840069307 840069343
    0xc1e010222030510050c130801091205190f020c090f1b0304030c02040c03020d1a241603053a090203152802070506100807030b04020105130305 63
    0xc6500800305030480707030b00c000350880c1c004003510310f05800b0940049074460074044100e86049000016100c030001940c1040740c850795510511000c0201c600c402250f114214200b1030706100d103802c41d00c080500c2c44000e600400841c80240b1600500130000c0099409000300b01480c0c914109202c0c840c90142110509c54403402e0010701d5868501c40004c40b401581c0542d81e032000916650244405041c0b071403c1e04007050303803c01400c4150b00b194410b602d40d03041110000c80008602e602040102d8510740c688001c0d600d1045407070000050705004442d8010b045042c2054180f5503428156014000d140d19400c03040001c1103246075034030605030b80d1504801c4c04000303086210300719200e8070110b45501000039010b601c1480242080c210741e000701070f80b1040100243d50b80c280c520800849040c100011003207050740215107841040340612810764000340101824030403520b04101150340c0c0703090b0303c40501081c2c2804041015039100c0c034110f44800c944500c0c0b640090342c1d41d1620a5858002c0249417100305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 840071807 1250 840070557 840070597
    0x10020c03070803130f080604030507110a090c030c02060115141201151b030e01081918030e0301050f0c07060b0a060e090a09020112020a03061d091b0105040b0c1e0102 73
    0x1c4003400e40785d0240e404000045c01a0783e51641c080d070342e603844000f096507a104071600c203028907610003400344058042c0d94004621031140307620240640b8030305078600065402c12001849420703111070075005081c10074505290024414103030b030b0080344240305000c0f0038620420000b01e04442180030b400c01c03010303440d0384d0f00320700452124005c9003a46010400500140c5138054500c480e6105220702e070740000592800804905401c03202c0011505030850992035907041a0a5034141074014070310700600c500c00e600a00c007a26103610600a8954000d20448403000e000c9000c00a004641d03000c0049000041c12070a03440d51501d40141234000010216403054081c54005800881c0c54064031242d10ba06842d0120754481d40400c0d070010f900f00143c1030007010340d00d102c0081c021218050032005044d140000c0c1403203040c844081410a882c600c030300240138107030030707409209e0383d03400b80c100c9048030300170800c843e190086c45082d141000340415005c540410642000c050a540640c024a9100e404a04603d403035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 840073057 1250 840071807 840071819
    0x50103020111060c03010b0306061308010c120204240912050a0b0109020909070e010e0301060b09040b2b02011413082503110d170408191110020c0307080313 69
    0xf032001150403c41152051004024030807911000d190013120050540d0300b08582000400d5001c1c2003980000270703580d1281320003c103668004a0041c651001d8107825440d150618010904440b010109514010f42001004064070710521210000d4001045858a541ca10381802956076022140503901e22000e0000010418841d01c2218101000034184240c155902d0105982c80380410301c096050280901c800c2c0c2c003964081c89543e01030083e07140d83d2030301c42d06d1120920040701e030030300586401203451110846010002c040300905c045440c10f003010596055100485440410500708803520001040c2c000047ca0095011b10590745000111440d11003818807203080343c000d0107103a41020350640070070b001040591000c030030a143c3c0501541d90650096031680b00c20800300d5207103002400301060a2007402024082a15504ca2801d84990403c61944030100c100d5001c0401600c5403003c6403501e48201d00078428a001907030f0040656000550350fa080726100e80c0243c481c220395031002d6a01040c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 840074307 1250 840073057 840073063
    0x20901080f12120f07090b0d0905010b04090302150a140403080a0f05010609090207050f1614060901080f040302070519050f0d120f12020a090806180d0c03030e0a06050103020111 78
    0x8401403d044926594a4005808480200c0608800c0400080207030114103620312200512480220b880002000c9030141002821030b5025000715103e14102030030070020079800200c1548440c454072081c0d22580b14018210004c01302c01c2d0b2080018000241000305058000110602c190080c1009010a502d0700a413582110300900880b408250020010b100105130760b4040c00b0007030700c00d0080f6001d00480c075003c1490a1a034030300c0340342074086609007808801103d02c0141e204030070969495080c101c8040c00130302100c0000300b0301080f200c8402e000805062013005030f0340040402404181182038441e240c051540e1050180310b0051088010b141e04030706001400e0440241c00c80c01c20105c25070464001c0f5020812450000104401e0014889528405100520030700400d92100c64403d131619480386d0500f84020040141c445060303008217079400300801c02d003000283d1440e208009402c00c6c0340031390051103c070604041d91f10942c40b2020402070280e029034181c82c001d883d1140301c00d10792210296 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 840075557 1250 840074307 840074317
    0x1404060204030b101a0702010c05120318150411030c090a053c100b0c0303040b0a0207050d0f0c14150f100311130c03140705181903020901080f12 64
    0xb070012941c400341c954138841c009446d0b01c80c81403400800d250400e44032145400e280ba4580e0b8800140002886010109204031400d0103840d00e02410122840e403501400d41d41c3c0c0100043d28400174000c8400c1c007540c5c1030020500c6c441d0000d01003180d9040105142000700802c94840007406170f400f0280c00c2d5222031041c2052105000c540d44a641c131910051071603000405400d241650411210200e03403050040c01516110701c4280c001d40d00c80c681403e05c05864407016061100e01d40c4100038600104101007441c0108507064142230f2101842d4580c2140d0803c20a00c01030007110303075150741003002c03070001c03031103160042244013603185540301c0003455542185c0c2550003019440d4051005c100081c2030150b540c0340103400900340c444800755206200140d901007001c9400095480601d150b0341c3c0d40341040180c1200040c6416400c004607080c891007810f440000b03003442123800030020035194186912040c040d60b4003520140e01540d688101c50b96034201c24400c2101400f910b1282d8030342d81c484800380d034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 840076807 1250 840075557 840075569
    0x20906030103020d020f0d0503070309090b0303030714040503070b070c090203060607061503020907020a14030a0918060812040e0f13030c0204110408070303110601060e1002011404060204030b10 85
    0x40c40d5910716403c220f648441e40504a8000d601c0446405c4a03599040404007c1401280590364610b52880c005002e11216000000b5141c03900405c01d45544bc0001070301c4e0b01404900382107801c1c1c2c0c6070340c441e819103002e554086070b4148030b205000320f00341d81644040c00d5540d1041c150101100d4440504800340c2c0000c40305550481400d04c04480450304076000400030705a2880d005448503243d07000300b2001c0c40202e4104016030305c10041c500400128095007041d0f14169006141011352214000381111464812200718411051658011103000c5c2c1c4150000c1c02440100c2d00448580514901650040d205518420407418009401001c0000500e03210303075051444025000d41e10b96040c0c80c0345401101c140c0e0003940d103d00750780455091000a00c0a8171072200101202440e52400074100040010440c0b1b103600450010401d039138200125580f00141221843d203640d45150040b40181200100640980380c0d6405102c180a01c45c2d008200b503900031365a02940b650360705000c0e2074422a901c600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 840078057 1250 840076807 840076819
    0xc040815010b190c170405090a09030e0609010311042621071b14040f14070c0f0f0b0f09030a0804021905060324011d010c0206071b180209 61
    0x8203941144000c0d1200c0c1c3d40c0802d050040c00c40181e615011020106035900110032100040c05010314646203403d01c2e030200d0381c81b105010047d040c2c0c2e4010190000310110601804001c55624003e83c060380103803040a0400340c0c41070302e40e6175402c031912030003401d096260450328002c07018107000280481d90000034001c130b0441e01144031191700c01d100c41d40c0c08480265214058080700150041c0c6052008008001515030b00710204040d1381000101d50306561200d8031701e032070441c03040c05485c50030a180350700c405941441034003007200341460300030011000402024080d401002d082000f05010186009401000405500b9520707122103035600d02c40c08041d6404954890001401440c10b9001070303411030a00314039034400682e2140424501e800655013008080a84032038003401840030030303103014015009d01e0400810203000d43c1c840d900904138200181001284040c00095407030300021a00181c1d80145498003065800e014400d034441e00d401028141040042d5140000c03540e4003c1c1c81c1c00e403d0060070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 840079307 1250 840078057 840078067
    0x816050711060c0a0507050301021e0a05040503190507121a06030f0703050c090703060302060423130e1c0e0f0a0e090304170d080403050c010e060c040815010b 70
    0x68400303400140084a22220707852281101d6200c0720701614510606800410300350015180403800c0c0f0050303800c042d004c0e038030600400711501d294100260783d030701e40e00f081e0507991803040300304692601c51604281d401d403103828000340002c10064a228003050003a030590321159100c14104a1903144220013038515083d900d82d40e403e404180f00c030b02e904541c00800f140c40d40307058130103a1070070884a40d00948003900140d411504c1030070505280390744040b807890b0401c26039080da07001070502d0056000f40484081d030304200010104002c01041c00c040d4004203034900c01c9800e5080540034000b903004801d820300400e140303095a400c41d003100c00c1c0800300c1500e030304506601f180180001c1001111659901859044c00000c0c80408140031902810b0310a02466482c0c0c2070030140030680c14090507003a040e9026800c807004e01c591200696410030f5040c64440d64071151781485c00d0260401c011844110700414003808900a5448010f0044500796001d03a0741c010082070140346000300c00d1155078212201084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 840080557 1250 840079307 840079351
    0x12060e0106150e010306051011010614010c33052d01061b020603010b040f060f02060f04030507021002010614010c0b06090408070519031b05070e06031005090d0306050108 75
    0x43c031900c10b00f410300d80043c1150340c0300d00044c00d0303032403500c00c8001150402c10070301d441ca0401e0240c03002800e1000501032180303410400003041b0800d401400b030404010701e2003030210b09070042d04080381d8020b4040f0282100b10000900c1c4010501074800c90720020099946520a11806000070807a48501102d4001d0b80c0c0703409410b80d07001c103001c90700740b0080100340000c40040c4d5403c0050b6000e002c107503041c691a02e040c02c1040c104a58290055028000355200000d01d15038005100340d4001c2c0340c07255006403500e4929041e20103020701c40e40203600412140325041400d80c150700c801c0c111040f0301013039403c0281040040d0351260a61002502404810000610504200f480f85401500c90075500749400c070180c0303505080c1055080c135400070405e1001008181544008812380209110880400b44643c40c1d0f18290f0342e102922955015400c40c80000d0000e94080c00020140702e80c201d402c0c84149403010403261184034916880d00464940340b80070815504c03480310603102c0c1007045010a29294141 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 840081807 1250 840080557 840080567
    0xa03020f0105041823010e04060f09061a0406090608031206011e03090b0f24150703080a0e060f071202130611120a0507060f020c010612060e010615 65
    0x10000c0e05000303003044000b40c00e07000101c040603488242a0001342100441001c80d11080c610103900c1d01440c11880148507040e079010126801c1a0720400c0024170650b0901284082d040e0700001520040c43d16040b04051800000d5060207100201c40401000740c40b220110101c0388680650318480d032040c481503044039001d54485810580504080c00321119200c02c00f503008402c0c21188000071703203c0808404100600c54166040714044480f0b144610b03264450359110b005014074032080c0b4941c11404a03040d11280c5018030f20034034121449684940c2c07810060000d140940c0d046d0511854403680d01081e039408510726000c0c031a0368058050359200c40008980700c41035443c03103a0a06900b001188000e00030351050500038555601c80c562968124420241048152101001c0d00102000481e200c42da10208941d92240c0c17000000408081d0126038000a00035503040c0c00f442c0d0320700348001c46d001c001c40184a100520403d014040c2c800040d4242d401d1794414803452108600411188107424095 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 840083057 1250 840081807 840081829
    0x60c02060f07080705060f13030f0c0605011d1308031f09020a1106060a080c01200118021e090a0e0c10050a021009020a0306021e070821060a0302 64
    0x1089141003000300c800c5400320354002c1034202c42d160000103004042144c01e0207025031000c441080c10382540f03004205948032000041004040080f445c00100d04140184d00c501e20f983e80010301080103607115103078008a80118500420380c410408001034490025508804c19182c3c030840c41402e5449000480c940c1181340860a16401c1c01d491011510304281e02c05082024600d40d0b401180c00002840329080a1010303280c580903c1200d0014401c034040013071b049900780b1003845c0862228907900c1e50300010a100e400c61071055402c24241c036064009110201d20304500850742d4200c800d09242c80c0340c1e182081c3d035416580101a240000d08070764141d91113900400c06040941d04004445000900d2004c98400000d004c10000302e02c40d0200c40c1e04110701102241210390030001d03031301d0940010f1003580d02c9200041032141c002950300030915059220740041d00d0070719410b5440c3c80052420504d2600900c00e801600c8602071a40759610740650362090140002070f14000c046070558007840544007803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 840084307 1250 840083057 840083059
    0x120b0a151119081222020609030115151707021b0f090f0a110f0d020304050106050306040503040302101e0e0303040b0d05100909050d0c020d020d060c0201060f0609060c02 75
    0x42c000780d001c154411009032080c034510404038240e9440342601462078a24029025005000c102e9000008000d9040589401160100c42e4a40c4426100002034094080c01ca4034103290762032180300040b4080001c0034010450101c0d103c3e0001d2040003e1070403c410000c681a40042c0c0c05038582e981844500e0990304145c100c040d00020542c0006004200744007420b90b03050602504400401a07504074a10070002c916803021000391801201000700b4640d4041c010050303c4a540c00804a010040c1c2503201c0c100400002d02682e40030314007800e107030b07842e900540700a902425299100880c0d8500c80c000c14500d81100301000d50b0140100102281d480c0e06002c00190948401c000201c1c4003150100500000c13440d140020480b403901c8400142200400d5110a00090800c3e0030600003a074045070842030400c007440e082e1103020141c0000741980d004190043e4105030540d004400b8003a20780c11a5010354500d40003485000d41e581c110b1711f5410018031444002503080541403111134400e810b07103101140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 840085557 1250 840084307 840084313
    0xc0307170a1a07080109060506120c04030204050403050304050606092401210e1009110108040c0902032706010b030c0703141b120901170702011b120b0a1511 69
    0x1c066070b0342c052200100ca211031219020b000410040d1940320383d03150b001d400d103000309100003803416001c18010300401c0110228039410304005149040781009131401160001d000b88010304290034090001d500171341c1c0c10390341401204001490360070440b500f0f5000d60b4842d039941086500b4020240310400c5900c1005042250a203103030040b0b040a4aa0100300c1c1010100c006800009010401e20305100726102c2c4800d1030500c4030880124010902e0001094402c1c03d1030415070b138451421445042c0c440d0412a039852021080c0404640361120401d00c00c50200c29600c07e1030030039203890769100400d200715800d0342d0b42000050035007801140600001ca10030308142800d0004600388410b147c0040c0541500342000d5072141c0d801c3e0000304104640c1b00039611126242810040c0001c1c0080c00c2a0700081500800b00080383c8510700c01d40c002e034000d107041810110f43e2203101c0801003066080303140190540d410001689654a012454401100c503c042144c5400300d0400c1c040d070340c00c41c08104403203586c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 840086807 1250 840085557 840085573
    0x6110715030209040f06052110020307110f030d0b0f0907030b01050d1d15010b1614250515070f050a051606031404031209020a0512010b09090c030717 66
    0x512540200c120715010102d02050302030500c0180700b856048215809459161110348c42c114120104074103881200219001d41e503aa01c01000352480000685c050125109411045460b040c0100142503012705550f0184220162082000044034100c1c0c0c1da10ba102001c103021400c054029032282d420180b0605200c1d0904290648400c11036010001c201c66909504901da1b0b01c07000c0612104009035015546510340307504050b490841c034014041300c181e48100c107403100c000340300030303a1181510204090219030145804175000c4005050800004800000440e8041401e160000c4222540c0c1d54400e03134982040b4440e2161154115641e806540364040d0000100126006000030498094100a8450002c0c908803006049a00c1e0000c0c0030020100c0d9024000000c0e03000c1c4001d0103003c150200442c20111030700010384241c6c11940010b62007414400440481305041d0003e5150980072644000301d5510403410f55244e03484904a41d91540060350148034245580f014030900e0f20218081b50890 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 840088057 1250 840086807 840086809
    0x80a05071503060506030f1b040308190c051c02100203150a08010203010503030f1602100c03020c010c23010605030615010206010f0e0408030a02070f0606080f0d020303070e0301090c1e06110715030209 88
    0x2340d80940c2003512011000611010101541550f080381541c2628141c0c0181050b522501d07190541d110000d80400411450101424400c1041c601321060000d0110759900f031030010544100c0b54510028014480510002130171003061003624102c2d18058041c5240039000100c5540c03e901c044009045250402c8448000d6190340307441103071400312034031240f01140c11030802a1600041004240c1004041d10800300001c440801c400a011584903114000c403040b41e42d83c0703002d041c0e203401039905441040204102000d030441c8510b00c0d2102038007500c0f10f40c4d80f80c1a014a00350f9040c0140700500c01c15001060024003042c005550100d5594401420b021070355480303101c2c001840506030755154031000c0074080a04d0034402640c12001800040809181941d000381d22404020b107024180300180c0c9403000152070a40141601981c0509100c0e8041d441310041c3c0a0074525003010410b0030000040410483e0140f18141d5031601560000c01e402894003c15a6003c8414090002055001d1003a000c80d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 840089307 1250 840088057 840088111
    0xa0e010602010203010f0b09030d030e190516090b06031302010c08130306060e040b0723030a1d0a032a23010e34080a05071503060506030f 61
    0x1900c516030001d82d03254906003102c4e2000c41543c1108024000c08c100a05940c0c1d000522001003a20f282070104100c1e40ca41c0c1c09030309101521112a243c1108030010030100701010403640200d044c2480e1001c141e907244c54800040f58008002c1a40282041000c03c3c165036802c0c01c1c5402e41c42c414176040c502021159103100319034212003240102090309803010b00401805000c2d1201801ca581003500325840c3c2500c8643d03007902c002c0c0200f0140001440105040031900901d00c410908860070250b403814480a402e0061564840da040d0300310300382d40d409000e243e0214541d442c2680681d40c10701e1010904030398400c449112001c10303030700d40c140c0c0c1d1110700092900c044403100140c802c3d0302d00e0b1003020440c114038291126101c614070b0541120f0300796448900b210701405020b260744020008481a041c02e00c921341081a04034608910942c1110300070040f001881c0015a51103840c0c08003061191035013a1701b90380701c074012158001401d0000034621000034203120f0703105150401c05548815004140c581b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 840090557 1250 840089307 840089309
    0x308090a180f1103071b0203120a082502100507090510050a02073215030c0a090506030c07150b040c0e01080c030f0705160606090e0d030e0d0c020a0e01 67
    0x100a54441005500c0403102d4800d02c2d58041c00800c010340b031803520340300041031ba10f6420080700c0884c841607103800954070b00f00300b040b04010004006070364a0a100c030700580301c0002255000d5005134102004515000818642d81c91461250005c042c5000100359902c040c2c20020300d89401c01007106400509651000c2c541c8400008940f5400c1d55901000700082c18116950004800b50b03a032183ca0b00c688016000310500300c40901c4991030400002d410010b9418010107591040c450340c00310500001c048d4407401880c03a00140c2d00c1c7c04000b6655002403006900084440328158a000e010180109000325049083c07850441c1c40000d201c600d00001030202d400221070700f07001883d030505070700d02542c12107402a0005214000c1030f081d0b113003c90300c841d00d0020040000c0100400072980d1101182110b13070300c03101294400030a1180e0b6481c1c81b03001c00140b0a0840388000e80c42989407034110300b4060320030351044221000140c040780d140c040061b150301911001c103e80001d004440022221900b440241c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 840091807 1250 840090557 840090599
    0x1f020903150601030c08150d0c031a01051003050103120302162f03070b07030e01052b05070318020f06090909010501050909162705040c080607030c090308090a 70
    0x2090a2102c001000c840c402c0c0440c50900941c2000d109624400d88101c4c038104c0c2d0126840c10340e041d15450300441c5c06165900003050039100d0300d0170142c10b4950b044001e040c0c980682c2c2146071643c440c001141a603600b0b10028013041c140c01c8d11801c007180300b90002c01a060fa4030503030403070300746590360b0b451580eaaa0f148244d0103550120300c940c4184240741d400300e007160380c1203009083d043e0074000d295200c3d12500c28000c00384010f0110008a40e4001c00580d241300b48420722405400d81018079030702e456450003a00707000e80c610707080010302000d00910405942a0200b1084107180245900380034101060004c0c00ea48100c007842070b55080d40d56601d5040c4945180c1001082d29403601003404020680502040b0702504211301c00c2c10f070300c041c00303c61f8021907000380328400c0340500b000d01100d10300651200480c00c0608110400080c03100c41080e00d42140d032048111070031540e07040c0044040b111000441e1001944807501000440c0300f0ba070140040b46002040715030010398802c0d04010010202c00c41c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 840093057 1250 840091807 840091843
    0x1002010507021c0503010e04061b030f051b03040b0606220e010501090303120507050702040f0905061005150c01181a0c130b030a090b091e010c021f020903 68
    0x1075250303418481c850842810040e00c90503074194020180aa000501034056640c030044c000405000203a088040c6409440410b14043c1d50704020080c060030032100b0000f03410742001b000c541d0007540044017501040c0190140e0b03040d503c540da2502005a03001d0100b50b8001424058980304004400f0820102e4501100f669080c0303141c100750f8054110142c0c021418442140000c001098108005802000c1c0720080001c1558074920140c9160207124800f9401c036140110140c1610a15403260300004d000e9001c480c0240d6410302c1d8006a90003074040e068119842c01180e80c000010748015000200345c890003c1070100124440140b410b03422003003595044000740c10350790b8898401c8a030340e4201c1a00300d58140340100e44107810180c0800d61003421400707000000000d0240195900160381c2c0c642c071607048540e500300310044941e0b07910112480840302d4403090440748401814030444e1460052600070745168402c03801801d040c5c401e850251001031b9000c00201d4001e55051148654443e032010304 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 840094307 1250 840093057 840093061
    0x30303011217030f07050c010603051f0f1b0c0510050c030601080112020d0b0411030f0f0f0f0c01080618010608010611061b0f0d0608030403020319030c02010e060910020105 76
    0x7480c00364001200520320000c0081c41140f41c4550a0140c1c401d5407806d140d6036504ca10043c1d1801001503038809405030140700794450780201c1c5202c1c204e07076044c0e4440d4140200c800001c080c104540f40010552100d2407543d10030032003140503040703071101e040c040d5066581a202101c2a00c06403807086416403900d200004c1007000039070300465554050401d40000b2020900380d42e01081056840100140480f11400005410080300604a6200c05070180c00c3c0c454804440004981d00d086a10002c5464020b40d10702c812101d20015003510313081c08190041c0b0072803c4003401565103140c090000b580040c50216600904c1501c00d009500a0226644003080c0e50b150104c01030001c3c1e0148200d00d9190401c40503c000c0781c28446030003030040c1100d03485583c0c40c02c110245044611914400582c6035041920001e900003001c00908100d034000c0c0c1c15036045981e8000403042840e81074800401144410000c000954840d403240086414080d2a561500101600280180c0c41245640005039100c00c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 840095557 1250 840094307 840094313
    0x31050a0605071403010302131b020a0302010b010e0328210201060f15270e010e07180603020c120c010c17090a0209061305070519051603030f0b0303030112 68
    0x8151a0300c4041c41c40c1c030f030000d6211100380040b5488180b00180c41552101c0303202d0080c1d04240d010f484911070381070110500031591140070f512034210390b8041e8050752130205031070181d5000709070725138802000401a10310b101c0c0c120803041c10007a4100108082142c0c00c0440b4000816055000307003c50101e249409015214040082c20349802d03030040880c1044000d07080003203d002d00030038070002e4020b0600381d01c608211100d9510300510b10012001c0404d0713007500000d0071564540704605a5520b030182e09050303a950f000c10354150240210a491940c81000b040200d00d01c81c1e400350031002101c4c41954410480c4428003084c5400180340080180d5448824184064215055426850f00384c0c41c55074141c901804000d440301054400a409110341400051144e070324045910680c1c8615001085203041c00c0d200140710317801c80c002c42c0c0100178907040301202841c05002039501c503d465445a0302400003d640441c05481c0104d00006810380f00c804a50282c2c2d400e00145000e0603c04507008098500c0741 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 840096807 1250 840095557 840095561
    0x804060c020307110d0213180203010b12061f030f440a0309050105090d170402030a080912070b250503030112021504080102030f0106080f31050a06 65
    0x65610081d94030800c607900000d04440e01c030418208040f60f5880c5640301030b002013800710500510651403a0320f4075806410980c00c4c8030402445a0094000b003001e042c22070144820585550b104a4032a40400d000814004a00704064101403044501d4080d2070395903a03c40c420f6254071001219401c450620031300d98040b05190150010900e03200512608840002c02208a4030718495982c1021380001c208601c20b01a401ca0103405074840004c00c45481d0083d0f646444030007240300d0340001811f00342800e100082071400c6600454008000c0d000104040d0740e2000c0c0da030702c02c0074055081482c0b1808280b503510309100d0200200f00301c0440d5662400c000c500310708140d4258107400200300f0b603403030148003007280001600d0650700d2803202242000181c0c000078046220510410007241000200030500c0384064010314019400054114120b903203882042c0c40d200710071581c40c0709400c040800540700a1403545d240d9a400d03c41f140c80e141545d880b040380c0310004034000e4150344a0f0b004011401c2000300d98 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 840098057 1250 840096807 840096821
    0x4030507061404120e0303040f14010e24091c0b1b120a020a1814091302010203072411090306161e02120409050f090c06090616020d03080406 62
    0x2103a424003850103654901d400500007410404011786491849501c1c0c804000300c402516102a8a242d42d07540d640031142c82820b00c000403030005040b0a82d000943c24415003080c0d0b14001101070107411041310b41c0484240d081030b9001580302e00c240c0030f000c124024250b80810070300c0c0541d1509086141a1100419152a0440c040c004107010408880908000c100c03840d00400b1403807016a442c0541e107007c480031408040c0110500100380000110b4001d160929580c1d0314042d41c0f900001e950341180e413000a1000c003000380c0542c2041051100080c0c1c41141013001ca0158100c48559882d40c84820701110b03440c1450000c01c3c8000940110030345001c00a4587c046079036614003003040a044002030160f040f1040301e0011465984089480728000d00175600c020052842c401d4899907076080c6c1030041c2105483c282d45003040700c000304159040100c1c6011080b407020340040d19048400301884016408010030300003009400c041c90005039110004120301d03c1c00f0780e880880314100341c20240211205 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 840099307 1250 840098057 840098081
    0xf0906090a0b2a0315100e062208010f0f050403091e240e0108010e1b0f040e040c0f030c06050c0c0a09020a020f010b0a121401050403050706 62
    0x210821014000c005400c0340320a0b4890032074480342e101e143c403080c0c0444481039858000301c002102c1070804412500614031850568801034500115001886501c0815048402c001409a40e0f000c282d41848001094540321f02c2e440d440c0c0c1060481a42c08022845405c80042651030f00400c1c4005071944c0644c038604100084104903506040d036015000800d544034180490121649806000c0d0b5900d041c3c2c8000c007900da03080b2840780100300292000d0500f2030f8400c00403a00c40c4820b48000c0d44201911416542c2071403207103c0d60b489801519601c00d41c69412500404410490303a121115a0400f80000708101550354040742854940800313514001c7e003107620041c9003940d00700301113030212803400f08079011402d19580d90406201228104502c0c1c00c145a00202e10101c0020b0301b0045a00602e0320740a25401ea80011801e080a9401d82d0b03c800007580c0d0200b0b41c418188032800c072784407045031401d100741030249070248840e40090940d5411036040c0d0125a010401c0b4041c088240500c46004034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 840100557 1250 840099307 840099313
    0x4090602031527040201050c0a050607080106020a2303040f09060302090916051e100207080607020d1d031606050301030b010510080a0c0306080703151406060d0507030902060d050f09 80
    0x40040f50002c51011100c801d0b0802d9900c0f40214003564054400c85a0603507500b403d4030030400c7e150500598a02c0705945140010b111000006441880491140030580c2d0207068507660320010201c1e1048520b0f071141e2480140001c200010b5510ac010500200421100c040031410303903c0e41c010071444c500c0042c1207015942200701669421051022140705944003220000c0302d010200c0314408440c100f0034038168100c800301081076042500020414215606101100c0c0c00d0742d240a02240c94008a440e03000c041040d19408424009074194016013020000c1d0072141d032040030b041000722a1010703500440100350000010310907c103401303035814090103080c2c4400c1d0840c2d07044132000708503440082008903015a0f5007084018180310303402083c000c01c595000c0314201500c904044402004c0d00f0140030045141c0645400303000c003c0b140c42c620620000b000c0d0350410365581d01c00c0000d403c0c0188072008140c0c0d1044610b00503510640500703185c1c0c882c0e2200190701c0c0340c54003a903001c51901600c0718100e030b8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 840101807 1250 840100557 840100579
    0x9010c23060919020901120303090230190320031b0c0612010902090f03030c0f0601091401050607081306170703050408090f01030f0207050c180f070e060702040906020315 75
    0x601c41c02c042c6811102c07e070403003542c40c0301e0b9070404500410b00c109009600880042c40c034540c3d8010380308514244404103104802111480e4801d5660303400e5861008840e105843c80e81c0302080c080c40180341d56154100e125201c0d00d8580302210b081d03501c070385940c0301c03a10020711a81804c080104544200e00c1c000740c078524034006410300a002240350506c2004c1d000c40d00007a0b038450a8890708008080c0000282c2241d40307910100701b81070346560386840c105d42c552041400000b40d903001070142c01e040e00c0010300010320316402c1506000156000c035506582007502000f0780c0d0402c0c0001d058210050103582d81c0d50b40302c6c200705042c1550898014100c0d400301410242400003040c000740031100c1c80502100c030110440302040050300603240c9000d03209a50741c03006c5000000d1000210785404a40030481d040360f419900d04056a51403002a10b00d140241210000a1151401110348100508000302498280710a0303900040c1583c010316411a14a90003000340105606485800454440d00301c4000c4120 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 840103057 1250 840101807 840101809
    0x280302030c04052206290f0f0903280303050a021c0b0a030b010306270302120703031103090d1218110114070503031009090809010c2306091902 63
    0x58041c5010b45445180944c401011a400303105100064014074a024050540e03140710b26440c01d01142c50700c19600c0ca070003036000f6000749080120f0707540f0b01c41403a99a0404000140f0f03141d49800841940c0e07014810396103001102034241110703042c4449001c41d0007030200c6c1940340040950798041c100c04079107401031218604d0184024865510100c1c03c40c8d0008180d44158009015255903074000b07010503c8080020040c03260b01d801003002400c502d48501c0c5840000c00800916240c1020080d00507003080c111400020a54001448414020300e00401c018903000305a0b815640165107001e0580e03c500d4903802000e1b004404a682014a50402c0185e84015114855000107000008025041c80f540c601510307030003100041c1406841302072080d110105072400d0b6590b54004d94203a00c04810f084800954070401d4000d50403840e07400201107041c6402c1d04010b6807050f03a213280813908548102e03040701c203074848451400c0c5401c030144000c00d024100000171500b000111031049040c2d00c0803045074005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 840104307 1250 840103057 840103081
    0x60f14070c02011421010812030705121015020d02070e010f2c070c030e040b0a090e0c1512180706140d020d0902092a0f0d0228030203 59
    0x2000d0340a013030040c1180c01030418000b05104885403c03408042c1c0002c07046001401030035560584030040c0c1191100d80041751042c640e80001c0340c0c4080092010400c1c400c0030492103501540104100c8151400152071340e044441c0c41d00040c60910041c2e010202c030030070030f40e410041240103241c0440782c0d21030b650400c09103d4040c0410b024001c3e50300d80344a00000c1c0c0203420088415880c0d8050141da40a0422600003020565401021f400190040700e0a00340c6240610030620001401052040a01e1078807403190054800c110940c0c020380a4500601c0e410b44502d0310001c0c640044c006082d683d0506036106501d880c4c8090308103400441d8400300764220f000009006e4058a030030b4200a68040100c0903800b04603c107940303400c2585400072418441b0700c811600105c4060740308468943c2141c0c3c40c402240810b080210451003000c070720140c410070701741c030b0100280844480d0ba00600d14100c007240c0c19000360784c41042c40003590341b014410544601d018201846803490307a8602503145040c480d10f8001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 840105557 1250 840104307 840104327
    0x70306061404140f0121051501080d020d0f3b0a0e0105030a02010c02030f070b13051c0305030a140f060901060c080d0522060606080901060503071a09030a060f1407 72
    0xc06c1c00e41c6912412005d50307441d074251302d846a00004881c00100060034510b2a07240c2842004224405c00214501c49400400c124803801196680c5186000c1c2d00348041310890070b1161103603480d2075400d0071014450140c0c1c3c400101100401c0403548528003030f90038801c0c40d003010751040b800c035000840180b1681e500400d070000c02c5502440c00180079a1203000003800e042d0704020311741440c031a04100090291001015024039200f15071109402542c074401c2c03203174401c0d00300e203c03843d802060350411000a01800183da007000440c1c500055009000152b00ca40050583c2c0c1c6403200c1c0c60b03642c1040f80340d24080c62006e016054518103544112026551a1124081c1e400940c040d5615600001c4803040240ca080741358403001d000918400d901801c244004100d617005040002e00507000194240b41c05010718421154041c0c001e100b901d1030807242d0080c0c601542c500852020702004403449581d410480c0040b603901404001603088000078100b400c80715440301703156049040c0820400a00e03040000c1d05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 840106807 1250 840105557 840105569
    0x72c0a080a03171b04031505060d081227030c280f0524040c08030f040b1305030d08072601090504030309050102190908030f1605070306061404140f01 66
    0x12103181c031903180104034010813486080c0d41c2c2e54042000810b1001080d800c04a0160212003000542c0310351003405200b664100014061080401201a10440490001340d1000030801480105240900002041c4061604d504865800410704004140c4188040c1c0291008a644000e50020300556a566401d000e000a41080f8280a141081c810306120910074103090039034000303044402ca00ca251202400380d400366206002c0e0200800d13840000821643e070047c58104036418a0700e400c2503072045603c01c101c1da205500c12340c0c20001e400e407000c0200c030202e02000c0d1103500961400206c002d140741e646842c8009520301c03030100213180b8000c10b00d0560540300c10b400e012170b80b0791f15414140c000d4146001700030815032000840c1c16812061003506002001283d8a1000c4181d0398100350b5039034001c50707a003800148030401103082c201c4910400a0981c40c03140003620120365598070b484041741c070300c0e2b800014040300206031141d062800b4400e400300704511019440e0305062400003030041c0d8034140107103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 840107913 1106 840106807 840106847
    0x7060e010509070608060f01020c0a08070e13150903020a021807030605032815050106020c040b120c092a040801050726072c0a080a03 59
    0x81030413101c85035280b01403500c0d100c0c1000310f903001c400b50580c194400c00900002a480d6104078000600c1d503c0c0160004600d042007a00b0301d900e00030000807450055620f0700b40004c2e07030100302c910030110b00b4000040da0392440c07038280d14040800001a42c0705d84c0d80d00d0541c003a810042c0380c440c803451542c0e905011491b82c0d00245540d17040d44041c405102c0c941d44001a101c081c0e0362030459900c2d40514100d0210340c0b0010481022102c2c01c0e003210005030800840f5074010300702030080011251050300d01e1000300f0211465151140000e510192080244101060210b140070401c04130000310241d082125080f040d0241c2055441881450015400c05000036034650044540c0314040300051400405404900047c10b4014001820360060000c000e00740200c00d04949008558200d101303003200214a1b180040040c104910383c88050300f603120f8800d40300000e50207079803040a85202c01c04 = true := by decide +kernel

theorem cover : BRFrame.Cov 839928057 840107913 := by
  have h0 := BRFrame.cov_init 839928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 839928057 ≤ n) (h2 : n < 840107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
