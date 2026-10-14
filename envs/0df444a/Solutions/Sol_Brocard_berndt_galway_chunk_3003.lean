-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3003
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:22:26.469867+00:00
-- url     : https://prove2.me/submissions/02b09f2a-8065-4036-8c1c-6e7f7f2c72fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 539928057 ≤ n < 540107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 539929307 1250 539928057 539928071
    0x1332010506070f020409020111060a02030a0501240e01022e0605040b031b01020307060e0114092107020a0503030412140c0d030503150316180501060c021516060f 71
    0x4101c150700402000902c4400300c100103100508064001004061041c1040d042d00010101e4030740c10b011048640303100031035001c41040040f007258000c590060540c1c04e400011241491100015003281c0315240d820710803c660500d4040e4802c00100107001300c440e180241007801c200c910048112103d452680c0c550428074007040900e000e101e0704215001c0140101038480c045000f0000310300003849201d055010a006080c0400c0440c05960400f00582e8000170300d000c860780c4413041c000c4015180528680c4602145c401c1d0382a82c80040c003000c815082d2494944a140c80010098030040d00110342602010500090000d20f00600184e1288a01c030000304d01454107110507a10050140e8040d8024044044034000c42d002e10002d44d001491700d084004500016404a4a4180010000c0740c20703581c9588104241b000b1100c00c50003c005000d00be020039403400d00000e002c1d1802d9440a0f10540d0311103103064500c060b4104444030f0a10858240904a00908002c80140241c0e0896104a410030352 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 539930557 1250 539929307 539929309
    0x90c02150c070311010b06130503060f10090902030a1406090d050703020c060a1206060e1315150507150501031502071218030f120e0a1413320105 64
    0x10214800c540c2041e600303003014010b0320101c0d0b03d00000442500655a41d4440d50302544407880100400b500d01900c0b80d107072601d042c09051034258004e00d02c1c5d494060040a2019041440e0300c108210b0320610408205048240002810030300fa60100070174100a944584801d120080399107803103940d880c02540e4425007100d40c1612070748a031110082c016042451032940901d0310304043c1a2500e100d00d400b4002203000c4801c0d4085801582102002c40c11180001c0210310b4031260111101280c2003080c4a40142c1e81942006056580551a88132103a1010f040c8614864402d840c1045c0d0040c40c0007071441900090100281400c2c0001e0301c01c0c0f4154900c007003007120507008595040b90321854203541c1070300d440012200891400301b0780003240c83c080400400f20744540300c01c0e200d06024000c0c0040007a400f51002d0059040d00746a54001d4003c0d8400700300a103811400341c8040803054403100e0207114200b100c0001404118580c400a654481320701e10f800e8041c81c80f50000c03414241c25020b884e40c0701c1c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 539931807 1250 539930557 539930593
    0x9110f0d0b030f07270204051002060f130b0402060702180708060f040638120f010e0108030406030213030c030f060e16300b0f10031502130e01090c02 66
    0x401a24080c91740d64040d80a100034900c030107088201264001810151280700049046600c00c40c0200140e0020003848020010049600d8119244000d0001da4114075a14405050700c000c001034418080414030000755110005c440051000e820003402003072a04880c0034181d1942503c1f101d00801500380321501d2030400303100741801d40d481c0c814080d040307021a41c0d60321000d5904100c03111001e100350603494405088003001e0940c1011410003412940740c0303000d41c407030070a505078011482000140c0c01041414000310491b03050f52480e107005a43d41004a00308205401c1541c401050404808800001c0c040d000c1444852544580c5050007041c866042040d5a01600c1c412810142415202007290320b2400c0128100700c2d202c280c4c0d00c51900c0f10b0581c04800c3d116484029148500c224040200c249070607030500398020905960b03101035908549503285400305200e540240b150380010201101c40d9401528001091910141100c1303684072400070000d821410340c500090b01c42c458610780c003d1500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 539933057 1250 539931807 539931809
    0x1f120203070507140a080f09011407020603062806030507020105060117060d0c0b12090d0804081e130314010b03010605360403180801021309110f0d0b030f07 69
    0x1c0c0d41c4141c201007260b12104062905140071111610a000b1502e000420aa004c0d009525501c4044c51300c5d41541c0c0009410100c0c242c28424500c071080000700300580c6d0f01c40507290005c3d4251081d484840e0039040c294446080f580b0000d5100b0701c406400641107a05410482c4502690390007400350381c40c0c1e24019544101c040528610b22a405400034050b400c0140c0c1400368580a282c5580320956130740703500e00c45a4000891002c0301182041005641e101c01c00540c40c4696440c90204114901500c0d90780250144001c42e03050011095049100785c8050019280c50b0301a00f8411b10b03079103607645400c0861200114598806509000080200d4a0b062082d9021a007000d448411012912064001440c0002d03c002901c1c0c041205203d4400000b030003060301c218440d0301d440090412107a070481030040d190307100c010313180c1c01040110042c44001c01c14008035069004003241100360b51100a01134001d03140360720f66042021030302c4000307004285c01000d05550182c1c140c42c420301030042c401d5150046 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 539934307 1250 539933057 539933071
    0x2402090a0306180f1b0806150409020a09140a0501090204080c100306031a0708010b040803191101020715050a09050a080706112205010302090315040602091f120203 72
    0xa0010804a2502d8224545428403101042030700d1070380f5614051400c015000c1903503400d0b40c403107005170566285418500a0880300e4020030710361815032056800000e10a10b15401a611203821000f11349482c8101009410b40c000b050001c11030350101060380c0d076011038010100d141000c00020f1605c0d81e520844007541d078a440600070410001080c4814034000741d01100402d0354804000000c44c0e80740d01002056200009411141d04281000502c01c00c13040c0c020610000e800c010070840c0710000401c0711500c1c100c10621240c01c48882d0b03c103a6078150b078005410103950000a40408200f003ca42c00340d405d6080c044100060348690209030226245d1078002450303603111a050b840400d94180c0940b403a941300e00f4001c140d81c03489540120740c90b00320603216524003e4050380f0a12403100c1b00d54100180c4002e181c114100401000000ea44481500600c07281040010100703060082a804403200500b02a01040851809407501b5400030b000441a400160440c100c50303048030ba141c02228000d0740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 539935557 1250 539934307 539934319
    0x11030706020708120f090d021c0c03090b0408010213080d090512101e180209011a04050a0b13060207181a180a0e06090304030303020c19240209 63
    0x1040d5036004020b40c40301005840c800400d220b05251115a10410343c40313000c01060705d0040c2d041c15000585854951a8554250f40101000c00f0380c1e04205031504410709414500700c1d240000e1342c10b007640c502105800460724800005000b048a00e415001042140424111040c138140c2d51411b00d45c071031342950702c1d14002540c0c9020030001d51420202518410300680305807154080f0104200b81103840c100e4901c0c6451070707100100110a00c15104584005001010142d440800313030b4005005e1900501550003110340b00000c42941d119210152400380201500b800c441548800c0d02c00c1460304404141c050914400001250852020610808a4100c004080d90308000950303001c2c0a08031400802651000b0780381c0803c4903507201c41ca55240040c280750344144d281484a00d0405607610300b010000c0a5004800b80584650300200712011a0707003524005844001c0d294510382051003c20303003120020a10700c8800141f01c400a01d64800c0c7c040c0c1024106001d040d0011b56082e40070f0300142941c495 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 539936807 1250 539935557 539935567
    0x403050607030905070f060807090801020a210b0315040b070212030c0d0f05180706020c0906121c1805010c080a0807052a0105010506090d140a080d0510061103 70
    0x5400b80e040702d50442d10503019122a15250110b501c4245640ea10000000314040144024644c1054a074405849040001d500c1c2c5040400702816864520302e58807c1c092120040c8680c00300d15034000844031030020260389005c100d16025110784403041c5c130b003030310f42803844000f280b4034600000d080c001151200101505541d18139041401d00c1d004540e40d10003490715481400b08a407001d10809101c0e01601103040000070000820030318198080d0801000c1d58030071804021140c0d80c4643e0311742e109034111141164a01400452800c1c10589110607010780c04003460822120340040314905507400c060f25201ca0a50345a004440021110002030070340c440401c00780700c1d107902c1646010360002483c1403245c90700b440c50402e80360070803182d1311090070310002e8281000c4001082c003900780180b008903042c80c2030414200000f0360503d40e5000040815900c2400f0244242043c042c0d6010303c0d41215610b9199100300100030094141200e844001051410006c1212805100d101030303480d41000c0214242 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 539938057 1250 539936807 539936821
    0xb0a050405190c0321030b0105210a061d0415050c07060914191a040201080105060a0311073005042607080d080f040203150c0702031501050f01020304030506 69
    0x150342d00100039103020704043c1d004800310b1159660394403d0150700401000e400840c000c01401ca640001d14281042030401c40b04020442103c04140390195050b41c0454544814054138014543c035030102d41e845582c221000c50264080c0d000c075101d24040d07284031501c4500c640140b021103000b10740242d990700090001c0d0300401e4056200030611446800d020349444071207620185091303e00d05002c000411145072501c20028100c081c2c405002002c00c40000e0340c10700b9130005e401d0078814000c00c2d0003410301185400d0450300c01e410042d80070600002c003d60741c0455040102e82000c8a510184800c84400c08030181c0309120007aa514110160342c0d041d0405040c50401400da02d583c0f030342c006d11003401d01c0e0360040416042c400100241400d900419400400300000b0700440401803640440e04504410803016032004101006036010800c030b01882980c46400d503403010f0080d401b001e5058171404101844c619103018005041e200220307245ca070f141201100480c0d4a00c40c40c00001c0aa8204034041401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 539939307 1250 539938057 539938093
    0x140c0604030804030c0b1f0e130611040b070b0f133519030b10020c090717090a021e0a091802030a05010203150103060308030714190203070b0a050405 66
    0x40313031192500361102034003520f4103d004c100660b5a4510b28203a840c1c41840700d011850400c3c01000c0c1d840c5007450904d00b00014035440c0030400c83c0540855110b070740c0c00b07064448420032036000e018150601d03600d0f21a03900740329011800480300341202c130b450300001c03d0508030703040800c04140ba4090980e5440801c01c000c0e485604240c04074000940c4592003c0708468032104c0301801c401e8035242c1d11036101400b02e800003026120040700307070b600440605070f141f103400781d001c55020b580c0803083d6082c44c0302c0e44072048101c071020f91400280b440e154400083c0100c4020118000540c28000c8941c4c0040b1410510100718240b004040c007648016000b20801008070f45800a141d030f0f6020000013406100180c010904148412504a0b4aa5400020400349201c3c070042a0420802844d040002604680d900300d4248005009003080c412501411001110000b049440e0701d607088120040022445d503020b90387e50440300040307518076804d80c00a038100c8098803d40f84201c4e041002000401500034440b00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 539940557 1250 539939307 539939311
    0x607020a1a13090b1c0c0b0708090a0608010302032a09072d0c0b0a0f0e0601030b070504030c1e0b1903060b03090604020d08070b151309170d0228140c06040308 70
    0x42c2c81c44032684001f030f4660303202c0d02800840d4003810f0b540760f844c0a00303000c000c003401130741c1c2200c814401204010b10141c0c60018000f0302c15010040000e0358003040c004e104441c04000500d550f840800303c010804416800705003085008440e0b00c5d80703290004008802c4040a8030b110710440003e6030317086820003048480d032006400031901000014120900307400c800a0b03445001da10000d40e4440380041041203142d815569100b1214500242030606581d200444118984034003440002e60702c0100c00418116121807001300044210507682d50500701c842e45032400c030b140215011070324060300011318140349812071303100381041070207005280e03a507900b000400e02c092001514040414464440060a25000e050090a41d41704a10701c480f281005c10051000010170f06031250b003002030f05c1c00000e2a246110303103140300d00c4110640742c030400712100c402400b07148944400c2c160080301c0444110200482c01d03001140396a6590b0300540034204a106500c944a030f0345116034030910008020a100d81450740d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 539941807 1250 539940557 539940563
    0x20105180d0e010e10350a0504050c0a0603050a0b030a080a11150109050115110604060b0d0c030804080717030d050a09051501060210090b060607020a1a13090b1c 71
    0x20702c44e2118030120b42010f18005451380881d0f2401d02030b002c1100340281410000c002c410612607155009001c0000840000d03192606c041d88803000f1600304242804030400d104000b410b10000560f407540001d0141400740e0f007008503035141c04140303086401c0100328411030030b03040409d4625158003000d0440c0c900003d18150390050040320001c41e41e18250f5840c2c1c0d8020f2940d0300002c10b55504120100702485001e03c1c0ba40d0510071224103841141c0c0020540c1c540c40307a00000002004038183c40820200412604d0040501455100100070080380360040c0c0280e0303408004982c48140c8446200f4911824003a034400250300501002d619a000d942003d40d015800201c0400c1c0f01c42265600b81c50507600100a8101c043e00c1c10051000e60740c1080041604070700c0c0d50741842414182d49540d0301c01400035158070701403034002070100b0940d2940c0b40101c00070140140301506013620b00c1c401441e95000f00d0b80c0c10540f51240b91001071040c405020b407018488000309248521602e1318110a035103079000c4411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 539943057 1250 539941807 539941817
    0x130c1a19020c12010917030601081602030408150a0509060408070b0705070807030507110a120204051806041a100e0601030b03100203130c0503030a0917010207120906020105180d0e01 80
    0x2c610561550b203441c402d264407030400858610114501a5907801141801c203260800a00801105a90188040781c01801d03010b481c520010f0021022401c500c55a04003c82600c0307603c0c1355110000400c0301d81c0d445003207a00710801803900c4c0c012403d500c462060303d029040d08424840400412130b405c0015800080908140e46807480c580d452400d260404241507006c00c2c80410130b0f40900c0a00451040000c40854201440c1c5041083d40350350f4898071003029012b1540c031400600b0b0020300c205050781004c0140c0445080340b5003494821154803500c0010008042400042003000410143c00426602d9040401c0500d0741c4200044000f480d6041c070443d810b2082151092404400c0e200550103401c103020080408141d5060800c40200c40707031b111500035801000202c0d00694006070110541d141c1d50602c051111080c80300c0d42c0607004002000d17260307a4031400b4203005642c00c2200b403011110150000c2c00290b540f0b1203079406940e184591140242c000803030810303503507129070007808460f4014144 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 539944307 1250 539943057 539943073
    0xf0f080a1e02090a0f140127020f070602030105103b0d080405030d110c0103150305010e0c040f0506010e010e0103270512030106020c0f0d0605130c1a1902 68
    0x481d40d60059a240c4c41c0c0c0b503903413082042c0c441524050142074050079610b80405524103c0c400c01d0010a103114031084a0654140c6d0305146020303011942103001540e4601c3e02d400c3d0605081d8020f600030311a81c1d00c6841602e03a03100816000741081e408442ea002a0090301011994005071300700400541c0c4e480701051104204015070344e80386a44003031806418040d4943d810141814a000d00e92042401404040801107034030590008418400d41000e00e40807400c1d020201040042000c2c5420080c415404c0030440004650002010480700360202d405202003070040c50007100701d500c00d44101d0300090700900c02000c2c0b0350203040c01c1003e00c2018980002d00d50751601595024000c0125100140c04420b8041c006200c800c0143d5042c80d4504600145154174090001c2d5981c681c42e07100500501a94070340c4000c3c0d07902d100d840c1c80c00541003a010b0050b45451a442da991003810fa4080350300b82030944000c2200f1401c084000369060861807010f140000042c3d0301506c50480d016010111710500031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 539945557 1250 539944307 539944309
    0x6120207020d0f03030b0406081207060b06130806150105090303090904150c0810080111040e06190b1b012c0102042c15130903030605030d05040f0f080a1e02 69
    0x101400f100c0c0c0c040d6a0010303520300020204010f44207141d208004903805004a02c140d411040215007149270701c42800981c8100c842c1c0031444c3c5006103008640241401d01001495500115030144605c40709403005581c810312400548860142d0b844060b010b502c00e112080366030402e48101358000740110741c408080b00280c01001c0582d1040c0b5038403c0082e40f08000e201804481091043c0544184170003440380c8010004a00c407640918031401e030038160441c001c90645d80380e200c2142a91a00c0e05030f10307103145480d421600443e0707000d44454030380305151207103198640c1c03810301c200039240c154210040600501100c980748070718120b1782c80f8a4a95800c0000081071142001d043c804140c0c03076810104020204500501c0850380140001c59680501c100c031410f9a0302c03105443c1d40b02c4840540041c0000c09030904400418060b00006c3c0c15204420315080d402e0b411001400883d00542402d0800710303110410038841c0109071040905a038011502c050010b1190a41302440c5c00e1100040b14075100700760 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 539946807 1250 539945557 539945573
    0x72402030903040311090c16080c030d020a0e01110304091508030705010504170c0705060c0a050d09080d1b080304020303161b1202030a03050a030f110a0e090106120207020d 76
    0x20701c82104980c80010f0810800582c8940441616400c490100980c43d011810b403449210b180141d00300149103000c03180030808000141c0c1d800b9407140003140d8480c0d00b2004031a00942c015890304c0081050198196501c1d845091860703102d02d01c0e04061800c19140c0030301840500784104054007181610b20000c02d00b02d900708040c0030300b103015034000305090400e41010600002c044050701c2c00090104800e18401900080020440d601070b640035030f89000000c0f0080c20506001002800d43c00b800598010403584441311509403421842598010380c4580b8094444040450003200940401041c40c00414000d130f010315030050000c0c040c1c1745400301101d15503142c0070903403204840016004681c02011811412008090180351407056410a52600066a03031030301d0b22002003c111002988101191007900424000d4036040c00501142c903c000c41055950001055500010800c105540301460b0481e081d41c101c0754680c40321282c0b51540c100c2e10b006907100d410166000025041942d00040d152 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 539948057 1250 539946807 539946811
    0x30d060b0726270a060801030f08070f082d0c10050a0e060c03040606050a0803030a0c02100c1709010204230303091c12030219110109020a060c0506070201090807240203 74
    0x90603c143c0c41d5601104001c4001d41e42c0e00414100800b81005000040004070400c515a4001c0703101c0340c4480c032034503007030000142c400401400010089248225034403c611500c80c80b164000c81454200d00300220414940650b01003a44144d0140320641c100040c1d0390300a640010184001003941c50301840b00701c0c5010310550b1028a250b0000041009010301d0340b040e04082c00c0112613031034165290450701a43c2c5c0c000a801c5640309039403a607001400e02e00801107040301d41100c00d014080b0f0392207440041c0211981c001d0018001c2049400140c04420602c2103c00fa00c0440c1d1800031094540f4121180c41200c01840d41e0305840200100303490781d0f4030f91541d042d003c801c030300b40c0707a40c20402c500e0610449012002e1140034940140814001c600002030601c045405c18907042080c076500d140e56034050310303c4000281d040301906001107035143d0b00c054480034403401442140e100f41c40c0d4080484c200c58500348083c10f803c2c014030501c40000c00e0600c2410b0380840030300030840321503a10701e0580708036841 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 539949307 1250 539948057 539948107
    0xc0910031a0613090b15040312030608121e0703020d05130e100302030f07050907210507050c1603020105030105090703020c121b0606090c0f0f0c030d060b0726 70
    0x90342c20070440500103000e0316031900401d88850706840d5011400046c50f01450000030070b4220034405019a2a1081d44001e0040c05164200e6007820081040d603451644106d420340619092010b4402050300d01c0381c1103d0b07866500d6402001c4c8960070210803200c5800c101001810f910b1000d42c0040d1055110404a000d82c17030702c980300307002d60b85588105860905540d089030301641004608100d05d507110418503901651034184950403844032004a90300c07501001071030308002c1c40c05050021180e40075010b480c10904000c21142a00d00d03403081c41140501c284002800100c2c01c00041c0303d1410710381c206542000c040d081c00750514209e4001a0b081ca11090412500d0f100c010483c0301111064160600c6100d003680060304d028240300c000301d88411401000c0484050000039034454414a24088170040740d02c40100c240c0321211044e9003a12603003d001d1328102035003405804250000c0981c200c400081c0d0040440510714280742c003028150b5601010503440340d401340102c0a00640680c824102c5103c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 539950557 1250 539949307 539949337
    0x90b06160311100c02011b02060f18011404050607080c040e0105011b060504050c090a0c02030d0b0d05030a030501080601091404030e04060b040e10090903170411120609060c0910031a06 81
    0x95420a01001f004058a1045601c040244191051054110303900b08031208100c44241034a160b406024010760141c0c000023804090820080c400081005401144103985586040c1c40d85400310b5a64041c5020b80d81070b80183d0b40040109600070011040e8065400942e4502041251941002c071a070840d02130340d203500132070900c5105280580849520803640380e82000340240ca400000e41d24054000e40c0c030009a501e80140c1455662240001303041c0b036020080740d0b6100c5c041c0c840240540003e03c10031071340d0b100780303000400c0d000d0881c0a04074040c0303803642882d11165102c2c0c908660705a00341a2640e0440d95031400030400e00643c000900280c07030103110100b0142001c00502040c5241d90340032514891402c102803001a51004600d8240620000295015148e80c205441c8080003203581551000440882d107110b4000401c145e0b204207001c006440c90303680c0d0262102e090344500000d40c0e0348a1140c94038681158020390210300f88a02d10100c00c01c50700f842e80c02142060f4844c43c1c0d0310680a07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 539951807 1250 539950557 539950571
    0xd0b0a0e04060c03060f0509091c0f11010c0c110d0b0a0b030c040c080105061c060306060312030b130f231602030a02120306010324090b06160311100c0201 68
    0x20407036004403e0002c00c1c1d407134100512490140401403841e40c0b4016244a0b050810100c2c808074400c003e084e0419260500e00141d015074110082c00c003200d5001c41101141105500141c05a01841168681051030b220600320305044d94900c1d5200740d1040d0301d80d900400c19000400400c42508625104020741381e80051341a82c0c030820035107003103440244203100303070704203048560341aa1104909044a0041e2515071311240e000c650010a5850040f4209135103241040001c1885a55000b920071280280380168070444581821400d030f4110248807170b0030038100020f00a004940d64402c041e44146110001400c480300d904176110702c80501da0441e603110b03959081c48004000404820ac1d5210035000841c074082010304d0294460103200c10324000240f02200160140c3d0180c0c00c0403c00c1c500094000c5428110700c402c2d601801315a00480904034503041801c411030030172004880407401c090000d8251064030b0340e02160f12005840360b160b0075010b201030b040949140740c040c0e106004450b800200d028 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 539953057 1250 539951807 539951813
    0x601030507051504030f030c0206160b0a05011d1602030c010617010605030a0b0402040c2109031b0809040911190312030207020108060f01051c0203180a0c0b0d0b0a0e04 74
    0xf01c07141c091030b003054010041040040c031041d4800541c56490b00702046a8640307800003400d01d02411200c0e9207156101ea40000402c4120022076100d118803560821803a600c2d0980c440244004140900b82c1c007420070301003241c6980090000d141c103002c51040320310305128107060b0303804c1d1101544104a0b0180c16140c5ca4240542802048046e0405400814003032030b41c2d07201c80300c6030b51000d00042e00440c0c0c0d40c0c00304580544611903a014109400310280790700c54000c04070740020151008182c0024961606c16144102c1005d03008500c48c4d009802a800c0445907400c1100801c04014212284c00b902d903500140c40c0c0719480008910083c034040399000c41e142d41000317002d2a1030b062242c42014410442040180e0300000315581011007aa00e400260881500580d05440391402075104003d92050410302980d0380c3c3c00840c40742984603266007600420b551202e6480510800c01028110550005d00008101c2e20140c40c00700c0800f0408103c841c801c2e008070368002c980340c102130711a0b520f0358100014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 539954307 1250 539953057 539953069
    0x220209040b100807050f0f0a0206090f0106060c30110f0304050a09021303060f201222021f080f040803070e130c0c1e03120b060c060103050705 63
    0x7100141d801d441d1144290034001d040b8000100104d0502002240340c8244201c0c00080c0c40c03599100c50200b0fa41c440c141040a55510f40498100003c0e11805082441310303101806688101e0311691103000141015a0f42c14405145202c1c4400c0000610585090000003c109411010042d41c49038850b50002818040c18008001d030000000d500c108010441521018003650032101c030b041d8010789a00e442246121045240c2c0c3c03025042c14148440c2501c0750b406c80d40000110041440460402c0c41503003501c91081c041c480402d8503204468000600c006101a4146c854038040464071068564543c0055001030004e04004500c0210402c010401c07a040002c0a401408030b2007802c040d80f42c84d07030b80c3e1200e0344402030082d400c100310802d113000b42c4e032034000e11200d07003000c0b80d142070141c8041c400000340030144003030041d281d08400d494443c15406500d09240e240307076019921800540703000481e24010b00325402545030011010000000001d80c10b006240c0607611401c003070403030945070504001c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 539955557 1250 539954307 539954321
    0x2010207172706070f0602070f080301081009080a2a05060a0f020304021e01140c0a121403041209080303070f02070f05061204080403300e0d1122020904 67
    0x15140d03160b80c25650385200c1603400d5140c4c01180040082c00c6461300d10003030300034980300038000c240061200d810002031201840c16941d07088115503081d94050000710a90301d45003c00b401c001e400300031200500d0710400103040d445000c0c000d26000420300342030b901d07010291203805603040d401000502c210041a40516030307080740d4662042d82136050a40000e04824480030209030101c0400780e1000700b69000d103040c1990704034114246a2129698240152500307074180c81154110301d09004140b0240c012000d00307042e00a41381d0007e0841d9602d80d150200303080500f07809801d003c105600040d07058020401180715017501d80d5100c5a0042426000c0d02e0240d96030000e840030420b003401444103803180c0040d40d8038100507881848a07a1510304150b80030344950781020f8100c441c80c2c0300d90010100001a070220401c08004440415005008100c6160071461491540140c180f2022800b20351119400e0507210790080446148180c0600c0040803410f41c04c5c41d0340041038010800861615003407181070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 539956807 1250 539955557 539955607
    0x70203150906070c020102101a0d05010207060c1809020307020c1203130e130308150301020a050a0e010302180907021501120308063007030b0109022703060601030c0201020717 77
    0x801d8584e50b580003039241c00c0c244000d0f00742035964050501d100303e003401443c00d280340082e200e000c100c1014203046020b584a0401a1307415420440e51441c0305224102d9000140180291580001c0c00c1002c2c1c4000b9500c0a0150700442c411154204c10940c4c80a480c11a030390000e078010759a404003891407641c99401544140c429080440030407442ca41420b00700c00c01d559040c82c2070a40340c1d03a5003515002c91200848140d07003542c80460242400c54100000b8041d50406443d00d400015900e0011026445600090300b1411106c011010840c00c0000145401c051a8019181d544e0103411b18482064004d0b80000002440e0340a07281c01d16810040131130300900c0031b0710901414204901054808a000c1075000e55200e00300da4181d102d500c0c207004a8010f1a400110060b403540d440401d100690400c3d56212a040d82940a8441a01a880d08105940b90140241c1202d9903040c0040d0024001112200c003955000c01100e000641c80c12880c0300030b1003204600b15101d40040c1e807200c043c1801000d4403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 539958057 1250 539956807 539956817
    0x71e0203150c0f07061104090c14030907090c020a17030a0612020a14030f030a03140105040b090105060a051201030f050d180e040f05031c0c02030a08060402090607020315090607 78
    0x444041140b00d022158491a0141825903c0c0c501e4a0300000402e1068200500c00030040fa020420740c840e5004620000e6440c1e4402041042160040c01c4910003650260f481d070340322907020050080ca031b41200040c4138003070064450303000d0310b030301c03000c909041c210b107040308400001040040c00480b9101c0c02002d0003902c080c10b000807040b503000c02d44103641e07406150304c10346900e44525081d035020004120341e0030b02107007500d80b601f01c80321014002d404442c80030100c48507450004941c60a02d0b00c540d0001c5407000b041d00016920300300600100b40e0040080004004040105102c184081d0000500852261403601403444a6003015818000d0042417101003080b910820181e4015000e0350509a41c40f01185c25007a880c1c602e81041078150309030300100540000b042481c4000104144018007503090441400400c41031441282c8130f00c1040daa441c04500c58001040071070904e5809088040d0014024516020306074000902d46094204542031030785802e000c10030100003c0c050103801491034204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 539959307 1250 539958057 539958061
    0x40c0602012004210f052416030b040b0415091413060e011e0518120f1b0109050307060e060c0334020a020301060b0a020d0c0602071e020315 62
    0x2c00240c0d104074410750600084148000d02e8040c4103c031070040e46684601e06032280055450000e840d0700c1021042140798241c03004025032143d03517900542c401ca03a00c82501c40510402d4006400400303058443c543c010b50b41e81403011064545205000d040c085c03584c0d1030624540b4045000040c2d030700c4d2003101100c41045106100300c07054503a40445505612640202e8280d00c1c80480500404204081c225005840560850500400e0b032102c0e02074502031003c0301540c03102c030b542940e1b540781c450042a0134500411081403c0b01548024040d04200d00840c000c010014051580c259a00543c00340d440ba000094044200303c958810010400d03422005403281d407401034940c218a00000309144520b0242c2c0045a410051100403000d24221600c907400b01c1d182101c100942d904100303c3c0c128025841c00c54013089218484094901c0c61040794014090b2011003041141c14880c0400112641c0c1d0b02801042e0024603135146c410540c604503140d820070010980109031416144040c1c1542948104003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 539960557 1250 539959307 539959361
    0x10f0b06070b04060b090406091a09031b0c040905010615020c01020d2d030501061b0215131d041a160518041a0306160507030311090405040c060201 65
    0x205840c03001d60001484815580e80d8141400600002c2510035401040442000304000c0300750300074913050b0700400c115600c010700744100c3c3e4a10071095500c3c0c8a56401802078051700c01100541c203101032803c0003900e0314181c2403000300b03050718515281143d141e5101c0e9420b0082c2028a07007500c254100320302c001c0180340c046000203520794032111090000c0060000c1502c2d119600960100a10f034a200d14201004070450b4000340100800c2c000c42c80003035089000034888401402400c035509400074401c805031101001030b00781039800308252a1900100349000118004540c2c0600000c22012182c07041602d440d01d001c01407902c02d0684450707c8003d81040c0429258100e18110040301c4a00f4550f640305082c1d60055601c6a000348000e9200c0c0c101848080c0c021012020700d8450b520560482d000368994041c044070361142d03a900c2c880014024848840482c0c809d07045440302403202000c0a00d0006200c01050a0310411a000e403080000c401c1d08210f85175091144901c84044003180e501e4a0040007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 539961807 1250 539960557 539960569
    0x1203011403031c15030203030714010b0103020403080d020306010c1a01031b26011104231503041205040302040c05030f011e17151003050d09060f080403020705031e010f0b 75
    0x4501401e1166032003001c80c0c104c0c3c01e4141c520001c0c5070003c0480740c03151603c0c9041e40031710906002480c80703542006020011b9500038000d46013900d5010024904124051ba0020020b40000708030b64100302da403000c2c1a012590700102c0144041c8028042c040b1581941080d0006100c41102e11940c986214401c101c20800801c00e07010444d494455401d0a900b40c140741409450200d0300610302d068006000100008058021400701310b041280e0020b50460300e08004841010350f000b22600c440c00c1001600180b9001042c05522140d030504a00340358490b000320f000ca504414403080492000003d011030f66a0a044540c0100080c6188006100740b842c0d0800c20f83d8654420303061805c90082c1602c0d441c0d00305001445030f02c1707005014201da41c170f021000b82c003655071548010384441c018611940003841c4a40300c441c00340c46450b01c50890400b100b01c012600844001d0047e41103018901011901e0b9605115021140c0e00c1021b40041e4020f0b1400e81c10700f1980071030003440782d0b0f92a04c0c030260410b880304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 539963057 1250 539961807 539961847
    0xc03090105090d050d0b0d0210020c0f100f0807050412080a020c030f12070606080d18240518030a060509190c1205150c0706060501210c11120301140303 67
    0x280030003040e068082c80100d42c0da407c0e0480001d510105940082440541c00031311404e001d0400c698070b52000c0c0000080c08058012204124001055041c0d00c2014900900b041500500c2e640340580c502907448106080c502401282154503c81c001080049a54100503071803000404a0280c6002c0d0003181d150740e2345208030340301540620404900b450901450358031120080c445c490540c0c01a40544000500c03c41c048400c07000003008458012882c107042c070190b030b01c140384903000d484d07400145901c6c00c3d9002d81260300c00b0904554a4034018080e41c4040c000d58546520031500403c0504060700744e5403c10300302c0d410310542c1403007503000c5201060b030304443c400884031203049150440301e0500303086083c4010008010180241e5034244014890120024045d0780d014050070050503880d20f004540041001c84c0480350054690030b00094a4480e51105a101c041ea003045551303e03c008032840d04014022240d449036080100042001d42070005100703450301ca040f0095490f140d81c0d840040100489 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 539964307 1250 539963057 539963077
    0x18020f010e0a061d13060608070c1e11060d1a040c0203090909010b0901080a0b010611060712150605030604050a11070303150302180a0f0c140708120c03090105090d05 73
    0x1204c110014001c0c400c110306142510107808400c074000c5045d2040e010300321621510002034520b50015005c2c500c43d40607002940c2c1d004040200d001d5480c0d023180f90b41d01c84900240d4010050f038001c140240d848800410420400c40350118001140391340100071408599139040c007450609116040e09503011085900c4c0504c201c512075210346890740c8103401807004d542d1881c0c114440c10001f1405110028200028500c034211502660384c940b1803c560399030100c5411412170340050080750500d4000e0030614481301380390000040e40000c1e1100c400c20a04d17958130440c0481c6001080c0b0102c0c3c02d05004081d44035900304001d001c50380a03483c5170001c501c140030b401740807d81e541e0760603002a41d1192400000b96001800c0103150a640d43c1070011518050f946041c1c010724008079200160f52500610303580601d5503c440801481e202001000c0d03078050241210b54034010006016100c2c00f1120040c010b4000705c14860b101e24000d0802c5084400103172600c1c50381d5100c0f640c50100c0641c40b404842d51818 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 539965557 1250 539964307 539964317
    0x150504021e1b0105010b0c0f2805010e010c0905131b080c0706050c0d05090c0306010b0d061a0a1404051c02040209130c0f08060d080f0d18020f010e0a06 67
    0x184072400d80310080d10142c1c11510550900c0300001d05070001c0c0010f02884c1c40e0310425102d510404140c503a55942082d801e81c000c1490280020703007081000d50840e83c40798001c000228000600c0800c1c1ca08440c5501a41c00200e03000c110107018504180030b144241d00b0120b04100044845e0b55180890070908550110400c034626001801081d101d1041d034408039400803050005080004910046821680b14406054585000158000c0300081d80100720070002e0081e011030b07401c0408181880d44050000c05800d0f4841d03a0015a8000701091ba90508d01c80170440c54482c00c000b54007c000c0c28000041c079004030401d00040c0213070f40c0d0380e9461030380c282c0481c6075038600014284041400f80c068401640c0d480a40703000324040c0550315030001e240c407680350307902c03c2010200c2c1c540994072070740107841d42600232144030b02110006081a0040c0344d81d0b410003101500f03101c17030110143d007620020b1240800c140d4011925a0460401448181f50b40c3e01c02d09000308a0849100480c54401a501c59141002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 539966807 1250 539965557 539965567
    0x3200612010905040f0c08070e09061003030509030705090c031f0807060f090b1321030c060c090e0108030d06050940050f0d0309050703121809150504021e 68
    0x1104000008035070715030100c4003c000381e95490b821034890005120711341100c0c0780100040c0c3c40d210040bd001d407040805000c0c2c442300c0c500f1518100c415410a1f2003c03500361280300700c08180e07503403021030003441035186000384d41d80c0c0e02d07100710120702104038003421440080100c1d500703100c1c1c03a034003085c0ba0f000c0c1e07076880c9080304000000d03000480d0500030039031204030400000260200c8800144c10000141c2e560079a01a41c09004134501c404569604400900020924124100013980580141c41c207880d4500d8451303099030b02c426018031040003e0340b02c2c90143d400040c0c80740000d200d0713002d0b5030014042141c00b96001d20b04402d0b4540d42099407000c18152071407440c00300303e40e070003030042c10045410302c521581642d012910384680d9452100310420840d20039041d05501192007802080010355202000d0306100e403559585c00041d04800d4141d506120034508001c10f01c51030244580000c0000000101c5c21301420049050040805d8101070b00860041010000902110040c0104441c051038265554 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 539968057 1250 539966807 539966813
    0x905030c010e0609061602010920010e03060615130b030f0a06050117040605070210150e0a051e090c10030f0b03060403140a0e030307030206010e01230f010e0a0320061201090504 78
    0x41c608104024078108a44203607102c80d010758008400c0170107081c0c07180d203400c0d09420201561682d089907015031240c1440d2010510b04c42100247040e4001d42c4101c0c071412103031141000004c1d90812101107081025440801007641c0312070081d500141070a08014444401030b05440072040c10040c0302500450700e68000c181001c0c42003004840c525000791080201c1400c901602580c03151a2113000c1440305e510f404281c441c51103228541c010400520b103000c211081040c03000d900321000b0700070f080c40c0c001c100f0b501c00d071a1036114042000c2d010070b030f60000d44280030a284100700d45e0300b007203c0c45c003940c811420000025041400c014a03c1131041100d6100d01650b8402c98402140f40c4940d600340c00042112000c1680014919068820600f21044a6a00e54072500250310b80e100c52451100109034044100341400340d2000070256062400d0340c01c081c0c400b0003003034a00c0c0c050751045401817680d080f00c410b00709075621510051601200c1c00391070480040c0c01d00500203c10f001d0b044825541d1004a010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 539969307 1250 539968057 539968061
    0x100f05030712150c0206100602011103041e08070c170606010e01120905070803040e010824101d04020a06020c01050d150509010905090601060e060d050c0d0905030c010e060906160201 80
    0x5484032000c05100e0300c01302d0003009460791810f6400b06005040d90401182e9a030042c0104043d034a10589107030f0a544c0c85071a41100c940500c0009a00c608420420001040143d030003810314502a2002d0b02d4028500442d0364188068401344081036086201440110385e44817980040d0300d2000d2a00070f040f190701450400043c030380b0a000401c07910400c400000c480d0b00110140c0b049070810300418056a0382c45c1811071b11240b5240ca1f51004100c031202460000008a0b40035810020710749900717145170789a0484001c00c8000c2c00b400c00307144003104100802c524000b0700c000c005d081c1e14800b500450a10500180850083d41c2100d101d05480d0707010b0640304100600940001c000050004919581d60400a002410180c903801d405004220020620900607040d8011060000d048a07140403a4400e00c08010f100107000407100d0002004080034090b403074002c100b0358034020405190b8454200302c10350700f12040003a5504940d00b12404001800310b001c6142c59000985510315038011011b2038040b40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 539970557 1250 539969307 539969333
    0x501020405040608010f0c02070b0313051507110c040b0f0d2a03032601150c080c0d082202060d090b040609052104150905090f100f05030712 62
    0x10b0010700d01200042c190005400c6140c02c6030350050300300b1905442a034102c2c1c1740d010b00e0062083d00402003003c80c400c07910b181100c0c0c0030280036900b40d8080b101d0403008004810300035076505001a20426990352603034028018400c44420444007040644150310105241c80c0001e41c415100303040c4c00c2c062401f8042c207103d50301d41e4129031441c1c500402130340301c4058614461074082a03001075826824402c00c0820928010142c8a84400c040416840c20190041414240c3c140004119810a01070001256140644080c03c41a8040c00780890142d82c01440c110300241000031492800c8030182d104c0d050780419030410782d0141c40c92655510381100020140599140040c1509652002c020911140f42c1c84400418403c10030349140b12000c0804101407a2440d088524082042004219102c0c0540900c1c2c40e55006080c1031003941d03507030000156042c2084540d0805c0180a008100140e2240d008403400303080240a050902c80c20b15011998408060050f14070654507085d00e030050005120201c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 539971807 1250 539970557 539970559
    0x102040503061f0602070302060f070204090507091a0a2d120f03120e0d1b05010906020306040e03070503120a020c011a01031b1d011103030c13140d0605040501020405 73
    0x40e0700c600f0200381c0c0c2861201801c2030000300802e010008030b035443c40841c16108490700148514105040c1c50f0130400310340e0142a040f07030700a40d9450103600180c000d02010000b442d07068400603841c81c1c0b401200c1a20208205c00b9031003040c091300d0a100c001006c0d4007400481081c2d00d400c40000c030340c0c50701000c40b046035174210010b072000158101040183e407109000100380b00c0c1c0d8418010158001c1e152040d42c0d080b100f220701e00d070040030030101091b21841350580901c1a0503400c0d15920381c5500c8150071036200120558000d900002002003d04290081e43d49448a1000030751412a440e10345985034091040c0c0d030310a5420280c04903003442e030356070180d40444c1ca00c9002080003000c105c640c210140d407000c01c024040b03800c1180000321031804a80c3e00c0a88070094a80382d929954016250707e4141c040f0f9131050510036403845c401c01d60001080a584030340d250000440c1d03030751101c08068000381000e40c0407501a507a00d18121100b510f50380c4041d50850351240d030114054035945040360290107540c004d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 539973057 1250 539971807 539971813
    0x60b040b0d110f450a1506030501050603060d260702030d0e130b010306180f06050108150108040836091509060406030206031911130314150c120a0c08070c050102040503 74
    0x201010081e46d40c02561000c99107403c1d407828650740c5400303a003521000d21450313900607402e00005509091030518031800910801e040c4009181d19843d03080030642e02c7d1380c407021101011449000f181070401c40b0206481040c02c00d880d10781c00d44400101c0d10b40401c0c90f41d8400c151102074400312640280c0000c0040d08401c2c0c00c0c50701403441100c2010083c02e0b4000301007070681c14480300180e194000c9402c24020581c000f8820f11805c1c01c40e0041d82d0503c005030048410319020001c5010582d10400100018140c2a00c1032120b81000d01d50701983e490181c01d001c1c49011104140b2030701e19007103071180140c104140d4101c01030350765007c00100100501d44c03000e134002c0030000c100410205c0c005040300d244400020200034080c1c4500360316010703000b000ea044052800e105014408150300304c02c1200b100c0d10b50000c880508800c440d0000030400705441d0600c401c07002103085107800109842047d80810340180821880042110003444a840a0035203024080012420010f01900f03404660140c41c000d022 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 539974307 1250 539973057 539973061
    0x110f03030a090b06091611100e03121f03320d03150305060c03040c0312090e0603030901020a0803060d0606080d1704050604060b040b0d110f45 63
    0x785000b400103500304a0b007201c1c40c140003c5280c80c0c04200d150182d0680780f8200070746d102d451015200da203c648200c180620a42d100110003440798000c1c26200c94201002d1903c3e0107450b40f039501d20200c045c042d101c000ca620070a4500d40003101c601842141e030000c150a0310444044002e8140d100030091581c0380341e400310410240c40720001440550002ca070341e000c202c00ca0740303c0303820b012414103400010f1203034124402007030071112203002842d0080d0042c0101056642e8a83d5500085901d01c92614041441e4401c10411101099851380e80008240c0184d464050002c000070b4440c20b080300c0060044401002241d030301d44400b070200c0c020039031201003000000c2d240ca00c1e0556038410200340200181a13522003801090400c05030a014036070000041000d03888980d10715001d440c002d0101d507000b40d9a050b10400030b0b85c4040f60005c402d40900600440961a04207120403081e4058100b07005220795030b07000c2e242c4900e8070840c41d20b1000320b4100d500101e0240030260485049110403c08090000c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 539975557 1250 539974307 539974321
    0xc081603090b0a0807110703050615041d013218031903060806090708030f160213050f0a051302040e03041d0703141003060b03010f0c091a0910110f0303 67
    0x13010303000700443e0720b8200f500c41e54101426a554404d000c0148150041004110060701308801d00000e0380000340b022031141540360710510701e42c810b00c00c040650303910303100941c00307800011090240c00d1400d51820a00c0d052040070360300032541c0c06011403d088406088030810701406201303036191400300c0088040309450559004000d458a4050314001c1e00900f004142c0e0401c001030b03c40c0c110780c101c03402780d410701945c0140c80245401c00c0f045555004500609034006079580700d9100e20b010010040007840b420300b191a10b090440043c00f210701281b9040c24000503c4000e40f28404540d412580421468810707617101e400d5005603030241c0c640c450300305d02d040403e41401c840584213098581d01046950714035500e104104000380c0341c3c21040240c10704140007081c99070f0007036285494082c0011802038100220207044449420440303000410440041c03014100c25008030310b40070008800903080811030000100d01c01d428555080c00c1c00110460f80180c601c0a0001116516420050301d40b6494406 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 539976807 1250 539975557 539975567
    0x9010c02090a1e0b1008100302030a14010e07030c120213050705030601080a090b06090a021b070611030c03090d1a0106120605120604060c020115030f030f0c081603090b0a 75
    0x281e40c0000650f20b2820004484082d842103900103140100408600c5090031000c1d07460b02000382031f513140300c851240c01201688007041a100241d01c58034850041c12400d08003107003181e201503a0b00c0703840e400540d02013000c2141c2103450425210001055840500c6a100103201d0096004003001018204020081020341202c0594440c0800f0303200da00860b034480615000300d540040008000e40c05d148046511420030f4080342c1d0307010744040001490000e481910140c1e07278200c6e402047d00765000c0381c010300017180c0c13000d103210000404000460404504800305500c0f03024401d4964052040da900c0c100522446900c103411000701c1400050407561590702c0102803070307030f00c64500380f0181c10650001050304103080707816100001c41000c0c00080e12240e03a090301a124900c251000c540d201d811508203c40d034500b220008603c92074891150122038a03024109014140884003441002c404e1403000c00c0703400c5c084071800044040350a10f101c8541c0380a41d590f0307006030008501c0f854040b51801c0d40b15080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 539978057 1250 539976807 539976821
    0xa030f020f0f0a110108010e0103170c161707060914040b06040b07031b150c200a170406020307110a12031701080c010c0803060a030b07090f0608070c0809010c02090a 73
    0x61504c01310300d2100e040064400e12030a200f9050740c1884a801000450030440100d20781050152030240303024142082286004610b207112400c1c0c00d1141410840d40100c601a0800d02595201401c0030520303012014203000c003640305404980e14018000d022664495104000f40c001c01801d2507184d0303441d2000801290004070085000c02c0c0900c940c06880c80c04802a01001c590142d41040500c6256036080090907030013101c28103100c440c0b04901d8141d8011013120410819000051403a885103041c039009074030078052070000100302000144038881d4044203c4174015040500007008060070750125492007602c1e4001010380da80c00070f00c0410503501c124800e02c900404440f89801d81d8841c00600d40f40c200004610340403c0c3d420110341d00084401c070103198400070052684040c513959856002c40c12204075442c07000183c2c040400d12004200d00d02d10b00150506190100c0d0b680340c0707501c1c0909030604400019140c02d00204000344203a102e800460a650350142c000304183c1418400f0002600785 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 539979307 1250 539978057 539978063
    0x7020405100e06041404030c020a0b31290c16151125080105010603020703021c140304110a0609090c0e0901171207080307200a030f020f0f0a 62
    0x76140100b0000d00c0c190090302105c02100740000c0a54541c0d40d010b485109841d203080707030403c00d503030000120b000c0d6070300c040c20484007505e2243e80544900300d0041e02614073310340a0920701c3c1041800380b061804103050300c00702c01c880c011380f05400e02040003405583d00402950b011140718003450b00e202a0b410101030003c80d0858100c924079848808400d58540c01784854a450990240c2c980080c02080035101a464402081c00c100c01c040e2245501401d44034240c1011010035000696181050340c100700c00300010001c180c4440c85004100c00003403150440c280442c1820001101103014081c083c0168180d03500c00070000120150355420282c2005290f10404100614011000c41071a01540d02188080c03030040641e0116820100611680c002902c00000580704142c4a40800c06500c2d009041440c081c0d421a506c9184c0b41c1c500030485c046074032440c3c05c5d01d810440415419400020b4160b010341d4036040a1618410b000822450720010a0074500584a602502642c488000c40c42086041c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 539980557 1250 539979307 539979329
    0x30e0f010206190b0111030309011a060a1407020f040504110306150a170a020d080904060504090240060f05010306051f0309170a030b01110d11030702040510 69
    0x400180103980390306003112100d0f92910f01090352900702503264460210300030705040440f00000c5072000e1074a190400c0382e182c5c1c0f2580d075078409081e20701c0d42a9800c1219038000c85007107103010a1084028030a59542c0800031304841e000c80c00c0320031580c0c1d0940707003080d0500c040c108200e149401e0a114104140b046c40303081c024040c85010817490711030041401c05101b0058840b9080ba8a021400020032421001c0c5000c2401820494030042c0c1d5030103d510441802030321a01d8036008400100804c40c4d440d40d1005202d0b901c0c000c00b205c0141c5603405c0800703207001c4098032000c1403568007510200e002c110a1005495241c1d114048280b403440c0e074003200039141c00c05544040592148019002c80b82e4900841e0340c000c0a40f921820001c40640e03003d00f0b003804070b203400301d4446403d03039808001c0c8140410b5000718800100d040d030041549845070001807002441c3c88806117207102c44654035812400c0d400341c20462445005041072504004841c00751307030b010340304000c546450210a240840b80d4041e012841d2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 539981807 1250 539980557 539980579
    0x60c0f0e0603091b060d11071208010f2607150e0a0f051e0d06020702030c0907140703050903190506131a0919050c0a0603090c091d0604030e 62
    0x401c0c080180d9200e002203c000f0300c1138503205100faa1952140d010b84a5010708104020218030000c0d0003245810310180c0501070f02ca02d040d2038428001c0c042d42005c05d0030041c03100c1c010400354072141000c60465550842e0444105c440c010590001e5043c1c604400651042c101f0000700f0111454080300c1c54461942d4850150409034200301c082c03440340c801d92003208901807007808039140100100c1c800380d15a0f14618060009d42e40403c020702c1e942c2500b07981c00303603001c54071100391708003030202c00040203044036a0701e0903141107480540307038090b010280c0d10001e6010a0880030036000c1d100300c80054000070121201303544014407030242692158030842c0c042c011100410322183d0001c0c900c03806268080c0881d1044c107500360301000314070002031108140d8403030300300820343e80c540b9464004512401240600242c8900c00d080c080001d005600000405142c0050640880d0000b009401a141d903200c2c0402d0100120000500201e000000074405000d284244030401d50400c018030b800c024151200c1c1006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 539983057 1250 539981807 539981809
    0x30903150105120c210f011515020606030a080a050705030313050c061204020f0a1d07020705010504050d080c0a15021321030305100b120f0c0901120203040f060c0f0e 73
    0x162807002425800170840e1000c24606441240225141112042100d0204050740310a509540b88001b0811071440f15083c20300c45002c140f202c50080040074001012a800d004002c660f81c2c00034004050201c40c03011407150304451082d0100c50b0540d4003d4212174480c03c1c900d4004e150440010800c440e40d106000c14a513890824000b40c0e000410f4000303500f0200d60b20380d024015000c1104510350350041d105003012a00d960301001d50321001034840c403900401e00d08070a010786802c1d541d81020b410f111080c0401c10a40e614620b081d840c0f50f500c8903000361181903d1010317070329042140740002c0009200d119086004a01c0d0360290200130320300c84500c4110340c1d594214031242c5241d030284400c15500209041d000c070b400b94000c95009440403420040c1d1301e0351124280016001008100c404030b5691090001c424001102c41e600702900c0f0848600e4000e00380c3c0040d20540c03000200e4042650040300090510944081101303046401101c2804801d01d5110002c180032045200140440c41c060888685 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 539984307 1250 539983057 539983063
    0x1a04140d030c0b09010f050103110901080f10091110020a0b010501090b04030818060a0e0a080c0a030b070306031203020d0c0c05101806150614030708010e040503090315010512 77
    0x10300c580549a60501020b2501c0fa50094003005210401540d03e80c98480341c458124401c16000b940550548805240594204008084103034030030030041d03000e60540c0d0003040c4042150002000800c0303002034a0100341ca00300140024200140b5480188407005e82015500450059580c1e403080442200c00d0382c1703400042d1008441c0340100c80400d14140000e01c0010202001011032683e0758510002003204000003c4185d030103840400001901210300d0501400c0442e101000342480e0800303030800200000c0440c69000c103610001e801a00d06002181d107040c0a0f501100255811610a01e5010001e06d0b000cad002e50710506250340c403549408018019184907001c40e010040c3d01c03401500044085100303010140040c428541d0b40d21041c41d10070310018205216844070000a0440e400300c90b071a01c0e10203800e203586800c22040f206410010801c0740355102e50500c3c11b44845070300030f155985443c00d1040c0340d40038501c0180d030144610b80301c5010b80f15500006c0741c100d80d82107a1004076010407a01d80c0e51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 539985557 1250 539984307 539984329
    0x180720010216110607022101061403030924030c0a080705070201090513110301090b0909060c07030f0e04021308070605040602030409090f0f03050c0d0305070807181a0414 75
    0x2040b01911040e400010f06000030355062548001c040c2420100240c001810500b4040c00600c0c50241060512138901e000b03024800040000a02051034002c0001c0443c1d181c1c03180e48901841000d00c805d002d85020940c40c00342c4449418078150321348a2406020202140d03101c07940d00c0c1e000c242010b0018020700e01c1501112410359060359200072141c544001e00010706801a0740780c46841c2c446443c1501071014001a5009213800c07440460441d5205003401000340380548490900d400941c100000b00604c0421a007050340d042c035080d05198071494080f500240c0c00e295007980103000151401c01104082141e405450b004425603c0103a941d000655991140d4864000942c04c180410051080c031030740010071a5004061008280c46207542d008441401040c00301e004c25030200d10601840d10404c060101c500b01c0342810045411f08000c05021040000c00090400008403c001020b000d0a03190074000c0514000601322040030031030410031034106025550000c0b000c841c0c8031496140100101c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 539986807 1250 539985557 539985577
    0x8190606120e0708030a09030c0501050a051605031c050a06081606030e21071505040b0a050402011e020a0203060c03012105030c0a060c03051005010f05091807200102 73
    0x9580d0601104a240a48600288019a4043d189001410840500003000d0043c155030302c4070422829440d005030f40c400560002d0781086801d010405007207410100301c2e0b811035440307043c90044019500e40703145180b04a03244512a00d03007001d12000740c8030003904058090844194240003058484d03609903580d1500074849100d242407994104403983c086e601c034040c060082c81c22b5440c0c810050800350245c1c10b42c800303050300000d0300090341d03800c4c802c00100c1e448211007002028030441c2440d464000d030300300001c0c01c038100207981e03400440c08580c040c80d1840341114212040210480514001945424001405070702038002e00001603112502d240032641651a03081c1c2952605c0301d006100b00c2001e48898044130284405c01c441e40c903000d400c000b00d50015105d24008a21151068002419103001410191301c290554505000513a00600030f01c920100c580b41042d110141ca500051015004101d55116040d1060600c0400703940044900c0c03828900c1c2240e4956201c114032614204d104001c401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 539988057 1250 539986807 539986817
    0x70c030503061c1a01030309090e0307020108130c0b25021e1528110604080a1403040510180c0501180803030702060916050609150f0a08190606 63
    0x10300c41d0703c0c140210751841c8000100b141181902a582c559140054006156451030814010000c156004000801405100300c0c244040018817500c29a40d0080d00d90003030501c85a440000c50300d040b400c2c4a00c8403903401100e4500e80a9842c0425480d5900c84022440403400c0e0483d80141195564462402c0990103841000c0110b005041014250000680c45d03070301240c0c140c016640880003202602e001c044100c41c031212103007070781103448004600071445000c1c80b00d1000b22201250f00803850396446908481020303507880b6505400c80d40c0d02980741d01100e880c5408414403040c81301c00a034000078201500b500300300c030315210304441300032080c02030004001d0781090f04240429480394030300d42e5545120038a00c8000a80b500e05c902d081d6002210040700680c485800c10444500400c282d5100040c07404601218904010100d08030f0300c1030f841401d00620303e10b01c6080c101c3c403212045680103c250113103a41c41702c400e5100103013196000d94403a5404883e1000010141d6003500c580e0046402d29111 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 539989307 1250 539988057 539988061
    0xb030c060301120512032415120c04180203160903150b150403060b0a050a150509030312070c060506060f030a0c030e011803090b030c03010501110a060c0c0209070c030503 75
    0x1014040f074502c810860f020b000d14051494800041400385010340c142c44405070b510050141c19201c181030b040846403084142015214503140c1e20400c035004040300440b40d402a554988070804544075980c05151090312510030350441440a9002c2d50090000303802550382d240c1d00702801c840d511b44500020f040070b554030303030302540800807944002c056105c0940304081c2000c41410030b0003070341c202e1350041d944541c03100820000f0303141100664010380030840380ca1a03220b0074865811940c00640b122481032020004840e403142d80e08005840030310b0281032030700c00c8614000070000e2906407410800c58005007481c02180716450705806881700e81004100c02070a580e01c110301e1102602d0302c0030000046c19034602c66000007a40070b0055903014004241c00e84203911003454018440a410381c0040417082062060000807206c240440341110805d107030102c00d81944880280c280440d0800080500b8a4201d04038122504112140c0e0300038000c9034040e02540d80c3c0c14095440c00007800000b0700103a0f0402c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 539990557 1250 539989307 539989319
    0x9140d080f1b0a14040b030a0b030d0906030c0908010903090f06090b030a090f0b0f1e13020d1704060216120c170106081911030a0f06050c090910090b030c060301 71
    0x8040c3c01004840e140920507805100c248103010303400794003d41029880001048141d2001f40941d00348800294020110b82082c1c1c007008020b0344039805218201500c82c65050781d50340c0b0421440d0003400b1040c0082251491914016110303000a00c1440e102c1007010200140b4280160208012591030194451844d81d0308004c00d070091804950884406036980e40c40c201007501c2c0003600d4864040c0b050029850f00b0404840c212040c56035101c911061aa0010840c800540501d070f40311030780d4140d495450141162400000d283c4030408080050003001c5000116660300043c4001d420b2a500c08002a04d6103030819801113410010700136004a64900081103064204c19040c00c0006441c000041c2d11512414068141240442c2c0040c0c0528049a884180070806002d10071855081f0010011454181d0b07810801000d50700e000751186a4403400280c60303100034000ca071710840b401404c062892510f40a1007088412902640307800311301c0c00c0040136103410002100701c942c0100a04450a683c0381817 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 539991807 1250 539990557 539990611
    0x6020f040e01061833120b040b031905030f0c0a0201080a0c08152101060e060307032301180803090706030c0207140f0301060303090e0c030103020904120309140d080f 73
    0x200c089005c0100e60645074201007084285d20082d083c0e03541c421807500e00a002250540d81e074440f00320300c10f901c0c040956805617800030b102002c4000840300d0341c803180000d092070760550003120251a10100c0c001103e440480c4d0124490008034400d88443c921500e4203041c0008481600700640041059000410034004d50803051117507900c1c0081003120716001c611600c00314604c0b80323610000309a46446041c0580700503449001d9226a0903801840d2007449d540380c6048045950350035940c9070350b030001e10180404003900440c0c034038004024140f030209110f03d0070460942c812246590300740900400801d0b43c0d482402101c424180ca54003c011003030a14145494403010184020380c0501101904461510203024070704c001d5000e40c03078115a003071401d15440f0301c0b040d000708035001c4070070300300b00500050780c50100803508135802403100a0781800604050303008140d020b00240201107440011a85088009002000800d1943e16460641c441007448880428169040501c43d5042c1601c00034108000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 539993057 1250 539991807 539991839
    0xf120106080f1f030203160521060708100f0f0509330406030c1401020714060a030902040b092e1d04170f040603180b01050f03010906020f040e010618 66
    0x54002c03280c43c1d500d60006c0c0c0b51000c908254000155200c008011500d420200c0500c0c0600c0389000c003d6078031994021948070100288040140215580030803103010b1b07508809405002582345c0311840a484010240086045100c0e0341d204861610028241100000460358211030302c000005142c04d580880344a420b0351260b00c250005d656001c00408110f025455100510103a89031100c0f1180b15000241411031981040d940f0404001e00d420f066151101260b0720307041c991900091103070b074506c001405880b540d0f050a501849541c14881101d00003403c01d8480b000104580a10303039801004000740e071140380701c1e0200583c0c0e0071a800003681400f0070300d5039126105458101c008050f08100c0d0055070010304480880d44804142880016014851042c501082410911b401d1205584100d501c40b4140182c600944190100080d00d403800d400801c0e8041e800102503403640d0b074182c030005007034000d88a14080140028000244c3c90700074807010f480311081c001c10121060074902c2c1c180c9040d110f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 539994307 1250 539993057 539993101
    0x1023090a0e100c020c010908120d0e1c110a0203070e070203160c050a2310021204030605040b01050103051303111e030d0b03030301080d030e01060504020f120106080f 73
    0x6440859030801420720558002c2c050500001944041001e0000e01d441d0428440c1410700820482c28084103c0004218952101c040c1c0c2d42503951103840300d581c024280000b001106441034076a600260b401c400b400d10309480055640520801c0b0700b0701d0340ca40c1c440b103c00010790550001101031200d00001c070445503001c42e035401128607050707003440900c400c40107103034080e0b40e40c001c01c00c410300103441d00c12070031401171081e800e0027040c0c2006120176181001c510f0a04c10b01c01c11610030721642540c02800984c8001000d54040c0307444980d40e0401001511040781c0884940104074000310341580644110380c021085420070404c030031501c1e942990a91f660040b0291648240456801215005901c503a407a604102c051a12599a1700381d80d030135105802440740c0720781c2082c40140b00a20b00080d40c0c0c03000d800f01e85404a003503000d01d100e89004000303a41040d40c0050001a2158003001ca0304020b004084072000b504049a03a16001180c84e07540598140d19101400300114a00205004101c960300803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 539995557 1250 539994307 539994311
    0xb0f040207080f0c0d0e04270c091514030a050c0d05100c0507061803020c0103020f0c0f0a0b0f01140607030e0907031a0d020d030f02160b031023090a 66
    0x180440d01d10241c000710003d01056202c3c064161500d940090707010101b03102640d050010301c1015202c82c8404101e941048034100c0c1103c512400c0c02080716003032005114485040021030f4001404292884050194609100c1c00300c0d0590b041e0300b00010321504454108000e8640340b00480204032400414440a603124450540962143c4840d44100e0703c1d8203d40d6240c55595110034038101081e03540c90620071070310b200ca031340c5214003194010580e241901002d20f001655031880c6c1c6604400da019121041c900d81c0f0400002c0940e03814001240c1c0c00c000c4c01a8000b03507441d50b448010400c0c0c40c0d402d004500303905403505620055403e0031005041101c0c40b80c140018414140404200980310484004c80000c3d00c490100810100300f42c035860720100186c4441d8900202e50300424040012007000404001c040f01580100314424060300d07070714200b5580c406880b42d90b64219180b541e0030660f8500b0244500c5140040c0b0502c45103181d4940c03001e0445000c0062283c003040029205c80201a1b40e0265 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 539996807 1250 539995557 539995567
    0x90304053a03031d100b0112051302041b05042c0a09021002010e0c090414190b100302010c02010f050d0e15060907120e1f0e100b0f04020708 62
    0x10700380c00d100700710a203070030418040d0014403400e004042e03c055041c0301490500010100d480290b0115031180e580c20141c802203000b0400d0350040b5030301003080d040c8909040c5820284404031841c00c240e141054000c4030240131950005c1c001800c905400301e4004003041d0200300400503030750500ea80007580500f50042c00a501010070344c048420004031030038425513585003610800c619005926010142046c8001c21901c0202c5154590710002400218841c040580024040104d2595074440d00c40c001410355a07010030030180e0510520b11444101c0d9401f884500141020300c00a18040840390169180d0180c030809400540300d00b0540c003880301c1040380800c20b40c492840390340203402c020341c2560024140140b440410348140ba0000d0070961146905c01c046c000f1255110307680e2001c008910200060b02c3c0059480035241c0221106074910f000400320f20154240981c2d484603030004405400c2c0c03051051603000b00001c90703030b0b0311840315030003c1c3c0f401100ca1581840d60240c0b41051040484507e0030b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 539998057 1250 539996807 539996869
    0x306010e041502040803130905070507080c1207081305030d17100801051017010207081207050405030d0f18230402220612090c03291611030309030405 66
    0x80da03c140c1058107580e000095508400d41f01108100003010031490401141c10034410062140c4200d02029040040115942a4030b06e400d0124a05220740c3c80300c0d459642c40c0b02e00c1c1c00180d94111018001c0c00b0a284000041c0314180880c446c1d0002c030007603844d05445090b17458020866a0007422014180001c04c2000c140b941c000d110b82070048101900940c0f1041ca000c1d210304a88801800310815a4018030105d000510800f0642d80c4200c6040d00400c1d03141d4850204417014021076001503498030030300305215546a08401008041c42c81651020515000e042c5904440e0703008d48034014120700200078042034240b00102c0043c4c42c2900134405458154403000707040050310b40c1d281c80304144081c1c40c2d00308907c5800c4001040940c0f0804000d02103514140c0b18441110094803010703100050480d0383c003c00189a6964052000c050b40305443c40c1c2c1080d043c00310b504845044040003154000084558500000043d60b11458032400154a85818401407003d20040e90314680e4070031012540074071513 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 539999307 1250 539998057 539998061
    0x3300309050a061419060b0f07020d05031c050a0c0c0615240216080304051e0909010603050123010302150c0616020c04060e15012a02030d0e0306010e0415 68
    0x280c184515603074071384c00e203104c4540b2059401518070200520380304003000610485015a9032007100002016201c0c413960020503131084a000c001003141c00002400c10078081000540240b80302a14420031080d5a42820101118100110140410241c0e034070300c00081c21a400c00700036145074102e010b100c56507682d1803901080c0401c00d01c200724035070183c0c0c030700b11103604103c200c0c0c01d201e0265030755401500d003a400607128800d81c041c01e802030158111890341c20440c000a891501c1000c0d008844a141201d107850080c10680000c807603a50901c1d500481142ca550942078401425014242c032130b07440c40d82080038000b81d010804c540450b0611407051100c3c0244000c6103d0f058142030030140f401415002401c04003000c4c01213100e50305c0c10006214603448600b800da481320700e10010903003c000090040e901c000c9240f510260303141041d11065002c05000c0741c50820f00e4429070884098007100c20040d45e215181d51849034161744440b00401046051440d4150000e002e1562220300b42841103602003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 540000557 1250 539999307 539999321
    0x2619060503070902180a030803010e09031204030c0b0603120d05040c05060a09080f070e04140a020307060c030e060f0304331b03060803040501050703090504050106080103300309050a06 81
    0x103d1079030110303c40401200d101c0507405149402c642c4c800d2003e04640d0782e01403500041c02095800d00b110000a0f50f01d001c208100c6803c10f403003007011402480c1c00c0c68020888007042d03800301c2d4403510b60380229801d41030000e0088440c461005000d07040030f4402106c2802082e000308241c0364469241c3c00040c4a0319200010182c1c1041659504a80b60a206545203811152110b002882c0e000d000101700030f030691020f094110341d00400c0c0074128250740c0c1f0600d20b000003102c4007950500074a0000500c05400c604e420900398030945540312840c001c4400c00180307024108101d0710130340003000018000754056014000943c000414400718940c01038000700d48180c42ea655510b21546e9110070b407500d00c501c0d100380d0400300c2540381c04d0050b582065071590f128040c3d886154144400440c1c58800c0600803c118006800040c0c0100501d6a40345030051501d24203100a8440848071b660707494a006484081103401c20340580103c50034000c2c290101d005061a0105443e10300504d004400000c0351801a01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 540001807 1250 540000557 540000569
    0x602060c0702010302221e03020d060921030e0f06040818010c08030f0f0c03040c05041d030f03070929071a040c030506090705090f0709030c0801020703261906050307 73
    0x103200c0750070090341c28006441c0300140e181f900c030300c1c0e0410001681d41c1d000032002194486408203002281346845082030702101c0349011680c444c1c00000c080154954042c028400c0c42c0300442c1c0140201402d110b4403407400350350141c9684002c0140140c04e0751104a01742c09548185807c542d01810758852507120f40064078003003c15031148040c03003510311030414103603007008000040f10701e103050590303940360441c0041c40341d50300960b240c0c003506086900708030b40324403001c2f45002502c0da00c46840402c3c0390150f0081f101c0c41e01003044104003184240106172607501d0100ca0220a400704291500028180e4102c40001c441d407c1c440c02c40011901e10382d9016a0140d8800d0340d001c659a4218900340c2e0030031200400c4001c036680140020001642e07948040740c1c2011a00c9125803980e00c903280c00700e40c0c1c240c09400103032040500300000542080c055000f000000d001e0341d90242aa80c8400c1c3e1000c003408501d181c074002c10030100c041341200d003042a070050482c4080e1000070b9640c0c1d540022074213006040d0303c0f107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 540003057 1250 540001807 540001867
    0x905191b0609230f041d030703030f0e03040e180c0a08010c020127020906030a050607021c05040b030601030e0c04050a2901200a0c03080a180602060c0702010302 71
    0x4101c14200b500809031024880e10f111054401c0e200c0c085012140018492403080c1d881c0c44e11171b1410307402d0032080c0403400e10f541c054a90f20812030401030f01801e400908010200d10313003407003045d0385100807040c1c0b030a8854036040d010240d2241a900301c1902180300010016020744d055200304d55403030058440c02020038400200f14000c0a110107400c6a401d4506450b2402081802d50031a40004607154a4103a044616156030f0f181c031800701c0e2400c21800d1004000f80b10780030030f00a140e0780004805401c0d003804000100d0220710b0320b404031010b001da8841d40034030a4042c404103105602039000089000d00280032950110681400a41a50350540700c0360149035a130740e10101d80c03030118800035102e131041041c60402481c0311800204801e842c1d0070b003681e01d850140b2659002c1501445003041003900711920740043c0d92030b42001d022030b41c010300505020500c0c1242082c41d030501880e0020884010b43c01421065a88204941041e807100d9001c904040c1d08102d400c2d90001b405255411200d000340344 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 540004307 1250 540003057 540003059
    0x304030818071d1504090201020c22110408071401170601050c1605040b01110303070c0c1e060f1e08130507090615081b0918150a090905191b0609 64
    0x800c4944d144409403980150700b02016140984d80010b44548040010343e07602d03800d070001e588840e00324001131880e90195810301c2400314051440a01410940700c80784103440900b03a0f04e2440100e0064490404d6000c1081d64041d01e0582110100300b41c0e200c607060404910784080305a80a040290380e250071000800e0180042c401414103104089c5044801c0c02d00418116100301304e00e5903400024009010420610042c004010380103000c10010259150b020701c0d90070030505d6000c4c0242c0907024080000c3c0d842c0300b500340c1142c40b80901c0c1300c0c0c0071184580600d03600103d040440e66a5401055002008582164000014010010100204801100007468a0401c06050070840d000c0680200b08900c0505010038000c00d030055040c08840411116600d061070340206102554240d102c01c0740b0000c08003000040c4070b0940c14620001c6040340c0d0342c5815a20360840004940103488007408540c040c01d0740c081c1d80c10300300c8544903502d405501203000701d00c40480c24282124041d08118005414008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 540005557 1250 540004307 540004321
    0x1309030305010e1005012703080f0315040902100c1e03020c100203190c0c0504020a05090405160905060d180f06360303090611090a05060304030818071d 67
    0xc1a41048110b1320041e8400d00d40030008080c0c000c0004174000155840c849480f00c4140c5010740c20085a10211340c03a103a401030407558615400468190716440c0e01d1111291451615209026a10340c0c01030070f40c00084072f08141164442003c450840d40c02c03500700000d415071525900c030b00046500c2503009020140c05a0140540141e022002c001554001d01021394840d2003201060386c00341d014034006032005001e080a400400c410380c80981c00a20018000b10090341c003071300410303406400381c030140030300e4031411402d03425190054441d40001782c1c4900180301d285030200040c07100541e8030801003035100c41c0041c14001c204d188502103e01c0c0701100f4031541080301174040d9403c1c10880100040c2c2c01824000021000c0440d20f42d4920040c4140b094402014003c2c0c1c4240100c0e07400040410510060013100c1c0c9035980b0400c3c8283c404d1404000025551400100f1a4400d90389952450000e450340b42681010004403081d900d01c5005144001c25036040c842e910600c140c0c0c1e5444980b4090a1143c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 540006807 1250 540005557 540005579
    0x114101401020a020a120303110f090d0503040509010e150307030321110c011d010b18090a12020609100e030702040203090f24090607090302090c0f0d06060806061309020306130903030501 82
    0x144260741303410018042b0300440301c00d2000b540d00d80c0d0350a48510750680f10360303e08541907100307603002680d102c50740c1c02c00032400302084200c00d481072400c8031903400328901c0c1404040d651041d900c8000c0c0010f03045403440d040804020304040f202036592070f000c00d1a4168a58540c080c0c3c21440d545c0d0302d83c1e95074440500c5070385568144440c01120800080012801c1c51020030624070365045520480d41080002c1158250b040010001e09600031511800320b21084000070340b80c101c1540d41e50f005119804180c03207001000d100700214640010021450640c0507400e00001e90001010403040c0c3c060401c1003880c4003800e2105200300d86440c03100c510702d40e1103c1c1c00e0400e070031400b800d0303044142d20140030080d0154020490341c0960381c04907880901940c0704088000c0e14880c9220b41079505001042200c40404290000401e907003550711204507640c0c83c4024810385024070501e0f0001c6001e800310070040402c10b0741c0115004100039203840f00d81c2c54042400015100d442100300d0010b503644c00104040c1e0305035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 540008057 1250 540006807 540006821
    0x80f12060604030b0a0902132a0908061605090a0b03040308130f06050901020417032706031503010908031f17031803010b0a060207080114101401020a020a120303 71
    0x494815003068199281c503080010004c205e003400700d50307034203c107000d540c0c404852804044c2e00700b405004071090f0002c60400c280306001e0540e14203100b094100369041c05041d8103403c3d03480040081c0229510081000d00b54092800c903882800010868440540c55961700d0f41c01401045502a07540d08140c50014900507006005240c0c0c124202c0558000070a070001c984006500954013003483d868121410f402880750340e100b0180100021060410442c0c04006003226a04038000010240210661101d104a500c200303640d10020400c000b0b5020090343e52440c8030000b000d000010301510300e0740c49035620351096440c0e0700c20034146030190100b11021480100036045008020f480b50b00d00310803080e900d0003035660741100c8501703821009490b03840075071042c2180c442c000d02d60380f00d460750780300e0113500d407000e40c0203e603615401c0802c02c90540340d00515803070143c0a82180c0c004c00a1a092907030184105091055045000b11009400036aa40c000d8820161007590040059007a043c0740c090201d07419 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 540009307 1250 540008057 540008059
    0x9060a0204060507030e151b0c0405040f0201050a032423010203030105040f0b030106092f030c0307030b0907120c020118060203040309080105150a0501180918080f1206 74
    0x400003400450b90207402e8600131941410314150310382031800000d0496112010004e400c40002c0b580d464240010202d09000c400b2181c2500e280d0031048041c0415110111805081c2c102002e40d444010752080e0024400c03800649000038445c5e0340c0c0c813204400241c1d10500083c0b6100518410f00c814600440900540c9000c503401c1030700001e1600001c0d4880c001481400d10840d030f43c900c5011500c886030800c5060b00d070001c00801a0540302c2c4049402810005034130001c004920b41701c00e000302c85103043e100d00005c009035244e003150b0f40c860b48114560b0000340200101902c0e1100b4040310380352290304038010010f5031501d2150a03a500014402c07a200c40ea0719200316030610a0300094008491550955103030001e101595a580b541001d41e03001c2c00c1684481840d620300302c200b0103030300502d05402c88601400c172546401180d0b1040115040d14514049400440070346004110801c6107600c4844844010154507101592986a40308245c00080300c06000c07080014001c0c00d1081036610096020070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 540010557 1250 540009307 540009311
    0x30206010e0906070f051e040b040303033204021305130528060216050a080301090609090308150301061509080f0601063504060b090a0209010c031d0a080609060a 71
    0x58203813001000445448a03690902c5000109031401e810b1100e4018420701251880560380c1f66502a215981d40c0103100139400030340307031049004038205480d80344c03903904a124841151010000004a07a4481c019000300c0c0d01450f1042480e070b0080d0a8010079101385448183d1212010050401c40e05201101101405615000c0c1f9401321041e905000c00004e15048580140ca450040070300d003d409541c0318000c1d006106190400d13040041308801103050340e886030020321001d0f40d034001c20001d0f110b91010040100780d600c070014a8040c58903040c0d400c103080060000c20a182d80d803542801100c0026029400540082030034081c8810402c403599540c040078009121a624142005050450410720100382ca00031180e9001500441c0c6440000300c0390008601310a810180f5180c03006200440c0124001c0c06240c0000e65a41c00360b10036200d61100c1a10303540d1204e0b006680894007580d080410b074220070503021007038039161a0030003043e003d8044d26006000c2c9003005032000b40741407030040c484070510b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 540011807 1250 540010557 540010561
    0x1030f090303052e0b1b1204090c05040311010302031b040801091109010503030912012d0c032d0207150204051203070812060622060e150403230703030206010e0906 72
    0xa0380e642c040304c21100e0017140c01c3d4407018006101c03015850094002010340c0310b155030614183d5024401081181c0c0007001c00c101c51504078406540500851001078180c5401c040c2a80c01540250002d560116140048841603d00c4015041b0150842d0b00200c40c0341e0354581c1040d040140d010300229135004115080180342d0f14250009940e0700c107140035240910350381c044041d80d26500b50007440041060025118140e501c4080d24042880400038196605003001d13601490240248503801840c14000c1c2c03c1502c0080101c0100a000110541d00c40fa480d4200301d0800401c140340c1c45500c003160ba0301c101680e160300d46000c0080808020340c030740720250410040100043c04000c21603203100303110348400015640b800002405030042d0500c1c0c0c84004505e85400c1d20700d10091a43c1000d8603001e89034050b490608070103214034104d94111401e0500010802030000c115140b0030b0150030102e042d050300451030445d15441c200300300340d40b040b000f40c0d0212005200581c1e80c460419440030b400c00003083c1e58 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 540013057 1250 540011807 540011881
    0x51804050a170d1b0f170a0e030403150b12070e2d0712050a18080702060f0c0d0f0e010c110f0301060b13050303070f1101030f09030305 60
    0x4aa00301001011034188506502c0000031480c20398003400a0f80310100400720030101c0d151010f10b2400640c000052070440a0010180950b40e004000c5d860350041841544d100c642500042c5500c050701c61680c4014000040000c0c082c214003c2a802c05080200e107180700c041c240451410f02010114440d00704400c00d1109444440b05941d02041c4100f00644031401840264901c1da00300d034400c5031000549042107013040d0044900000d0340183c12040140d903854200200440d02074081d400c01c0c42040189030302c003065400002d015143e000074022403602d401c0301e0280a2076440b8901b000040e800c040e00c0244429040034003035035140950308040b11007030720344c000003444c0881e02840144178003200264911103480e180440304030b0103400750003040b8103500e8041903019038006d0f503d000220b801400011461381000b20a6401c8980d005030001c00c8200d056540c80314100070125800e041681d6400c07034800345900740c00b844061a010703440c00503076800c042c0e1348081c000702c5007280003600a90f210707071000d14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 540014307 1250 540013057 540013063
    0xc03151413051b0a0c051c090b0309010e1c02060108120403062c010b040513120f0e03011a13110406231b1c0e150c100605180405 57
    0x1c001c9689000161a43e140848141c2c42905400071641400000c104541107035000000428801c2c0a081140c0500b00d400460455801c1c410b60380368000380590004012032500c401c00f131a00700c8079000c0007042c4072510020040ca00319501c1d0642c12151107031503055050075018007203903014114400103484942ca000b440c2000ca40304d144401030800d95214020300400052180c40740303501c030044c0d0044100d412200034050181c081c0b8041c0603c146c9c41d00022a0b015180781c2d428500c4d840d0310170100d00c080d000e1840305860502e464425503060000b08810300082e9507086c0b04028800e800808280d0b940e03840041030010081c508443d180b00540b4041c00c500d00501248140c404654580c0382c910340c00040c03641144100c00240380004001c001c041040d81c2021948904406508001c9040f60141800f8444a0704015185c1c00401301003512100c050400b800d00342021003140150a081c00d00d49150708905e10316003140d101d02c0c400d203282e0b070300320600071894000548000780100500d04007107401e10340c0320651 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 540015557 1250 540014307 540014329
    0x6060112051b3001050307090501080c0405101205030a09150215130f11101d01031505030609060a0e0a110904020d0206030f010e1003200301020d0c031514 68
    0x1902541c00700d0f4829110000c54810311500c50791281c0c1c0100c02c4041000300303810003c2030141500c81e000e0500082104609417050038120b8a00d00700510300a4500c0d0248001414090005070355100800701c08100511058101c0440764410f10095a171000355060003490300f00300d6000804881040d03407840d02e50a43c0050904d81108590058100c42c0e15151100306190f020068004c02c500c801c0340780c00342800301405d0528640b02d02510078207450b20401c0d0040b20081160244100030407410320340d4000c0e035446644107000d800044071203a1240c1742c9401c0001c2c070b800300c101c444c00c840d0340c400e01c10003032412090b014020164418400504036a01d40356518040e06403540e55080c000c100100000741903603030749404944c00a03009000f0940d0b1b81006412030100f81000d014503806803100d4400300f10b007000c480c0e840004030b070340003040b40151400d11138a01c204070b0410702c82d00d58159000c4c0044089080d01c2d00c03850441d184203440000d50400c100b06100f1101c42550311a0135038081082082800342c9427410004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 540016807 1250 540015557 540015601
    0x90b0402040c0504080a0609140a0201120f140c0315060a090e101a030403081f050f03150907051f050a1211030109062102100c051e0606011205 63
    0x1161840c00010700f19103d0040303900c82816485022000b000303007d4594041d0791400d001d00e03045800c01d8020301102d5a91942404002e00083c081d0004548814960b403003040c40e110030755404250500220680e0320b5104056074410400d80c3c0000038014001056685426000000c1e10400d04200e6180809040396000f032081d01009101c000014030b164a0300303c00781e005080c0c1d500b10070080145010340b007185c0b900115411800f280e015404a8060f0780c44000c102d003440d41484000500c00e003001e05211078812644d20762034241c03040015020203032181d1001e05102d401224001e103849807a01d002c211101c14000e1012400003002c4d200284650f030300400b1038454081c2c2e07082800028001800300300050a881d220a10300d101c02000200c1c1070a040d400413800c4900b01c0124424480c001d80002d0b641d00e142c00720096012035004600c104150160800106503400788059680000d003010008880c00360b83d035105503e41d04403500b00142d41d030704410790300750103140a002003003186801c2000c6801001174005070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 540018057 1250 540016807 540016811
    0x90b09090c0f030106030b040515010e09076e010c021306090605040b121005150a08030901030e1c050f0d020c010617030702010503010e0606190507030909090b040204 73
    0xe041251005d400c828010351340004203200910301810315036103510284080050040c7c441e030001070302c80a0180018083c8500c1c4014000452908810002402a0040e0600100c07207011050040744a0302151040c0502e00c410700300d00d64890307403a43e00c0f00c4d004071440442030b202928045c000485549080c00300551000e00301000c1106050000030704102c14a05a400709a04041010035203460640205d011118107440a2103620501820031200909400c422a5640d00502a1489081441e000340b908002030b047c0c0040d004801002140240101d07400c0400298000989510309582c148a0507142e07003208809000c41c502c1d41a034000600c0205040c02040010101d00e01c0b02d2094848111106c80700d405a046503140e13040c140c104e018103503621070342011f014180014190300b20b01008a900442d416543d15103144e08140e0054081d40c0d000e840c44e604443d090000d0312614440501d43c5501d90550340303880d44c50350860301d0b005100c4010342d040340c80500e003481c07612000501152a9103030065030440e00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 540019307 1250 540018057 540018079
    0x72103030603080c0a0209060a0e041104180b1027020d020d1b020c06180103090c0308071b121502090301091e0303060803030708130507091401090b09090c 68
    0x32400341070715420103407410b50001010600780c40c0004810309058402c0c0e400b605665603020400c002c00c3e00c188a10074080d1100c200081c00100901001404c41c0c030b00802c0000c0d0030b02d4007a04010343c0c07001030108541d5504d41c41d0a00001c1f0200c1c0d126600103003000b40c4035040c481080041d524820b5031010106d4541500441d01c54041c0920b03405030307403240d041800700300200c185924080321001c0c0032055001c00750065200040c85810401c089502d01100c2c0d60603170728410400c0c00114020301c610442503803501680c0002000040c1c0c444000c1405074095250b107111410181e100105407015540010700303140894000c400040c50101c01c00134041001c000040c0c480f05644d011038050299100c0003092800c4001c0080c2000c0140a440365449003e90360030410325403928592566480706960400200c0c42d50000200b4002514040e03100081c802c4040d220000d5030340c90004d058881014555443c00b030501d00620400040388183d801c1e07400700700e0320754515007080c07401d0070340303a80d13041c00b078180150f007c095 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 540020557 1250 540019307 540019313
    0xb01081b01110102091c030e100f0c11030105090c03100b0108060402070206070c09020a0212040302030a0b06060c060106020307020f03010b0901291b0c090903030703020a030e010e070807080721 85
    0x4c181c0c1d900702c2c0090010307400c010b504001d8045200120001303e0205034070750081905428a008139070b80401071a10b954a1018000d0002e54400140c0c5508031800805071000d400640c0303081c024540504e81420081403604e920200b018140807101c1040000c083c608004c005e82c1c0e030b0380800ba80723400c9001a140166640c1c100d00203d00144074505021b8048511300c13000085c80001c507401003408150710f90035105440c520000e2031104d40326074400694540d03c010b08120100f0b00506660f0382060b0002c1046141004004cc40c90174040243d001344056000800c890003503007008000c1704800344e4202c0080090241c0c01c80014450340d810300a07000b000708801a80310f4000c003202204500d50842c1c5d01d40c01d44036026082e02205050440b40000d505001d4110810540d05110085070700507000580618215034401c03070114002e41248410408041d115400e110b1990b90a1107082c41c55083c20000e40202420310002619000301580482415400b0041c2004407a40d840001e420400e0300709a040d9038219213007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 540021807 1250 540020557 540020561
    0x8091507110307050c030c010c0213020f0c060a060f060306060f08060a0f08072102090103060e10090b041a1b0d0e060f01080706050304020d030507020d17070b01081b011101 76
    0x203800c0d503218440040c20f4402d114000451111050084040360707460315403500111200c41381303894001e401840443c8070b604c03103103016001f401c80c50880f090318906098024022615108054421505843e502c5d01c05002da044404e4010010700541d040a0141070700e88880102a030401300c405408201d0320030089503844e0b8411840200402001800000558a9220403a22a10721784608100d1140300340c50011030340344030aa13071103220740c004092020381d03032a54071018094822505500101e019121039000b40b050b40c1d1088807031050180420f0b903d10314103031905000114801243c20100c0804034100300d4041c11a101c1a80020b0b006000d0903220800380403072b100a0041001001000d000780d008005000b9031039013100341201c401c101211081c075521350f03003521030303200c182c401079041031040c1000e5000c2405107000306209403019103d0490300e403080c2c0b90b243c0e040d90030740c00a042d8018002030507024800c498200780d0150840c1d4024203550b0940c01060905992180c3d1054103000c0801055825080f080d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 540023057 1250 540021807 540021827
    0x516080702160b0909130302030922050f04020306090106051c060603050106061e0c0b01050103020315040e102702040518030d0b010f210f06030611030a0c08091507 72
    0x680b603000034180c07a03c0c0010040c0c0c1010600c14020780c0c42c00700158030250711310314509113150560003440c60f040440090181c1d613100d80c280000d000300c0000340d00040c1c6045100f580d109008080340700940d820944105410304c4c40103000c20005a051000c1445541d07240381c0c0341c000814100003140448180c034a800e001515043d44003072304075464000300080094100c10351031003004145088203001c0e06c2c200c00a40310141c1c1650064454191700006001e1540a6401980c201400080c540b484441c494001000d032071101401000d590081d124142c5400c40d107025041a40b07002500d08141c0071403610b84440740080840c806440f41c2c0c2c84101007000b541c441c20007800c8817040402500d96070700c0e00d0201240500040e4141ca400075100413102641a4031994940d031002125142d100c1c03648074079203100d802815a500001800310303a90304001000a50034843d0100e024000c405c11a02d0740703083e44894046450111051040c4022081001450580802c2c010030390790742c100c0f440c3ea40e03480d01601202d685c554 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 540024307 1250 540023057 540023083
    0xb01140118030609051908030c1e0d1505040c020a0f1109010f180203060102030715020f0d05010302031006150f1701081e0c010c030e060f0403080301180516080702 72
    0x400c01c011061081c0b64215072540c0b0f008001300c840f81158190084c0101c001011301402681092001c181244810001809500b403690f1043e807020389400c0c1440c3c000d03070005603442002c540d1540b00d0040c118118071000010001214200048801d8460203919100380070001004c0440d500b880c0c1080002e844500617820502900d8501c6075078603a000d02c490600e2600620041c0c0c800480102928a07850003145c3c801c00d41030b4055802c12002d030380d6022840f8102c1c140401083d0302403203816007e40940c00075080303440301e029001c2003e51650050504040c1c0341c4001401c00c0d0704008041c4110351254002c2c140c1c20084c4c0c98070200381c001000c0e044130380344020340c0009004007031034000113440c8000143d40c40407940c21304420a0801d0380c404405a032403600701805070100b041c1c02c1900f001303c3d0003002e40b5218a10302401041c40c0c50000342c901310b9103600030b41040700c0c42d400110040c00342200390300c46100300268507c0204007609000607030b80b9a500c02800203004024150b00001d420350b00c01d0080328000c0362 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 540025557 1250 540024307 540024347
    0x91104090c0f020c06090a120203070312032f0318070909030507060c230a0504050628030506090c0307030e0604080d0c05040b04140307080d1205010b03040b011401 72
    0x60303030755030080c092020042102d005110340720000e0300078a0108215617a44030010010710740c551511203c100205c05c00c010903039043c014100008003140b0844201a010929940e00098042c1402c152419032080f140c8500030003041d44403c10620b0103100e084079000500c0b4180c0301a4040b106084900c1c1696a8200c030305802c0c01d002682c8205500f02014002c0184525003d0080110814044449905448600803524030341103a00c0c4491701010b00408a110031440c0c95850300740c484000c603419074807021808117030040c12009810780420a05003072240c565039140c01c5c0003908224000940c25039000d042550101c60000225001900035808001100c54440c141c8a0604c0c0034200860540c0044404100841c1401e20fa0880300384260211003e441d103403450f080c02d26040105007941c049101101a405210301c034804075443d0010030542241c40ca441d550400c1000c40150719100340c1d441070780882d8243d1428800d1100091844034400d05560720404c0400c0250302c4980100c03000981c0f01c0b0161524a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 540026807 1250 540025557 540025571
    0x50405060d050d08040b0618060f040b0a17070806090601031e020405040f111c060507201b100e0409080d06140307080d020a0b090a020a1806050f0a09110409 69
    0x80e00a10b1117845280074100103921a030380c42d428081420f0344046141d107044107403c0040c00724540068012018072005c2c0c800945000b60401007100000c03260041990140440060306885004000002c05841d01c1405021203050003010181e0740d0006000080101032400d140308401800f424041e141b281d001042405641403508087d11141040c1409944500b0b80100441150410350101549005840081418014140c0300d0790f0040401070541030030030800401c071182d0003071910541001c9010310700140445510038048000b00041901c0000c0c042c1d0b02010306c803041250007829282c500c02081c0c0d004205040c8524254149108061591504619051011404031000d10780c502160a040d81150800d68440e0119940ca107804260307240103074000102080000e0b80001d105401038504000c4074001c0040760b000401100e0107401440d81208460302070761140d0503a0040e1001428281c0f180441061440c0114071049038a003e5500300070348601100d5812001413084600a19401d6020040301d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 540028057 1250 540026807 540026833
    0x30f080304080f03010b0d060b041503051b0304050d08130b040f0606170a0203070902070c0b07080d1b02010b010c05030f160f06020903070b12181006080601051018050405060d05 78
    0x40d003142d00c0c9003085a25206d03010414039044001c441c1561310340005050be42504880850280c800148100d8040f00d800c1d0501d900080c8100255002d10321074005800907601c001801403141c44000d00705948075416203556408600c070309055036001900f000203100c0411035428414007401c0582c2c0709004607400c2013030184448002044008982c0e2003103040c1c495090761082524140d004000d405408083d6200040000001250050104901c01e4041e2030500d90446504001c40d61840c0a4005403034450405c1c0000c0390303080c49030340141d07170090078200100002504e45940d07038028142e0610502100085160b41c4071440404450030951015400419400d5894010007940110380764030b01a1040b60004601d081442083e2104400740003003101c607030354640304a401e80030039000e080050350158114440a40d811806071034050078482c8024092949030030140003064402d688100200420401c4100c07410b000310705400100d83c000c450220b081c0c1ca82000040d041c502c2403900a20501c07542c4908142 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 540029307 1250 540028057 540028079
    0x606090a0e030c0601080c0114030603060c0a090807060314060103020712030c110319300c090504020c0a0302061513050402120a0b0702010b0103091104050703060504020f0405120106030f080304080f0301 89
    0xd002d0f081c1d0b149c0200081c50200d0761081e000643d22a5415084072000840590245c1c0140103915030601c5c10111b1595100002030403d01c66420410020351107058002400b0518074030141c00c01c00030b19045103804139a4969100300348050001c4400c0545900300054424850b00c00c070320465040070b0540b43c0e9a4a040c038460000d011003071111010030004800c0e910601d12044140d04071607034030001c58082c0541c91182c80c000303255a0402d0001d001c0da914010909490318406011204015002042c1000542c01d000e45041d000600500c030038080c00b6500403682e180c1c41c200500d5011198404200e81c1c8079840000c000c8081340d0121520742c800c0107161000e00a51403480b501034105600208508800140110251400300c080500960b240449412040c1400c0c8e200e90380c401124500025903d8860002406aa001d0003e900ea44000440c041c8420b14044900d4116810210000c000c034030718542d64107120413040c24000c3c2040e00c000c4005800e006007a41180c040c0c0700703e07400d119520740c2c46068645e9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 540030557 1250 540029307 540029323
    0x20f0a110601080f10020705030409020d021e0310030b0405010905031c060f05092a2d0c0a120309150c122a02030f1305120606090a0e030c060108 64
    0x50030340714800002610800c08203060303041410746005040030089600084019500c4001c080301c1c5448108800a00c044852000e8500203141400150f6a07070000482c0d80101803000000082c041030403c20712100c0c03807024103c10222070344184012015035680c2040750042801002c00381071070000290113051300040c10500750302c41c4503d200402691f500c13540e074482c200300a80145a01300e04d591010540d248901100c41d01b0499404e0b003440010070092030580000d0300031080303c1020805101071003400040d400403505e00000ca0102e10343c1071000c015a000c0e915191928080d100c040d142c01d041c60b590b8440e8100d52140c980000b0441206039004850300010042008205c0005100780e44000d58285140104c50600c260a03804c9540c1c1e00440781201c40d070303486c80c5444000b9844208481010080c2c2e860151403403014600c044041c2603d49000d120601d00806600b140a0304000c0130030005135118940160040c100c1900000d0f04015090518914402c0060310a2284151390000800c03c9001494403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 540031807 1250 540030557 540030587
    0x10b04050705031b041a07060e0a06051806100b090607140a0201120504020117070504050d060501060e1c0305160204090501050103110a050f09100e011206200319020f0a 74
    0x135007038000810140405004074041d60301038080050b04007407001039030000b9081c0c0601400c0006902071808040c1481c00482038001c591245c0c80f5010014000400e245612001d208035001d00ba8603c1d1011b540d007110143c030f006042900c8004590310002b5200c0d03000f0b440c0001d0380500c2d0303100049001e606c226519102400d040b400079008011400c0c80002c10300585009541c1070715408494a00454030b200c1c0924000c08a004018051000184d25640c1100015219000e07100006180d41424001000740c04020a501e008489940e025150080703036511100d8140e40500d08203403a00030204414403000c0506d04041c1d846814a400c00092010640c41f550480c2d1140d40151b8a08041d170b4240000c0c0b044074402c803903200030044240c034014109400f0040d0300071244116094181d8480080507451202a00580b40440b0180710010421030980300e4140c14514490100821920740601e480c00340c0b10040418107001c02c0c800703203004060415015208100c00c0c80341d04640b1041b07440c1c80148651500d031010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 540033057 1250 540031807 540031831
    0x3190b03030309073f080f12010e01150804112103180f06091203070f030f0f0302030c030c0711030105070c0209010e01051c0c0503070f08100507050a030e010b0405070503 75
    0x2c500801220152001500486203c0c904050a10741020900b8405c00309881c100c00800c140d06ca0010003600900069892821801c095418644183c170090016084490302d03078041c2140c045815088590a54803650184103111480c41010100701240401d200c00d0190b214100340c407200740e00c004406004125003800040911622260402807508072406500b40c00c0a010402d20186d400c04420030740c5504203410849141840540d01c00ca80340480007010385c0007a402c01c0c00c4c1c41c04035038070240c000340c4654549015030030342c202042908028800649603966a0800240103000c01200304074070031207070b40300400030482440e2110001e00314010190049108641810001c107000e9041c4082c80e040e00e00152101e82006a00200f031350411111400a0f241c2c0300302d41d100006c20b980c00300544d0000c3c04c082c22582054628001007986002100940c2014590034601003000e40c0e40c1c00410b03a6404482c074a0041a4034007003440c8240140101003c032500039061a04000c111a007200c015406100c43c2089 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 540034307 1250 540033057 540033089
    0x609190b0d030c11220b0a0b07050303071205090c040b270907120809040203040201050c07030c0608070e010807120e100b0a0b07030206011a04150f0210060b03190b0303030907 77
    0x100a0248005c580c44003c6058030f00f5841e95800742130313100c8074000c18007502602d40c0c80d4451040030a030790401e030070465a1740e00002c100521190b010495100e815080c032001e1025003045a04642c4514101080324040da0352070b00804042d42d1550010141c5d00005080cac0b903a000980025480d0700c41089460340b40f1403042060009041401005011703420b5008860706003131100d8041000060360025005a0400a090000110f041c0c011b0207510001e500c1036400b4907030360345060405020544003c0251040c00211540c0c56003c0e60003103055a40030143d854500031410500381c01d40c0061910001030201803055800c0d4840000781d9501600641c40200d40b81e190490b030700c442c080e006225502005006805c8000100000715207000c0304d6103010000038000342066150303454010358410801d183c03c0005e900030450700b8080e4040c0500555080c401d60b040c00050f0400c18454100e20015002c11101d81112444540040241e030150807140c400800b80c1e9624203012440341c4d5035850a020340740c429003070400c4c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 540035557 1250 540034307 540034309
    0xd0f0e0a020307031104150f030b06090115030506031204030b09150702190510090510050108060105010c080c071d040501050f010f09090201091a07060b06030609190b0d030c11 77
    0x10314012510703401001821010306540c0e4004210481c1e0781c196400a40700d41034110700044030b50305100035001d010038150b20140f560404035120305001c1e000703c0c02461110014009010b980302c5a04c10101181004070307882c3c40b80404a450580803544c07101610720301060103c20084105030707040c06a60004c044540d01d00745001c40d5102c16900740c03040300140e03212040c48404064030304035030003285000e0300070384050300780d030003403480c1690b040420488868110001034000c44c4140d104060150894100808541d030404002828041440c2c030702620114020801c00c0710000b08000200c0a0f198480b01d030400000c0c1c0420311841614280d070201c2d055402e0100150310080000b01d0203040f5241d540e0b2001c1c2191800e100c080c005d200c040c0301a0b0400481600201d017001305580c01d60915442420469a201d40900b0010210382c8000e080501c141010030900c441580c0d80b03201c9540081c078515071303070404000110700031004000f08105140c200c1c000b402010305140d005806614114044c421399400c0304402c0c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 540036807 1250 540035557 540035563
    0x301091e15150c0501150e1302010212090616081c02030f040f08070b0f07020709020c0705090612010e0a12030e070e09120301080304091506050f070f080d0f0e 70
    0x400340801e81e1006001c201e044640707641204501e207941042c004058041d2074039030039148030700800b80071040e0502d4108411454a426140d011140f1496403000c1f401c1a030000703444074400081c8052030300000c1801e10095980408494022500401c6a400701140385030110042d00103c420101000c1c0030319204101d420341d0b0007240c1c850030501c4902c080700e41e2a0b9480161010440c070701a100000d05000c030400107480300c071001c0d024211002034041207150a481c028a001c00342d40060f0f075914010310015550240c00545801a1442141c1c2c1c80c2c020340c0ca041c00b282c185200d4a8425450398240311800c60400004104859104c1c00b8031400c1141010f02e032070660940301e18280c102299407000204000500c0801d080541100c0080306842c0415070070743d564002c0d50800e03004a0a541c000040401c6132803018490b5481c02199202c0c140300b8607161041c0a02180586800c80c03481c0b0400050b01c00070814003140b416a0349034810b4078261034003d040d8002c40180384a400c02d5078060310b000d6003128044000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 540038057 1250 540036807 540036821
    0xc030611040b04090906090b1e0601090b0d02030a11070b1509221407031104150b16020a0b0a08190608120c0f06040f060c03020304020105070b0712020301091e 70
    0x7007102e5460689000443d50080108500540340250381702c6000000807941003420340107070b811001d40d0501c40c040611850b00c4078405040b1a040c444030103005c002100214056a189a00f0340200580301d81e80d25189a014110041103683c4240c0001602810002e03c0040e042c012090700041502855007074040c403414040558070300f8280d40d00c1c22041d0b0074103d50320003d01c21240c42050440460031841200c00e01e0007030690404c032044031549001d0849810540304049050303050111400b6100c0c9480b0700e03c0400e20a01d11060911282c15540d1819074640030000001010250244d5548804c2542700034807100055424088120703003090100c1410b8040d005000a070f4803580040c00382140000c01c1418680c2c824080b8a54a00444240307401d219000c1c0805403040e800b514161030400174500c0c0c034104441501c1010800c0c14414414803000d40d900a05880080381d20440c840d04580380c142042d85d4041701c606401d5079950002002203041c5009400c40c1c40d2181c1c2141c0c01b0717140c4084003000300342070702c2c04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 540039307 1250 540038057 540038069
    0xf040602060127090c180b030c2b06060f062f120c0f010c170f0112030305151f02010b1c080708071505150636030a0c03061104 56
    0x1400c0420f00c007000d00364000d50005203d20b0741401e03c150349030030500b00e00d042c5002d035102540e0340b54000006410144046041c210040384d0410043d01404144242d0040d4407500443c001d547e01ea0300c004000841c0d210744040c024034685250710070b5403206c00a042c0301c2d800c0d60402e6612888442c010075103a5240e0084440400070014180d03600e030208000e4525044204012050310488041c41d9840d8420301c5000c0300d070780096980c0b41c0840385400f141c1a100e00301506040c800e00c540c000400840e9606004070790410350520300811181c940112485001103120781e19584a10480e40341c0c4890209025a2200d2100e5900280071016000701008000c1c80c111100c074142c0b1302a9159040090203003001003002d188150300490408c82c0707a49801d1141c900c001c035103030201603686007440a281040030751544900000c40c0c07030b40d00e4810f20181a0619001d102d0342010381c52034079200c01c6405440b5803941c109090f80a007c03208580c9060620400d9801d9500c07007901c595140184140490103480104e1702035940b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 540040557 1250 540039307 540039359
    0x100605070507050402130509041b0f0b030604020a0c05060f010314070b16050a1b030c050904031e020f030d02030a0501060c050703120201020f0c060a0b0f0d1e06020f0406020601 78
    0x22420f400c3c00040e503c0401180600d41c034014012400e41d40707546406000301e000741210b08480c081e22001d13020102458000c86004030300c0380020030803003820408903944031500350b6000d40c484201002c255000c80038181c00810390b02540382007201c0c98107003648940c101c3c1d0203500c25045003144003102c5916408a030007002a900c40401c48540c1c11001200c0b8651911301c10022101c030844075442c1c1015a000d845010f8070000c2054200b041403103400303444607000d004122051030030350900740d402406032032003540c2240c2e4900d03005484592160082c04404a4042c148080d00c2da02c82c032880145000b54400c5450b080014640b4001059841c85210403500495200c4000e204050454540743c160039080b068140440d03400b0003a02405010305806000001d071080010140c904000d810041a24030000c00d40e030248804040320441561401491555260040901740c0351151140c0984882d610206001e45003600000b2590300c00700e449801841140d18941c240c40059032a520b051115800411190442031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 540041807 1250 540040557 540040559
    0x60604050709140604080f0615041b030506040906051806012414040b07060c1d0901120201030605100206010302100507030f030b060d0e060106020d0306030803181212100605070507 79
    0x21503020b20190915100030001402c0c0351b601c00d00035152802e0f9004030201a04088240890015603090f0b00d080c00c2812201400004503420211036442c43c20400c0004050f15180803500c6611560f000019658101300280a00d2070150920040f4500280b400002d41c42030000000c1c48001c00c0841d0880c542010842503072085a204044403405a084401c0c1c0008501f003200241c0c0f12480b6005091a078807460b404124000580d10203840000f01c0c03149030903007030840030310b060311641c0e403400840c19036241c20a00310ce408541d00048000703061640006401c080398658040e0090740028420b4100c4e0300c02c9980d07498900c1244000c03111070044000081c00f141e8510140e2500c036000f500310b030800d82d070007402d428140708942c19440241d070000702c48009550407039801400721590621155113002044e00f030a028107891a942d803032452000401c081188203002c88140345407081400348180d101d600083c070b1900c0c0d003d00300104507c2041540c24030b442e80c600d02c1c0c0016440f40101d082e214003a4015000e01181 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 540043057 1250 540041807 540041819
    0x30304030e01170423030a021e0c0904140c030d0509010813050d030f050709050d020609060f0f03011d07080604200a0e09130210180906080d02060604050709 69
    0x40d01044074a041c4000544041c0741d102511110070303c114001d400d0383c1034401c2900e4440507982000f410644d9150410003d0b4401141c00080c40349580025042e0031489031100e41d0111300305100c83c000503500000a6081c03005001c800783c00e02032640344e41010380d00e41401c1401015030700c0c0c0011007800081507050100501c2580502d4407140d0200e100c0b090a540a00341d565881d00744001440d8050122b5550310054400b00010721075103600c1110f6041c44102c590070324000900801c0540c000a1181e100000d030514683c455600742c4444074403000603076454400c4089540e800da0070034024121a070041e68004003806821800c0ea40c01020706032641c190700e468440601c0b0203040f00c040080c103058282d02e007520860f81d0484c01800e1003200c035a2442c2c000c000020030414000d0000c2c04020703070f00729a0702d0084017503624800b02c000b4003000303810303e418803500015003200d40c070350264844c5280914201c0001104503000c150f022a1121590030b8801da592400c04120850300c0c20740b10303803002602d00304080c052 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 540044307 1250 540043057 540043067
    0xf0503101205030304032010020f040f0303050a0f08011d042609010908150c1831050c03010605090112021b0f0f0607080a02160b012603030403 63
    0xa40c0e484103002155107908100380551000d0404481c40e500001c200001c0c164080400402d10762000002c40a20600b29803842d0b81d6100e0000c0c0c080320641c000b41c12083d0501c2101264001e00c81a150b0f4031006a0300e04020300141c0041c0d00340400303d401a400744802c584038203210f60585501b220020300c000116801e03800b00044c014412600e1600240c039030404825840350074400d10800c00540390340e0303503642c4000401c03100b0745602000c6103500200342c6c0c8400311081c80d40c0641c840a02e400320b42e2030313444a8240d225510f50400700107411401e10400148c1c050001101025886481400c00c030886108615100442c0c200320fa0141c21040244018820303944100b00403d01d50005240400c03400313403410480c008aa00101c401600055407046660141c17005019a442d031030741c041e0283ca00c40e07042d8500641c803030000400b28001c1084006c0000c240d282d1507415250003076220181782c001c11b00a0b2500c00e401a400f805600484181c4a03010941900050650030083c4844c00c061825900d4035501a03039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 540045557 1250 540044307 540044311
    0x180513021c0f020418110313031707030c030e031c0e070b16020f030f030702040c141b0f0c0d12110609030711010f08150310141602010605010f0503 65
    0x14580203803020384541801c140203100c000e105012005a990345825940030041001c0071480540b1782c10203900c0e03002081e2103800d4075030101c0c003c0a401c10781c0c0310780d1a0880300511003003036403401c2e131240d08240301c003047c1d066002d40f0191049480c1005001c45861081d0340c0c0e0f000700c401008001c0040380c18007a02c01c40c1504140303002c140c21003c9402090300c4080c880b4458102d02540069070312003849032030035480d181d49038941807079040c0d014102d02032100b140c01e0745910402001a000340c0d240c00c2201045072142144070560501ca080f41a06e9083c0c0300c01e0503036064001400185144120103003149510804154407058400080c48042c0c000302555440d00c914410301601d8080c0040c1581c298012802405107900c50300d15140039503a01c00061520030f22411001d03280718101300d0070028261040b0382280d19103402480b540514590746000200180c1350103214180d00b40c800c0c0c00e11080094400c1078100d81409040750f41030b154140400e600e030490881e4014811540000e07000c2490954003401080215 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 540046807 1250 540045557 540045577
    0x914040c030b0607061a0607080d0506061b0a11151e0403050a031814130905011b3c0c06060801090f14150a0e030904090804050118051302 61
    0x12581030700110000c0e915400044d41640d900307860b180d030007440c21000004a40a103004990365424810152105040360040044c00f1040036540c0001c1009559824192014681c08544503115510044c003690349490310700b181282c4028261300580035038a007030200c444c0501c20712030031103092503032480742103520011803519900389600410001c4049481800010000d6000781c030740c3c03c03400c1d041201524075443d0541c00030180c180211a01029030751504038820034030f12030010219525602e42000c6006040005403103030250b24600e4683c076001c1e0044840c0c2101030310355a1541d031000e01404112100503040f00c14203400c02c1411161340149029880e03600344d80f406290005200303501c80ca600d5007180d8101c88103450400000c0ca040c41044100b040c07c0010301401700c09072000c80501a107034207259002900550746141c441c40c81c2d428580c820816284e05000c004c2060104841508128140b0352044c001d01d400909000c01182035100004604022610050240300c43e4018002c0424000e4000e15060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 540048057 1250 540046807 540046811
    0xe0f0108040213021308030c011509090807290a0b0f0102030313020d080c030304110a0506090a0501031a03070b190228150f051f0f050d05031b0a0b06010914040c03 72
    0x710790070001f080a000100442c2d000024948051071000a4260081c0c1c01401800d042200c5200000c0406058900d03c9a00402584814201d08031041c1074084803001c0c00a651100800c100e54044c0940109601c41030a17a00c00c401c0d501c05000490316440121606403420700c0442d03e032130060805040082d0032900800001303013000300f182038007800d552040d00c00769841600170501440c9403400450710703402014100c4040b486c0c0064400402c2c0281e940740b18581c14585d407109041aa074480c3d40c51548001c1c8020142c44007036840707036901422070300012001c1e10201e18280b00c81c40c0950000484004558204060070503103070080c040ca1108005d0b002c011140c0c3c01091003142e402e000240641511251110f001195514000e14a00c5180c1908045062051407450080000352800350303111094030002c2d903002e03285c9140f82c01d0851452185a481441e408529100c120b0000c801240c8503241600c1182d48031a540c480350011103850303000d801030105c0045080000030035460942e1003559800e8640c140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 540049307 1250 540048057 540048059
    0x80c0a0e07110a0503041d013503040306020c070911070822060c140718051b13030606050a062a060c11101406060a0e03010c0e0f01080402130213 64
    0x201d5070030108602c0c2c0440f505d9001050034020110807114181c0f03d0300c21602c140d00340390700d0034641000d8040c0010100c4641c017445942909401100041140200340304000c81e503440e1350300d09c0c1c0000294021142d04015006090001c101d40c04d190207001c0c659507140b180705003060b00503120884984d0112a81d2400300b1027480d03054004000008003900180300c151224400c80600d420100c0e0341020b0920503040c260400c1030203110207001c0e0322810705c0100025600240c0d655070044000c09030a042c2c1202e10701c52801140500148084500410075248100002e000d22941d91061141c0c85a181c010785012441c200c440c00c0c3d00c48441c41d0004d1214143e510911004004c07500e440c0102ca46842d1050001f401002c0c0c16811000d040103002080d2a80c4c1008004205284c02980800b107806080380e80318076000901e80e42c525100b076802054421004000300b21403000c3d010050320b00d054141c2a50701624142040183e6503006044040c8141e8010304800407001504031024000d40c0110b03043c40c1060000c0700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 540050557 1250 540049307 540049337
    0x6042d030b1023010f0e0d172d04030b0402041b0905040b060c0601120218070c02150705060a11043b0108250b130e01080c0a0e07 57
    0x30a0714040d0034032a1030544040d0503c08075103d01c001145070700000c0c0415140540e40e9992140800c000c4400d0fa00e0304585180c407420004001c00856080903003100f1114400540b4991224004c214400c071400807030012801070100c002038040030400000f04d411003404100302003100e003003103e54441c1c401003000130f01565890011018209903141c1b480003564040c82031195050900c00e000c0400e004440203410081d0303d5440903078441c0c0c140a0a200d001c998a5030004645a1075071202e00095440c00480d402d240001d40140300c0c251803030050b442800c1c4800540c02010046003210f202942000150078660364024108015098446003001619410000010200d003224019a0001818200d442540f00b0900000800d104614510302d042d02c100d00c01004081030000c1c0309003c083c0c00759091002280d9204502d04034180c035900c00c220702840002e10007014607145100744152004261940d00d1030340c032190b180b41c1c1c81c543c51500a40241521105100c1e45000040c1e6940c40801440d04280f50301c1409 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 540051807 1250 540050557 540050573
    0x60609060703020c0f120703020d060e030a030e120c060f0907090608330a0c1e0810150e130905150f0622020a11030408100b06042d03 59
    0x76050340141c02071010403410307190080c40c15601e428100c07401444502d0410855468000768031000f440f036090882e44104100d580d41060020001350001c0c3d0b600c886407404086c024000003805040f440c000ea401d0380640e40e10010035500b2052050001740003a982d03800c80301c1c3c840100544000700f1407184403000200b003034181c0560400303000000c020b401f914591030040030791084681100580e0811001c14400580c0c80d0641250340100c1c0c0e82c40c0499607488445d42030703413480600807050704400030044144481e1500507207641e0040107040000f5a4440d80d40c0d0038200c1c10039002010a000401c410040c101074540009911007010064500052854042c0d4416241007031401c3c6c0c00d1603142c0341c00100503d03104042e13000c66010406468883e4150280740c03410030880b8894000000030f5a0104e0f10400b511b2248080c2c485413441c00003202d41d0345446a40d40c0307550f5070602109415031410014164107604008040e80d0860f0a01d10401400030b05d840c1003a18400c844030411403410300c50b03c030b000010079214 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 540053057 1250 540051807 540051817
    0x702011b120e0c040e030a081302030c0907110a03080405151501051b030d1b0302040b0d0203131202011b021f091511120105011b02060319020d0c0f020601060c030806060906 76
    0x11100559a1307c215030030140144400034800c0c804d244641040c5800768602042d0b0b5008004c08480e8104541e0b0b414009031840c1401443c080304600ca00003000c0c04264220320301e540243d0090b4101d40403c501114420030100080301c0d40442c01301e00d001c40003441c0d405440a814034602d0200d0341d9810034210040185944c00812480c4e42494441d94840083c01e06954050701c2444d0500e419454070741048010441032142c07800e000341346540040010351481140c1507568849a12054444040c0316929000f4043c0103c0280031806420880f00c447c90b5070b0001030100041582600d49904244001119174000c002210b0b0544010810000310601117145d0300c2002040b42d034010000d40c5860300080c51070b03660007058100034103000c14119050100554100c0c4c4840c45030b41103a582e5602e40c1c411415002155401002c9440280041049071141e0860b03000125105002c1d40e410720414104001241d40341401c1c85480081408109440c0c0070900c00e210303050b40030740c02070205032502c0070100204e541d951013 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 540054307 1250 540053057 540053081
    0x51c0e01050403110f031c06030206030a09031b02030a02090601020307140703170c1b03010e070f0503010c0f170601020106050619030e0c06160512040e0702011b120e0c04 75
    0x2540040100f01900803140d01206003450307008005c1d55035410076140c0d4a00c100070b04110184401d003240d00880069400400185502a000e03503201d007800c80510016041c00303003040b40882d14a2006442d40c45115070703050692500200280031415035a02440b40c1e001010380b900c0d0440c00200700a80c04101038154001403101d40100618a142ca1805c2503004d155038003160044a001c100000b084110000900d14080751850218100c42003110f00001d0050152104400d020300404000007600c101d0900d2200441e9016030081c420050b145000710798080c0001c820601181e60240311f0500d07001d00c40c01c01039000c1c0040c000013460a441d44002061034021010300c6e40390702c4a40110051072030345401000100c03021103008208901c1e104000547c180500d014144608a03442d9030f107003d000707042120321000030b202213002d55281d48450301c1e4840824100c4440c4059800c14a921782c8a045150707943c1c03001c503010364640d07110444d00084240a8040100d003c94180b2030000310203281d60b80d51080d1505034030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 540055557 1250 540054307 540054311
    0x2d070c150804020a030201120e010515130603050a080d02040308040b09010f030603031b030215070314090d14030711010c08060114041a13030606060f0815030d051c0e01 74
    0x89003590140004000503291020440c00d9802e0100680b07940c9450700c00d0741d034242014002068054040760007010820b040088560801080c01449402c07a40040c1100034180c803100a4000742030190310541e1400d1200a00c3c0790b20610321800850f440c034010300f4101c50480c0c00540b6090f96504d9a0b035164110340c00a40507100000740d241e18542c3c102c0040003002c0c0403404c2c01e101842c40c51310042d00041c200394210841c0703404100305c00c08061090001e1400e402c80069181550300344071100130000c00d4100100011600c441010410b00b00e00000c80c401d00318543d41c0c404820071041816076215400141480090006801c101804000300780500c41452240d07554802c2d0728545180010480b403d5102c52200e0321404000078010011201c210101c42c409500400d5900c100d244031810f4400d04540c805400c0d1880d00c100811030030351201c041d2441c07030286d907607200242d02c42c908138050101c1c031101c807550716521141c540480140070768060200300d0718044160000b140182e20640680d400504c1c02651030f5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 540056807 1250 540055557 540055559
    0x3150607080f130905192301080d02060108031306051602030a03030506031204120618080c010608060609190911121e060402030709051302060403120305010512032d070c 74
    0x21406400704020044c04505100724100710403542d200901020003528031a03290540150160b003000c800c3c2c25024503441c035511440d81c3d2107001707039281c0f22208034110041c0603c0000054410f000010303140741410750040c00001c40e14018064805a010a01c0e003605041007403600f81c0540c0c5c1c24441220640e0080e1000700f110328080e01090f013443c00e086800030dd0303048184410720068050103441d05000c0d50141002802015109000e03c0788205620300a1100308001800c0e401c0702c40c10b4000000301c4140d44100c81d6140c82e401d0400c00d100008a5014040340540c07113040b80394446940045103150b024503480100c03032158002160004200c0400740c5500c2e84100c000c05a9001c7d824000f10f80f441e0f2090181042c0e04099000948541c0700348075894445807900b002c507541d80fa20011450600754000e12480e03403140d6a10340b4080c6d80d210b43c82c03030741c01191030310000203298101051f14445e5040804003851416200420a0070302c1c181401b2140507000007040103140004803000208072250041044c20412 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 540058057 1250 540056807 540056827
    0x8180102161415042c0105030109080d1a030304170c04090b04021201180c150804020a1512020f040302090127020702040b0a060914040203040803150607080f 69
    0x5441c0c08403400900c0d0000100b0440315500c600074110a82c1d0441d09641e04942182400c0240c0c0210b40160f105c2c044c0b54a45580700c1c1e2424407590351204203024071200e044c0e0744d440c1058202c0e0070030003015211110800c0408418040740c0c0c0300744c034100c6002001c00c81019070040428a1900903401c092000500000d480079822001c214196201a00300c0701400700950654076401404070103070000b80200e00042c007908600c4400e400c44002d0080104904c3c0401205042068034000641b1a5100290705142c181035400e10506080b8030694000d03002c1c0390200c0c81d00d1152980c03005125003100421422421460202006000511105081c0700d503407a1540d0440c0100070740100181e2260b403807501001c01e861001c684900225007816502c120058842d50b09001103005000b1f0300c1101c07640032100b2000442d80030740044249003070740c68071100b1044000031803040c00100c3c402034402929050060000035025860b40c402c0c800c0448018015509201c00380da01c0e00001e8200a5400fa41c0302e1020401c4804 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 540059307 1250 540058057 540058063
    0x120b030c154008120a05040e0f0f01090e0a03052a0a05010606091406090112020c01061809031706180405010c0e0a0308070209101a0417061608070c08180102 69
    0x28010b00d481c50301d40200d2500b94140e0b41c42940489004146001040882d40309006d44c0669004185071f0b00e038200c4038504222428212103003100c2c1c113050303503581030000b00304423505114040070600031a0007440692071301d4a0a444076040b10a1540c68100851460465198949010886110311000420800380c240c5481403c2d07a09982201c41008801c4004124100d00700d0a01d04003200261740140c4c1e07420300c00700100e46d028a01000800d109000045070740c101c0c40158480c404407403021500c0004800e80c01c40e018186c83c440440900011070807001d084141c0144040503030001001803600310072240b207241c80303110890f00322415605031b5942c40c440903000d504048010b844020440d0314140341411652164000c0c011890081d004101c91030000d00c006010f07010b144060010076103240c440d00c07001c1c84011204d83c410b00605511064500d601403080d500055410700404103000340700c010b02c403107400460381910010601010000c4980a10000c00c80c0c4400500d00440c00d030b545042d010800700b001a107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 540060557 1250 540059307 540059407
    0x10506030c01030e100e030409050c0c010c050f04090b0303160c140a031709040b1507030e0604121e120801140307031e050a0506011401120b030c15 65
    0x1060505203180e0f40072130700001c074101000b0902258009103441214203d42d113940200d03005051200d10300018448103191074009040d41d10b4100b80240024800520704842c43c1c01801000d40c902d220038002448000501d402003503010401038200c4c0d05003400b100d020760011102d050156021039903401c0600400d00380d8000011655000c1d81c00c4031110f46103640c1d50310174241500207845140004684031404e0790380c607044000c81140060800c0362200300303c0c00c0c41200d64811007003100810102c80c00b04505040000c1520100d0f440101d580314018241d8441046d4100102411a00c180e251081400060224003450418031243d540b100318660500580189444164400f94800d81c401101000042c0243c01ca01891160a02070106d4608881c600a40ba104175844000e04501442001242d004401a0001a0f2400998130700c10011019203a213400c80b4131040700c060b015003295403070707100b00d0800051038054810199600d03860460161640306500e12009100d1070302c0c0300d40200035034151205486a0b5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 540061807 1250 540060557 540060559
    0x101107061e05070803160e190f09050610350106080603010e0607030b0303040902040b032532031006030f0212040f0c0305060109020d0c0305061c1b0305010506030c 72
    0x14940103030b51300c0310391940c00001c0030404807001102810000501c108000810b00102608400704210450201070306180c06002e1020b80da5210200010242039500660b409210040c000c04039214001c1c804075505143d1000c0c000b890309032032600403e10344906109045a4044540e0100f95505000004050103806012603200340e0610066040310f50001c948150810007608002880301c61740700210342180900d61222240f1840410300081c124040002507120b440110b0210801d41003a81a04800305206602103000035068a0488401d20b1101120340c03440e0015440d148002c001980549140d900031960b00075004072502c010428540c040c0210001400e0f120800d604140034600b20140540340204040c0c810889411040700b030201c1404c0300030145400400f5200590b03100c02030100a503000520b6000e0342840d024100030468403a01c521400794500074030201514540c640b0380708000a0095050b960788441181608148084492400045110321f001041d00d2034508101424420850f00803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 540063057 1250 540061807 540061817
    0x90d2a2a06080f15090a1806060504320a09061d0c0913080d0207020406030309030b0c030f190b090115140a02030906030a0b040903120f0b0f101107061e 67
    0x10142e141c200c120344115000050714440e01aa030344c11021300180603403182040743c0c24441c0900005108082d04105d050b11012f40d024400c04000403000115041104050f038007849003099001da5510344d02a20a03000030000102260035000c588850044400e400344819058039240071b41c41019005015008848034201c07010500c4ac41c1444400305840c8460344c0c000c100f840d0016001c0d41c2c40341c481e07050b1984250054000c0242c6501c03403a01030b20440b021b00003581c2c0c040c140c0c00001c1c0100c0800040700d204d41b890308124040781c4c5602d00140c5001d09204122180240c4448072109542c680c0c4551a00901c1c1d40b111480f0030300107981001d0030542e0403503001500d0321010001e0392001d0f60008103d5440c01400c1d10300d241e60b9611001c2260003400c940e03035019441030816120000340b5500c0120f004c01c00d54103001c1005840070740148101190681c40405070000f91550b041e102030701e002c0005854500080c2002c3c03500e40f141d0305900b4200902034002002040c031000d08458201842c401640301036455045c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 540064307 1250 540063057 540063061
    0x50a020d0201061a07021801080c1f020a11060c0607030204090e030c07060f1b1101080f0708060913050303010e01030c0f0b180409051005090d2a2a06080f 68
    0x21030241c0c045030104891310500002500411911105070b41c40c82c1c4540528201d010b540c50300d015944602004c0e0400b07100c2c49100c011007a070786c28640d298090840c42e9400401c0141c843c2c0da40e20501c4c40720940000e40c0700409014442ea60042401054030421540d540146c2ea1824000c40d03208441c0c0044915020354014001c6080703030750300020840700341c60f07a5042040d1100c144030402c480740c52000810012080c807140d007400420141031480705a105090300c13031240300d40e280c2e0303255546000100d0340c03c8001455080072500900700030220582108441403401c2e2650019140d0500d1a8401e90202c003100038218010014070891201d40300150030603000c501e4039140f400c4581c09017030107000500c00040d0f18084c05940e003651984d001e0102c5d40d034003500750313421106032503500c20041804581c070944500030120503039891485400c0c80c80d50005d000310000b01102075101c0d0442d0240815400700d07100d0010000d610144081030030703079031b04004c1c0506001c2600d0382030010003440018003902000400f111541 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 540065557 1250 540064307 540064319
    0x260603122b11040b04060210020712111e06010315140c0f0d050a09350f0909010f0303020d05040506030414150a02130f05030c0d0f0210050a020d020106 67
    0x10055002041004000c401d045901d48440c009090220081c268103000140009404a40c4d802800c00ca500740c1d0282d8040c039030022801c0080e031003000700003040c182c20901c2d104d00240c0035035024190072403690101ca5080e0710054005078070100d018514541940311000400400003070252038050381500740400c1c80980c521807105045000050131405810300d012400c4847d9a042c032090304c64100c0e095100b889907040001d81c060080440d50b6054441d5800680070001303c40151842d0340707040d03010305150300344114803400340082034004c80100030001e00204080115907941030100c5003e00030403d41c036007440e41355140203894221014095420f020081c031040203140d8407042520b50068000c4d0545901900160800c2c0c14110501c50384034a8200b0041404881011a80946203140e40281c441c14250780301c0303c41186030f6020384100d9515500820103907240f420f2407030143c020140714241001c50b00142c2d034009400040e4501d0340b140010004208211410750410030b801c01034003140003c21011741004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 540066807 1250 540065557 540065587
    0x20f04030b010503013c1a01030b010e0108070c0c0902030403030e061014010813060507030204080f0714061303120215060f0d0803091e03090901080d0e1026060312 72
    0x300c02040201290340340001c003c6c41d2200491440f144610017008000346192030103813003000c06254980040e03c2d01c04401c400d035004040382d443c6404140c41c6c941c02503403810421500001c47c480103d0340308240540018040d0000d002440c051361098030041707580c641c0e032980e151400b030000303280352007080030903204001c00075503c0f9041500340000c2c0381070095136682141103104280b07000401000c0e9072070b0000b0404140c0c1d1540c00390094920000c19607080803902c010b50760345c8030700901500008400302020040d06207400f1005280b001c0380c880c101003145940740c8440d0390300a892012500960000280d403400d50780c003007010943c0840e048072402041c0b0400800300e03240528140b8002d000620000100b204d101041081c9010348030707226000c108181807210410780782e4115264050144040c0400400e400202140c1c408403521682e540a88501040e41003149001000003094240b040c10b4919880244107550598048031340f1101a00e40ca040c510149442d181c2035181c14912403009108084041c4811 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 540068057 1250 540066807 540066851
    0x30b010b0702120f0c0a050406061b17070f0201140c100905160611060901180312020f03010909021207050102190501140f070201060503071202091306020f04030b01050301 75
    0x210115544594240c0b012403c820500002c0ca20309208601201c1268000010329211059041c0d1b0100c002035034520500c410f40b000703802041d010520781d4160500a0300302c46590703c403690250307440d600480150401c0d10120342c0078440942c0c0c1101810700c0c40c0250b50708564201511b400c2ca512040c80c0080c0300e41515294001b403881513803000c1c1c03104a03400502c0010444155072050b00c2814000c1c556490f2005004208841040281c07030007404002a00c0e2501849400d140480301d44030304c5000905550700700d0f11840038802e01c03400260b0901500344d0820f141e102460190440d142d00050044c51030042046c100c1d4480354007003403070b404840e062040f6613010840740d007800b00f9920140a0100c076031520390f01511b2140c50700818000e02004001603016002c59181c05410035030000c2103c50740320300906480e240d2500070360a0729150060601c0042c05e01411a661110716101c545c11307041710a546a000380da1144c00e49945964010070244188403c0d000c042e030040200f00c00820005190035600070000f850 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 540069307 1250 540068057 540068069
    0x40c090e2a010c0602030901021b01020702030a022701140f041a04110c120712030603030509060703030f06081f0b0a17030705060c0d0c020a020a031e1707020f060301030b01 76
    0x901c00d01c411040e40200b0082c0c1003141d021009544034584410114000c1d0403020a5a0004920700d00d4802441e4041c801c44000325005405000108110340070b00c102e800c28269220215880c5900d00078840a44800b1076018000e02280f07040544038550403c0820340c2c00d0784400380b080c0d2400302404045040c0403024203002e04150b07000315040d14038400c085c0c081e000e010309511b564095403442246980341e403802030000318480c2c0d41200c0b8451407040c3c21421200d00d4040103003c680200081c1d45d50b0314103c409022018840c1c03070040354900d4187c1c10a03080c0c448a601501c9264031250840b00d00e418104901c0c1140052030030200461107071400000d2044c0c40038406d01c00d9540d8040002d100708502802142d05094008007201d1442c00c2660b0084c81d25400a8903230340d045440d00c90324074107561010400710f6006400a02001445003542c0f50259018440f0491005009142010700c00140d456244c50300d0300c0e4410030b045504e8024038010f100900b0b10306615244501d80c100f0050000494030015a411740c1c132 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 540070557 1250 540069307 540069373
    0x9030307080619050301021908010b0a0806010309110d050a02030d030c051b010b0612150a03021810120c0e061507060e0106030212010b100503070e04051b03040c090e 73
    0x200281403d040d815a6085181c041d40000340814501c0301c56050f480300d100c0c0f15524054160707a100910010380c00b410002e100020403c0340881d8540d071080e0011a03880307000300401015045c20000040c440704900c2c804480030340011102100750b1070240b0401406003600e00b03046c444001100002000740c030801001d002c88100640c4000c0c0030032802d5200600402c1c0151615aa0b054041e61a030058401201c1050314000c03502c1035a036150400400503c21258040d0002400003003200340704643c002c009000b8420709154510001d000d192803100800264043ca0043c1c0300c06060070140d1003903600082801e0301039000c201200301c650240d01e0456044031b402c61000904030070007980c004e01400c1d0b10f07440658400c0442542d6416008117612009086800701c8803c1442641d040e4161342c1d601040728180003244440e1010511800d00303410455100e584000d4031010000b20400c68241908256015102c002c440c0380c040c4032045162040322861109070000f005003542c5404401c0800450380711040c0508 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 540071807 1250 540070557 540070579
    0x30206091605270903030406062103051b060a0207051b10080a020c0d0f0f0f0e04020a020304050918193306080c0a05010c050a030f020a06061508090303070806 70
    0x8800325404241c0711006028800c03d402c011501e02c2c0d8075081518143e4040f0314000300043c04640d810114440880d02c0441c5504103a071b01d440035602600f0402502c0f81a030f000344c0182c48020420710841d031007011030500050301c81c03140d410080c3c51b0101552100300000054104649295500780c1214640d945625080c0e20306d94609503264045c0c0280181495207125205400c0038868020401d10010101955440000c41c691b010440c2d03c00d00b40042c20300458141144c1060505050300140412402c0f40101c0385001d0340c80010070b140000072541c8103201e8610b000d030240001d0081c0407085011001340a4951500b0b125141c2c4241c0b0890040490381124115003800a04014000c0d0380ca2607901c244410807020f99121207082d00c4422190f0614030403129440041019030192052400554100000308002e104543d401d8500005140b220403c0d441030286c0b04000500d28000c50340030300180401058444001074005e0f056101c044d03c801c065401c10310811145903400100103611041c2101c041c4248 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 540073057 1250 540071807 540071839
    0x30906010b09031009031e03140606090a0e040b100f1d0402040b0d0609060c02030a050f160b040807020307060311070b040201090f231c03140405040216030206091605 73
    0x1130030140340148150700b40083d150070700da00503180300c00c20f030820346010074407554586041b41140d110003031407240d15440e100801c10314200324002d40507011002d0440007145884c1c1885680d40c0740e0440c1c007100c00c45019010401700c8000c0803c11002000483c074001c1009080001030b9051201c80b10b00d240e1003551803000541559601e03081510a880050502116828a801d080001d80704800e01175800750f0030102c07502c20f440c0c40001100c400c0c0e0312560740d05003010301c4441d800b41281c0c00180398840e440c40460036800801d00c103080140c00b031886004129030b100761382d2050505242c03681d0f100e01c1c1814544400104205803650072034110316809501d103480c2c0d41d264801a100210340c0d0304143c0c0a0b010340c540105046810030045d0441241d52003020fa80e906105040000320850381440070f40000da221103a4000900543d00101c981514010080c102601c0b180410103d03009003000c2c612403542d190380203060503010f0214981140300702c00540343c0c0c020001b1942e120100c50344906030180c0c070440405848 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 540074307 1250 540073057 540073063
    0x1020a03110a020d030806333703060609030803010e190e0c01030b0a08070e220b160e030d0e06120106200a031205090a050604051011030906010b0903 66
    0xb10b150300808103908440b182c14011320f04541200d0441c0076040307500034081d05503e078250300050441c1c042c440003904400d00055450a800110510303001104600c06d0311003003201c80d103140c080c985c0d101803000840c26102c100202610390a52000c0d00744001c115043c0040f40144048031705494282541001c591940c14850030020b040f150710703090061500c0c030381003000003000c44e0110752100c0980c1c0a00c02017000d00704012029405202e0a041a40013041c10001c44000d4034800d07500c00c0c0d40140d10040b90039402d1100035600e000920440706040d884041040c4054404110b4610702f119280c001c82110480001c680d6a4012190344018031080444054281c1d540c1801c0b18010214a0707040c40d55569907200140041c1c8002a1240c4280c3e44406014102d0350700261030b508241d019075401d0703c90f6134140f0342c000003098050000700ca1030094110000103c0d2040128038081c500c1072005050349200a1212000c0b00d540e240f010000388810000d00c040d42600248040c1940e4407e080b5564410280000900e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 540075557 1250 540074307 540074323
    0xb1602060a0c020a0e0a0605010206090a0b07090b1303030f020a121b020409060c030608060907060f050415080a1d0c040b0406030506340f0804030504380901020a0311 73
    0x135004051600119480072241481400b40381100c00a1104c03640fa440166100c0f0400c8480e800c041c0d000b118040041080150b409400c101e85040c500142c64441000620903441581d5410318001061000c20406a006100303941900041c800382100003210b0f5105078413001400340f684200000b1440c44d00d0034004988608a220358020310400c400160392400901800108200380301092400c0c0300000c0748007000c5500762040070700e078024245950a051041e610031b81d000e4030b01010400c041c0008600c0306480c0d0241c5525640c143c645924900d008801b0b9800d0360550700c200d0380d9502000c0ca60708003c000004041c16200f01c2260003049004801340440d0060110b50700c044c0c02307441000d0603c02004840c40c084508010303030070485055003207040300c003010648100d82d0b0a4000b41e0424581c4044610a0000c15005032082c07900510b01566500f000d15800e820794080c00e00340e41e200000b560103079082c00450600f494800c00302d03800c0c81710300d20020f900c440000c00080e0522410b600c0007194401c0034020a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 540076807 1250 540075557 540075559
    0x17190c030b030a0606090c0305010e0f0406090b0405251d130221060f01030206030a0207020103110a09080f0f0d110a0c1203080a060b0313030c0b090a0b010b1602060a0c02 75
    0x25440340c100741000005800d181c411b0181040c03800c0001c2114505c80c0c05030380d0590b00b444511948603200e030f204403405071b48000c00580d46181c4c1c4a085800068011000a001d00d0140009000030100907041283c50324860704009000310340040c082120000c10300040580601580582525507544007036000f0031414400c0c001d41c40501c175880c0102c80340400d40d0002c420080c800407a030032a5100f01c1c1d14000c104080c0006540801c0500000c1c1c6441c0d20364009140c0c0724810300d03010a840c003544100d480c01e81c1040c1e1100000c180107100501040074100818500c40340c03001e0082105218801c2c955880d001c0e5600320004005c0001a42c0e0244203080140380c100c2c66009044c480c50640e1144110b04819003d181100054210004603d5400e940c0c001c0e00d0954407801865480e43e221a018108001554a0114184006803108034041105880c1242c0f0524403100a05821179880c40d044c40c1184058200340c2d03a00c1c00034050b2a168891422004042540c10380e4030b1070341ea858191090ba204000141c0003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 540078057 1250 540076807 540076813
    0x516120e03070b011a04300b0c1b1906090f0f1a0c0a1d0a05041a01020606010801080604110a03120309170406050d23090d17190c030b03 60
    0x21004004008210354101c84111405151008031022202c5c418880c0b486010401e80c01c4040c203261810600c400c002035100426003460b400119540d5682010200b2035040401c030300301041d610800d425208802c0303611080e600150000210389001800e020700c0030b941c041c08060b40d507440a010060703080011022981c02166400c0303595114509000d14124004071070640e03500000c0840c02160700c1905585103800c03281c6030724107035a08032883c00c20840071100410754403a40d50300c00000d030398407280f080212140010901104503101c080c006450410083c04c2d4604000101004000034a00880d03041d80095100074500301c007015550005002840a80024003c4001c940c2200c40503501a48510070b00c922480403254080c01501c00304200d409980310714404500c0420056404941580c00034080c50740320714141d40d0b010054149402d50810454910006a2110050114160704400c29090400079403040d04018505104159049501c14090030705a0b40c031482408140741c002c0c2c003d000080303400750031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 540079307 1250 540078057 540078067
    0x10605060d06030204060f03030c11010207211e0b0414010f2a110c060c01060305010e070e0c04301407060306140108010314120f09130516120e03 64
    0xa001e0050a00b40b008921443ca0700000003444a1548001c0003180d8154031a003500507410388a60308442e0f881c066180c114051440049620000c156803124121140491103031504030390b19003a0680850038448844242c519000c0c000001c0006111071b903c80d900240210320320202c44403c5016001c440040c1c802c090512401242c0320b1840c0c07025000071000313155001d000e9003205100b91502401c200c011691904810350414032400d04200500e1041d081100008615903a61a214215222072401e4034483d00f00150030803405400d6040b0315000315006203800c2c0740138a00580304040705500561101c600303003401f40d88107401d80351429400e0040d030082040c02d18803c00f0002940c5508440c02403030042490300c0004a0310303100d40d41c006680f141060310b8418150f420350b1101c406a15180c0e0706c0710954400e01d0001d8542100b0880600340c2c0301c2208109030303154040641005401d4145c0c03444070f801545024100451640c540040a00360780890510b00c0c00640002c5040e03002e0080716031405424400060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 540080557 1250 540079307 540079327
    0x803060102061302010f140702090c090a060e010f080c07120206070210020403110f0a0f08010f0e19060f14040f060c020a0b0c0a0e0d0302100e070e0c07020301060506 73
    0x1144556000da090b0781940e0b88140c9424040e014154019000541050440320628051118541070b645038042d140d05029135170780001e814a07021a294a200000420743c45903d00b01804898042c0c0b1903400d004c4110709808000908400000341040c0412481c2e101003a01b1004c0e102c1260755841d0407491a04124185040203542c981d010f8403058014031540103003002c0b0103154402d44055030340c0510708401001c14203040141913082c0c160f0f42a40030340c000d0000100d14480800b118020204000003281806a02c000401240e02d2a1030742c03540e54002c1540c0b5494200c024a20001032903000d1800901b01c0283c0400c2c03801051040002c07404084024248070a02410f0748644e0340703842c46043c05119424401100b02d03202c104c141002040c000844000c00c1e901c000101c050000640c0621303001844550000000b4605812840c05801680007900108803d0009008108500f0040c0c0028a40c6910b01280240c940c03200a0249507280310204118045542c2901301304c00030070004202d6900d80c90090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 540081807 1250 540080557 540080573
    0x180708070c08160507050a14041a120c0306010e0403020618100c0801031b0501090e071b1b080d05090d05100501030c08010507080c0706020d1d030c1e070b130b0403 72
    0x31001361420700c40c0f008009201d10340141c00d502540d040c01c00c0080b00015102c02d000103005c40c0c02000e4031800345070048010f01e071100c44c402d8050808100082c04001d41840c2410f080600607080704846c0c841520820011070f03000104260070540704c0d1003241c1d600c00e0b00e000c4141003280e0001c101d405182800445cbc0c00d115031000d00785059a00a0b20f160032500d884003108038000415100300d6011500704001000107210400340254080303c2401c011125004d50074052480c0d5115078011540c0d8a4200c0e00398240100b2440b250340600102c10060001c4100d00401038402d00500c0440c07841034026481103010400d00b4003154006030b038880710502181d6124500705c00440c5083c002c070900fa40c0780000190f001c501c510701131405688401d40d880d10300082e135100e04002c2c0d0300100e107103120140c581c0b1490041c010142503020414008038007640e1101c4c00000c000c0e0900b43d100005c02903141468040076000100829950100e40201c0d01441d505c0003000002e8006020aa000790111003005c207001041c000e07a6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 540083057 1250 540081807 540081847
    0x2e03060c050418060317030403030e03030112060b01020601060e130906181502160201030908071403030702070f0503060705030712050a09060b03010221070e061803060105180708070c08 81
    0x3600f000440c0c0440282d400112103192001500885130b07031140c11001d1940382c005503040340c0207107404624041c100c40110300d10381c0280d0250b681854125942c0040c84500e20900307400b02c500b44040c02c910751611200505008002d207109114100c50303640300c1d039514080e9011007880ca5000e4424850448903c182001c0c0d0b0b00304c041e051b120b500340c401c2400e290384040d1003240c2013400c1c94610b0a070000c44540045000f02800002250740344000c100ca5808181800707108003d212421009558a01d801d1000900740100c61344415246560903a0a01151ba404a40ca5900690f40d103000c64a07030791400f000303c0320407422852984103107251105200303600c280c5d60084080702d80140018400b4645100506080780300304041d266080f2a8242900780b00002c0391221a0440c00518110300e040010740c0018141e58040703084041e00901d0780d18010841c1c20300b44041d41c010203007129924903c0050200c50200003800030111420820b451001a4000340541c1035a0001c2d90000ca08540720074804841346c031400d0380 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 540084307 1250 540083057 540083069
    0x70e04091505160212031506160f03110d0e09040c05090403170124030c030b0312120106050c120a020a0b040302030d060b0310090f0b061c0e01052e03060c0504 70
    0x485008201a0f40000313040c031a42170040c44800d03c0c540c3c90302da45440b03c40c0c00c640300ea076202d2005c01c041c1c0005c400b0b00b030132061400c1c05100100783c0c084207031601408248503001c0d01c50b010b4114003e000700207504007503040d0354684103640c084503903910781ca010480c85445070881688032001c88144020300d54001e81030481908460750175a19640c850000031084960400303440c04006c40e8401081543e4132a81240c00c1440d418140400c5038404480041e06102c0aa00055440348002c10300c41c0070f10324000889801804507041141c9800c1e0321001464a41c9071401410200b030000050b44c10559108101c0702103c107810040141c40c6007854a0029144d030311001c030740680d050130044045494500341c4c00303ca014124994040300c0541c50600014050304d03a28060b0604640d403000c00c800d07a5107a007001460a060341024500d100001d10115408440121200403ea40e142c00c040001c000050000c1e003c481010610202030180b1011480300065035540000b1301d80c60903c104803c3c610303005406407040e182 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 540085557 1250 540084307 540084331
    0x8070201050c09090103080c01110d0b0310020702030307080f0405030303070c030315211a01080106030b310809030d051b060412050901020a050109081801030e06070e04091505 77
    0x82c0c1c40c075600e80c640205074500c1d5100c1154801000000e401e00014000313100c80400210b03c061005e81a0421504400c0921051a4079001c0e090018035051100d042c03100280b020840c01c08546801082d624043c0c183d00030001c0d100020b1350700242c010b4800303580003004014100caa50b03140111005000c0903041e5000c4011a04055500700300040f004104020743d81e03c0c1c0914024244c103040d03400c0b07546004a00a8031043d040d458107e2080f6004110329018080d044004074520b0324504c1d00e803008020050800502c4028045d01c4844690940d02e0303118507110881410400f50b0342401c00820910034031191a40c1886403010f0f8184090b0400d02a04042c8015585000c105961078071881d12420222401404001c2c0007155041090061000d81a1150180304481ca00e107032980d9400d0859118541c143ca0608011410080034240f080c000c1a21500070302e010700600d40c4050b40c4c26a00e100142214050201144001d81747e602c490f480f02d002e954202c10701c0002c070b103100b1264000400e010380e00c542c9603039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 540086807 1250 540085557 540085561
    0xe0114040e060603120d060e0f01050108091c050a030e01050406050117070b27100201050103060605060423031023010509040c0312090902040b0a02061506040911040f060807020105 79
    0x2082c001d11034003025020300101506401d0726903407a400400395029440d40c0707078800314010100701c5109200d1110301e41c07111032950510002400c10303180181840903991024044804440c4201d02d4440825164180685c4400001c0015409040803482a0140e58a00701c200418040310b604005c0c100e613446c4ca40b60000f600700d81c1000d07441d80b4490040b512254000c100c3c007403c241d036a22500c0c02c061442e892002000c1100400590a8002d040c0100c00503074556006100703011040c0b2907003004040480e6103074074142c034182d16483d1151100820880c0380c45034030120303004c03910284298000e0b881c1d03041d400c0040380700001e091304004208840c00255000f080340041014140140014020f80d081510840114030f1552510f400d54a1114032000b0420f800d100003800308110f0000e0300151103071520f916111061280003e10340340c0010503c003810f9011007076000c610340b24082107400b61440c0c0d44002c6140e040c00564202d05201c0c5601020031042903c000181c01c0e03a001d000c144c0141c0751540280116 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 540088057 1250 540086807 540086831
    0x90112020a0c020603090a0f03020a061b210e01020313140115120c1511061f060f0201020c1002120a0614091f060e18010311060307090e011404 63
    0x900407428010003240c2441a540d0151030f103403018503480380074070044902c002800e80d035454080000120840c0586c0c85040c1250030411140140080003112108480513208a0800240141c0300b403509000c40150300d40040500d001c0c01c1d0400518010300304000d541d203082500621408140c030142c107a07504020104091001c00c018003a4410302102038180441035800e084007150302c0c42010100f11500316425800291003a0312001302010990340da112a00085040036040d41400e030010101c00503042e01820288070545400e01c40c5056a0503490911820403917200c041e40248a19500c001c401c3c400d5500004819226030000c0880d1058608441255160440b10750150f48040c040c000c0c84504e6502d401c1ea050900d0790301144d00c038250b0314061540881e100c0e002e10311880d607600560300241d40080381c0d051030704002034524a0010b51007004001e961468a9103030f01c41002c0b08246114030000404a85032a10030b0070b0031400b400441003428a036507565034003414100b00c0080f0312402141050854180703 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 540089307 1250 540088057 540088061
    0xf020d05040506030115050c190204060e0622150306021905070305090108040201170a060e0705071a070507081b060a0b060306010804020a0f0305010905060624161403090112 76
    0x46440181501e819039017001c44446e028802e13400c3c50000c103e001d0206010082c01085000c00025114480a00d81030660060100b42c40b86604405400c016034420f20606e03803545059240f400c0c00d403c4e01e22190900e05081800600f0681c102c85400c1800042d0100502c551940140811031010070345400c0011542d2050703c1500400740f02a001c0340d414005021194002c141c0703a903229105162040020030340100c0050050380580c1c00004055813042c0130300c480d0014200154100a035030410300d007803046076950480d44095482100820a80d500d001c00d0f4010701900c2a10309043d8000451a1140d11517511404a00b035000302210041c03184001141400840b4030032151a110302070501442e6640e01c0c4019111004007600480e000f5058420008031104c02d04c0184c00a1403140c0e0020540744541d04000707141c02e10251181e84034000d001d50880141c1c0c0404030b100301512443c0d90031500c808040050100001041d880604042e01242a61000d400007200420700c280098903140c08000c5080d1000c41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 540090557 1250 540089307 540089309
    0x1030203030712090e09160e150d17030c03070e0f090a1503061b1d0a06200303460e07030503120601120207020915010507020406060f020d0504 63
    0xd0160020810070300032440c03031600207000c9442d07814090742c0c1039561001c088095400b103814220316040301c400165840c0024020780c0c000c0213107018140d900c1c10641c0080a9445a0000c801e2140f100b003203804c000c00115409100701c1e000c0d0010b90a4981c42c000d481c0440c9035208a41c00000140c07007452002e99071030300008586c3c11620292450368550b4841d84420018042c840759800d000300d0b86031001000030854085c8200c1036072181c98071301200c0040030000c0d00950f04c0b059010051900c04458400c0c0e13031501c60b00942160040d1030a5600d900200034140c001040501c80680140030010030030807603600303c0c010f001e29085a20020460032000c0900c0d82002e00d400c200c17800520016640201c0c0741d040d9030b00400c0d24041d294007500d04441d0749603201c40c5181c0c03000c0e100c209858640c0741004425078000c028030500c18071040303056241c01d0032980002c484000c020050f081c110800100303e80e10780d12582c1600d0400d54080e0003000180e4403184082c1051244a4400e001841140b1106200b01c1c2b042007510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 540091807 1250 540090557 540090559
    0x80303040809040e0a0c0602030a1211070b0c040e040b04020a0803190809031201090e0601051e13090b0a2a021b0105120709090f0b060a080901110403051014010302 72
    0x41c140442c4104003c003400c41512200c034284601d44091000c602c400860350001c0100360000e60b991000b584d000b0b032aa5030b24002c1c5440d81440c081e2600100c1864404880c60700d6404060b06250f903591101110050103690086a80f1030180d4040104001e4a1309020b4000c0b4000c40e194144030340e8442c0c3d944d9403131003070101003240c1d500803544050125001d841c10300c0c0c001245000340c0341011148410900c035100b090f44107505040d15072409409600c418408103014080648284640311000d1b1071003a0f02c5c4000c890342600419071285500d001c00004e91012021951001844025081140018003e002070312030001010124081094169240700f51503500c003d8039401500100080a031240c00c1c00c0d1202d1a0541030140070080118441c0d00200001d2040d126501d601800c18207100025089072900b103029084145018258616a0748040075600004418908040555a001c5669001d003208456050081d80003240200804c4000708910556004010007004100b45074020168140342c02c0c4401307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 540093057 1250 540091807 540091823
    0x90504020f0d061e02040e09030a0f050f040302060406210b100c0503070515090706020a170702032a01110c1804031e09170105060a050409050a08040b1308030304 71
    0x81c40d11810005502840c86009100000394503242001c0d203054034404120343c054031a8006000c6c8056180446030316000108100214101030030314102401940a10b078815040c08000700305c003e84c0c40e10010856002d2355000c0c207400d444554400c4007400000070307807041c0c02c210071f600a40c009500e00d051103804a0507030300912150b00408000019034200d140c0440580745804100000303000305000300040e00c21004100c0041d07035a440c200076024103019180e00b2030303001c6400c40389508020900404907828a00080f580d9641d450b4100d2000910b800520315140814281d815504040a4012204840a90000c0c2c8500351401c4460980e5030300c90100011180c0d01410f40703800c80100e18009080142d00602c41e00784078401000020a00004840f8003000780001601c2e50014003007000807000d0f1261808145009101d03030b040100000c2c0b030304051406124000e40d618401d43c0140501046040055a000f110190b552506d41307604910503440750614003e01d0018000029407100c0c000b00300c0c1d1145801a0007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 540094307 1250 540093057 540093079
    0xc0612160e010e10020a06060b07032304030b2d060109120510051003141c0507111201090804140a05090411040911091305010c020a0803010e04050f0d0c030909050402 73
    0x200300039144d0900e0f583c0111320a4061403c00240030344601e0014129200b4569220f80c49890014403203070b9104011a140402c54203444038000700e80050740d0070b590340442c1042c115610504290840c1080d911a040c000f500f80b40c00140c41c08d040d0b1400c900510003a62003109441c0c542a021098080d400d10080141e4000382ea01c20075601d23a80d00003074020348038514424145503207885e11f0010107201d080304080f40d00025500305581103080c00d00c40d40160350341002410a40701ea100c2c200034925000c400b41c003070114103c0d1901844000e6002c0c1c0c103007991010040ea12a80c0741d032260344000e280a40c056010b160318031404030301071400b540442d105035884610544030300c18140601016081e00c05049400b403a141c0808005c5030348505101344103071003a80a0b003406032080d0800e182035900103040301c0199003115650402080882c01102d040d112501c8143d00240c68a1802c685070082c083c00004182c01100004c100007503202c0d1410103414000e030355401d0160b44429071402190001c0c0e400a50240254031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 540095557 1250 540094307 540094309
    0xa0903110d0309090509030c07060503011509030f0b06031606090302090615032805040803041b060c0311070909030c1518060c02010b09100305120301030f0b090c0612160e010e 77
    0x451ba0100791901500e041c642c8646500740760a2942e0890000b01300c001c801401291240d20b0305e0100300040780303004100c0714a5502d61040f03d00d0701c4031000d00494001d00000b0b015450411512020718100c107413071304000744e8480e0001c00003903250000320b101d100040b0105a040c541103024503103102c0c0da020713038a02d1178948000050080d004055444a03200d080601c40d4050700305803148501c83d5005050403941d92078036140a0143e08075030000d000003815040c00510440b98000c3c0c070030840b00c1d4541040200350b003d8021252514a00d41c1c03100d0941c9044c02c20800c00c069000003948020342c403c5455200042485000c2d00654041e01003210541d0041036450000c100260084a0194000e00000a100c8128000304103100011034401410342514002081004410043e07403900511003401d1905650440da1002c0c7e00c441720050242181c103888020601847d802e2007084640c0200902559031807030300000011a6070400c49030040840200c440165003907020342001d5401c03000503955090300c000510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 540096807 1250 540095557 540095561
    0x110c031206030a02100c0c090c0e030d020a0b01060f05162105040503060c1b1507020f012318070626100b0d020405030708030d0608030406170a0209060a0903110d030909 74
    0x81030580e2150719111001401c660544503041c0404a0ae03543d049030b2000d501c05040c508002d0005c804c04640c8400c003000b0100710030030011810342d01c551421044070540303180300719814082c04441050740c03643d445c000c1d010000c2003030000710b1030381400c40da1800c04220030300300342c441d400795105e29500b5401c520002041482054020f000710355542d000d101024001920051620175441542100001c0070700500646903010444003042b80d210100030300c111440c0006001c00903203e4030311550b4040c0c0701c1c1d011404483d400114030b041c011051b01150314940d0b9410300100a880c102252480520b001412003507051043c01405100e0f003404000c0000441c50401c1d1000140c0c0058800c107141c030390034440462640c0c2c0034400a0020002c4400668549114021000864842c2e9100b00c00759401040101300c45a041500c40080e100f90041c404e1040c1e6600400d00f02901c42d44a200d0303804a00041e141c2151030f00500b4140550b17000b03900118880f02a88180070074140021030160102c1c3c0e50042c1008052515 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 540098057 1250 540096807 540096827
    0xc03160f0e04150e0c03071a040b03100305030705030304031805061204030509030a03020303060406140108070302070515010b120106050307270e190b0a1a0a03110c031206030a0210 79
    0x1032000000302c0500f050006040703400c858402d005941003e50111010714080100b00c020781020041001803020204000407140304601c21049261400f2002520b854440c040110042d608002030b00d0780c031801883d10316105d505c1110214041100c112a0203045401480e21b4001d50320060b228a14100741142101c001d800010b20480411504000e200d003162400d00148241500c20380065803a420000104401d84a040e0800c40d50031107200d4150029030703800f0f00032030340003407041c2801a641c5180d410100e0510504402d50450b811a60300001881c241e04401004890600c034000f90745a43ca1700411507061000340c42503800220380300c5654000d180c80e0016a90710361801a00701103035903914003882c008040304441c40c0b414280b00b0142c4401c01520740c004c0c09094803040b20a4152582030203802580200302180c80012000c5c00324051800318040c0d4089a442e50201e04081c1d122498186029500e0b80f1440a483e196114000418928100058a11560381e0700400c3c030403455200460449040b810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 540099307 1250 540098057 540098063
    0x70207030b04110d0507060e010e0904021f1413032604061b060c031d070305030703030515040f06210c0b0a1e031b1814030c120c03160f0e04 62
    0x12004c9088000b420820a080042c5840e48405030403104c0000090101445100c1450040c030350741c001c100040e5034460300d12100c0340c03016070b180b2114503007403104440381c4d200212820038101000400840c1000c10145600403a4400c2c1030118186040c0084241a040ca980202d0340c040001c3c0018405a4083c652210706480d441e09542d52000403a00c400c3c096464010030311000c47da403498180501c2030150348445009802070028140740d85141e4030b0786d0760b074410301d2030280425540c0c02c01310b810f0a4580d216400d505c40000c1c428403007290015145e10040015100d900c4025a20022071030590300c494201511160700580c820401a00e0b004502c5810f030b1000c17410f0010800c0c012241c1c0a04400290013140c546d0596074005005401c100103403400390104070303100d01840104035414400100314008141030300e0300c1c0d44080303000c551000042803910007460041c55221800254004400c0800207050301e841000f2400c4a1490000000340c6842c0d2015018103408003410001c20f11000d20450801038020b44 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 540100557 1250 540099307 540099319
    0x8061507151e0501080105060a170d0e0f04020412030305010f0e0604090c03061a0909011a040f180c0f0e06030613171c0b0402130e060d0b0109020702010f020115052106040302070e070207030b0411 86
    0x1181cdc3d80014101d07032164024074010b03000f40351441c0508d98107109880c0508404800c0c2d0b0421800c081c090340044400900b8188226298200841004480d00d02c0f4401540d01003410700007181d0f045005080c0150402400740a0010a000030b01d006405000315128407801d2000c00462401580c140f00151010aa00b0312065444a10305010031040c003c1006415000e211030110f442d00b031040304101e00440794424600000c0e4501803109030355000c6840303500711144841d01440e03147d4a2512003da2030f51a04400c4076008045160700d00d10620840c50348035034011081c100315a00600080100300d004810144000e0f21100c9001d02a0200040b480f0303400c1613008050441e403566907a92911001000d8010004454000c1655421560010034204510310789000038046520108080e900e049494070607948100c0e44001c000361880c2c80c503401e9207401d012410a464561800e420003940e542d003144622040c468044000410840c03000c10080b0642c0c0e4030400d0000316898030307125900c90040d11039050740c1c042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 540101807 1250 540100557 540100579
    0x30b0a021209060901060603020414190f06050a1b0f02210d050712022109060f0304030c140601030312110c0d08061507151e0501080105060a170d0e 65
    0x180c222150602c911114801030680d49441000c0324207441c6158071040904d80144411b00640d10100c0d041c2420240940b00750002c8100103410a00044042d0b000220901c00d80d2004115198004010001030519445a900d0300c03c500b0800b815101308410083d0500ca5080708510040c038050724a441048202d10402c140346402040d01405e00d10304001c0720380801c000007078401c00c005a208a00035013403031b940058640b444026a201c1c054280640290491130360000c0e469a642e51100245c40d41c2405400040782c80e031800b8030f009000c101401e00c0590384604800111a62803d0010309141a00d40c580d849803210280b00104601900c00c01205843d02602805078502c1010f04014001d03007403245584090142c10500c05200b003070002e03e4040010340f0001c103d124049114101801e00039910108001001c92041a541e090b103088107206850300c07030030000001482d910541040d4003600b0211100d400340d5580d4600100303071070b00220242c10150080440d0042e1a8043c0c0441c138400c0c000500100004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 540103057 1250 540101807 540101827
    0xa050f1309290601031d0703030e180117010b0307062705030f07030b06040926160b161e030515040f06090e0c06030406021309020f071515030b0a02 65
    0x200d103107245030040e510b0710108000c003941e490300a10341c40b07050381c5100a5119150300070081c0c0b80e2419000c040e05000349050780c0445925204500c95601241d040c42900c0e83d6101c114560490700c1c2982c03101c00560901070031113401d00d404983c0702c1c202e03074082c1c88540b541186003802c001440c1c0c20300107441e0f81500314017002400b91814000d1003444403104d00a4000c507415440c10303240c100d40150500d80614513141003040000e491540001c134007240041090604121111003c0386445103c01502c03090000303007030b4002048444d01d4498040c0141181744d5003511001fa0080b0f800d0558074000a0510980d800c0072485503000368021a0060076003c2500319024240340861309a4800081110b1115aa0401084005078610441d80a4113003800506100039980c2c00081007804090700c003030070b1f0507030000d4010009002040301074001e060b503010a6480b0f1842015440f8550012401520100c8105070000c1100c1320303621415004c03013450031f10340d5031403400c40d01c4030903460000030411a2061781c00c11200d516 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 540104307 1250 540103057 540103103
    0x30204090f0209091c050705010204170a12050304020105091c0506091005100b1c09120507020910080601171203161202030c03060405060301090b010b04050a050f1309 73
    0x1802000c1c028100d030098414050745080043c0316040c0d1343c00401c0141d040c1c030300c108801402c0215a181084c2c8030740040c1003103802446664450014050f8990050307101c0c41c40880e1410040b4090b801c0481415604d0600791104d11003118000d00282040110001c11724001c200f0072191450b0fa41c0c2c05640c850075680e19031501c00c003941d461038254081c88400340006944c0c0142ca90110500398040c02161074031001c2d5081e030080c051480613100c6076100c20a440d000c03d6005034000b5030031041085800f8030300b00d03001c2e106510441d0141d00900081001030040c848644040040300d95810041509030301c1c0c80e40c0384812030022440c0c07950a0065204110442c0c040354091401032200159907201c0c041c0d030340400b801d40c00c6003c000f00482070042c801c005003055000306580e030008094074040740760350350440024018884004018a401540b000104a0f503107150302034020b4481c282e86055103152280104210040c803401d02d1944203100b09288508240d1913000000c4070b42c815104204a0310301c3c48107040d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 540105557 1250 540104307 540104321
    0x5070c06051306031b082a190c050714060d050a02030906180304140a170c030c04150513060302060307020d170601021509030d02121603020a05160804030204 69
    0x26800b040d445a40d41c00c10012200500306030071308000418401441344180100802481c080c04a294001050305691444500f811110781c18001c044041c2c55528075001d4105503516107091110038103144903d07004001c1507901d2134101c00101000c13440c1816240110540d40d4034a034122000303100204d0642814054140120100c40001d43c980c41c00c039580c4c1d440c282c8020136070342c529101c00448180409010040350113441d09130b881400c0038500c03c40844d19220043e8803c0d003010f03240d03132aa80c00f0943c0214041c03202540440584a90704490004c00c8291441c01c4a0400e0600b0f40503000c11840c6071110314007100d840e02d4400844d00503070300e800150325900110344900140c1c0022039910320303141e48141d01031900210201c040c3c182c0d041050000707640e00300b1301403902c07403010030600428101c010410580e4401100e2690966841080d10b103c0000c9203400c0e40c00582066980390500d00181c028002d50b48031108558409003000003039005442c1c3c3c401c07000c8042c2c0d42c004082002002603111409100c1e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 540106807 1250 540105557 540105569
    0x708130c090f0603050d0903211e0e010809030c1f0f111206061204080904110d06030302150f0f070c0512120a060308030105042c070302010f0906080c0a05070c 70
    0xf003051135420003d05201c0114000310800250005c1807001800224000c1e6000a034490720700e48080943c241580c4102c00e2404042e000105c42d080c10780c000350700400008a049086c0d8580c4e9090f01e4105a031030780c1e0f000310b0081c111240c01c0440d10b002242c98545410b40d80484000010462400c040700303d80031142c4402c5040101c0e5000603a4441c0d41c9100a20150031200503105549000b8103031040340004807001c1c00003440010300080603e0b00d5a215040a840107000b201087d540301190200703c401003489100407005401201100e50042d2103450310684103240c03a1780c4140c16542c480026180a080c02002c1c481400301041d40c00010030410010502c2d28400210300594030a0844442e90f522003000300ba680ca0141840c10500008011409590450350141c9001c1400b62210b1158449600400b1080030120107074510121003150000b4000200c07030003070f26045081e544840d0121038826440c019000843c01500105401190f076000400d88403400c0d1802c107082101c2030391200100280e0307602c18 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 540107913 1106 540106807 540106811
    0x108090102093c0319030c0c0603020406030f15090c0306031506030210050412021507150b040b0301060806041b052d01080708130c090f 60
    0x6110100300041c1401580d2040c07503403480f4641d01d01c02e80501c802480c10000292580c124450020004010300030f000c40301d40501188030b6500307003680e0407070801c003009014501240d1000c1045018111640d005070352280380c010700405554448002400c1c840c5082024070f032541c2169940d20442d001110302140010003510280c00a028507480039100d8450846101c550121950000054074400c40da164103401614004035518007685c058084c148056014a401610703158800d20341202c142c4c1961490040903540300c545100f511007010581c50344508141c50280340500a50052020590023044642e14240c0740c1917846101402c0544102d02c100ca0840c012944c015152000e0f1001a00c2030040031030a92258041111060415120702480f1034a0000c540c8244517150060b03032a40d030745032800e0310b03030744050003100200c80f2080342c4c4004d180800103070180d0240607101c0129800400 = true := by decide +kernel

theorem cover : BRFrame.Cov 539928057 540107913 := by
  have h0 := BRFrame.cov_init 539928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 539928057 ≤ n) (h2 : n < 540107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
