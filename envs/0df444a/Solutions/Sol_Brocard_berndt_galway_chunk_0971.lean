-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0971
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:34:44.642899+00:00
-- url     : https://prove2.me/submissions/23e99348-ecb5-435b-8b01-b941e2731766

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 174460431 ≤ n < 174640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 174461681 1250 174460431 174460469
    0x402030d09062f030f070c0e04030804060b060d111e0a14161a09010f020306090703050402040902060316020601050a0b04271109011205061302070816030207 69
    0x9144140210b4441d550751800212140400d03201c5681c0b00d490803402041405101c64071000b0400040212141c080151a990112403d005580c00c106420059544c00c21006010120703502c1b060a5170030540100d030004070a40310000043c0148509512581c01508109040c410404590007802d5204180d50b07008030070400c200455002449004816400b02c4d11480e2580c0c00c800c212800703031507445c2c11124500010a5140c86045000802d50180c81c40c14003031704200f0004410a000c0e9981084c0c580006500310b0510700001200d51500520400030541d40d1000075056590b540c000141309900030301840e6580c24505101c079a200340c8900741c8000f5100d07030000081c00b410244c00d01c208039008005000d084c0390410b00d00c03807003440000c0c10003114403d01c0d6a48203219401da100b10105100342c04200c5907a00c08040016190380f541d01c4210511a15050400085807140c5030051800c03501d40c1001a82d40c4042d00d0150b8203405038500750652006186040c030105a000038031a01514030360303002407071000760f2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 174462931 1250 174461681 174461687
    0xc01210501060e030105330f0a0905160903020a05010305090114010f05030706020f07030f0507080303070503060a090903090504020a0504080102031005030f0601061706150c010f180b04080904060f030303050402030d 94
    0x34484446244001e500044054801e943c45401038840000e114641582907500014032002031354021604840c0e0b12f209005842c5483ca480f040b488440e0304080311010708e16000102c010a8a20440e81030540340d80c00a142c035038080d881000c2c00c101d41c0b500c038210340d6101d0340e0031f02c06100c0c03a00911303000c1c1c441d1440208005000240c0224691007001c001e00042d400c65030361094a1441030f000b11928400c00c00e0208a011003440034601c65040c1e44c0e00d1980300c0c40c0090030001e840e00e6503401028080d280c4000d2001280d404880041035610070303200940c2e1821495812921449250303c0942c4c075520207c00d000f84611140310b6001215000c8044a202e02442d20307995480c0c078001e119803408074180b482c8160000c45040f0b0f0141d4031210007410041642c101122240f0b503030303014000c410b040e65034580e280090200c01d40300e6050440320780802c0c10f0200314140d1b00c03000c00c2900074201821090011030450482d41e075540101020705418081200300310b0781c9150240140109a408900c6800383c400f58009140c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 174464181 1250 174462931 174462961
    0x130303051b0301150509060a030c03050c03090d08070219060501080d1427060a022416081314070f0509070e010804051e03040503010e0601080c01210501060e030105 72
    0x424440a580b0b180d01c1d129001c0c400d5400c04a01e5070034841c00f403200700304941c1d03010b0180c03810840644000c1f0740c89811207001012168010b00301e00100d003040c424001b0b0b0440c0002d120082c40360900704808252511001a407402801c00322000e51440d030a21640c2c100306003908058100c03000c0d0740c112151420440e00640381860744424038000d660051146001d110900c0034200801b0803409503040f4258007241c08203400754001402d10002d41d00c0381d00003a010b40d04030040b10703031011004502400e40b41000000b0b4540c0201d1400d4003410040e400c00416249a042264119410b83c8415003500c1d040352000c1c525200e842e00d1103402d60020142100040c0750416049541c407660b000e0f41ca0705841c41c5c4680043d140c0c00710141040d5018400d020807040d800d001b00702915000e00c0c40100031901d5501c0c020030103094402849004039103401c003000400c204440001c1d2a01c00c22000d0908501002942c90712585002d5409080003a0398181800082c42c9a0000703603954444800382c1c000d02c141d5841250b03042c40c0c1d807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 174465431 1250 174464181 174464221
    0x30a020f0c010c020d06150f0602101109010f0504120c170a0215030a09020a0b18030a021e0303120a09110303070b070e0303040909080307021e0a06020f040503010513030305 76
    0x5280446883c0140b41c0782014162444c41040002030032910307950050340b00e01e0b03140c0010700201190740b0b0900000f601082070301c3d600d1207002401c0c006000d04078500a814000e91442606008070a04480c159900642c19200640355481d40d0780c040055900700514130041e54070030081c00e107080b42e500c84e4941c8004030300340020740d4000e84900441d207800000d80c2040d40c401800100f10703e9484030702d840140e5503852028020a03000010035140c4900040b403403054030181d00c1c114420340c8140e00c2c050051322541d000011140c0090f100600c2004480c012a05611913101a01491200c080030407010300c0741c680c40720a0040c0600101c08101040106040e901c4c403406801406001206000542452051500400100b4043c050ba410580e5480082080e00d5a03084200c401003001710411112680c1040b00a00c6a140c400c662108242e210010035120312090f90040d040617000a515161880c046048400034030015008000070304e00314218001010140340200d00007030a00d00452455034118002c01104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 174466681 1250 174465431 174465437
    0x32101030812070c060c031a01090503150a1e0e060117060f0601090801020a080402130c08130503090a0314100506011407053a0f14030612060108030a020f0c01 70
    0x12882814841e64820070041c443d80421150b20b0382c1800144450084042c4901c1d07549011840c00c84d1100208501402c5100039810001d440c0780800c5140c1c0e000440e8418100c2d000b01100c8551a880010b80107000102000605011101d012000300740040c0d0000441c0c034503003425a251641c032042561121002944814580d0f44900c0100d040e6144220405030080014101501080e40d140112426030300006954404500024104019414613a82c90402d0b400d00401c204928640b030600500f0806020780070010186a9101c0038003080010401c0b514045002449154070702d6403480c0c08590390741c4508400300940565074103000c1d41c4c421406036034000d420503100c515041070342c5c0c461b90348030303402c112026a090b1084008455000034411480c401080000c4400d940303103000c90201003020f2072950f03010410030070314003001445d4580c0104441c1008100717040c540e0b030381d44860000402507130242e28007012500400c07000081048000004003408049178080d90a181d602030303a92071310780c620f00002d03d001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 174467931 1250 174466681 174466687
    0x40504020906091008100b12010221071116051822170a0e010906020a08070f06020c060a1506110d0f020f060114150306010c141207050321010308 64
    0x20300e2034488601544054810544c807209603854140a01d0001c44010702e000c456521071224596082c811320740700712010508020b62500324000d030f5242216075191240b020015140c1c5c08280c4442c8034160044080b9041021606003000044000c204406c0501c1010b00c0348100f84254003454980b00720a41c0301d600d80780c0140c402e4103440600400041902c1204450800541d0094003042c904035025100041142d1340d803280454107400050407200d80c5410640a641c04004440d001914010440701802ea1050051800361103515055001c0c2c0504410100107010785d0007007002c050b040d0741c8142440d425012200d038185985d440f0030f40f1041000303d10f4440ca0f402850507100100c1c0103011200300440039104035001420103910250410100f138010b4181084c101041e00c01c0351610108064644107120040c80c911f042103000030700000fa0542d8020007000003420b40050070007081c0000d801000c0b0a581e400e80d200803503d000307030b04c940c010b00045031000d00700300300d6824503031441c04064160380e4441c00d260300d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 174469181 1250 174467931 174467941
    0xb211509010b0a0e120109030f020f0606040c030609020c010b040b0d02090a020315030601031104060609150c060b15030118090b0c070203072103080601020303060d1106070f050a060b0405040209 85
    0xb560380d0000490388184108210400c40d107480b00d074482013036108010000980c2e40d074603140042c44640d081d1081030865101e011064010640803813000d42095049034002192011400140e01805c125404065000d20218600900c86410b4003c141c3d55070084904001808001c0b007006070f15991400060f4010b005100062401c0701580e00841c1c00031145005074440500e43c20000345000c000343c00807600e000c03d80700030784960308041c0502800350809040803004079040281017006050041e4481040141a40c029024400d240e44903080b480c402821811052111001e1205c00d94407e1091940c2c0d40c202d1aa0034041040501c40d80d140319900840c00301f0700391910400102180c0090005981c14004d408001410384488200c50b5003104c08001051902941810050300000b001403c0c3c9041d90000c0013005040c0c2c0ea44566002030941c04910480400d5404000c103500c1d0045140003408800c800c84c400c03003030140000340307550190701c1080d0a001c01d2100c4414801601c5003604c000350006455000300d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 174470431 1250 174469181 174469199
    0x3151f0e13090302070305010b0d0f030c0c0305060c0c0c030d0801030213110d050601120608060a020f0c060106051209010b13090206070b2d010b03070e06040b21150901 74
    0x41050007000c1c4040050080035010486072240000c40141e8410302d400c004104082c01044400310b021034803017940300455110140b81051441e0700070200202e01841204005060300c0da04040d42e0040200c0c1e07840c0c50045820036083d80500941e40d0b2621503038040038113514000a402c203030340390380380e941c0311300790740f0715420b00040b088440020002c10342c5031421114921081c8000c1c24002c802c40c0f60215a80c142a80003501c03d110b00402c2009942c00e0040900400e580010440c0c1c02115030840141c0c1c800c0d0380540006c1d01d0040e001c22040902400000040580c0d114000d0f001010940c80391401d01e0300c42c4440b8500702c90281c1001504102c41801400401d00ca81d4000040d00d030001d0010341c5814850341e82c1a0341c40c44200c40103942404407500e22405030882c13418004043d007103c520305005506280c1c2c00101c03800000d1441341000102c054014240e200d64003620010403120074581d40360341381d44c0c12420a01160351300001b40741c41c28000042201c8080001e52248260141401c411a400d1020803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 174471681 1250 174470431 174470447
    0x708070e0709030b1003030305061e1002012703020105180601060e04020c16090506060a200f06010905090c0405040812040201051c020315030a03021e0c040509010203151f 75
    0x90001c0c449090302c00400314040341c066610030819041000c120a080d8a0040c0071100c02620b4140180d07186052a00c120f01403803411004118101c44900d900c0024a0f4101d002d040d0704929044c40d0280760407005000c100c6070a81004e0144039400a100d946d5411100114587c0c261000901036400310b030041050706d0207000980320104001d440940f40c000c1c03424906191422030301c40c80d1900c4000040812220174030b403150715000b2038202c0b20545404200d49000740490408000150b4074800e0801c02d0340808001c0095800281c1c41d074081d00d01c2507a68140c8040100000c40791200c103405005100c0507149800e2041c9440b03903034030131030b500d0030b1031080d02d010846540000c1080341805410402c038443c2d44500c009824800f0314500b805a41d074507009030708180742064030311030364001d5101c1c1c41d500000980219020107031540c5e6070b140203107010304540003605d1b00302180020b0f50010b00c0c00c2c09000d28064190000c40c0300302245547d03e41031812210510000740403071080104170305030088005084912640344 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 174472931 1250 174471681 174471691
    0x111c210f0810030822060212040e1005030118031b03080a0f110408010e0c0a0b030c0c03071e0506060306040201020d030e0c180f0c09090406110c060f01080f0708070e 73
    0xd200e01c01500c99071130521030b921014401c0c103503451000e0840a84e02ca4602060b010303062510181000b0341040d031050019014074001c2c40d6142c140500016211710480c0c0d0700000601c0014001c0c005511a0880054000000d01041e4000360100c0ca80c0c4400708110042c103c5001e605035140b129607643c00106100a101c40140311807a241c80c0c080c45507000341c3ea5406400a07100c100000161780b0081400141381501c10110300b8000c1d81111f00c1000000d01000036039510411882449542e02d2800f20003d040d0701ca105001064919400700d01910103100c403c00b00f00551050084542d2912407808043d03607020b0485000f40140d0095203080c00a61081c0c2000e074280540104030340f5818007041c006850000080b0800b40103403d07010030840001c44668210390803402c4400c1452414800001199a4460007400601501c0e115074114019801042c00c850f000900c110940310350f8141010040700c502e10030b205200042c864400f100c10b101b2404194a0121428540204402803415007103c15010b00280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 174474181 1250 174472931 174472951
    0x1170607080c1303030509030f060606180111010c170c03040b0a0b010c021305040303050c0c030d020f070206030405010f05010b09090a11040e040605010f12020d0f111c210f08 77
    0x890361003d0203686001901840c400d032a0750752079241030000c0c145410408a8910140e6108200f0b100c219200c0404440486d080030400182050319080140e03000e402681c40d00d481c039880c3c02400d10f9199480302c01c00008120240c410607250300c0e11101080b0a010a8801030407014100011440f000000d46c0100c40164040c10140c82e0060103400207224040c3e820f4124440a0b100c0c0100410168036110711540180800185030404514062180d503a0282c0c800742200b0350781c001025220460408141c0b40640c0d030042034159203140501d4500c1c00b910099075180e555030b090200100b5610000c405035401e144010304548010750f101e00690004d0b00d10011241303400b0000b00404282c603104c101600d442180110804119945018440003011009070f011041c2604000b100d140140d85502c4007480720380e04840c0c0c075615070502d404c210400c07141c2885081d0380309084000303c00b016012001081050350080d2080d08501c8181d90000c0c001c40314801e5808001840600320b81c8689001d41c101e40d40101c2c2c449 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 174475431 1250 174474181 174474187
    0x60e060d09230a061b0503010e070201060506030414060708011211060c03070507060f0e1503061219031704080301030209070c0203100b121c050d0b040f05040b01170607080c 76
    0xc1c01e00742c0c03031810000d48140c075004440d149042c0034080c05822072044031400f030300c0d600041d0542c005103240018082c502c03081c02e82c1d40204075034600c00d4000c60041c0600408840d604e003071610300340ca00601128819907050144200142d416801003e1107030481d0b5448000d00d0001341551359400820b41800701c0c040d8402018060111081c204001400c2c0c058800e000921010742812005460145503070b020900f040300332485800c10340c941d225209609484840080c6d140d899a0b0700040650f560203868050074814030030340e1220351000700c550188280c020303101d45151000f800b82998031054219000340134801c0c100010001405c001c44038a034042c1151900c90403030445607000038103007511401803454440c0c446540130f078030340b0b0000d149001c050080d44c010049980c01c00316130807001045060f48820300c8004141c00d841584540c00103200c81400820811141542142081c001c0c041660151280e50f5850008164082440c009041140f070b1200241a99554058129602c03a0010301d499400381082c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 174476681 1250 174475431 174475463
    0xe0604090c0918020309070e04020d080307020c1503070f03020c0a0803130804090c090501030c020a0b420303040b0d1512030c02120102181207180204030c060e060d09 73
    0x50340f41c001e040d2201110140c0e5901340f04103039520f0b003120f0741c0000308480c204105000042ea07031940e110f079a980d4003400c0309459680344201070382000100b0002d00d0f0440d00354602115007259005c021442414181c44e840400c4080c031004504900510101102d298440c009080c04914190061a40300314445044a0760200d40e90360010641c000340d005c101e0380d80d1100d004120044d04214000007900e1b0031300c2c0401151325440301c020342d50810b20b000030702518010000715104443d0b02d11140000d0b10704030710003040305401141c80b20140389180c44000c1060784400c8856624600441106e003115110a101802c10031445210002080404400c43d64410000c100080c8010a19903c01c0500d0003030701c9440101d4594014030404415400003042d072a40704100d2001190600b1a410b8501503042d14001d043e1280f0052640c034003d1181c0001c5400f01480b00481144441c0340c0081090703e201d4219005030680d5000180c48160726250000d5009006203c1140e00d40900da1041c10824001c0300403507406400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 174477931 1250 174476681 174476699
    0x8090d231b01140609190b0103021e0405090619060e060405040c030509010506190b480102271f020a0212070b0f0a020a0512030609070e0604090c09 65
    0x50080c005001d81d444507a111121043c0700805640180103503240e8920b03140945584403d440d1603500241e11980d50a1011000d901c29419a180210000081c407810005030b88145420b4015100d6640300e2080600011a1400c0980440366140107400c10119403070b04116041d54055114035400f80c10100a000000b155a034030300501d000c0c400c0d40e84000406090100000e429228001c0c1114015941e807205904c94081c0c014080703085440c43da58158440003c5070103050050340f17005030103004203c03070003103440c00300d06a40104003003404448a200150600c030307600c03a09070300946054103040c20701c0d55040003d1003070b80c40c0700000040340207050030007018864403104032009011450340c0060b48002585000c60034029002c6450208200c0280011460050013140c24803070801d120311080b001143c14840c49000b0024100c0455100c019184064840c805000d03140e002142c441740f01e44040000b03e14008d0103080101c2000c4030190032140b40500b00860800900b500700700020800c108840700140d5144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 174479181 1250 174477931 174477967
    0x516050a060615030b0a140102030702060c010c02100504050303010306180204050c03161112070201110607021b041526030c06010303030617030406141207080708090d23 74
    0x441840c00044650400b0201401c180903e00d03000149403404602c03400b0395540c03282e00340443c0c0681d407112000850040040381035004142000350401c0010034281c40000064002422030440c40c2e00700d600054403d0342000a031740b002e90740034020741c0080005001099040c0c2060708440720a010a4240d00ea080c0d01007000c039030003150b4280140c0c00100c1405800000420625983c5015240004c0400340c02855181c8807242c4404c2240580c2000070308004590240b100c03081003207401025200c49140102010352201540400140b84500724501092240707020f118545040d00740f50b0003814240c0c2044031641000700c0d0030010b41c0390f803c01e000c01001001d00400081505400e0500a8803c0354918034001c1c0c255031080c1c0215802001c181d21030b003200716000007a2011160f45192010020280a0307500800384200194904845580c00802104a821100c51800703022680d13540903960340c41000c45070303d4845103400b01d03000030101010320780101641010300d280501c2c8146240d20b0100110880b82c1101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 174480431 1250 174479181 174479183
    0x6030b090a0201110a05030d050a0908070f0b010e011202040507120c020715030e062d0103060507110309180c190f090e0c16060f1a03120f0a0516050a 66
    0xe885079500108650b40400d0441600b04410000c01c031031040c5a544540b07a01a080c1c1d54428140e890000682a462503001303030134190b4001804030b664015606100b00f40110b00c25040e41d8011000000207102c1c0d0b151981b450480b4903240509090500c80e03800c1202406010b001801040207041c80200210014880c14a0010164008040241c07034103c0300119019251a03403800d040c90b1000c4061108000300700035a0101e00c03906102a040c2024130300221030714a941c0c0030003c0310202c200200c00c00009500250051310704c0c1e10385120b0140c00d14041980d03442907602c000d0f00107040c0e843c0d200700034008503140d5420034401c851190404842126030011a81c4000d1040c000501d0000ca1154103074005d005240a007404c0c2503030f003d152400300d1031100a032040d140201c004690b032a800400b4422154040b1440601684043c006250041072060303c0801c40100148280a0098004600342c0d4201c1256080b00c0d2400910b401c0049807441940c840c0c02c00380c1d40c03001c00020341c030300200040c200b4070000d8801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 174481681 1250 174480431 174480433
    0xa061d06130f0e04330501030602030a051324020c060a02030414010c0f050714010c020c0114120127060b0a110a030206181006080307110607080d05060406030b09 71
    0x1861511280405020032944402942c2000300240f0001c611600005c800f484110280c01c1c141c00c240c0e9503001c5440784052145003010b0324042c000300400074990000c40c040da0965600740065240e405050381038000002004242005020072440040001d0041c4107280b0050003005040041d00d5080a052820455001190070303400010441007000b00080c128120300c0c41c500801c100d140001c0b014060601e0003011000707011001c229681003004c180b940002c075141010081c0960402c50310f020795141c5607107409501040d107080c420244014114141c030b404069031403022403903920780881228180391030b14480d000e804282c070080411015a01800b0000d2504005155032581100c800a00c3d119014080d141980c20a117180740100342d00081664008083c2902c48507005400c0c0c01c043e2030900c818601002450400100040106020010785606806104030350509140c180030030061384240c074030080803a00180f11400c2e01101c554030003030780008040c100094494480c1c4a1a0501204032121105 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 174482931 1250 174481681 174481717
    0x301020403051c0c080d02072406030308060105120a0b0d020303040e0a060509070e09060406210b010f05030607050901030906051906050901050112020c07030812071b020a061d06 78
    0x74203603008034007011208a190101101e0001d55505d1100e00c41c044908441680204104042c4038030300041790100c06610030840702c030465100d9908054841c0e40f000341e01085a0000003041540980119041480079070f500d03a0655aa58903c1e10040c0110a07085410100100329080162000c10081c000346c0b1984a0031030092601c0e591101c01d44405401003401a154003041c05030a58101d048008078030811a21402199600b001060007003995a206558400a00054141d0655a0300b401c1d400c0c43c3c040c0301c07440c0f450b83c0c81f01c5070307614203101500c41c80d50954407100020316070301c0c450809018403840500d000315605030b15480c0c100030380f241903d80c00d1102c1c1060f14181100945881207000030700d02903950095541c54100060300c0b0801c80e120103051b2540000d40d10700d0220303007400070230b02a60384004440d8680c041d0001000803290212100c80214070501d1143c420f440c10088240b4089074001c10804d40c050030944101c0b01d10400055075001e41144021324250303555000b024113034001c0c82e650301e489 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 174484181 1250 174482931 174482953
    0x50907050a1d100b03040209180601090209010e0414061017190b01080912070507080f010e0f060603030a110114040302010b0406050603012907060f051608160f0201060302030102040305 81
    0x155101c0152040d00e400500143c10445114044260780e48190100e407a000d10303a5030503008014030b13200841018503d000b140300210f0740e5845940600b04038038080c2c1c0c40124020440d4207101c221880007003820070310800d500000e0110301c0c090200840e071381850303c1e10482107854000e40410242044d00c500041c0c1d0804440350300f11810600c146603100c4024030700300801341001481103880d60f9400d15036804000000a5101c18488100180700082061104450031060980c080074001c0c42c442400032018040c035844a40c3c86c0c000000c00c64001c000c01005186448105882910030600c1d401e5014541d5417a902003900644542c0d415034840c43c0a030b0004a101c10803007041008a91507030b045a480f0f290280014448203c44085d0042c1141c51080c00803802ea070710700740c103e0140c00b800f413004103043d04000b003680c80c400c00750b04403c2c080c1c1401c8050407030190921900355001c0100f1681075900c43c07007060701c90303007513030311896480c001e548041c000002c906850340c02090030380c0d203d0b820a031020751019030115 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 174485431 1250 174484181 174484229
    0xa05030a03061403060f01092004090b0103140709152703030201050709080c1002030f0f0705060c091c0212070902030906090a0c09110d051305120f090103050907050a 73
    0xc003c118040c10036403405800950b0030031018001c2c1d260362662101200703081c0c03042580fa01e04040303000d00354030380702e42e1303986181806810b41203801030001e0300f0a0300550a400040a40d80e0082201d40c9a00c032695092090002d082d03c1c41042c0401004803a0024010300c901c845208200b000300e070380c220f00c0c0311402d5080103400c0d11800340903082001851070080002c42d2000c900c0c004403140443c0c5200450034008001c030301d0340c0585000b03400072000002d0704a5206103908000c03d5420311540688035140d8a07044101914001d1f1440305820100400c107a00102c294181131001d00d42c4010301c018030018003003030364a10300300c0246c2004051680c00800d02c403150404003c069800b0414200410800b0600e44c2d500d81c0380c0240c4e1061541060b150f444c00d00b840d1113400c1c1610002c041c1050100302c2031500ca840d6902c0c07442c0304a000e88090151760384030580040d1080443d00341640b1030040c14545501e55004500038100113000c1607640c0035025022555a4074819214000d100004025880304d00e624009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 174486681 1250 174485431 174485459
    0x4060608090c011d010804151103010602070503010618050a1d01090204050f040309030213061a0d0b04050c04050d0807080c010b0913170d02160c0801140c1b0a05030a0306 75
    0x1440c184004d5000340f030a6542004421075a02c0c00a1820421a440c0e80c900509883e620040402900341040c2102d84818a0880954100c41c00c550841e03c03220350390424182242c0c01400b5035404200001c01c041c07190421504425040051a100040c3d0880c28130104041c1d8124501c41381c3d9141d440e00d4440c02507203000c2c0541038000c0c245100065241c14250f0f0003920550b002e101c001e01410040000d00c800c6803244d40640010002c01d0780c0c0d40b840e60b0608a80c4d48440c2e11011160142e1440c4c1130605066040ca1310545104810001909140c681014200300281550006c2107405004c104000c500090039900030b060440d02d040004940e4140240401070175000041c24200000f000301c801402080c481c00540481c07130101c884190f912464001d91402070304c6481809100400400038100030056900408002c907080304000b000311030240d10020180c400141c0c1d0348030013010241300c48aa21015079503000d111304169011954001f01d80d035203039030958001e030719510046aa00c8004000214500716a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 174487931 1250 174486681 174486703
    0x801021c060b0301030b091c090e070e090a15091d07060f0f030c1b0b04231c0302040f0905161419090506071103010c02030c10050601030b0406060809 66
    0x400d2001508040b642011400305101c060700812121011032500c1c5414040c0c140c800c0d41c1865141c01920f41141d001e840020301d88566024002c034800000c068a10a04212400402c02060a03540d51650000400900284084040a0160b40c5000a41c050082c40b51111010251034004c9904291810803030414031654401d80c00d1101c06510220215884040000502e180d03090000782020304400c01c03901e040811040300d5114040443e80b40600030740303c4039140710ba841290305035030a00102000c2c80d1045c0c8500c88040706503200b21083d1010048142401d42112041c1c58018201a0f40711100104d629041d88680f08144e030ba0010b0100100580b0702c004010041c0307081403a0401d9400d04d802030703030f4410420030458000402e038041919601c0740501c03c000b090002c1003c0c0e214030742c3c0d0a0030305e460805040307803511a42c80d04a00c140f20a0000c000c1c0c030003c8004002811748d21000070482400341c907004181904041d074542458007581c0c1c56100e001c000c1e140b1a9a407442c04e180c8050381914040c0c001c08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 174489181 1250 174487931 174487987
    0x1c09020a1401090902030406060b040e040b1807030f05120301120c0609031e030314070f26010314030904141f18021b0307050c03100629090406080102 66
    0x1641d40d98100d480c1e9012a00c0b0040016503030707500c6040010003408036802c00103020f000000c001944200c80d6813600d00580c000d070007612807516868000c40c00e8003041140c914050308000c0c01000032595149801c50414000d20544041460141c2041145c0d03000360404514903031a9404039040c000c803e49120b01401c02800d22403561411034598106d41c0058440d2129000e03400402070003054803d0700b1404d042d820080908407242449030700031300f006001048820024907100d440c403460303420307614079420708a8080041418603401e503124844c5411802e50010b145101c00c0050b4012510780b485880d05400c556503a04070607080600311000084944103181b11641810001402804410b007210b6806005030080141d40d50341e50200b0001c42444079507103103441d010129250301440004290406156402c809654900d05010942c3d03040300c1050244c03500254030025149141c203040c0c0385d421221081100318504140c1c540f400601a03949641040016940101c6c0900c0e07031041c51003110b04411840a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 174490431 1250 174489181 174489209
    0x50f041a06030307020409110904030e0f0105030f16090806090d03050f1e0702012409050708191e0203070f18051318020607060209181315021c09020a 66
    0x180000e50f03039010309500644a642e40d85801c44c00c00038010192016810003811158151620742006006d00c4e0480943d5400f8010400d0038111540c0328400301c0f441503001420a1041d42c98010307214022580800204090040e1058081410107003002410310442804c0020b0202d07881020004094440140c00000514000400e111800e20030070020060303020100301c0c03140f0b13554518508038007614030041b5104440b07100326a18504220400c1540e0207490810301d05210503103032800110b03610402201e08041d4501480061b00c1e078420075402051400e007001c280901082000e0156000321703801a130b240808203171030740f0080500079000341c45541542103913400c079a1524506804500403400188110300741e11b03554800402150324001d0b0000f00d07241c014001644681c00741c5070010081d44111000c61041440b940c40003019400e4495685c40760903001d2020400c0340d4955039846046000c1880c0388055500bd0090004d20700c20304c0c0b907101698100c0d11010a5289041c0140000305100d81c0044082c0750600c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 174491681 1250 174490431 174490441
    0x90c0e01031103070f020309120f0c010906080f0a02041d04030905150a050d0204030c0e0415051504020d091e0b0606041d0c0c01020a050d0e0d02070b1b01050f041a 72
    0x50b0054036400b41c03107400e00f08007180c19050100d0951280104880e8801c01c124450510080c00090280c6090300410884d501c0c1c1001030015034010b40b00344103410000340480000f80c2d901d0510004560030a1403c0405402c040e02e50f4801401d11008141c2613503c0d09201d400c1000b0304d5031148072400146030a0b20600450300006101c0d007410311450480d078007808000100352442146940c116001182c200c1664004652a440040e603c400160b40c140c49a030440c0c0e41282000c0c4551203a5406a40c0d032010340191051441c0078031003c1c0d045102c2509149903690010f002280180b0396100404881200070010320341d6a2600c2010014003a28181c002c0310103000a100c08610018400c80c42d414400b8980500d5840460f150090303c40c15114030000e500101c1c03c112282e40000180c800e0181005092040361004e00010390b80d1560107215800590003a4410010075035164002d01d0185100c2032944c40502c0c01c1c13150107080d640103807481c01e01800468100014000150310401700070800103184210390401c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 174492931 1250 174491681 174491711
    0x41415060906040b030c0603040501090b010f211a0921070c0306240f0e1501020706120b0409050a0201030c0c050d0e0111100b01030608010204060c14070f090c0e0103 73
    0x20982ca01031039030780c030342c042a9a50411681c5013800b4000c10310343e581e1505191040c080c0c9050030301128030b1103200c000416000e941540000684400340c011021031203080000140daa60260302c207482c42d410b1800604460740b070760441c1e588200c1a100040c400c9401180103244100d403044088020507c0900000e0001040c8200c05001c07290082800f28188003101101000039101e01d004800070540c0c014001b55004041c3c40c904100c80c1005d0000c0e5103a0788103100500002064801d041c0140c000460500c003c0f40a200c40c0c40d0084150200011501c2400002c10212007a186040d600c03070380a1102113046680c035000d0303401144040e180c0a15451420b40e212036076070b040464498240402d050740d4016a0740f0030440840c010f03000000300c4280524600d0b1580040c10058107d9000900b8218080303444001402141c0803030700c09582c0e40841d04a5926684141e0b00003941c207110502890400017261080070000e14050301200b40006058440c05a0141560f8034141c103040c10316003800003103070043d50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 174494181 1250 174492931 174492949
    0x60e0a0605092a070201020114071706090402030303040b0c13030516050103090b07080703020d050103260a02120306060c010504080a09120b04031107051002070305101b1d060304141506 81
    0x12003280c192204e00a100603805030141000980c03504490004002c2c503240e100114805c40c103408070f40000540c03603801c103000e006038007110040d41682c4204085070014000c0d1580c540c1c0003810a41e89410420018100c0410381001d81c07050b01c00d40d010200c2e4600e0301400031103000040509080c2004040d00d2955254000100107240c1018040c8080028041078040d070102c0b5090300700d5800c10091503840703140c640c201c6204458180410142c0c05a0740c40c278031900104480d00780ca541d8004181e00c2100d00c2d1b1650b19584002c100d9600000284240c00b540c5c4000d0141034004c0d4403810f911500d0b406960310017860035400303a1200c407030907400c26014004a91241d51468110341c061a0030041e013412004a249031007000e5102542120032000030544071680424036800f17407881081502c0704d0a0f450b07001c02e42500c084a03032005911220700d542d60b0540b0301840e10420000c2c0e46081104a00036035200248454101300c0b01515504410010721120754812f01c404000c1244842e0a05030750306080300458a0b1070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 174495431 1250 174494181 174494251
    0x20030c0a060f06051c0602071506030b0a09110d02030a020307061e0e0a051e0d0b010512010207020306010608060111030f07110117180c0607061a0a0b070b0a060e0a060509 75
    0x610500d04c05d0040c4125601103864550b040407250405962001600c0001c0c001484203842c1c1c002d0141c0480c0c218440c901070840e80c0f0380c104103010aa14842c104102c0d508408030401c80e81031017146005001078070148509030080c0750a440e00310602c0c0704000385e4140040308500305c3c0c0c20051050040070031a914280d141c0d040d1760003955641101e10392140c0c10665003501345141d641c0080026502001c002d4181426810380d1020b440c13640721000004450350903130040c20300c000c0d41600003000502c01544604103c41c0e00400525201040c0802e0b60f480900356800101451910540001c080b41401892041c2e00c180d01030a107007001540d0541d001d450b8000340082c0900c00701d1401da040343c0052103420032107070301802c000a02d601e43d101c0704c602c3c2000040c080860311185a036941c240c009200d161800a15044030031508100745051181e0781c034a030420300010480160503513214000310390200305081d0140300d0f4602078000110181014100010814000e00207222084245c902c50109004a02c043c1104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 174496681 1250 174495431 174495469
    0x609030305030f06010903020414060f151206061201090608061b120405072706090e060112060212010e07140c0c0402250312050609060f0120030c0a060f0605 69
    0x15212840102d0700c1c1b5aa44d880654081c1c00c00407500d502d0b4000400c180c1c003c801c2111070400a66001c414024500303411448220107220510a1000e4444503890040c0c1c0710308010515032910450900341a4640420b030000d10140e55105002c3c0050758003045100c0e0060081c500c00c282c1d80716070a07012401441014008015401034101003001c12004010380806440b454914000d80d0120f811161424144000744515003810f0200010b0307911528444c8038030303a04c1400082c0c6030036800c000c5101158241c281d01121000c0d800c0080850400105c20001e010780200c4801c40400c0c2445c00008000d644406182c4003002c0040140f450b001c00d00080044520900762000743c0c44401064802d038012001401d86152418002040d000b01603000d544c03c802c1c501c641c00200a651100d00c103000d4152021980190801c1035420140283c0d030040001c41c2c01d600d0821030001d64042101001d5003950003010402002c0c2d406091720f98208500d500404c5003600c1084010001c0030300e008009140824045941114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 174497931 1250 174496681 174496711
    0x4020a0909020d02040c02010b01020111090d02100c020d03050306011101060e0114060f0309010603140703170705031303030e0102010c020a1a0c160507030201122f0c010f050709060903030503 84
    0x2103403a00400743d595207400500c00c00008824540103806401c00c01a0240194600b05c021000001010180d603203005001c2c14024074070b10103078240101c100d580582c41003802501000440180d8038012a000c50510a51b94540c4904040b80003414071009924404c13102e9041460500c503e1100c6042c950449145200419010024001080703031071140b003c40f9010382d10008100405120150814400c5030b04c0303601c0e0b03190120406180e8540783d01c050f0000600b864103042020300350f94802000780074224054415649080c1410000211081481d0b20403808a450300e004c0e50019038083c0308000380c040583c00500400240b56440407581da201c04030031b20380d11414001050368135291a09891100408076410b000c0b008690a184c0e503a0030340342c030080b40081c0030440c10b4201d04030b0314000c107881d41105108852030420319945042c1c10b03174070003140150104018840b90201c030a09004200c103440f003603080050541000038006000012507000f500601055101c10000643d000d0100c03a400900d0703030040f0304 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 174499181 1250 174497931 174497933
    0x90c060901110106080105060a0b0a1202030a02250b09010207050c040c0507020a0e0412141605010f09150c0e09040b070c14030316080601021005060409080c03040906050904020a0909 80
    0x21070245007520b280c095840c000340441e8030361055210301d002c1c0c802120040c26160782d918410107a84100c0e02c0301000100170b001e04030241a075a0300510b0300546015805424140c400070107043c000300050424907403602e01081031091000190354243c00001550003940381012540b610f80d0b4074582d00300543c0c011580c035018240210721400a89820340e6001301046049a61004140040d982c1030b60155449480100e0342c0c0702c25401000c0603804801d140e0105800d040d90200b0085c0c1e100388070081500c1a5484d08495694004503204203440d10344141200c1c00f48180000c0858100e95404141100380007905501260030754880c2001907001c0d41c4a5010206541c510b58200da141c0ea6080c80141081e900580d0303855103000110180d44103c441c0440d032410944001e4089915a00a883d010b000d070b0000c440f42e0b40001000d07000207902c400060401300c0e4203000740e940e0000319804800142c0a541000c0741c14099894180174140040c141241c0c0444d0b14149a00000c44200d01841802c5106941e8642d2030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 174500431 1250 174499181 174499187
    0x20a0905061c0e1b0306070c02010c020312030c130f0f120602090d030507020108060109060906030f0e0a14070602061905180111030105030f0f1015171c08090c060901 73
    0xd9107451042c0611042d2031440760b40d400c0d03072403044c00428012224105090070005500340c41b80850b95108101c5c42407607001560504000c04059030103001c0c1c210b00503080505c41e0020b501500145400a07550140031107202c1c01104e8540002d00c941092120410001420003041e20a48a20010803055014523183c4400248202c0101342d4000100c80d1440e414140c1290290507a14001c0c4c0702c0c0d40c5256911001150281c0d02c0f40510808100c03018010700c5100c0c8283d0200c0c040046100b80000c1c40000c0909503481d00b668044201e40c644071100e45400d54120511024000b03182c5400181040d04100001004800207105100c1c0b1030395403840015000002d00e04079180c40007000c4001c01411004040d08460380c0e109000b014064800d2803058007100b4800102380a4100201c030213041a080c0003144280a001c0d108903800d080c110b0608042048020118902d1a46201d00d00609a0400300c182e0707980c21054664240080c440944d041204100c40443c10944102040303400719a5005640d00503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 174501681 1250 174500431 174500467
    0x9080705180c031e04060203040209060405101a09090c0a11030406020c06070c0b03040b04020406080f1f0b060c010203010602011503030e10200703020906060a021902010219060c030609020a090506 86
    0x103841c908501e601841306200c2c440d1f0096004074020f0764500b203103a80f88024402030768010b0b40d5840f039090900700208800704011601c002007410b9811001c0c540454140050f20607501a20002c041074400200300800d1a0801244544ca841000c00356041134074000f03019488800070705403980a02000a4440d0800c0503044a181c09005644625900c2c1d040504050200c0308040705d003207004074a000404500c034800010405809116a80103000c055104d15110780d0105000054901898885003403544c01da5801c4080d101403842c240c00180c4940c0b42035002070035540100d44880364558290800c0c4080b076400412483d2140c0c0a5904a00901c10a00d04403403e0310030f1480140c8008403094401c103001c10224890046074001c47d8200c0c25500e0307400400c082841517a41040140c5e1000040c0a014028040d03180d8003240140141c03005088040b095858041d0300800880300c465881da04110b8258040c41000003421100310118101264148081c10003007582c050203108400103d030110b1039500003c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 174502931 1250 174501681 174501721
    0x60e0a0b03010e0615090d0f02030a050303160201050f0402010507060e0f01020a0306030c05030304140d0507150c061a0a06050c010f0606020606090a1a092509080705180c03 76
    0x1103039580c2c1da9100200c10560700305950441c85489041c0d811041c28440005580401400400754220400565500c44a4800c02d190803a01402511820401301d00b090003e540325500712080ca61400410240003803c46d000140340c1c400c84a4005d05010140c1d0380300c1c06854030b031940150006451418414800d103004142002d0a0042d80009904110b0f254950001400c60744a08400181c00b6110410180c40b03018030b000d551034131403101107141d010f840d0400c10f40c0441d07805601590556501c4840920501034a8238658022401600d144820000b180c4901c11001280426140c80c1d0030702903000412030f0446224080400c00c0220342001780e90401e41c083c45d8092020882004100d9403524042c0d200e11080302c14074801c011650002c3c082d95400c1c014010011003028000c0c00288030501008803080028051100e00138000b0141e0000543e25031a881c40821036407603810f00c407441d00302010302c0c01809400150040b000320041804c180000c20449400050001c0301607141d0751072a100303084294080f45 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 174504181 1250 174502931 174502949
    0xc0c06070e0d1403090109240309031e08150102010b0d030807030b1c14070f030803070c020405130204060503011103150102030f21060409051906150b1206040c0207060e0a 75
    0x1c0c6001002c03c0c000010032904000303803642c5504a5803840d801a400b080003200e0650f40c0d60804030040c00d40d01c80e5006640061280c20101c2070080c108007004039000300000d010f00414030080c01d121b1802100001c0e502140d07824030080c00720084910201c1c900c0c0200110007002d12042c07201144c0224003031b8000c80c423030100c00391440c03031000c0402c0040703810340024900030f44015100040d18400044086a800203484401c119540030078a1503a03581507031741c00180708004000400082100507940c43c09542e0140c2c060302d84c582c0f24005a0300410088850f16441184a0b0b85090329880e0425212800d80e648121185c807006030071042200181d00314480c8224105458000103035203410101081c05030109055403004542d945d035508002e00c8201c42c01441d01801c90f070b2025095603d8644445254004541b04400100b0442078401081c103400c2007039048400c041a0100319000b401c0790843e84642d00000c201c805120940d0b64030000781d02c0343c0741402241c0070000b1204e07d9400c01d480310000324009001c00d031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 174505431 1250 174504181 174504203
    0x10020a020c0f04060803030c0a120c020c0f010e010c11060c03030c130f12080c0a05070b12100b04230a03030e030f0d140a020c0306010b030f0c0c06070e0d 68
    0x418025201c090a20110388101c5800c1e0703110515007080d00c2400b059602800080d480e6449114074042c8981243d08001c04000c04681c8400c004000d500070500302c030b0f01c6600140074064081082008145c01118054100318040c403019a042e82c0c400d08003040160800003403011402c1c0800480d030140300f01c400100c02c0e03100c00000d2162210000c0014408880f03825040b0100b580c86000c1040090024030030041c1c0c00395250440c03004520581c00a14404070140c0032506002c50995845007090010780c4035070340c0d19101098091080c00c0c003100c215440054030b5034490309141000c5107001130340218021700d210507844103000031481001e20300e01e1400c5200101010415590783c540107081c1d0030b0684000703000c0d00503e4100c920000c0001601078103010551280040241880512402500803000f04070071441601503840c1182c40901c01c89020301a120038142c3d680c945010300780543c0d800900b104004c40420006024181004907505401c846180380406480040b00d00040000050000140c2060046 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 174506681 1250 174505431 174505447
    0x608070308031e0403021b12070e0106020c120a11010c0813030303062c0603030d0207050d090b0708090f0604030219260c13270606090c02100e1002 65
    0x1000698820000c0703c000d26240181c1400b1036050352002d50b8010301607804001540485000c24010035030562024140c8800d002d140041c281c50503109500c8804044001b40c010300055906002110107c4401c0e9007600c0d02034040c0d0042a55010070180c041d208201c420300c81e1004e60f10626045a84d079030042c0400c0e441d03402801d0460481ca00504c01200840d242800c001009070144002a005d81d400c4448050004a100c66a505c020f100421080d40b60004001107008070b0404c1c40940b01e907900610051041001003400035003607043e15004002c2c00b0303106100c1440058141812110070b500291050070707054140340d01281c00b900803074000941c40f80881c503160003104600b204050072102c9071800c0445542d0000310522441d800e00e0414600340e04044828082401c111480007550040c07803000140241074501d45060099400d440742091441c03540102c0b0a100036130040001030082076034100020484d9030b101030f42e034400c069a80d00440da154202c40e410281c0612030403144200c8807405641e20311807 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 174507931 1250 174506681 174506693
    0x40c121505130e0c1906031404030c12051b030403060e0a0f0624060513090e0c01080c07080307110c06030f01050d021809010209040e010e1f0e1b0103050a1103070e010306080703 78
    0x39001b0440041c0c50480c00800000c0c4e404d6075980201e0b0181c5985505481075110000f004840c4001c0384140a0100700c0300300039404802c2401080100da40103180c0341d50561a01005480700d400e20700f5003640c4048115000f00e03e021400b01342440d07020400240401c071020441601110a42480e000340316110030000e01d180e000001000c0c0c20117007252602510303031141a94411251b08015061090b84001080d0000754002c0c11800c0e00489403001003410f00310707903550341c00c400d0380308232208030026420b44c0c2c410414400030029021181003c980c590b00752300d4007645c1882a1641481503a1040807441051829503e40f60060300000700111440030481c50507030000b9010794007050b0708a0059160100c00c0c9521403040c4643d0b075404109401505080c01c904400400000d552039040300980d5072010f09120b030640411842080307030200480d00c07880c117641c4000501200c0d00108014442400c085980f58281b0341d0b2030880b0342c48041802c0615425030301c640120000c00140d0080011885615400b0050200c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 174509181 1250 174507931 174507979
    0x30308090d030c050a12090602030109020703020f0d05090f0111070b030603120c060721050103061d1b19030b09010203181b0405060f040c121505130e0c 67
    0xc064411941441c81101c4101c0441c0d409800c1d000005000b880209086441882e04100c9195001008258220643c86080483c2e100f030340115200d0303500040790340c100358040c88000a50803805018096802600ca806040f0303124610310b01d44200100c880300c28040c0c6c0108140818240010300700c46499840b12454803550b442a181544644180140001c940318000211410781d118180900241d844e081010f40e1555940280392410b8406445203449450007486054000c50180c140429050740d0f000841c9014201081a10400e8100000808000140c0210035800c02d805039040444c4015210705c8c81c0074418990001000040c4040a02c49104015006140221000f254100618180410342070343c5110002d000105100300503110f0307400f40741660105600c410080c00b8403580d0f82c8040c00184c21141c0038501c1601244418110713070301c3c0d00c41c2446118070100c03051801c0145141800000303140c101a074088450071644a19490b40801c10074031180850150282600d0045c480c14a60718075014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 174510431 1250 174509181 174509191
    0x20408100e0106140d0b10150e150304052e060608010e010503060f0f0403020a02060f030a0b03030921010f0c0c030807030c05040b090117070c0203011a0616050c0a030308 75
    0x9070a00c3d0000c20480e082d00d00404980c00c0080a4200115442da612070b420a0000c0000d2006003440f40d0000d00c0080e91500000700400b66031750010a03000d04d0003000000e681c141210700c0780b1030702442048001103000031448441005140c52680c03e136040f0390003803500580410104201801d04100296454002061505882e03040e403c03030600b680c03500306169440c0822074410100c0c00c400c01c0860b00030b0000f0040d0540080c020710560b18500c1031900410072a50043da01081d040c034001080191414a43c803402848010490240d4070b0710144e00000f420382d50004074800403501d61980030034580e800035480f40450310160301082c850171048074406401008003030b0040d00032403c500d00141c10240300f4401c0555484050300e80c50f0806081210454003500544013450510071500c0001010341c188015861088101d41e8035481406054410725003034070001d12404000300b1401001c10002e0b0359403400c4d12000b410030781c00315070044014100b1078a0300201d6940b564000d1280302c000f009050b400312226210b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 174511681 1250 174510431 174510433
    0x91b0c070501030f05040804060f121a0f03010b0603061309020a030b1e01080d05070813090e010605010801120b060607120305180a0210032004120b060a06120b04020408100e 76
    0x3144d802e03040c000941c0e10458001b40f2458041000b07004241c0a1020713075402c5c02080c60000000b144802c039240480c2c030007a0340700a128044c200c4070202840c104402c0c802d0003005400034400aa03c203804a0001e02000d00300300d110711b450404610180040354003102d031540e001442c0e100d03a240c2e02c0c01c1800ca8414190349041c1036400f80201002e01014a0301d29034102c403000801020403c18070401168650032424080701d1480c020030101801e001a111210060411207100041d00130810349950308484165004d1414001c2b0340b001001047d904000c407855032504140140746998441c0c00240c400d105031000200580d86500c0100140380e890b0b0701c003520540003080c0c1035010b8840300744250707a00c001c00d0708020351000c40307286425030f114441d801106c1108141c050540803100c0010900c103003900147c20000c0c00c80d10700320a82090080c0e031800207030030500560740c2400c0eaa007840c038010615002621000395858640003d420661250342c101d400034600305083e184411402041100030b000211162082 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 174512931 1250 174511681 174511691
    0x60308041d160c110d0b01080c190905311a01032f0a080a0b0f01082806020d0b09010b0a1b1403160605090604020609091b0c07050103 59
    0x5030010402400b0700580d41e508511041c0400c9100498148000c4081141e610710614a01100c503103400011071551881002c078000701d0760501c80250b24000403070001d140301780c100070350351040319040028240a0301c1d01d0020100301c5a8030800185400e2f601e80d00c3c113594028403921500800c03040c1603e03014925204145140946e80701c07c0716800020402c1c0005020345540c01a1080c6c1086819111822841000c03010f0b02d40c58501d01c00100c03c11100d81c01035402d504801600006c02101d84109580000030007003090080d414104010358980da5614010f0812102a403c06c034103028120020f512954460000c0d9614040c0302403200c0030b81051000300380980683c0c1d0020807000401030a503905402c440c0e80e00d00782c01e12440c480d0441360142e08415a850900d080342401c0c0784100740014203c0c02c402480c014582d0505103000030498a000b04901c200b03800034400d002c01a501c00c802c03648001022105506103468100c540402940070704201c0007000b2000626056540001c00c03c203045580980b01009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 174514181 1250 174512931 174512969
    0x1205060103110a0c020a030c140f10140310080319030b0d02030c1504050d03200604020a0b0703050c0607020709180b041211030d0209090601180b0f0c0106030804 71
    0x1040c0c480500312a060a0700920003800300c3c42c494458491100e0004040c88601c036660746076007016100a4104100a2803407606501e079500380314002000c213420560b4245208502c542d401080c589110000c03216246001011507000710810348000c0181895200b940e5a0b070301240c070300c52040c5140c13100090109080c202100464a080e40441c3e4281e50084c01810554030343c1402c00c035410b060341178085502c41061101103125251200328410041c40794a4600564140412070034003528030103250910360340800304101c0142c0780c0c44541300440b0741c40c1d44002e8031461070385401d842d40d0080500c0c83c040d601c41c4804103c03402d40c0c0011904110750080004001043e00d10340380380700552014101800f1a290000801e000561400010103142c0c450310f003c00202000144050841c0d010300e01001000b0b40100700200c20340341103604160403590034208045101d50004c5a1076a80c51030f80705140d0040720102e21210081800402c6903100c0400000812840f6203d02e0011810341003030003524159441d100c5840 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 174515431 1250 174514181 174514187
    0x301120c08210d06120503030a0e03030c090d060b040c0e1207080a02100203070f0c030b07030504020f0409020114040603230402011d13020304050c010e060306130e0705030d12050601 80
    0x24040001c031200c1c80c04030729502d0085504035070100003028031066407a0400207040c040b4244c4000240e109101071996428401195816030740c1841d40f03404503420400600c2118403000040701ca490105550300741c0040c2e003d0810400a020442e0036503003050808442c8d04285038400035034081040101c61004151300307030184c0d0540d9481103000d14075660340074002c08005450b1649402c01326450368412645030410341c0c0e0750181030425074042200c0d1045c07454002c0c0104402d1940d80c1d1ba10007400d10741003200345090b40000c3d40c08503001e000103000365030b6102d4034030559100f0301410181081103101d150742c070781e41c44100400400c07040c10844980c8a01d0005804030481c030000507400741d41c0580d940c02c0541c110100000141030707180040e070b41c041091880d000c030500c010700141d44518010000382002c096194000342c400300c0d50965031446000c1c00c03c10003140d5901c07802c1e404094050b4100001e42a007804000342e25000700d54014030ba0501c218106144082d500c1315403030f00790303200e001024800303a240d920042d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 174516681 1250 174515431 174515443
    0xf060c110705060f0d06080f25060309060b09070507150606020303040b0c04080601170d030c1b050c13200304020105030412021614181e04170301120c08 67
    0x30381441d8000d00c20800140c0340c50300143c10b0124003501018546411a040d001c00c984040c2e00401c0280c12500f444508044240f02c12000c1c128103401d10410094a0464100244041c0c09001d0078555140d11500a0150366031141c1e4030007802034103090700c0c4e0510000107040380d08962030442c0c0e0403081d42c12548a000f114020700080316002d070000c50550310350b90340c3c1b000005001000d0685031a4244000100c000c400c000983c02000e1441401035040f1030352850b941000c0b94460f0401c00e041c00c14001c032006c0d40c0c0c8601e80c0071480301410b0a00c04524201d150250030041040b40702e66000c0782c00340139800c1380b400b1644852412000b10f10080c030140902c80c0d00d20003e00046030040e021510910000b0080b400940031071a01e000709105450860001001044166003250403005811400501482d0141401812020148280e07103094440f403405030030140c007101482940300c4554128001103010802e01e00c8541c0c6542c0f4a514820b5107a40e1104000c02103000001d0007658000c13a004000100304e400451a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 174517931 1250 174516681 174516707
    0x270f12050601030f03110a2102030a020a060c050c100e010605010816050315090f0f0912160203121c0605060a12091112070810020405060a03050c07020a030f060c 71
    0x2801d56a80b950719a01140c0010b00c00c1078060020910900c40003500512841000520031203810500139082d4034800054240c5203441020341d482000f0200300160000ba0b003c1280f50b20400c0400c4030102114120754a02034022080f03410320500340c3c250300081985d00203c00d80311a45000b000119502c0303004442c104000c0d00c0500d03202815182c8018858800e80080d5032050b007000014401012100100e24001400c4404c1c0400703180380802d1000e0385c0d554410198110300104010700b2800107911095100744a03c0344041074402020700001d0454406105200046005060454480009001c141c84851060f1145103a240c503100c0041000d01d0540b00351740280c901c40d0317a98082440c405c0103400081c03810318802e491799808010210b90541c2c0e69803c0c0d500c0c210320741015007043c5140000d45880c08114900c0e002030540140400d01075900c6d40b500f0380d10859080c0c07074041140d484060482c0400d10589001940001d42c2d49004030a010800442d002c0c514411102006160300e400303000c881541405503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 174519181 1250 174517931 174517933
    0x10e0102030709171c0e04050123090a0e0102030108100c0f08010504020307020a02040c020a0c051807050d060519060e0108010807090903030f14011a031006080403270f1205 76
    0x10a00c849403e07050700c8090800110102c03a0313400b2a245c1c0151071000c2c20110040010070449040c241400c050040b6801030820000f03810060504200e10444001d0304800d060041c420180000c80014040d0040080940c480008640c0c1c0d58440380102c0d01c845008910411c0e00c1e0508200002042c414419141e541546a95801c107036400c02e02004040e42c009000c040845c4a400d6020b000350f0784511481c2e944044580003803241c90322a1030b017555040803950183d40310340300072024043c42d11585e84c942948003940d403404540e01d01e4030022001c0188901c0d040190000d0001c1c45d00c1605540c01c0f44103506030740d900d444a10310a07a2141c011100707980f0900456522350443c000800c140d16090708000c19580c400c1c01d01042000c041038141c0100c82c0e0804c1c0f01302c121125080100641840d5200080102a417400b0261852a045010041200d810310031402005500b00008007070508c81d0941c0300342421480704400c02e94912003210203111b101801600c40b903000c20300c0e001130080c03034500e58401c1d8030368000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 174520431 1250 174519181 174519197
    0x307021806090103080a05071506080c0103020304082505060108010614030105130b090a0b040c09050702030c061f03050303070207050306070914100903021008150f03060415020d0c0201020309010e01020307 90
    0x150703803217100d90418540030b01070050900007200010a00340f0504030404180d00c4c0090b6281c80c00302d03018940484088624107052041050002084001c001c4400098010084d00940c1144540c0d080c1050040c06005d03159015240000c1000c03541900100122004032000e1140c45030f5850400d401c03280c06580401d02001c1042c01e00300040d4107403c0d25a0311444c5401036500f152510b441344030103047e085038115181804464140002011031040640000c010300c011400c001e041081c1c599a800b0250030316011422040751308005440000840e40510340c49003e980c1c60303080541c4040e684c1c18090048502c603024040000b80801e1103020444101c1d15003250700130303a1024140030f01180c1c8026020401c00c10481c61b90100c0503844007011010380361103546e01c4a2080c81d02801d810010006500410300c85d920210360051070341e40010b600c0e5000b81d04003100106901011039603800920910702030215503400c00603c2c48c00780d901980034511031500c0340700074416100780d084218200d1104030398040c04a1801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 174521681 1250 174520431 174520433
    0x2010609060509060d0303020f070c03021e21030405060711121204090b270405010c05090a03031d040507090611070b04270207080301060e030d0815031c020307021806090103 76
    0x10351701d40001d00c1d0085c100185020480b80d40f0700c0302580282d03401e4a08544030700c41001181445680c10700101d1940800b49815001c80000441001c05460f8003100b501142358240720505040c0101c50007020003e080c160b8410007443e2110800e41010f103010f20401880001c1a42c082001c502c2c2c2c004c0000390034610b45001c1c02c016115000b03140307502d846900501492401d0701e210a4000c007100700005982d503108500e180c10303d42142564000303200c50007042010b002d03012464442038400820340342d1605242c01104202294202815030300b807400c075481400d0505000c4140e400000040990300d9a80e158991842a2506240d4500c03152040788000c0104020410640f91841c520b04844560131000280306011500c030318059801860307003550700700000001004210303040244200c40e41c000781c1c00381c40d0841c0070a001501420000740300c07030f0038210f5246030b592095800344107481d2480100d00d2112480c07027078400000d544c0e0300001c00484c010002c980540e41900d1050807006d00ca07100080903030322160b0075 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 174522931 1250 174521681 174521689
    0x305100c021203040303140a0e0a0803040317010e071103030c0301031112010903030605130c1e14030c0c0d090e0403050a0309050f061506040503030906070f0804150201060906050906 80
    0x80c09140411070160303078118005501c50100442c0264020b96020407100358548407072402d21f10103418911006e140915071548132001080c0203001982000810307803644d48074101a100501005001200d035540080045205035601d40410b0050440e5130b54500c004165181c00b46c0d82c1e22050320903020307200080c0010800118100462040560b01421591111440510840c295424910101c0229407186070904c49402c01141c0b0022891601030148444c0c00412009400002401c4d04400c10801901482d9240c600645141203803006100312030b60799250044001d00641c110102c1000d60703000741840400d041f40319400003c152000c2c6100f0f00751a8403681d4042d0b503550321002c105d405254984019802140003070008804202a40000c2c0560307103083c003202e8105030304010203507108e450180b00a000c05d880010590380510800d9501c00c0e03a030412420820098242060024060200001e021469869803401c109442c200303038000f80246a00d40300041d0a039111801a15040010b1000088042c94 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 174524181 1250 174522931 174522941
    0x6020c060a0e060c1203040c0618180b01020c0a03050c100309121b1202010902090a06080c190b041d01211b09060f050a1a091011010510050f0406030510 67
    0x900002c58405e0041200c04980f2a001290280c4005401d16001c1046582084101d2001c030000c0302508085030400e8621119600a0b00d1030320342540e0f81d081406400e07402085010702c0c0300710080401101d250340c1e02e0410342d28a03010300518004c0f03440040c1e140c403441c0240550414540d01c0300e05000010b803504003c80b081c3d40c8140035088062541c01135840410320f04080c02520705001d6001144501050042c4584124060402000c2c10300d0000c3c200440700011402d402201022a1500440701045404030101c000c960000390380b082d400900064440d0000c00b081d4240b00500304a83d845a90350f0145403c10380140781c00c0007510b000001c0c00d20000c1c1c0c0d91428912080e90788082d11501175242c02d006030440710140c0000c02c2c0d4031034101090081780307032094000000702222042403a108050101001640c00740b40c11700e600031407881c105c400304039000d040300051102001c00204002d180c85105082103507500d1041d1402511003210300202410680141c2003a00d4100c80102000100000b0b0240209 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 174525431 1250 174524181 174524197
    0xd061203020307241424010206011418070f0801170303010b0d020706050415150807060e010c20010f0c030e0603090106050306180c03071503110c061006020c060a0e06 73
    0x161000143c9603900d110740c02181301d001c24819086c2c5401303a000b1039009007600003040c4c030221303070080700d45260303400070361141540d9450506000da10b10b60804100e120105100b1a02c94110020400034400e511200810841c01a5075504410b40d07660140c0d45d81801c08450310820a820402c0140005c42a15000705406d003501c8100607c5c00b1a035488840071668159821114103022542c091500c2c5a40c0c040c542c124110600241510352030300202560b030b03034085e225000600a03800a034491a0b0701038001203515030780001c55105541c507039401c444103000c29004024040303150013900b150f005100d4807600090030b5040e183e10781d03008112410800c9a40005000c1ba0342036403218008607560f142800244e0043c1800b43c1001e0b621818200300d5800c1c240b0040c0014080c1d031202d01e0401141c034186186855104103801d000030350700c000d65003602c010b110745646050684100e1050003059212003500f0b0089413060b40c269035440c5544000c000d801e1091302400000282c21030318080084c82c2c0300c0d0041c1100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 174526681 1250 174525431 174525473
    0x906010b030709170109121d0409030e100801051801081e0106080f06150904020607060b0402130303051306020309031e0c0a0308040905070228030e03120d061203020307 74
    0x6644010304000031624030301c013034001e944650116003000300310103014001380d10504156503687c050307a100503202d40411708003520454907801903405041c014202c0c04042d0304054007100b6800c9200301d0140c4022828810203000796004680c14810748240581340e816100c824000d012030140e205041c041080c2d4502c004141c40d5a260b0002520080c200141406680c00c00094844da02e030002d502102480030906071402500003108000042c0d440b10225550540c2c00100041c96010320b00c046002801541c0700030244110b509800300500d9041f074058000d0807024034028425640f904000c98403801030205054140c0e00005074100c2d15070103001000400c1c0a0b24044031003100700440003800c04007640e4030544141100040a220030441c2d4080e4540c007039661b000515a0600b40c505070b00d5040e0315071101440605141002c242098461990013804150003000c0b00c50081c20902228070f183d10228801014900d0700d1000103242c1c414501850101d40c054025508240751501d915200030101800d610300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 174527931 1250 174526681 174526697
    0x10030509120301090c081812030403030b0a060302030f0915070c03020109120903021c0503030f060f0d03020d030b0109031205070c090606120f0207201c11090601080906010b0307 78
    0x24000d2403074080c41c000d04505402181808089001820302000a8109068880d0b281c0342d2030120740c4001810030792490458035450340d9a94a0030704400810347e0b00000303a40a41e0010340000c5450341034000e980038912101665402c3c4c0c903415003a507900c417054091140304c56481800529440d000f8041210514003c0c0000301e002d426079a80c1c40d40c0c2541c0951510041104c0e5481803080d8104009002c0c0c11802c034404114107610142c444581d00d0100810500a030303107808000500986580107408001000035020003090011071502030f444100c0c404075500089c0c035020070980d0039032041c40c50000320390300a0041c1d02030070b41d544d6084aa9600080c015240040714041c001a007107241d03c03c0d94014050b56449411071001c1c011101c1c29200588140441c60b40107201583c08903141d4100e884504a80ea5508105400ca0001258503288008009000544035514600501c11010401404014100ca45034415583c020041d144403005991044d02580108014004000c00200460704081c00382000c0c0c0d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 174529181 1250 174527931 174527953
    0x1903021b0114040c050108090601120f05060a0606120c0e0d0311120c060114130f0e0a1b0801050c070803060a0b0403140f01051303030209060904020708040f0509040210030509 77
    0x420b4620800903500c864844604010510201010881c043c06092900080900300322640a0350341c0010301582c01e22401401e0031340c2c01c01184d0b240301c0c2601c42e4410141c403020703d8804c0140004044502c1120041449200c0b40e01012500c1d11907415030021303c0d182c1000903022501030024191041104500b40140044a10a00742e01000982400142500460740d40c400f130500c6182484010382c06545440d05c00300225a8a07503490194504c91443c0380c0c00010f203030496003d030300060b22a0710340e01340d018001d01c220700080c0440031445100350003117182d11001c141d60f1100444c0c00c90b881200c030f89403841020b000719000510701c1c800658005030020304a00003552030702c15044a03540540e00403a9480c0541124900021060018042000800e0001c001525000108040d041d000c641c00038201580010303900e54a50312141980c0414001030030442d01d03540710340b40919141c2d2003800703103040c510902400001d1071f14002007101e1090354040c11550f0344240c0100241c1c040d007800341c6002c01b075000f00c071005a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 174530431 1250 174529181 174529183
    0x120718060f0305030720010905010e1315091107020a17010f060b0c0607030504020303040b070c090f0b19050109030809010e09070906030e0c0a17030d06080a06060504021903021b 78
    0x19020b1805540070350f07500d000924044440c20000c02e540c00c07509062580220b4681e80241300031003140c0007030a0201d21899903030000713014040d41001c9110303c80d10f80a11140c0c00032a2502120984952460800111409006000c80b601a00b2002036001001500a000c1d0740c2f6900051510a0551000807903548891501c0d4000d0711010303042883c0d4100086803040828000304174081d0003035102d023000c00030742c1440d4000c240c59201d1405480300d40d9030300140400030051725454803001440e00f074038200701107501694907030003801808003413600c10b4446c03180201c034045200140743d0480310705840e042c003013610310303910b612494202400ca10705010303451440309a10b40b20580240c0c41801e8603038407000054180540a42241c075000300c605115880080b03001d4550700da190301481039136a4004411040202c00e0780c81451445000007100140c1e04040c40047d20001c001103d800700f40c0b00c0c5a051010766202c40a000c102d008400c0410301c0e01c2c11401c0401c070224013a9009184c03280c0741580b8000d6590b49041c40e6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 174531681 1250 174530431 174530459
    0xc08040b070512030703020307170420030708060f070215070806010309060933060b030402090907080703081e07050307060c120603050709110f0304060510051002030307090512071806 80
    0x6022070380010402c0880390784240251101440c0c0780b0b2042b05818070303403038841e14411407100e440c841d00400744441c8030340d0343c0c2013104500400c0d14038225403203807078403689022061509440c82400341c0718400840ca040c000c07040781e46200d034845550780850382ea190307401100030740000300b010389601e69955141d44c00304030041e005c10000700c044070620117114814486e44220360945509012610302e040070078000c00c0c81c441e0407280c006030100c0f00c2c003031680c882c5035a1900741801a84411240d02c220700000080048050151400b0311028401d40c11802000a00e42d17400e1160603401000380c2c00410000001818a501082c2e205a8901c0c14561b0a4000c8800d8001c031500c83c4c20660302a4010882001785064a00410002c5014181c0003810444000c1d0114804d0102034402000b86440740c0009854502e070384900401448000d1401c0030240c01c03614080c2d201d9100340d50714400544604404655420814503103000800114003c200840c5403540c0300c02505060b40d0603240130b43c1c4402d0000340d401905054 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 174532931 1250 174531681 174531691
    0x2130807051224071e0804050f030a0c080705072133020a09080f100b0303040302180a02270f0d0c0603020f0708130501090603060f030b061c0308010f060c08040b07051203 75
    0xc0601b81d0405040031480d200349001071412030362041140905c40c66106101080142e0b011100325140c40701e520304181070424503000800322000c0e0040705104c2c24120780d41901f040d4051910310101500c40c100204084a1804a00344d001d003c04654148503600c641c024800c080c0c5924041a2040d103130207805007440c0c04041c1035000b541c020482c0060000301071041081c6003030110011407030a440c41d400b05140c1c403406842c3c01c0324513000d200010214451501100c00b0a5210410810300003216220416410300e03000c0801e000310020b41710340446080c000c4078104c0e4581c00c0055010748a00d403103000c0700654403c08035848011014015000040d250b50042d00d40c1c5120680502440b82c20071b000101203030b540381d0100c0105418a0810001407030390f410900706030380e00020510810317070324071000c52a54200703400280c944900c1762800383c00385540b05404505031050180d556080f2599048212040c400b07220000d8580c24007088100090020030f0000c01803103110303a043e44c00000005100c40c4080c2c1007190 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 174534181 1250 174532931 174532937
    0x2f0c1306051815121609020909060402161a0420030a0b060123040e0c070f08031506030a0e011125031407080309070b070308040f0602130807051224071e 67
    0x101a50903824170207140060a0750036001c43c00d0910303400015850144c0584410b000c0c0e940068a0b81c00c058032501448012500140b004c01c2c0e00000c0040440452400c66051300d0703494170660003000b060003a000c0e14819140080080c00503046589503070680d40c0000e06414180a140a030203000f4000070529000b10203c0002e500e9142c91400e103403200d145000501c1101d03034210820070900042d0101c07041c1c0390626007003202c554032036846c01c050281220b00c5034072130f5034401800300c200508805980c11580c00c2c030041c013000b8400a404c041102144d402904007038124806a0104808000000114048524003c0ca0889805284141110a04c5e40801c00603541001c0000c204841041c017009030030000c0c2812401d4510341003040c3c50003405082c0c06000104040a00c9101c0410f020490301621942030541e89020f68442c0d82e40703d00ca42d200c1d22441800c1c004c41808071071584100b00440c9007071550048240c0c0580c5075001e900c83e000c0f050402000e034000e00a060b02d4590800800c601c2081c0f02d688075807 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 174535431 1250 174534181 174534193
    0x8031e1b0105090c04050c07030315090501090c11010612021509061b0d05030712050a0924050a0612081b030403030c050f0d02030a2f0c130605181512 66
    0x40d0940c1080f0b200140300e0702803406c241c2480380c0040c00400725004103801d45000a101c0d0282c158400e82600c00d9449a0902c0e0f0a010020801013202d9201c41400a02c6440f404100a40c842c1014280c0741544150040003201e1074101d000350910800e10800742600c001110318011a2000044564200c180c03005c0c54001c1340ca010040c43c40c010080b01d10b041c0c2c40c03414107504519201c0303001424502038500e10300d0388e00e49401c0400c0e6035001d15040301d00e0305130703103d00b0f00055840d0804102814010f11340240e900d190510700402c8a003442c501c10181650328940c3c185201c0d5040b80c0300c000b01603002c0203d4001a501001400300824018000381000e10312a83d140c54110820341420361510302134182007c01038101104070740d0015000800c64021150340c6c1880c1050b2800041907098140711404035500b400740030305450b190403c000c920700820101c01c84503c40ba42c500c640091040f62810300542e038003d110800071803d400e0a0406d900d521912080a4101155a040c0810004070b052208994154403070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 174536681 1250 174535431 174535441
    0x61202070f0606140a1a0307031a0a0b0307090e061503191b0f0f120b030304180e060106050a080a050a0b03031804050c09030c0d050a0813090c0908031e1b0105 70
    0x110050f14010401d200806d9030a00304c1500d40c00c02c621014001d00c05140d0b8803500100300c011494066084044010a40b00c0c4459552080c08601d500071580c46002030303043c540120790700601500c007a01070b00d006460b240c0c4071001d01002a8403540090304e01900b101002d00e07810704140050007081111882800d6080300140120030151420000401e00802d100900000b0764410703901030050200142030200200d00b148403e80403e040d4804d43d04488141d9020903110002450540c0100c2070701410324044400c01e030b07601c84040701c1078003036540b405000030860130125000080301e411242d0070002102002031440d500f00c000910350384c8801c2801d1020080b01c2802201460b2a01c41c19503c0040091458605600310f4000b03a21072540b00005481622560014020301004211481081d9841000c1c00e030341f4041036505030210641c070302c145240a4145640350305041e1103183c50304c0840da154402141085d05c00b180246082140d00000c006a00080c09a0000c1c3d170070714024a205808260b000150900340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 174537931 1250 174536681 174536689
    0xc0a050a02010311091c1509050c0915090106030f060906030614010e1314030c07031b0f06050409020a2d030e0102070209060105030a060305070e090d0207061202070f060614 76
    0x101244e8064401d0b01800001c0e52a22034412050b45684c2e5180005428496844c044859007051022004c400d0310300003902c0204100020341d920316110807207289200d9611100051280d10061201981110242d00100b280d240039800c0944100001c10b40801d285841d4841d5000300e6142c2da00588145494981c0341408200f00c1843c20b01518499540c94583d1030250b65009503010110002050205515040c00f140c207024029103001e01a454140d85c0f0080c2d0340d0403c1184110300306c18005841036500000104010f030020040d04451080e00c50b00e0400b843c0114840c000d4002d000f00d1014000c40d50510080c4072455840304c040480b88802c52040c41d156000018221000c00c406440c250b8030401008015903503a14980754004403d1801e940d03250f4403002220301a02d06a4001405841410320202c0c10101e03404c8103a1143c500401115400404807030308130b17580e00c4107201300004603c1c50380c0c030143c05035a940c0040c0720903801b07640e04a060042d503a885000f02e613115809100c143c440c054203404c4d10702d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 174539181 1250 174537931 174537941
    0xa02120f0711040c021902180112050607020c0a05091e01060f030b191203110106031a060303210702031e0901090f0e0606070f0210080403030b180406050c0c0a050a020103 75
    0x44162010403002d191803401075503074080c0010f10110207014000e10f80c03c550323694080d03010192803503a00e000d2950351a5030101400d468400d00b16140e00500001032180c13480010800318000000341080303041880e2106000807004e0180103d840d556001503101425124003055600806040c0c2d03908400c22a00013004003162a0014980d21800c080c99801403d280300e0064101070360b0001c420054030700c03801d183c151101c0c0b0491a0f4082c0550800000000f80329543c04902c3c0b04c0310103090240c445a545408154880c4540c2046002007024803050100810481d04050707840701407401128502400c0f9950800720307042800321142c3c8480e002413031034aa541c0c000c4a100007081c0d20351288990a040050b5860405401070001d03008520124203c428071400904048150707801030122080d600c001c0314010217443c1c2c1241d041d000f10703007006410b02550038844d000f0031002c1010120710500d9140c96403910b0140002a22404600070280702076442c0d414140120403056100d0002040d40d0300080c800507080e15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 174540431 1250 174539181 174539213
    0x6060903020108010306020a2303041b0312030e010209040207140d0305091905010b1f0306050307050f0402070602040807060c0c06080c0921032205030708030702060a02120f07 77
    0x40008100010b03600f00c0421819680c1c400000b50b00d520f80d0500446800c0d6014410a4107010a440e1401d01e040d141c000450045025040c0705412031084800e11184c3c0f4004d110007040c4081c40304211035480d2080c3e12002003440948005450303c84141e0015059030810b64003a03502000c01c11180028078020081c088a103180b900302400300d07140101710641c5581c9903440b8a03a490b0b509001c030b1800c010f400c0d480881c6100005104080110840001503200003c0c51050030219140c0240411503140004083d011504000c16044016814106000280d08036070401c80b5031640904c0080713000c0806001c50006028a03584401d020041410500384440c50703070303019030705100060043c448001d00b008100c4110f0001a40d4483c076404044003a002c104901c045128030354040460318200c0b00c0b904021031241e001035801491324454990040644a0b90f0500c50601c0da54801c0024a00600300100645110800380c0141c0b1039410118245803450340c80350800308002600020b021080210a03c0790903400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 174541681 1250 174540431 174540437
    0x409020c07080609150709030c06050c010b030a120c0c05060d0b090c042301050c2e0b09041b030c0b070c060305103c1703280e03011e0606 61
    0x10305001260548405c503070b200300f244c030400500004130000c2c01004084006c0d503003c180d401002c0d030b680c80018a10b4209103680e0b0b586500700b105103aa030740b40000300069101c3e0880071500c10802ca000e415110a07603800030455094200000000d0555140b401800c5000710124020420324148010403030002801440042c7d4400c0a2000b445030001380040d13181e006002507504074100c5000700050311140160895407c2d24032548558a0102000d41a00d04035a01c0c4e9030340a69a4481c0140034009032b58291010302c0e041864070000070041403d1a56440301c40d4144d08040309896240d171103120510366150800c0d01305060019010040001d0610345030018000c0e40f40130081402c0050f100b96800e5803903c1000451030f074070780034400d070078042c1000c000180324071880707604d000c1c46080c4240380c41507130340e1007802c6d9140800c08030b48200c41000b10841d07441091840c5103501c62000c40c9203201940c00d65801d02005c1110359034100c2c969071801d01c21030f0340c0110861f507002d02c540101c408540c1030b240b441d0850810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 174542931 1250 174541681 174541693
    0xd0e01060b0c030f0f120709080606121506010e090405060f0105060a05030403030c030e2506080601050a111507030b030105010b09101101091211060108190210020a0204020409020c0708 81
    0x480d000882030b113400f4240c9035201ca694900c0d844003401c443c0600c602c0102e21300c02c01410701840c2d64002c4000801c540054082e220241d45510400084200b06144a80107421000c0e4107008052201407241d8868014100250300a42caa8041032001c0d508036003c070313216800340052090281021310310030f00400084800501c0d045145038000c4c12800007410007400d158552203c454654001d8024000c0010751004842d02401c1c0340140c0c141c010070a549008007801c0c2c045020031031500c2040340b40e200b89411384445286c10310348802100d4036040107614680d580503510500c00c045942c240e03040d0060390a07640114922195008143c01c55406920800c3c103e81e0800c14802e841c0c5603801c0035443c085c1c25041c180f1401b601040d0060160181381030080000c0341480409101c1508180d0000d07071040c0b900304176103041c1e880e00022075640d0300d265020719000c00e00c8043d4a0052801c800e0100c062600c62054550440c0c9a60210b0103a0b0031030f4000d01c0c04250046007a0680b0301b01000144010b110030070040c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 174544181 1250 174542931 174542947
    0x8100807032d020a0311130c02010b09150108010e07050f1204060b100e04020c0f0d0519030603021c1a09030d181e05030403080a0c0c060512010e1009020d0e01060b 72
    0x44001e44c50704c8010484003c4041411700e40d130f2613801031a000c004482c418010b03111003030402402010350001c030b1403140b845c000103e402031541074a180803045042c4c445084690a02c10200c0c0000f500801c4101005400c00c00800d40c4581e02001d007000c404200d150300702034107041c03404000307030b800309807066000f2551507014880d02030340006079002003101510016550305040c56424208800303001c40040310f120303880300311040c29406001030002034000130300600f01101d074241c2142030310010b1102a502c200b41d583d045c0141c4d400301c007038841200c0c841d00000480307610062000c1c100c2e0904035a042c4142c1c2004c103504440005a00510041c0f500c00058070302c0000e101d940b54140705e00740b00c590800711406440c1001c10840c08204680207190441410340e00d403041268000d01181c1c40780030844181030554000202140100181c88580340c6008888046a0800b100d45003100c3c4028403000b01c0c4408810000b562003034920080200a01da4400411918003052503c0d080d02c04507481030049280070402e900c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 174545431 1250 174544181 174544189
    0x30c02010806101205070207120b0109050612120a17040f0b07020c060304060b0402040e0109060504060b0405031b01091703030411010908120906070b0a050609070e0a050108100807032d02 82
    0x151300511142c0002001d0315031b580124648103ea410040c207918956034501d041c0031300c9082e0340c1c2c12a41c00034018885542c7d503030107001d500403111244402c11390184800300d50070405080903000c41c0b83d9520300903d0b9450041d9801b00c030301c2c1090758203888004c07a140580d01406510502203034014000d000030882c00c880500070480c2d91000030b00240907540e6800c1c3c050601e69558044500800321b0b004000400d58641d550321000345020f2044511880c9883da0002c0c0d04010304040d04c0840d04010081c1000c0708420100510381c080d103611081c100040b40704080343c4440303550644c0b040081480c000315200c0ca40351510407403824131034114034184020b8023030421041800143d6540c1d03030f00a41500c1c81e00c840d401c00c0800c03458041c3c3c030002440004030b0703010440d1424141d800b19100380c0702140d40e219180c940000a8450032440c0c03106a4004118443c00d215650240d164a600121410501c01c00309941c1c2155508101d401d4000325118114440f0640803207801c1103509016000c02d907812140212598005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 174546681 1250 174545431 174545447
    0x17060604020c0d08090a060c080a0c08060901030b060d080a02010c02010f1103010312090e25082203050f0a09061706060d1d0a080309011103010e04020402030c070f030c0201080610 79
    0x1030040001c1d0328006002170030b060058101c519440071090042110001e80031300310200403913049114a2400d10031300f5045206001c2d050040d14013915003880c69003961a014440e18008201c1c0f41c01a212030003502c0010901c40041c030b26013180398000030300c48021000c0242074600b0002d4820100e4106004c4203800c00c110782c102da045950040a22000c810064425184500e5603407101c6c0c80c040c1180b08000d18644540187d2075080e4103070001c9802d042e084041074034054030559940c11009122040d8800c070108040070b00c01e683d800b03402d00a00304816001d41001c80c1d444540600c0002d01442020001035820034162000700c180c21046020620f440f50104007540a51800c1d44c0e0b01c10340329008038a0354088101401503021b8541c007a0307080c101c02410700180d50303401a40d2130300480d841d0142903905401c7c50380540b41600c8020f0704031140342c0c42c0d039002c00010750400f41800f504ea009c1003052400148688083e801c02d203219882b20032400400f030002500d03504004003142d008040410020405c031390300c80c2e04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 174547931 1250 174546681 174546703
    0x24180609060320030a060903020c040c0f020601051306050a0902090906030601081b0103060e0f150409051207050c120c01170405030327100b0406050303040305030720040617060604020c 81
    0x2400ea419510303a000905c2e000c00c501c40589010301e040018001d155010944100c108826601841401311005044840050300554040140c011740014413140c94403a040c00540c01070b40b580401e5040c2c80b10002011200c1030380c414104d0b10360000d109951801c2c15140581d10850440140115624040e80c3c19281d00e0126070b0341a113041c0c40d100c052607a038000e9000101030040109a0819481c0c02211400603c2d03042d42d07500c0701c40090000440036460180035400c519548180903081c060404095500e007074002003030480d414001c841c1488140d881e486aa410780000400c01130400d180004000f40c81c81050380103003604000e10001b004007180c4004202c1b600080c07a80d50004000200380002c80f50b03400e050041e204035010325039120813221480d800400000c2812182001442c0d0344404065480c8907a21009202d07810512407500400d4200300000c2c80c0303248110b1600c68030341d40d10001038102e0300a4ac00040f0001501015850201800c2080b00e611910560b0110b1a14401c20013241e910103000315 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 174549181 1250 174547931 174547973
    0x210020d0f0606020d0e03011b080a0204080d05071502040b180f04050c09011d090f090102070213090302010c0311030105100210050109050708070918241806090603 72
    0x258011100c20300d6404074808503541c40741008015207400c00251201409458040018400c514003c49880d040c800c03040c94198010220210030a1180301703842e50307100206003e00c40340d401d010008405009200004440303000350b6032160380b0344003880e0034203608100c10420001c0500c140400c0c00a07040230021540009220241000402c41c00713000113130812000684560854200340c24420800900700281404078001d888105205465042003080149051690307548641c0390b01c085a42108900001504280d041c07001504c1c10104d6008241d092491a010512b03003030765001c600023815030a11480c00b05c0b201074502440380d081030344801d54490206005e103600c01c426440030248a03500070840344101c0d024a98040c011507075111203000041c141229050f0110301c0c8100094622441400e114068035079a084103102c10303021481c100010618089208802c40450b00342030401d0791425041340007000b103512503c1761081808103240688525500030900c82d0704001c1c003440081c503491110486030380017030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 174550431 1250 174549181 174549187
    0x411030708090706020d1b02032b02030306030c0120030309060103060b191502161d0105031203010909030c051b010f0c030e0d08070b2d0412080c0c0717010e060403021002 75
    0x3021f40d0403180111100130352512402d40301c8020a8401d81c404002048030784021002400c100c1002d0362070380b00031901c1d150306170003504400f11158002d078a00280940f001440f490202d000d50880c1d4a10380c82644d0202d65644a04010010448076000d1078000d8001550303482e008a0126906100d038101d0781c051400160550012907004510070085001d200004292a1507a1580c64410458a0914400324000c04035103c0004c640d6090004035994104544054507140d40e180041103070050801100407004c00010440350404110104060031314250294038028000b042400094201d9411140210920a00100d0000030039007020040c2450340d0103a81c440c3c030340e1100e131030401c100e44220358000340340e10a0101406010050090b519200251080e4588100d100810040444140131100100303040b1070000340c1d144d00e511076513a044d0080a8103080d281460100c030003540c20000389802000c4407030000301840840359000d000b04034180c031400d07003e0221402c160301c0c0203485204140765030381210b0b000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 174551681 1250 174550431 174550457
    0x60f021504110d080c010501050d0209160c0212010b0102010e062403210a0306050d080403082101080a0c05150a110f070f0302040b03060c0a0c0201020a020411030708090706020d 78
    0x2e18150303040000c2c0204801010303034061400d2100c0750810381c1401c1a81d1f290500104503801c110034480e0040790000e05040c0701ea60384540340c14500c0a401d201740304000316010303140b0068440c038491207403405141002054900b400d000090031103511403031044003940301409001003c9035030038075862201a100100070041c0c100c400420b03e0800103003d1400c0b0000c81c0a482b5079030700607440141c0902c10a07607a007401800c0d80ca80030020002e0303441034044c010b0700041100704002034a88008191000c101400c011200035000403041460109911241d1a50400b440050030003240350400000b0b00303c200c410703010000000060010b18040d4440c04018010411905042da80c001c01c61100301c44c0b2110b00f2900250781361003081d540d0b0b034018882240100d0518048504514001c07814074854510f00c86483c0c1003003400301d4104c45881c001e40702a0b0540c012112160003688840c02540b809500e04c0c0082070f503034100131500030600c3c0d20017014108684c000d8601881003980c04100d5031011801454090210944 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 174552931 1250 174551681 174551693
    0x70f0e19081005041a10060804050a060906150b070b060d020a17010b0411070b15060d0603060e0d050a0f0503060a0e090a0203070906030203030426070e040c060f021504 74
    0x70782120680c0c2c45450b450115500054002d1403082d40700e55402d1183d0010018542d62040b0140e49521403c40c50300000d208a40c80f46172000c0e4414001e0003102c0d6240c0c1c10344c403120102c0301c00d11015a41036451b251000d11240c000e4559400500c02d145031107180143d42d848102e441070300908103a109070030240e000303000d655400303007040d01030304c10320101e40c0018106240c128020324624010300e00603424034055800f1824080144c60b000764018020032515a500345040160281f640d002c1c6911800c10b001190f030103130035032140d6400307103201d02d000241c1a498804102d10301001c0840200400404000741c201c443d0303020807041301e10001c5041094803625548001440890550015014250b50310100201302c0c01c00a100411140241c00355422540c0b0351004505544280c040070303400da801040200014038252041801c14120300308080b018900c6009a5030419040c0e40c0060020702800c02032000b030000f500319a000411640c10a811752803000303031001e92540d000c05100c0c0c0381002c01000040900103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 174554181 1250 174552931 174552979
    0x501080a02031324050c12041103071a071a040c090905011127030105090d0c05030d0c0c0b0603160308070212070602070e010e09060112060b03010c03050a05070f0e 72
    0x2500115012400c8a0702003041030084010384004800d03130410000c100582200c00445403010140c1f0305007981039031951601e03000100c414140316094070503044c00007010300c20400c00d05a0080c2e001401a580c1c0510f08203041307541540012100a840d00c038051000161440c50202d049511103200070462f5409410178900401400a843d4085440000c0b02031407414044000311840044005040c0752440700e00905080b04c0e01200c004040340c0c00884c21039032080c010490b03c1180340c4684116840d142c840d4900205980b2611341100100d1100d0003281d0411414020240e40a0419001400300c0a80c400c1c0c00d0300c0d0300d2200c4c800504081c900085040a544800200c400120000c504a51700c803559100001d544940500c29545080206c000104581c1d003101d90303d50062a08100410040c0d0a08580c001c07001220001216025034500c1c1c2041c0d2620300707000303094103e4000e4800103807e203030070303182042034030030007003c030000c10548584000c0c103540c01806842d030b41007064440c00010701c01034401180c400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 174555431 1250 174554181 174554183
    0x3360111031c020a1707020c010e0a05120303100603020717030601050903060702070503190f11010215090d0f02010b0a180609090b07030e0a03020c04020310170a050106050102070501080a020313 85
    0x40540081c5242d100140d07002840015110340e030303044900785a000c042c001904c09a45c0d110044e04840c2c060741c1290b00c0f4004a200c4c1200083c101034a2694a80019240466840100c2820b81012082209166606048000509040c1020b52821469550b80d41030102d40085241020002201288035030348a48252000303800041d003121120700701082c010b9502c4007184206407092051590580003403410110039030b0802d40c03007030200c5081c0c50585d407211040480c0c400110704500c0384e0301c03d1002d41500207260a0203192001c2c09425003211741d030001491818400c0800013568103110350080c85880c0e1041500490340b00c60321040003004202e8800f07014048641c032500b90f46092048940a00c09803840460007882e958404002036582418103603211040c5e9040540580c0024019030903034142900215848401c030001510880d031034945000c40310b4101c80300c2d080340e68041407980c03040050910460700603003400d0008000350340c5404002822244010404e010007500800861041e41c01911440981 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 174556681 1250 174555431 174555457
    0xf3605030a0f11042c0c130902010e0a0e070e03030d0c03050f130201080c280c03090e100302010c110a0b0304110a0e040f21020336011103 61
    0x141c40e090811a003560752941041d106040300c42c00e00d000c980341070302c00c0c008141816001180a109607100e0000c0041c0e900034204028080c4484803480e5980b032903031001c40f05060f6070000440161314000104020000d2034040e0003103252107824040041c03400c031400e510900601c0d090071042c0ca074401003400c5002d1030b52003026150900c40300004498043d00000d110380704000c65502c2c40e0f030340c03010802c80700401340c200130b400701d80b8590100780002d80484c0181140100c0f030002100e003014030440c108100000c03884c85000118138207030315000c00d54858005001810801c058a4a500300700b441c0c00006102440000d040c1700801c86a02d00700001c1100700300d41c9030801003100c0d216581e9620f003140740d540100c60444e448050b10b0410005480c20000840c2130310300303c545892a036550b6a481685036043c500003610001040c7c0310001103032030400400900d070551a80556203400480c4144104607012601d43d842da819004001e000c1801c840c400c5070b0f2040800d191419464100841890452080000c48045 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 174557931 1250 174556681 174556693
    0x612070f080c13020403020105090603100305030d050712060302011b140607030501081501031e0809030a061a0307050906190905010b130603020307080c0318030c0c010f360503 77
    0xa0100045804182c0d19000d803800c008860b184403200d000c0b403140340002030104400780901c91040c00d0030005158440c00721209242ca03d6100d8540da03241d074200784048070313141d9250010003032041d034480d844c0410b901e00004144030f581e045a001902c101c01070000c41407102c12111440c030038001c59070001c503490b41c40d4105407088c50400000085c0502424040c0311040c1c410004000550366450714001c1c101c9402240d4641004000d03c0c0202d210900d5600580e0300e844280011600c65505010000c1420711840001491070160f203103803148410182c00b00d901c00c0c0c10480c2c0400c03007510f03202c010591100c000c070b65000e080100c01c4d50f2000940030940020442c0c40c50030b80040380100948000b40500450065001c003920b60b92141141a4030007200c22000003010900070461100c1d001000d19004406820b0704007007614860255031958001c0048440164003810b10140309507000030810304105220300e40007400c076680142c0c004011400640a10948459401007100e40c010421610044c22000702902d030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 174559181 1250 174557931 174557939
    0x90b1b070b040507080c0607050705010509060f0a0e09090c1f050705240f0c220515040f06050a17270d02010b06090a05061602040e03130b03040b0612070f 68
    0x25590b400c1740100c1105204105a00d0901d15003442942e20740b07542310008181003402c250044905400c5001744030f4103c00c0601008000d40c1c40f5401030070103031440e47c0d54441d809540800b000003006000c0c01d0300303183d600846110b00c4982c44190703403a02c1d40d000c8440c5400101e50f207060304644038444c440001d4210f000d0b011000300000442803403841228608606a01662981d042c01822810148c804800c980000c03c803414002000c003202e00f00303403101102180d4040d96201c2c0455460014840103111700c0100050074800215041e03500b1014003028607101d402c046041c00050320000b40769000126038149400054183c04204100f1036003026081802e41308654400c0030256654048080a400b550030248003000d5810840103958074254000d261600300c6142c1400d1201d242e0000d014031090800701005000035849030701070001c1c0382d40c0103002180c1e0751010b1042948070724982d4004100d00a010411300012030040400b0f1a00302100301c0701d0000b110311201c2001e1400c1038552204c800e038a09004005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 174560431 1250 174559181 174559183
    0x5011211040e130b06040b09041b09110a021204030302070b070c0902070f02030f0604050c1003020d050702031201120f06110712020c01020c09010308181201060f0303030f090b1b070b0405 82
    0x140414820020130025880b410308010984003610703001c0b50466400400a0003007120200c0c1642406070403460603000c55114810360b8265042646150030502d4001084010958100705c070420740e4012031801800c00d41180d80c025182c3c406449240000c21003c103080003409261070510000b041c0e0500115a2040180b030701050101407144d060f0311038015044a40007072000402d090f4425a40035010340111031580c010810b2540d4070515030810181e007070000d036468469611501d40660405c0d00115101c01511200c0138128030160021510028450300d90f10001d180400b8031108180c0c01350021070002c8a46a42c54000c3c01003010251448a00d1740762180b04513000310b2074090225082e400d1703554081c20710b400d21001410a00c0010003100d400c00103105403072035803041043c0024000380388401004501000a0075154070780c000b002c0d0360818503001c10030590580301d03440b03901a0701c0c0020f1080301c005440c0c4040750b010041c40382d03000340e60a40b030940d48440342004983da880c0d444860011a42010b08160b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 174561681 1250 174560431 174560461
    0x1805060118140a0b120a0c0504050405100801050709180b130f050f0915060409020118090c02070501030b010c0b072109020a081501031101090f08032205011211040e 72
    0x110f8011a032100b0049034080f40081154076945000c0650400c5880d02041c00d001072090010641c1002814000070131540d88900071140030b1221180004c081c41d007821103450840d01c001c0e00690511810b04401c12080340ca816114240d000724030390026003c6901d002141ca601014040c40c2c8caa50310302004040480300740d5001038001c1d101d441840e07c042c1e032540d400b0343e40c8090030440345242c1e410f1000000c41c10700d407640048102d94410714208040e0700c0c0f0f281020f072701d20089811000c861070300c1d44805000968100402d00c000e00d424602071000c1e401140000e031188101c0d28004d0007804241000900e214000d11811901040241c06548140d10700346940e030040120483c128810308140900085070a80005c0b070000c5030000c14903070a00360b461a90b07150b41d008105404241440700014000460507a000d00c010002c1c40741c04065030750b854200040003540380c10041c280b212209442001c0c01680d038440f01c403414080c2c1100000800610034244804240581d5001550f10201d4004108840c0940081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 174562931 1250 174561681 174561719
    0xe0109020324030703080c15040b07020606040606050d0e12030717092e0b04090b090c190b13180e060c07020f0112090609031e091805060118 62
    0x105402040310300e015020368040c4500007a505038070002c000d0011502e800010501c00299000308d03040f524144216146804d03045a05a48440d540c408200050350103001301940124215000c1100c1414814054401d00030070042c8161070703036113100c80c201e020303410080a1400b001c1100c2c1203449141004004100d4100c0c4200b180e03032142100c020944882000440744414900c0d034003104030458001c100070030044c88006e41003000f19240c00191046840c0c038801c1080190059068161516150899614001c0f41f481c4083c01075004030003c08a000141c00d580f001d48a0300016142c1d103480c04480b040b06500325410070f5100ca070b18070904d04002055540007940060302003041c1c030740d1a80c41e8031602400b0700440b0340103500551105140a41c039845003044052074080c0c440700281131802070312030b541240c14800c8110f0200c2c410500c080c0000c0c10000314038080c5401c51030302c1e50419080c0a0000300c0d40c8409040040341d00d8940000c00c2c0c0c0c980c01403042c284110500c80684081a40e40c03440300c145030b429980 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 174564181 1250 174562931 174562951
    0x1150308130815010611070e1003060507020307050a020108092404030e10171e0a050a0506031b041107151a040603030509092503050108011d07030f08040e01090203 72
    0x1003140e00480c5000b24803042034944031142c1c0c640308003a1280706c025480014607019400d004240c5d1000400b419000e10a43c090486050303080d03180241c12502c014014406540c0140290b100040c000643c3c403e00315420b00c0d05081940360014410700d48000360b1a286203844004081990070300c1ca001c0b500d03118500030303510303104602004014020444d200902041c001020310307404040003e458800a50032003610644034400b15448a0620302502c4203070b60003411952200d040c8000c070704050180c035401c0b04088010b8925065043c4c3c2c4144071031030040c45103000e07980b039034420000a0800d0041c3e84e08150031000444542180380080f038000c004508a0000c0681c03c10f540c4509400d01e845541c2c01e0340d41c07640b1070324602000003042002c414001084600007a6041c10203204408102506604880150300c0c0412070f541021002c6080d500594401301080190740c590000d1100c0c00a6900b04403900700004405022035400c110030240714503006280111128800017030740d407129500642c880e0760050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 174565431 1250 174564181 174564217
    0xd0f2f0901060e09040f410606010e0d080904020309030c01140609040303152c0f0907030f060e06180d02010e06190605030d0201200403020d08030402010201150308 72
    0x4100791411401d5881d0150002d0204d030026002416500140c0b4015000c2c210f082e0b40c44c0508140e0403540c0c189800500440c07017003200c005403200d0301520622070200658016054500d00000020440003440c90480e200340703904040c0c0814001c0a03c200d4a11980c0940150360ba8501603800b15540d520020301e400d100d61a207030189071a616000703a454060480142100c4841c3c0b40c1c0d0b1400c13409000c10011000b84070408000024040070f90195442d07000701807114890b002c881408110045c079038028903a4607a5110001040130743e000100e90300060381c0d03021014190317850703080c20302000070056454403000621803074050141d090f90710038641240c00c20704422030303564a1060408a00341d40100082c21078075400310700403c08100c1d200004544940c08903500207504d640d0307500001d25080c966001400907035500c182000d240d26802c4803e0203140800c00784985450301d1a400700d1441e0444110180603550088003180c110ba100390420722031848506080c020803901c0c1d050201c1c107a801004484500c848103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 174566681 1250 174565431 174565439
    0xe0f04060311100f080a02090319060501091103010506040e091f09210903030e030f03070803060906010f02060f0709080312060405071107030803040f17040f0b090d0f2f0901 76
    0x80c0340f01c0e0814407445d60f0b80840d40e1aa4001075004e504000304055140c003c08240e541580c0400c0382d01103031240140da0105483d45809224012900c80030fa841090b40ca00f08018030003a00c0310821203048404c2d03460660219580c54861740d050a4041040c084001c03800030080d40c1c4240660807600125010341031400107030b030441c41c1c0c4842181070041c04001050303900004001003030003408001804103028042c0c401c40300b0b07801001400c6034400e044c115240d107008005d1001d0750402c42407413640400c00f0300307003640406007016010f596444010110101d00c00c1660004950612880c0080010000c440840b921621904070319a803507482201d00500a134a00700000b8101031042040000568040002c3c2108070300750346582145500042059030001527110b20440082c08041c01da1050038212440340f03441701d0a06003910344601c110360014444d07032401d1001c01c10b5035442d030103503c034815405503441741d101d005480c0c001c68500d540b604140803035124288901a41e400301c0140303510342204443c41c001c02da0700c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 174567931 1250 174566681 174566687
    0x20d0f0b090a090213020a0c06061d01030602030a0b0a080604151b050903010e07150906140a05070507050a0603020a0306080607170903161a0a0507050a0e0f0406031110 74
    0x20660059620107259008a4001891a4031450a03a4005000c05801c0503040300010141e070b01c80b000a00000e900780d8025014000c00d841484007410310644013425002c0c1e032040981c0d1014040c003014100941c0000070400703500c00c035030241881d014050722480c0d5a036510000240c0740ca1049030140c07070640340304603248840601d500c103e0043d2008011221710304000240c0880b43c41d00582e9126415660b2444800380007681004460b0041410501c089240120118000e2003100349074032590038044002980e4458001010640300c100d5001d2611039154640303420803500d00490303030b44220b0b04084444004101280c0c183c00404072000d00e80c5003881034917a200c000c00e41c5d580048030703036400080c41c00241d0103200203140500c940008060049a040909462450786200f5070b0410841c2c0d80c44186500400c500c60515a1583c0640507010400043ca0501801741203841010b0001c0100803410320131810503542c08920504001010304200400d40c4c0f00d14100482c507006044403440327800c0460855488500c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 174569181 1250 174567931 174567941
    0xc090e0c030d0c030201110c01050712020f0706051302090114011d090708100e0112060c11060c0c070305011802040b03060106050405060904062d1203021e0718020d0f 73
    0x2030010302c809a11034000301d40d102016081101103541700d620011240c0c4182001d05180d011720000050300717050048028140c03480c00c92202c68200d0040c007100f00020a6482990000342d00010082440c1d0340c0c103124036680a245040096105a4407400498141c0d0a003100d0512882d007a00c904e410320345081007a007404c2c1854020b01e46d0010103a030000794218441d04550360408800e0391244640c81c4c441c9800b440200007600300c0300800e0f1180d03d0b804c041c440c550103400040001070a01603002000c072110103840350402003411040e5900001d1041600504019020080d07410000821411205015514041788082d07800da204604244041d05d8501d00450a28101c0d10142c0f505403074185450140002c540002c001f507540141e45500c00902c441070001c103074040440c01c40c80300882c004002c202e003031406440d41111006217084111240001d0b000603030020000d2080c0c1d01503250f003d8004207585020400e40014541004801c518440e862264014140c2c3c001c5140c4284001240300003944d00b114 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 174570431 1250 174569181 174569203
    0x3040b040308090109150203030a0c0503090606040c0e031501080d1416050304030803090a020112020a0c02042406200606010c030302071106030106050403020a090c2a0b01030c090e 79
    0x4601044108006061200140043e44040c18520807030b5a1701c2803000d003401d04040607040907030000803c01c65203150f28864204624242c0c20030340d0940c00c0003034401d6950600203051902969483c00028100d41c042c44c44604424802411945196418007010340040800e1195001c1031040c0718040c0206030044c8103507407458031030407034680c01c201c0203198030700c20501c0990782600c07940000c01010002c40c10300e000841c4500121401081d030001d040c400100f070b542c006c2100c0c0c00d02900c184240c49101d0fa000807014160f940445010500d901020940e40e50500da500c4458082c02c0328560025107160000000840f0150070368500e0341408070500c030301e520b8440c201c620600250100701c40c140064040d60144c84400c1c004c0001200d280000d0380410000d0b071003a0003034008070f040031900700214901002c0c07100180c40042d10030f000601c2d602d040070b4070a542c031030500c8a10600d0901100540d20401d0700e80b001d2550048402d00c15944d41e030034003280f0380c0f02d5400f401e036005040c407840d0718001e0b030000f511140700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 174571681 1250 174570431 174570449
    0xb070c0905070f0c03050c0607050a0e04060b04140a15090302030d230d091203060801061703040b16050102070602030f0106080402010207180209060c0c0f030a21110d0c050601080304 80
    0x4103a883c00803a4400d001e64011030500c542030285194900342003001e24030031001601e595984401400c000b51070000c1c00074072503210b00d08041082c4195030050080e1801c0700c0e128002c140c9030003010400240001142d81042e1083d880121110405c2544400c0391801c482c020b4041d200c1c1c1510500c1d044450200003942100050403100440ea070030705428009181200c030901000400c0000350b03442002003207215000701e0001c0d40320302d0140a10003007032140400805c51680000e0740030942009154030f90081d4851245000c50108114104541a5a10550b010780c00b800866580800c3e150410083d001503401c4070b8003920750030021514900900e445401141c051700105865460008510f00e88181904107400c2d0a800b0b000d0300b02c0b55202c81000e05400714003507015001c0f80080c0802d000c1412118441e45129600c81841c603c04a0420a12046e4203199440141c04500c08000e0a81c1c000016021880042c4035183c000280580d1040200b520700784140309403595641d271032180329603d003d00d015904003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 174572931 1250 174571681 174571697
    0xb07080a0c0830070203070c050603180a06090314210601030209040c120c05031b0c12160c0510120b0d0804031b06020615040e01090b010b070c090507 66
    0x1154020400400401c0c4076034015454030b401c07100301c20801411684881804a00011490840843c106120754001085e01c025420824280c540400794089031140d14081d490020109202508801c010101490320104a503082c1d042807a104000740420a4143d0008003003030b4440380b0740d00501e01180d60250042504020700385014210950801020b000207061586c05c0005a2080c0c80745d000303019a184690f10b0342d036100010a4845c800b9298541400010407008208004c6ca00c003ca200b074031a204250078a160b00da0015076540c9152851182100d000c1f0b02012500517409508004402602c2e03106400c0740348103568079800e0150260100c60480c0102e900002030300c2c4101800d0303000e020381c03074001456042e6010a9454a20300c2d5403080e0000e40c0c42d51050440c0c1205001d04c02200300051000c1e10050001d031400031080b00d582212003108130b10694a072640c1024600c82500012111342d00300802c81b8095a48030705810755035006480840d441c100c080400151100188a1948103076020340365928 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 174574181 1250 174572931 174572947
    0x60e030d0822021908150403080c0705160e0114010305070e041a0a030303140f01081e0309040f02091203070f081c09051e0c0d12030b03120301030b010b0708 69
    0x81c41c0012a00340e07071690b06411074004056951620055210500d41410840441c20603585a003401c0001c1d00140e01c0c0304407081408000b903404030175642d00003502c815181d02d8440902e8250306003d01c0450900410401a9003c580c0b06202d458260480b040800d000740308103800001582520300c01c5590102280201c0070a203210708098112514607103188806994107003040b03000404802140d0820f800203540ea40c0c1c4140344000d4542c010b07420800041418a440d894501100c1c0d8400107a41c0e0102c220079500202c6c003404004105440301e40310024414404d171403102c0c1080e002900101c00d220f1142003c0b204d404c03031690021080350b41250704440344685c1d081c81915800c41a078064910180103a0048507580c484900034490744010341e114602500501c0808281e01c0c0e0103001c0c0110b10401e41e003005020189603514188010b841684c03000039401980d8608406800a040203180142c2600031140721500d101c140200a50680e0f209011000003030340c86115146450007034400060495008002c806d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 174575431 1250 174574181 174574201
    0x206190b030f12070606170c19050d030804060c051614030705031602180c120703110c100c0c02060a14070c03080307080114061602030709090309060e030d08 69
    0x220010002404484022888040b100c0c81d06520310512a042c0b800421100d08224184c01030400401e02c1418400880c907900c00d501e030b11390b850840300611880350f8501c0032180c0008003203498001c0800410b840c0e01002c0c0e508010702034107401ca40807265a850000070014040c010f8060740c0d0013407038822000300001c149540d44044001456502080d5101c02d000c000c0025008100501185103104c1030001010745910600110508185400e101d00d00c1c00d004008450700c070101a0362401d03820145031050b030740b40e07000203500400c0c0c0d4584d00012903400041141e40564001030908000800359810030106508050455400d03501040080d0300103020401814150310400440d60000f26840712680380c84600c0c4e0f21240f108203e50b10841c0d02d0343c8048100039145030021002401022120f01411b50344060500045562060b076413604003009015894405540741040000060800400c0030090801c00b4103018064215600c5514006a2a84441d1985080200d40180d610940b500c6a442907110903100f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 174576681 1250 174575431 174575441
    0x10c110d140705030d0203011e0f0e0606160209091f051308030403030b06180102060a050402011407111203190e03032b060f06090f0e06060f0c07030c060906020619 72
    0x948144c0703c180801a00c428491004500800003411039001840342c0035180b80765003009a004400c1178660700750400c68800181940d45c0d0000085a50a956440049080c0c150300310910010303400021600400580e010001400d84030103080c5864100490404d000c000e060320740c1151007010038016002c40130002401d10f4007a40d0000c2c0f1034200402c000003400007003600340d046203000e101c4039009103000c1801940c051284c65001221414288402e1500d500040e000f0386a00d21850321016000845005000101e952642310f0030380201030001c080100310b000c0f40d4a4000c40461503110705640c0d940c24146009440c1070114240140c065030410000000e4090038108010380201078002c0075500b980c085034507218410207401c0c102c12540e0302509088006241e20440d0708150303071440d07400d10b0922800000d20380395070344008211420759a42142c0c0c0080085401400082c0d0564030aa106c0030080000c04000082981d46aa0716810300c140d41303000032a03403520281c0c0c40c0240d00c912111468184174942d00f01c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 174577931 1250 174576681 174576683
    0x20c0307121205191d0705060c0a200906030a150203070306080d0305100f0605180f0a030b071b02010f0e0303160b090c060702030d0f120c02010c110d1407 68
    0x40101035591042e241c0c0107440701110004501c1c0405010104840e03124400d107240100c1d401440d000051102d0075850b502c07004c50040b0b920074040401c0a0074507240410400311890351050600c150b03c403006410188403c90491031301e205460510000d6424100025603441460b00141080f00428007504100c0080d0300c0070f4054020180c980d0380c08902c06200b004901030550603980c0001d030519065940c040300d0100b60300600000c02480c0c40801c405580030f000d07200030030914205040d024540c0400584900c1204015a4005821030000001e100702c019015100d80d0542e21014030400850724085201c0b8442c8600901040300118602004e5200d1020300c002c001016040b24500003060301c2d03000c011425004102d5160744000c041040c459010b104640700c010080d90014200a190750000b519044910399000401422510340c804140c810712103c480095950420091600002002800390821626900100f60100807181c25081c00007070610403004150340d1581c030401d581d101d086041d0300c40e0f40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 174579181 1250 174577931 174577937
    0x305030a09020a030204050c030402090a060b0f0c15010f080d02070b1207020705030102030a0c020c060306030a081c020403030306061818020a0216060e032a01050304031704080913020c030712 84
    0x10200068580b1f202d5035026590395800961030f03180c14410003501000080c2902c01c441c1c2812010001c0400c00f50a03501286042c5c000581c0322482219558603007000f1b0720300b09101c0c19202000141004e035080c164010382e003250050307804015609000340c0c1d54010358800d0b01c40840040000600d0081c881e10000c0c0c00981070701c10f4402c05541c07000024266002526804a065540e2002c9004503404100c3c100400304203507801c0c0d023113240000000303440d03446105001c0d026640000d40351039000503094492038201c00114045460700c5e01e0b400c00900810541c0a0315001c01c000380800140001d911900f403089034501c9030203801010180950304007039002600a001544220700c44010501300385841d060207014aa51401c00c0507030b03c602054544282d209004041494040d107095a4802519445040c01004c1c01e003540d50341c4030307498216890a052000c020840103818144810844614014060200110781e110114840000729404030b02c0340b40001d076500e51007086900300180e00c0030103039003990b540e5003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 174580431 1250 174579181 174579199
    0xc0609012109060515041a04090f0506010603150b07050a020103020d020403060501170601060c0c061b02040c1d03032805070213020d14040b072001020406050702030106120305030a0902 81
    0x5048042a41d02d049800c9828030b8490080100c0842c0142021142d5076088600f4483c40e103454850580200302062040e014030b80f140c1940003407004d8000004955903000d000ca0f12340d5a55040001c00400744440541801c044080000590000700300c203690680da0810050105114141e0054000b944800320150100d80c09000000201e5064803c0354001c281c88003251480d403e4000189080201c16002502480b49110102001c103e454404009840850410351140d903c0300198240304803107a00025400341c1094540002c0c0d03039214001c203601082c0b61001c0d03404440008101034070f9006060748448603100520084c00414000c400c0c800c50403840d42401460100150007180c0d031130003100c69005007180c000400740d40900040c0f08800010450041c103981d1810f2941d00c40c0001c2801410500c00c01c80c0e40254480000d0500a488448000460003191380e181d42c0c001c080c140d03401c00e42050b44254640840082c0203900c2402003a4225490740d2004e242d541c0e0a8041c85c0104000300c03050346c1000001d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 174581681 1250 174580431 174580487
    0x10020c030106032603010f1203141c060b0c2d030406171f090b010210060906030b1e1308040315050f0a0c080604181a0106020d020c060901 61
    0xa10459001d54058001c05001a041202104508076152075014032031344100010403480f0100303c036100c162895981c44440103001401e04031401c0180c2203010418407000219286d034500010000c408007100300030b050060503038402050394940a189814006600600220041e4000002000d0b803541440404004004035420300d0702d00d140c005811200c0400c844c3d00350003420500100c9002e5104600d200c2d1070f0701000c2c8031482d144c4410b946220705001d281d103c0100902c1a03009010300c0b0240b49190008102d099503412040001d80f070944019900004078402081c0039092030303090340015003d52510100701f13072a400c02c0c00d41d02c0c0c0c115040544503100180400710028001090401c08011005008540390a01c071540e91021360004e8440041189008107018260340c00881940d4044030844002440d0200400c807201c0c144240a002854082c404070704e80d04e624074141140741078070b005031f00700c0b00020090138041e6502c408050240398030440030310203424198415140d11310401603820018140000d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 174582931 1250 174581681 174581683
    0xb0102070e2214030717070f060c0e090a0c111501120201020a0803070f030e0f0703150605060d0e0d051e07170a030c0e040b1c020607050303130c0e06030c10020c03 72
    0x12204403c4003c0e0000a1740e03400384a0662010001c00029002c01450b1100e607540d940b00c540b8000c100180542c0e11100d1120320640110241c00d040d40000e040c144841c07615111000080a680003010081190759408a842190002c1c0781c0d034010b1101c0d41110020303420601036511090540004038114800c504a000c00034903580080d60164110b89c03074030340d0075841426001c3c0035903410542d00c0d00303143c0c0003454026a922000550000b10303904020710403040d030f04411401024042c9030b049103800000000b500d00485889900c0444c0c40d800c1c10701070b40d01c81d040c0840111040d10504420010202e0510000740f801d100170b000070b000c034612441101030f00941c1c401d8006010f41104050202083c1e84880c40c020325900403400c482d15207401c44003001001c80c400e000071408a040e100c1d041101007520749002c1152203200c00c81d100141c22000701c94030303882c2114140242c1c00d584402142c500313400e10000070b10100c030214041d01401d80107000c2c04940d5010000d1182d03040752028110218410b50355501c0050f18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 174584181 1250 174582931 174582953
    0x50d110f1809010501050a05030406050603030f0a02030405030706030b0a090b0d02130902090a0e12071103060405100f02070c030233070b100b03130f0b0a02030105040b0102070e22 79
    0x5980c400c00345072005410089841030580c481c0f41881020441d0844169012013140e42c4164400310018450b00d5060200780b13140103038a40c18045041c00a01001d585400101078011280120204d541254441c3d00403001d031204d51100c0c60b0000c00d604028400c0c0b066940210716000d002a110948511181c1c000515103580b41481402d65650b0317900410960404820382c592005500c00c0900c500107031580115580e485803040040080303000300c0d070803007080034807440c00c944008002e045403928241400d00d5038507500e14041040321145001c0c03155403000407d009442003250000c0e41c0210003441e6800748030b0312a80a403a110400f205041c0c0c4000b801542d2500c3c07001d129602600c058550a545c0f80c002c940c01e00c090250107004030318400410200ca43c00c0c2c2180d901c080b030b00d5481c0341c21018918040fa0303081c601c0a00109130241120400090a0141d80994100d4500316410703c02c6800d400c0041e030f100c80240c0100c0e800c9000440008580010b40303083c6464460705a485c520102c4800c2d224646986 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 174585431 1250 174584181 174584197
    0xa020f130e070e0307170a050d030c020f1b0103020912010e0303220f1712010b07170909010506090d020a0311010305090f07050126041203050c040501050d110f 70
    0x300010414400e11104a508980c4115181000d2100040340c50009a46405a00c030b294840711038001d00309a442018096264005c0e80101200c98190500c40701802614510703000e03070010b1042007840410b044000403150481480f50b0706045000481400440c06035100440141c2c000708840e100e014024004d2050410304034103d0091901c9042024180c0c14041042c000c0d4001080840e40300004541c80541490f850303035010b00d032103880901c83c4800340964007410124041425204000143d0041e0704801000e141d441202102240854038058070124082d03000d409400565560051280b420a0402031550000003440c2c01c0411a41c0e03800100c0580c040d41003161035040c251000740d04c2e56018080c1c0e81c4c0000501005c1c02014010740d4081c0d44d03030502449520f04100300710300b6101c0f00c2180303080003000c1042030400b030400c58507190a28243c02036041e13000c072000928050000f4402040642070710b060352016900d0a19040400d11054041c0000101c142e210083c00c104031541c8141250080c60b00b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 174586681 1250 174585431 174585457
    0x50d02090616150b04060308031620150705310801090606050f03010204080a031b0210080403090e06030309040b060409090b01080d0206040f200307080f01110c0a03080a020f 76
    0x3c1a007803840c1e40680700030408407400b80741003680a01c00501c000c0192070b44205c1400c02000e0401d003400307046400780c03403004141065010101d419003400b5400309443c1c0030900751301002d16480c3c40b000782c2200c040c4614110b02c0c0302c6442e5a405111034028600140d051140500c4c1124461500c0701c0110342114450b900840300700b6580c54040006042c519201608868214021130a041ca071003405070304c94400050042c100400da443c000310410307000d2141403d058000d08010300403658101c028140c078000380c0d025404501003110000385100310680e09449860094007640c2094048020701c405841c16002c600d0340114144008076002c40c4510400c0701050061503000d506500d006005828031010780320340c2007150000002c02000c02d003074134155541154803000c010302460302410844079440010a2150b41802011000203292100060700c43c51107240344003c12514600c4002c0440612404040d103d0640116032001e0129001e0b032103596200228a80c050707d41142c0002510040e488400c000100c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 174587931 1250 174586681 174586703
    0x110708010501171002040e010302150f04060507060509071a0a020307080c3901050f070b01090f0b04050103051c02030f040b0a09060305040b0f0a0608030705061501020706050d02090616 81
    0xb40f00800c2040282a800c103100031440c00e41403803002aa102c1c414000a0b0080c0300d041c484611944041c4111000d48070109026034031303103803580f10050450344030705000e441c013a043c04045007030780401207014021100c6103149103540f06190f100409032500450021025800144840e002146114000b081e8459000300500f41164503190859156103103540140002159650a24611f0b44d140114131624542420310039142e43d0248868074082c4980c031002009501040c00000d80540d1580003a200c0d628008400e01c07011400000b40011070341c00344006841c40d40041444103000b580c7c04400c011009240c07040e285041e03c0c040e81e00c0b40729481a40a41e590715000241d800c034590b03122540801a011500d000c0c4110f040c9a242c1544107800500410301d400001400304d00c0b00800c0d07a00c035500805007802520303100d040508004d919070703900311240c00341d84480c8200c2e505c40303610200740300f0152012038071498209140b01030340f00001d400c00682c49400070420419020038440ca10184c2c200c0794860f0020142c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 174589181 1250 174587931 174587969
    0xb2d15010e03060114090c13090f11130504060902090a05040b0406030f0b01030c0b032802040f030b01031712070c061e020a09050906010912050a020d0803040507050117010501110708010501 83
    0x4128100500380780d0004003d00002c10b8038004d88d02050219a4100408618001c607042c0031001003d4180840c4031f403003400a21480000d031814404400c440b0225410000380355a0202070f401d078031030b00007a95802620400c0034002458180c2c06003500b080090800940c0702d449507a0455003c4840200340c1c0c030461920010010802d503e0b2002001d49194071906042d4140312079406000c12104042100c090201e1006c00d8441c0f10f280c1c107440041114070310500c0070607500e0822032000d020a01060300c00e00781c6580f8440c1c5213620700040b0751006170858184101696481022500505411421078200380c5400890710300c400000d0180319882e0510a00507034568240d000076003071500a5104c503004542150800c5403580e0000c0b60031040b10801c00d00c2207182002403820750300349050100000d5100d03c070322001ea0184030000c0d001c1c6116501c11801c50300c48980f0b900040d00c20390003460140d040000482c00600c0315510030205110f0300e12101c8111a80961a5180c89003950401d03040380c000b0300c0320040411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 174590431 1250 174589181 174589189
    0x11b0606120b100303080c0a12060609180e070605030a090b07080f06010c030f0f03200a080906060f0d080903010c121a030d031e090b2d15010e03060114 67
    0x15420414242d00580d070f803441c5560241c24941c0081122114100101d541c02225000d01100b003440e10f502c202c1004070607292500500084801d015212440e00c15110100322a0b2640c80740b040d112940c20000d000c901c3c50072900303c03030550005081c01d11491721140c0313410000c0d90b24801c02e402508192140206445c024000c20070352880200000d04008000c01e503040800c2c1c001da00f5650b08030081c07402c85044200b1343c02c1500034005c0c046503c503581201403603012190200e00d01030080080356a4450a4076240d08588950b25581a604075601c1549105481c04500d0103820316804180f150311201c0c200948100041d0842c0c0c010400c41d40444c1808030210b184c0c040324851044503c0000003030070104d01c04600844c3c1d03a02056100f031018107035030318109410301c03107020700f100404059200e040c00080c0e217501d05a180c2c45820b035801c41c4007200107549100e001c04c3c42c1610081e0314000740c01e111403958482a21412109000c0040c0d170500400e48001090760f1014441a400b038614035410000c0306071098280 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 174591681 1250 174590431 174590453
    0x2040b0414150c0c01030e15040204050907080601030c0317030108060a15030b0a06050f040603030e040513080301080307050d08010303020a030c11120a0507050904020d0303111b0105070f0f0c02011b060612 90
    0xe00560081188c0d101c10b10071195071a50483d4050700c001034a541c50f80f450524003880d60300041894400c41c40000208425440c050041d6882000c0101400c5030148001c0a5800300380074004550300b08000041c10401141c0c801240c0c400c1909075092a01d50341d46444074201070507121051304645804080c0a1800c145104a00c00181902c0800c800d601d1610002d141078010312741e0f03030301c195100c4007c5800407150102c2c40800e5034011045694950b5520812992a407203041d046540f80204401e110280780141c940c2030499815802a152121880c0d40c01c55500c06240022500001900d06544950704d4a6000210b06907140740101202809400d100703203001c0c1154004c91198002004000043c0c49410b00592034903814100030800011030b02c5207848034020781d008410900140002c041c409101500300703901602954984114111b0081d10486035080400103c0000c586600040c8005503c61480145d000421130904495421959074841c15540380303900034220140030081200c2072102e09944 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 174592931 1250 174591681 174591701
    0x3110301200a0e06130902031506040b0c15010e010902070c0e100513150b07050c030a0b041b060f0e030c0301020703081f0509011205010e101e02040b0414150c0c0103 73
    0x15050400d840217034420b00000d0305000301d1031800d801001140ba003030b2280c010340307510f0400100038940311074482c034040420350482c511603207081c822030f1f8481c144061006840d50590307044d25101c000603130a00d0040406035114040440c0d180d200e2400c00103c2e080c0710b01c100390040d1030300840030140501d414100004e81d40d40321002400c403071420b00c9400d00f044100302c07240121010780780c03940d407118034031300b4000e090100c2e2469403034240c015480c0b44d01c104080403003031074800ca00c01e00c546070003a11144000740010409000704000b1507284000c0740005402150710103443c800c010119140c45841700046800c2e40c0000704110003082281080c0610144058a180c4d10281a000092002450074001a03500795043c031811181d4040d00f140c4c4418440290030004c480031b5624200d89407150034490ba0b400800304140c40044100d1540c1d03044885820600071182114501c0c0903031f6092a0030030804e1561034144086203a4040c520070440f8800e03c4c41d060291468006840282603401c0520001409944407042 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 174594181 1250 174592931 174592939
    0x307020f010e0601140307080316020901060509010806061e1611240a0516050f0c120604020f190e0106080a180f031404271503110301200a0e 62
    0x10070b680100000180443c1142c0c020700520350302250030700201e824605150001180785c08009240a144000503982c2c6190510075910400aa070340c0e180c04403810301880c0c065900007205003011a4540ca080344c0034000c950100400e800041c0720580c0004079a6001ca0b1080201c0d1414034403443c1800300c16007412030404016141d1030702010042020010602075440310030742d40003000c610100458030502c1580d824030980e00c41d404050416041c619911481a20042c4581c42002078652042c2000c210003910121610000d2003c0c0c1c03075a43c201b1001c140d00c0404241c01009004802210305400d182101c001c1400c418000c18650600e503004003400c1000700340d598050f00303003618402c1d078900c184a45505142c0040406007584818642100c1003025600c0798104c00d0000f050101e440322240d007400510b01013504259003000c3c0280482400d0b1010b405410312040d41c0b01000b00041508410441101c0317a00074000035a4148040a142020154619601c0509408919070024581001c2010750b0b903d003c072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 174595431 1250 174594181 174594191
    0x20c0d0201090b1302060d05090102091302092d0906030a06090b180703170c0a060f0e0c0a030503190c06050106031b171f080304030b040b0c0421030c02040e030307020f01 75
    0x2401082039407140c2007d506056903910002000044294140c404400005200444403840003543c1d00103034201c01d0300c15101d68014881a01910165503240b80c248c100c00050b21a40081001000f0052000802090b010f000d20303807520700024043d02c600e00781c0ca031181d44040980d084c80410b01c8007a0001050070181507000310014000700703016080e1051043d40c002c00155807000705900341400c1410400d8000c05190a0a0b552801c03c80c9507040140007901040c200c413a811001400c104c024101c40c40f0180407a0402c000040010b00308820000802d000d41c05c0001d808403050f03840d4422510264000c0d00083c1e502e4000d5052650b000b0307401140d00c1e08901c4c0950107640395000150310308e82c0c0a029900b0241d00040040440049502540005c000400541c0d807215520304143d04562404c803000c680010a80002580c0c5108120035603040e900101703c01d0231880a910000e00c5004808041602840150182c15005a480d8001c0c1007102c1c003100003946e1a4101814042d00e000422500020f45034100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 174596681 1250 174595431 174595433
    0x110406080f09011a0409050124060f050711060a300e0d0f030b0307030c0f080616050307121e060905070c020d020d020120070f05090103021012020c0d0201090b13 71
    0x4c0c85910340a02d900301c4000460600c00d190880c018012007440c400884952007d40141c03000d1803c6060840b555a01d403440c907450403180849180c814440000c10031030000310381d29401d0038560041c0c40401c4107030801960000c010010700c0103981010700c0c02c248006644002c0c010070700c001d0140c42070500740700005003200460303e0b00244c19002940713021010180c1e80e00c00800ea50350700b00000c000964010340000e8080d1f480c1c0c000303200e485a2902a00c9001d05c180c1003c2045480300144014030b01c40c1903a0307800c0c2991124002201d51404c0c1180813030380c06403510300e580390043e40f1449502e01c4410349600040d220307240c01c01800c181d460081c0801e00384030562005c4405600e410100c150300d00e03030468aa1340e00000520042e80d81c641c52029042c2000c001c041c01c40034201d00052494103850414448944c40c1c2e40c0e074030800c1912542404000d400041e81d1105100e200d0140d4120200382d0070030003000d800e00309007035031061074a02c076800190b0050f9151000507007404200c410450b041305081212521004031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 174597931 1250 174596681 174596711
    0x709060b07060509010221090d090302060711040902220b040e0c0d02060d02040e091207230a081801090e090309150903060f0601030e210706110406080f0901 69
    0x280603805402c03140c54000007030a0384002c0d4101d80e5040e000c120140c104841100310511060b40850341c414480c0305041c0441011030282d8400804c1f40da004000c6450b0071010b03943c1d0700604600440b9240c02c0b50701c070b034a042d00582d90b03041d03100b080c6070960100308010001b0500503000d403603101034110302942c600710014080d4400807a409243ea0070550f91805101003910200741c00740b02d02001464114804940807804c0310300c081c0c425004929500071548102c0e6110540c1082d0711071103000806802c50100301c0108240e2076004120312203000302c291511036600d84c07a001c8056020603401890844440b40414003580c1080c226030240c0382101130b5070790928101911503a20300c17644003414441c4501000c861207250445c4200d134850903000e4299625418100c07800128a40c05507092804282050800e0001080004148490048200084500700c0e80c106840d1700700e41c0700c0c0505803a866188c071510f50840ca0f07004001d00051810395640300841c41c201d0b1094880c0d502c081d00031100c59050070740c66912409 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 174599181 1250 174597931 174597937
    0x130201020c01051608030a0507140a0507020f0f030106090b0a09061805060a03140106060305060f010e01050d140f01140307060e06090604120f0326010306020327010204080709060b 79
    0x8081c2003180c4d40e410101428607640206000c01031644400000300903003143d282d006240502ca164507803000b03940b030042440100c1c2c000c2501c10030000d141440b02c030f4050310f03056405200910000c1c8c0565005030400001c2800d44032a500641059501c4410203145424078051b240000d007003202c0c082140c44d042180f10000e40c940c0c20075042080b51502d000c2002c5036984403035038004503840300c2360384421500240c5040c0a0f0810744150304c0482e1500300091110300f45903414800c0290140d60703413801c2c03890010055496401c0000300d14102da40d552210300c4040000c40d00980500603402c169180d940c50294682c0c2c3e1900c20a42483c003a1300020810020560400510301c1e2170002240d0711519002d44c2004241d082c021544000d840c080c0001020041c800c0468400f03804a020340d03505c82d4030618121200b001e8005069000381d600950100400c0440c3c241d40c0a9038028429010980c071001408035008044074800c80344500c10f940c001000c020740c10040003480005c1c03101600c140075882c40d0003500e0a07280 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 174600431 1250 174599181 174599203
    0x309060414012109030201051005060306010f050d02070501050105030c0a0305060c07080d020f09012304210515070323040201030c0207210b060904020f1e03070b030403030513020102 80
    0x10740085608907503a0281021000c000741d4003640781c05010510041601420000c002a40035500e82030100d1000050910100c0c26214042e15480c83d6846040044609000765800d010801c0310600c5030a910300800d000030840c4500510000c9440d5062404050a06800203809440b80c1c015040400004030049a0f20f684420525107264441ea400e081c003c3c458400d052690704950710025a915403200c603d0084c7c05c1d06e20080c4d0341c02c002d48000ca0030b107407199180c0048170242000d0500c07040019220901c0002d0000a500300c4030000c60301695a00d41c074000c0c102501c002c8240040701088003403541842003d00194175000a4540c0369070b0b44550b07084401e0f0190000e4100b507101c20701c41030014020003008005100a10755202c5120780710201800807460220112601701440000c6410391410004190155400504c0c40c0c000314030050030801d0403120f0540310881101d207000200c6440c1d9042c000c40000b4588003079255a640313010300e0014110b50004081000c490f001c812404050303680010703072408003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 174601681 1250 174600431 174600449
    0x2190b06100c02130e01051003020307090908040504020f041d010e071b14030c010f15050607140604050c0109080a0c0524040b090108010f0b07060f020d0203040606060e0303090604 79
    0x140824070341100c02889a81c40650480b010320303004440f803440750380f044211000a100030415a103611210088040d41c0344806549071713100c41c0052140845c40d030b101c602c034a886140f2031450300d41e03950302050aa81200359441d0880201090070482c5800d110310703a04103610002c60340d0140351304043c176405440801030038a808018544400c3d080348420001210b04540e00403022104041030000760564943c4448000b580650900c500c100026141c1d0094400107064101c2008000d8180001d100c402e4001407000c0d07818082007807000005400038860f040c060b03030280000d010704030603210001d0444622036022070056805000d4480210b50107103c19401c1e11340465041c94010038101a0034070036401c28022000e043c90000300000e03112446002441d00c4e9400380c070707005044c0e079075584000c07954003442c40740051100c010800d80001502d00e90200801600000c001802c0004c03c0b280369003280c20032141100c0c295510756003032110581001c6605200e040440007540741070380340c9001c911280601c3c0310781d03000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 174602931 1250 174601681 174601699
    0x1008010320010e03150615071109070c0803010315050606040501080402010309080d0e06010f060212070f08071a041109070c02090603011103070207090b0103020a0c0311070f120302190b06 82
    0xc9680f02e00c10184019400a040720100b10401d800380800c001d040c0c0da01c40c800c2c0202c844201d400540c800645240c0354224425040a00d000340a1080058008058034204006a20344600080801001d503001e107005000c078981030346010902c0c200b200d001070120341c4664414401080f60741c0c0e0040200b607100781e081c81c0115400100e494204500e024960300b00c071005050001c13a4009400005800d41210b0101c1c1201011070356490050b80c0300c128510801c21240010000100801c140320301d0f1450040c86844002c1ca04081a10b40d0941c00d5454010132032002c143c2001c1c4828000c4501c01c0c42c3c6007178021505801141003d07100517080d14602003000b800f684034200018a5a0b800b1351140f0a40201c800103c0c0c3d41e4036200900945811541c056208100d18080c1111643d501c40d01c03d5404150058461602c41000d41c1c400307541241440c3d01d0a84940318a20010520074841e202200040c2008401202082c07000d00d800b07130410b800f140403d02c25070002d2300d00902103041c24003859040001a505184 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 174604181 1250 174602931 174602993
    0x515070f02040e011820030c0114040905011203030c0e01020c0f030f0312060a060806101202190e01021002030c0403080f0408061006080f040b0a0f0204120606030210080103 76
    0x40984070751007440c00f0300d5191034191200c0107001c0c40ba031100700d4402e243d01d00440c0f80c045002c02e02e121030440c450380c169201e401c4042040d4094580e4540028000007140c3c2003980d14044001a40d0302600702510804030804400d081541500440c0c25203031090074040501104c010000750b882d41d00500c081c1c0700b02e60070007494142d0b4400340003000c0140211002d603503845540e01c051142056003a15164011031180303400041043c4907490071030181d90014424000a480540d0032a8803984510880d0a81582040003036180d4542d0301c1c03c0d5411078483e40703498101402c00170019003800c0345184259861070042040241e8054248120380c10b4907800501e20303440b80410740c140d603079034003482e049000c880c414030081c4035aa03c000c901c010102e034415a10503420f0ba644051400c1850016500100f080351200c02081c1e65070400e82200d000d080d0b01000050502d955010010b501002100c81915461790300c203801c1c0b0650501407440898580e90b410881d6681d451940c1d54498500900d02911280e840e081040c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 174605431 1250 174604181 174604189
    0xd03050a0f02040906050a08060106020304140a1707032616050705060f0c07060c0305181207060c0507060f02121303060e030d06090e0706081f031505010515070f02 72
    0x76401c074280300c046444640781c0100340000c0401c0d00503107201d41170600001078114000100c0d036041ea199907000e142841d14111988640050a001c000da0190b00c500340847c80c41e001408680803005120018a0303842d14504210706144442c03021340780c690040340325000d42e2400700e604480d40400888800010080541400750914845800095000340c00142c03c2022404404c0604154001070055480c601c0c1c1d140000c0d1521603400200801281d001d103e0220419140d00c0c4241c19404d004e0000c0541c041c901c1100c505203409a0032000100340200014070501c102001108064040c90800045001003008041d55902c6540c00801424a000031391078520b02900982d8002994060024014064400d4100c0d0f1203401102e280117070240b0340303880001d8108080c09805042c0b00c40ba80501360280c180130041b03549001c010008030101e0701005032142000d803c40401070081d03010322410510b00c40d50314160340588406901040c8245d54134001c00e00120114012150b0003540100d405001c076100d40301203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 174606681 1250 174605431 174605441
    0x6090a0b0a1b090816030f141609020c06090d020705090a02090402070c03032613020a0302130902090c04030b181e0601050112020c0a110607080d06060e01050a020d03050a 75
    0x800308031828005030b0100903411240c040d0a4605110644a4400341c02c000600816030710312001e48020700701c602d5100801d0340901c00401415a540c02d981b54420000b03040011140d40c1c0c1d10082c007980c0d0004140110203801e000182c0c00030340c0e17079016012046800c10001d50b284054005d0502c11a02840803442500c5241d04880100d07038082e1080d5111451810818805141d071310042d07000c1010010300d5a0003d5186221141c4101544002c680c2502c0c0c0002401089481c0d07503040341c102c1851900400075a88107040071010081c0743d000803645150602c144840c03808007401e0307607528140c14401800014070342003032140d01c500d1341e200e85000344429500041c50070441d030b40d050019154000c3d201c000c3c1d00022416034140e50382a218004aa05004051812882a05d540c0011901312080c14800600a84580031644500802207400c20040e0380b14912a640080140101c1d0340c0c2d00c400c02c0080340c1d04040a4007088009080c000d04101213000047d446100c0040b407201056943c00000c0d000b03078103a42c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 174607931 1250 174606681 174606701
    0xa0e060121061206110c1c0e030a11040b0603010303020604062309010507020c1e0f0117090309101b1103070909050106140a0b070f0215030906060f0306090a0b0a 71
    0x42c0300705503503203259004400340504143c5140d801e1805145041540c4021220010501070050148140c2c0d6400042c4000e800c4200400300220b00c00f49541c19502008003032207140c01a410f07111401d84850403c02103130b51600045004500070310041010035004034034154826040b9002060000c5044000c2e40260b40d405826200c800d4480c050081c8040c0540c801807103107031690216030030400607904010800e2f080c150000c08402c1004c100984900b054100c215906006050180d11106002c0e11217000c2a81115034000550000c6003125203490714501c144000030710340c1000c000602c20700f00d20a64403c44a40007412403007050400034070b2510204641e20081c10301d40c3c81000196030600d081800b8000c02e11504568043d419000031507403a01d028500200c030341440c0254a04003099a4280480c2c00e02807099038868030900c2e104200440f024029449600d8800107803140d80343c0701081000c800e0340500150300035841001044003000c80058541c8620341c01040c0203503d96665800c400151070303403583d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 174609181 1250 174607931 174607997
    0x90201090b13090203041a0a1b14130b0a0206010504271a0703060e18071809050109150518072304060905090f011104150309060507050a0e0a0e0601 65
    0x4200302c05d00c04052100c7c2c0b400000c0c2c00013035803252180403682050300c42107154690740d003149210760a800d9005080305084243c64580d83c40c145104500f44182132051a03001550200000420100701c0768180074240c05010708407010070022000c801d122209401c0c4002d007120400e0500b84500c180240c00b00380280803403440300c60300d0661800005c000c000d403040c1e11600001c4503118001c607000d000d0404089035040c003400001c1200d80e1400b1001100244100095003a069494190002203a400c0c082d08000034040c0e01c202c0c1602122101003002c645004045075824a041e0014400410340440c01c901100d4000d1800c105800180e005045d466a113050130035803040c545000005d14071070039089584901e8505c01515001c14401f84010300766000305208030103052042100f0b0011400b8560515482200c518001030807041c69601c043c00c40381c06a54502c00b041c40400d010310030540c40121010044400c0d03914904a504e40b5500c40002d9901600283c184a80d943d40590f50f9409a0340340c1c250800408 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 174610431 1250 174609181 174609187
    0x8070f0914030a3008040f060506012102072a061107050d1101080106050a0c0204110d020309060a050105060a1e05090d14162306211801090201090b130902 68
    0x1500010303071802d5505101c400c03480d08202034840d045c081c07450503100b0750300034150400703020055480c1c3c2d0023030038010010703810301c00c560151641c41003d17240f541400340d822800040e40d41105040031546001c01181100da8104020701e480d4203580081d0030b034812503080d410300b1064000482c8881d41007600340c3d080306812a041c103e0710014040051078806000100ba201c501160740c882c01d0850703162107110035240100701200030440050a056225400300c0d280e482203d400d0082411948060340d01c241d882914550041e0280b0101840300c0c8211401001c00300d88407458061800405040e6541b09984000b0824881e102c101815000b40110b81020b000180040004545071130404000c0500701903210041c811009171700304105c01c0f000c4410030b4404110300251500701309030110801522040589800203010301c1b07000f000101c0b0906800b000c505032247d007080742c58421810416075200da211010581c7c181601d00001d030f604041d0a0b070a0700c05503c001c0f5520105c1f00000080e41c1100d51121030024800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 174611681 1250 174610431 174610463
    0x4050a1d07090b090127090b07050c0601051c031209171207032022060309050f0303070504150c05030313060506030a0c140a080d0f08070f0914030a 65
    0x204101c410307500c0d648010030150002c2c0c000c3c05840c020901482c0b00329405043c41c84030b0040d4021500070407001d903001c04150800c041d03854207522102940c14901140c800b14420034035800a0000e90301501c0180c40090310114000201960f0a00103200507090024904101c19100e0381c541100d8031017070700561403c00028001c5403c940a0b4031400080131a0810303440441d80e854402e01a031212031052061100c0d018040b03d200d900c4940c024003e0b24644c3d042d01c031541310008120b076550750040c10326032400940b00c032090a0090134104c000300c080c0b14940080080021490b00b0109560507034050001c802613016400302c0945603c034210101074110300c404420031251441b4038010500041c1308000920241d1140028141e81d011580001400500040d10a001418000a504003100c0004110510041e518480340303040c008902e16040006101003855510341d50051303c0d0079008603c51401030f11102c11103900030300301300060049a406146039030000040340e42c1000540d40a540142c0804168024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 174612931 1250 174611681 174611683
    0x18070503041401050c0d1a090f01081b0904060b01170f07090602010912030218040e030306100503010f03120915030506011d0a0b07021f02030a080f010b0904050a1d 72
    0x845040720030107042e1400c68000c01c2c060050b64002d419040e0ba050801d002541e0b1000034103213040e0130001c03a03880950fa0b8405c80d44c0d018042801070444042c41c2c0069418078070458102078400504440e91a040108401592185201103074050f400440c0020000b0940d40120b5048180f8103209103980100313401d101d000d5101c210664007400d013345651580300da803079400381e0a031b48000388042c02c40d1620740b40351421103000307400505580002c1d91014142c1c141860014086503ca40503129040c1c1c4084200101400e045541c84191089810b02d00e0856150121000d030a6285020042c0012460061002081e0082010344050884540c0c0c82a030502009801402440b040b201d4a0000d0b0408030545031030204000e262400d19409400c5040081c24030700c0c004030030381c8441303800c0740c0102215071002c0c1c542e9144d05110180c882c3c90390145540d08026400180b0599015101483d20413101c801004030602d100201c4041d02015107003c01c49642c1e19070700d6002030018070701c25a10000c07050806e090f1014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 174614181 1250 174612931 174612937
    0x6040602040617060904060b01021c0309021e0a0b0a050d05010e0702070902040b04090e0f0d08010f0e010513090f0b0c070212060601051e0c0a03030603051504051b180705 75
    0x1c10b030f682d000140e95040d9021060504140d41c842c3d00b01d0006008900440c800340c1182c0258203040c01150b400d210551a5042c0203600c601c45400042d036601882c0f03086240004620306556284100786811110180000307684216610900400e0b440010301801254010303820740340b100c8070300d02041000e90b96445142000d035001303d65440050003001c00218240d0750314400d4506035200c000030f2504050500341c011008196a01c00640e141c41010b68424004c0e0040024420010441d9143d0480e545462070003804010660071000c001c012000042c0200e440d0007016074504c410407a80880c1c010b9007414803d100c441880f13405028024041c04020100701d64000a00301a8404c0d5030014600d4070703036980035440c0c003416100140060070410510328805046c3d0114040302c1c034030007030007440c01501000007442c01e80c0c000d9080340404e84441d400c02c280b100038031004c103c2201c1010b0f080c0e05d40c6400d6034ac145e124200142c039035035800c02d40300034550161100d0340000724bd10301e0b4814a004500303101720041c000f50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 174615431 1250 174614181 174614189
    0x40e09032109010b0a0b19082e0b0a0201060609080d1704031803030915050403050a0f0312051306060e06030d1202040e01080a120c0c05090a4508030c07080c0604060204 74
    0x80d002c0d40c141f0b0751081540a100740309180c914183e5003d920b40e03280b03800c4140039400c1005020304030701041c03404281c8000c00545805400002d4240d2500c40003a02e0f403a5030364004503450300300302000c08409401000000c2c0d1403050022840e101c0e03460307140036120410100318540c441402e0000c04400c064108103c0c005840c1005207840060b9603407582100e292080d800018410b400c8074000d40002004d0b2078249121512905240000e555074511321411039004860b110017080310428107005000702c1d880350b180034140110001d1940e18aca800466942c8043c0000e0400b082100042200b104000398156809800f00502007203403940d64000700359031940c24035420b58032a01c10807485c1441a01500c103160105a201038043c0345140b80030104400c040d40144606405601c03082840715411111802203001450b024401c24550013110311031544001481d1000458085030b058000030424220550390300824041d8240d0f554202460418034500500c00c1ca41414410041404100001038010304140c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 174616681 1250 174615431 174615457
    0x607020115120605180f0a021009080c0d05072c0108011b03020904090614090f06010b09060f07060c050705060c091c02010309080a020102040e09032109010b0a0b 71
    0x41e8480306010405102c0c491165040b140c801c80314002103094100c030381d01c6118054083c0d0f02c24100d400381030034041c1202c3c1d101c035550442c0204800710703e0700210308000006545000c42199041c0700016581c1c0d00c2d07400d0014429001103083c007041250400a0f40003600c12a5840b000c80c11200c0d121030400c0306500824601108020008030344008140726000ca0b164074078062a07038000c42c5107c20390082d403000852b1034101f9151101c82001c141c40b40541c9a0302c40d001210003005140070101c26042403003a440c00c4c14990066001042440003550075034805042c2103820320b5880200c80119001d911442c1401070600b800c0140303040e9565000340281056601400c2a02e040341d440f1000c581e154815070b000c159109401c160058410314a205412408074410304002409a060b5140d00c0d60b540c21008060780140c0d00002c0500c28a2842032400d600441c2a800940c105210908010b08244a003d0040c100c120043d000034a2200e0035008600300800143c4442c080d035484102c8040a680400c80071180 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 174617931 1250 174616681 174616691
    0x6020d02270d02011b0533091e0307050d081905061e04020c070b0d0b010207053607050a030e06040b010522050f01030614161b080c06070201 62
    0x1414040d0160707003061200070640d00690340103500645403605c100b100d0002c00702d40030a00c000011010400c84680e6003003000d01e990356a00650314202e4545440c80c1d0f89101c45074000034802122000a548248001c400c2240d83c8039a01d5000c01510310300500c0c070050414483c0f20717005440580c00900050285001c3c02d401d0480d0700c000151201038900c16140582c02032624202c180301031802c05d042c3c2c4c0c1100d10003000036103403074814059246820301941100d64408d400207000a51030340d0071b105000841e102030024051240c0391200140c42c1c555921403200b00d80e0110102400701c8540c0c1c601c400b03c0b810f16107090121908205000030001c1d00103441c0880824134017a201500380ba0000744192081e039200c81498801c0c1c1c01d10041c0491540803003101000c51011010230140340491340240791190801010b12400e640c0766007000015030f40300040040f102c0d5100d02c2840304404000c410f41801301b103541402e030401280c1c10324606401c852100090030022001c250a100031a02069440c003408490b402070007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 174619181 1250 174617931 174617977
    0x51305150717041e0201090308190801080a1e11030a03020f0d08091e010204051819090209130203120706020a030608031602011103130b040602070603020a0503060d0f06020d02 77
    0x41242c10643d000f61461010441c110344024000c0b0108424610600d04017a15559030350f02e00c01c1c01e401203468a101c5201543c008546998041041e40c01007404a006120865603520f401d41d43c03207040c000004c10710781004001c0042c4140b0070880580c103040034045403641521410025241e1030b001800c40c0f040d00030365140045040c40b07607400758003030500c1402030518450411282040b164070001c45040c19502408002085d40e20500e003645503c0d034003100d0301042d190582942a41007000b44010b500c443c6095406401f5866800344150b01026181c0354a0500140307000092604601840074a540071000405600300329aa4010740301c590059182441581e4468424039268003541c541e0512486220b0300810156100b403c0f1149409008025a441c15010202c03012101c122600510307503c00000408011407541009a03d00804061500710308010701000010850305c805807806d032103180703080c03403240520a40c103030f200038015840780c01190380710442051071000c3c0d040b4411642070309004250520b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 174620431 1250 174619181 174619217
    0x51809090f06090307020f010e040906110c1507050703050f0d050408090f040c12022107030204050108010911030a0b01050c06040b150f06070b180d05031b12040201030513051507 78
    0x176080350f90003000111003118001c01160000c0b850310074207030b1090302c5495441c086465841100d02d03480c49046860350b200c0213000d05902d00012002c40658041070002000b0f80746a010095540d0640e1600d001c95590180000304980787c00340400c1007043c5440e05042c4810410322000a001d10241900e440c04050f808204000c00c40b4003201d0001c0c08212500018000d00600303500500c18800c481c0403142d80307003070b0303000115040607411214100441d500140034045076801c0301000e4014600040306104924108883c03118500024155012698840c80360880a85c011400e480000407900c2c103c0d40716180c01d0811a9480e4400e44081440602241848225007000c1000c1080e11002800e140e19048a075a5480318060004203c3c01116046610032080e8007000d00140c0c0d1710495941e1800d4807402e02c81409009205103e0202050348010080485044181da0302d41d40c2c01b940900300054190703600500d1010a060340e14004109024003288000d07040500d116030b50044100f51340745018400071036143c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 174621681 1250 174620431 174620437
    0x6010e0f1003171605030a11210706020d1a0a0b0405030318031603050736090203240103140604050a06050403050910080f071e051809090f060903 64
    0x20707018010606420301c041020104855507140f0200310181c07528140b6502d01c4890140281c01321403d0b000060003402c01c0b980942e0700181100010050040c0c2400c0c200403d1030080c00300f8a1905030b80c40480c07a4014083c40d6819203580c6284c2d0a020b10100c0b0f0940c545030760440360640220b126140d001004070300745c0c2100c415038058602c050029460400003400d00c0c0e210300c0720580c0d101c0d403611542d00c0710200294003203c01d02c01107200d00700618100c0c0c1002442070000c1e030300d22188400c0780c18801c0002002040322140e40d113004a4440b002401302d03070500100b801c00008030845480c0d42c0211061580c2c54501503402d5040700d025123410412000e442595a0320381c0d105540250055100c1d003243c070046a5250310050300a80b00f03041ca989407520100106014030340a50080001c204040d04000307190305054503056107c1003501e00140310044d110385a03160000e418980f201004808513408020044098410b00c09040041101d10725280c81c9402c1c40e901d5518880d845802c1c040c0d40046a8440400015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 174622931 1250 174621681 174621691
    0x6040f0509030405060c0f12120901050618090f01061401030f020906070b0a0209030d09081c12110403061401050a060905090402010503040f060e0c0a0608090606240c06010e0f 77
    0x1841c81d0514000420071146c03ca040350b094540201c01003802001420400e8064961010101940b01c0300b1801c031251008100500c510384a03414041008619030b60443c440002d60241d10f42c1c4041c2d501c80181c131620705448035a101e4155842e1510128001d01d088201c850611002d82e42840a48c1ea2800740e0800d902900e00d003139400440030f1102100040160b4070707147c2e000c8001140181040c03072500009280c055020b840d0008112801c0342031009800900887c4181c5510b512007070442c07006408002c100013000041c0d09503040c0e40e040f10011100c00c10382110005d68010304d092112504403000403d41041c03c2c801e0611a07610680c0014055000e8000c1c2c104880c07004181010540c0d0f60b40041d19154402042124100e000c4200c4030700055a900c21980c00505001c020512503000c0d07028441c3e03402c1c190b0043d8051123401350400020110000f541d0b907025209451101214200303400e03030b0684404c40b103003009401da80420042440c05002a075141211080c050980594984480030400c1810a0360 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 174624181 1250 174622931 174622933
    0x6051213050a0f060203011d0f191107050f06060111030a0309080912150601030b06041205070b0a02060a1811010e130204060305060f030d0f1b0c0602010506040f0509 73
    0x1403200e40014000d220068040e20555400b0445652280d651200380501100d28036400300060004403d0691046c0d0718a804115445003403c0001c2e007181a204000c1a4070354500c2440306c52000640c0b070382c00c1604030641c40c590060702c80302c0514005843e0070032004004a18032a0741e0006a0662182c1c800412881c0078030051450801f0803241240603001840c0180c071108010440c080c0c0e541c031511003601449008202618a503240150001c41858020301160f04160802c0c420030501c0e991202100c00300c4030b40c01c40d00e424180f800c1c50683d040001c0307548038a01041d0007040c0088116000b04005200380c54081e01001440c0e1541c0300c00c40445502680500346c2c0f9240e9820760302550003032444d25000d110003085054407240e444100c0c0e05a03485500840c3c00a0388501c00d005280c2000038401e44401030407406002e0200000e00000c0c40000b03c1c0e40d4100410100e60314014007003440600b20f2440b0340e0416403610255450b0880a0b01916081d04e4050246142540d00c149030b4840748a824000c5061234 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 174625431 1250 174624181 174624217
    0xc0d0f1b030c080a1a0604530c04050c0705060903070f2003120a1214073b100c11010c0305040518010302011409100507080c0718060605 60
    0x100c2e040009180c060800350503442e00b14440304031a07541c54007801c010800c680d50310000c400c0c0213402030807510340c25175500c105040003010305210030807006088019231007603891100c21004401c042c071300e040100034031240c00620304418090380c6422007004110403409082120003903281d003000300380c0d01d02c9841ea000c0d280750041c0070554002501c0076540c01034503c0d0119421018540c4800190400700390152540324943c0009085000c0c58000914400d21072a104007003280d00ca55144039612003038020003203002c0002e0345480240e1409141000100036401d0300f0b00000000d460600d070f1214982111803603201d07024100e00762194034420102c4050369548031944c11840040740c4c00540c5c5818120350210144001484041016180e1000c0000c606080d500300303c48952541c0005060038120004030b40480404001c680c480b0b455100c8128030f410301500d041a560060350810403103c0c06409030942550003844c0b800102c0d1311000006507102c0c00c50850070045a69550416960f40c032940101e005202152 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 174626681 1250 174625431 174625441
    0x6090b07060c020f0d080a0b0402040b18030a080d020a08160905100903020d05060a1b0e0906040905030705010f0f2007051507020303150d0f0204050c0d0f1b030c08 72
    0x103034010003642c402600407500400c030304058882c1812510030700c5a000445404c2042003568090180202d288015501140f0380f030f04015601540b88129001c03180c0030312450070380070341c80c0e1020449001f040d600400c4035610341e071044000d113020b584441c0a010001d03000f10041903003c00b0a2000c44e03d00720113911900752881c81c1a050042101c6c8076484401407010704000040035071030300c503206404144944040c000600c0c211100c90201e84000b03044001c0051003c0c108225583c00c100400f03041035044865100d40e036600c000003005803003040c0b40201a07010110b428000c10205400c80c002107801841d09004407441c110000d0126400f03241d400c000001d003c1501c86101010324000c01286000700706442c00d030440c284500c03458200c15104a40140d100100f00302c0b1205180c44413505030882100c07100010702e400e840e401c4a82c020900c001e0b12480e542c40102d28150908812a481504007240c01d224440200e840034005101031280b20b8107000640074120b82d201d10178807c00c01c01000070348408015842d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 174627931 1250 174626681 174626693
    0xb0702040906020c0a14160f06111e01050a060b0306061209011503030f1803080d020a110d03090b0906060d030503090106030c150201240501050a02070e0c04050a06090b07 75
    0xc1c0d038020303200150300b0460400451400c0c494024020300071078440d180328401c4000c8034602805243e2241412100101c18401080700034004002c0380c1e441e10f45036500b040041c00250038a10360410384003580344d80100a5032010019008a0305c20a03000004000156541051040c02c0c070003107840c035070b00110411100b03d1446044c1000c9400c4121000001106074842914000c840e0071904250082858404040c1c0d06c1c0354004c4c1c0c50b0106c0300d010307014031094500c1c665070313101c841c0640e00d181e04020b600451440341c01c1f4441d1400320013034034002003102e0141c3c0c6402c070060010b001102c0d05540755940e40c0e002900c242c40c0024014020b1001400030700304c1800740d440c200c8040d04080c1416465540b6404000080b0f8488900c0b0707006000000311400c02c08104ca000682101c620795144825949202024541011104c4041080707d07020b00f010740ea9484c8190b0f00328140350050b003007031000301d80003028400955400000340003925010303280740640035260302050f244c5080138464243d00200400401c00081d0b5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 174629181 1250 174627931 174627941
    0x7090501120e15041109090a03020d031e06090e01110705061f0801050f0708070e0a180e011104030c060203120703020f0c0d020d03050a090312020a1106040f02010f090b070204 77
    0x961001500c2458940e10f800407a07042d01a5400d95540725407541c202914581040300030b400c175242d0401028895940c0d50f01a485250801c151400d06a0300d41c04649207032a51400020103460411041050705d0f1a14240350090200d07617903074210740d860311a4881d800101e04c0111175000390410010407040d82c80e4400318070195a0b110360012803166080001520344402d0040a004103d40c148081d032034540310743d005140030001030846080080280d070045032034480320243d03000d5403039100e9410040f003200c1031044081d0400f03000101c0306600c2c0c4000d050418030100060800da0b4802c2206038106d66690304220303501c1c000d030480c032407540031010042001c560080e070080c5140c201201d4080c0c10100c140000900300500149070300096003200116103500355240c0b168542c03148040000700076440d002d49000741462040801b6190b01c1c1d90004605d11060f01035104122481c281100300c58613481c041c9440f0a80c2c1c0000030049011400d045c01030b11100340500608000d0350070000040d800c0803115020400902 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 174630431 1250 174629181 174629201
    0x5030312090f0d0914090606030609062b021003020a120911040f2f040b03040203010e010507020f1614040f150b13080102030105031e070b040f0e0709050112 69
    0x881100308001c81c501c002e0140c0e100c046202c4d1a0141c2091038403a03504009030701c0d00107030740c4500c20140811082d40d43d13403410359400003820b569100c01940e070800420940012054800754102d408050465041c5030030140d001030754401e035004a20110400c0c0180c02303a004080b07a802c04070b054600f8484054065510240d0350a0050a14003000502000410111828014100c002d0794076269080d82c1d40d0166100a0010f55421401c010004000c3d140e0300c015002e80d0145000c940c1000010806541d0250020003000f14005d008002e0750401071000ba5a500c900000c410440c0a030001e004e00f003a0171400820101c424082180441c9480181000300501e0300480c01000380740e40b107000e048460704846104001c0c02810400c699a20461120a20303011490303400411a030b80104014082d40d02d000c1070f00045617041d9800d150004c010b00041504210310b03904045400000071070009149900c00300240c00700e07090710380360b078400d07846416040710743c507009019190114101c02c540078442001580030300501c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 174631681 1250 174630431 174630433
    0x1106040209011502031903020405011814040c030b060d0507020f030309060105090c1e03010602191e05101109130905060103021002100e0a060522020405061c05010c1103040503031209 80
    0x301c6c07081080720b0020302a4804070800664041030030b00071075030030212005a80c0608140c3e414054a01104907540442003000940113503121105025518003035003110021500080841d6141c2a8000000004250460764000184211903903510800d10110440f802000d444c4050500caa003400180400000040c1ca45501c841c4100300140b103031400304880c0d100c01040460340f180c1d25494403600034134004c0015051b030b50102417a814000003c0c09031016000882041c88204103051141c1816802e0000858041d5002800c0181c220070081d80030300108583e207002c4940d00005030305020104121411004000e003183d10005c0103102615103069407401802440c030498906000c100284426100031a02020940e40705031844410440345004555008410040c070414400401c4044407003000c486c0406401190340d840400c4494540750004d46481d1194030070100460306913300f1500a251060424001404500049034050008800c0354100c81d0b0040065040ca8070140349110200340c050141d0300d00d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 174632931 1250 174631681 174631687
    0x12901051b0105040516050102011a040f0b0a090b15030106020d030902040f0e07170d08070f090909080d06090204150302180a06050a08010503010507140313020a15110604020901150203 81
    0x806a003d0003102d01c42d5200d44045c1803400042c0f80484018007041e0082030569040220595081d00350300340800074168100d40100f800180720b100d02000381406000250000607540010400030201d801010407400192500c50301b0841c58401d030b03211030200703000c1ca40042c5c0210300c803415214030a030807508480e400240002007003081496200110b4846040c0e600d03142d005028200f1005100c0c031082c08464110a020380200c090940000300700440040c08241031020100e4a0000740348625030003800341c54080c900b0800d1102ea4140103070300390031040c5113460300c605040020031002c030603000703840440c2d52140c800480ca940b5000154087c1d040002c0300c1c2c0c00e0b4840e0310f02c040860341e54100620018001170711425916580d0f0074005001d140c0580080b40281c1c14501409a519401810140418040100152030351130784945446940c1b15404003030340c40b0081d6500420801010441c001c0b01d00c030b880d11109203134100200c5840d12030030300b00c030042c0d0302001810040005100c008a9521100010320550349 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 174634181 1250 174632931 174632977
    0x90105090f090106090602011104080c09100305010f0b0f0a03020a180917070221120c0f07170d0e0a03020d050715030c03060e09070308090a0504020403050f01290105 73
    0x16084268444d40000780c1c000e03c20000f1980a110311444801468900c500e818240b1008664550b40207420354000c2c021080010089a4800e0056002e154000c000340801d6481c800c901000d04894480140305a0400c03a0205840c0f42c0021900c0441c0c1d4042c140000440c40c140c00a00703041044e18041d010a034450b022500000e04160902d13905445400b03002e900c81038240140b108102c0c811003108401032048030310b0400e84030002566050220426012581c0750380301012a410040604400c0341d003403040711404180c20151054102c0400c03504412030303842064401c0700310b5640440030144c03a00075030307111414405801c05c14808014580510101c4401e075681b1201a00400120b982140010741d46190402e110781c0d050013424000d1a40c50741d1256241404000301c2e848041d81d220083c6005800508031020341c461810360001064020701c2191a1079807410107075207689180c0000121546451044802c00e202e035050070540300c400c081c2c17818483c070050006403095800f10301480c1e40b14041c214410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 174635431 1250 174634181 174634189
    0x10803030f1b04120f140325060b040c110d030b0d02040c0905130203010503190b1303020c0a0e0f06100906030509190f060b27060a0314060f07020a0206090105090f 72
    0x1c1300840c85000020f1007401c0a0500c10b0011003441400c0c807507500304001c8220800d807100284086c043c441c0c0074031011a5010315000c00141510715440390814284084642c149800410080c2e40c114000103940000451000440c12500301c5036a00740d00c20046240800541010303401007880c00560b0601c010519100e10004110804081206040640010041c00141024800c0c10f04a80c801c500500d00d90308195580c004803030000700480e960294200b940c00c02e1500c2000828035850b03018000e4034080d41c403a10555003400d011516000c4910305100815100d00b001207640d0300000443d505e10b000300d4100f44d012005000c000d007449506100e142e006824242d44902c5d070840882c0b003291102559030706854003105583c03201c26074a04c0b44c0542c1c801e00f071000d00c04052002d401103000710002c1035599040d0005020041c02d03000038180d4840c195240a100c80000351240c010b4402c010003040c59541d42d0000c9135100709200c8002d411040c1401600c0c460b5010350094802c4801c010308a0826404c8a4042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 174636681 1250 174635431 174635459
    0x2091810030611190921050709062d0518040302031201150806010e06030a0b04060317070302060c030603030d0f0207060c0302190e030c012a0c030b010803030f1b04 72
    0x442d000500040c1800e60144d000c0c220441c0b84105041800145142c28034291072070f9508521881176000020101c010000b090045c0750150101c85420441d0300c0d200e40c1c000e41c91820141d1103020410181c400e060751411811080400c44000a02e03040485107248098452444080c10480640c801841000405282d490803903010f08076010441c9503a081030f2034003c000780000340ca600d044c00f0741003044100e96259081241d17803042540c0000700744221240c02080050485a2014210202a045c0a00c078004008020b16015020707501b11103650700e504105050501c000d17901c180c1d0641c002c000e1240340d2051908510512020798000600300469512440183ea04848100f00001d0b80007034446240c104100244000f07048902e00300803031030859400b00ba5103d1513241d006051010300d508642c0b00d08a0f5041d0803802c080c090b007561044401a25004050b404240001c0f00e400303c1400000c42d0365171001080e6441515002d0101e840b0f511400c00f20124100701317681c0308200c03d000300b00200e2a1711201c82c82e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 174637931 1250 174636681 174636701
    0x21140105151005030f0c160602310b07020f0a1d01060206010603060302030c0906030102040315091a0c0a080907050d0c051201060302150d140108010b03010b04020918100306 76
    0x3510700c0480d501030800004000503460001402000e10070f001d0b0040000b1045503021103000c02403980c4448001c0084d42d48035005e00010141800020072801445c985140e029240703003030008446950014009100ca00700c80e41c000ca280f2200240603000252908044001030001c0c042e01c00c9003140d0f2501d0300b451601c5200801c0c40e4031085070000400c151681000750900404180c9402c00a460465000a40340e0b64001040d910070001140030070141c3e9001c0d41220000c543c00380701c1146110003540c0c05030103044071b20b8080e1a2109071202024542d4440465107100b500703902c01451910400c0003040e2483c540183c80d509982c41650804a182c0d1113003554180c500b80030342d01c5c0d0901c032441e1008000c58500c0303002e1071820307590502c0800c0005031181e400d2403004421040c5205d84490700040043c004004070050080018a84000011030b00c4041d0301200b010030342507000b80501c0544400307000076403140c81102608500e0347c1c02c0034003541c0f00210b031594000e5000c2d140810125640c0d101d0070b0a031110404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 174639181 1250 174637931 174637951
    0x1207080322170a12020f0d03020304060b060c150105040525030b040c05040905090a05030f03090316030306030201021e060109230108061008070605041401031e0c0905060421140105 79
    0x491003840700340045000b4503013051008090460581d652a911032091061140c14140c010001c64100300399608070354240e00c40600b4907901c0d1000322100c070380d546030084100c415801440e800030440d403c6c01e00031759100d4651300c192105d420391b8689030040d110303001e0003248040556600380c401c1c1c1643d80d4011b41000262941d21162140d04003902c06003107450143c004410f95000c02d6a0800064021003921103240c42d2140c410785950340e80307480f18118851048180d0075030410010031410550160f20140980307000ba8225501c4080f00b001c0000748128400e09440540e1010004000403012078212402680840e9124411041d1110802c80ba580084e0040b80721900028100242c001d40310700403400400c10707030006101007482e046000d0094850350142204a1111840d07181c800d034000d40040846104041440400b511000600001094881200c0d400a02e11754000103680c0303091416101500d1500120381c0f080c00c80f0380000c41d008800c0800032540c401c01645156000340e028400c0300d207e100301c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 174640287 1106 174639181 174639193
    0x302090a05070c0510020304110f240708120f0603060705030601080414100b09090307150c17010612050c0a0807111c0e120708032217 59
    0x294000d44148180300130350170150700b598000e40c455405491000d80314602007081011903e40800619807180060381451000440449040300d030300710003292940761030055911104181c1100916069230300340c1c2001c21103450049030803da80544210050590340c0f43ca20303009040381c040501103504200c0c09a000a082210f203420701149140c4400413a901c0b541c08004044c080d01580c06d48500807104000403801d1b00100100340d6045a42c048640365140005508030303c0100b58080e41c0900f003188100e07000c228101c0700241c1c03c0c040e0006554404001c0c00c05103456058074005400200042410000b91290f298010611a0000305030b107001d4444110601d2a0386c501002c21000505943c01035400d80d0300680c110070700c0000e10009032002d040308207a40c03d5090f2200c010740301d1030380c05801c104085102c01181a104000790a000c150a840003a116800701103a071500d03100d010303a030b5031141d = true := by decide +kernel

theorem cover : BRFrame.Cov 174460431 174640287 := by
  have h0 := BRFrame.cov_init 174460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 174460431 ≤ n) (h2 : n < 174640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
