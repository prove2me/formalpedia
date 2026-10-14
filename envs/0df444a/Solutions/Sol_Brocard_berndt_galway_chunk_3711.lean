-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3711
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:27:29.678983+00:00
-- url     : https://prove2.me/submissions/e17b4c7e-cac4-4600-8f04-ea9bba1f84d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 667266187 ≤ n < 667446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 667267437 1250 667266187 667266203
    0x2d0a1e051f0c031a0609130902030d0507030306060806130c030e07120c092c0a021906080a1401060f0504080a062301061205040302031204261315052104 67
    0x44c0396200140c0b03090a101c8410381c0200d08210840c00b604040854a0010541505c0801c0c000c3c442c0e80064144240740e4079038070002e0b001145660925525010710802001c880c1070851050030a0320104283c0d031900261081c003107492348104d4080c2d52096114540700440c0005032000d80d81c44601a00748414082c806075501140702002013006a06803190004c45d4008071508204200f80b6003940408600b8400d06103540c0c003d1030205030240c2c660103d400c0d200c081c030300c4410350174500b4000c0103415404042d0031114542d10b00305406a2a07502c0300540c0d41910460304110080f548000411030752881160481e8095019401c580020031103107401000c80070200c0300c9484200921b4920f00105640e0074400d280008170f41010421a180300c1c0e5201542150092058903d09038100e40c005019950541c7c04503840010882c1c919052404255000e40c02c4d0032181c1c07200d14080f00079040d020300124030f0050f0042c80c0002400b0b20381c200d0040c011110200d1320110444081c0d02c002613000c4540c41d00300c6094074510 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 667268687 1250 667267437 667267451
    0x30601240503060307120203030f03090d26071b0213051501050a02120306060c06040309150e0f15040e012309010303080f06122d0a1e051f0c03 63
    0x280c040e0301624030402e0f0140c0242541c901c2c0c44040c0582081c44081607030907000030411010988d9a1500651150719100000c0031040d000304402044040e03210f60740488a41040c3c0c0300034107102c8901015401021502d8000c10300a20150b0564002180140c001c0d4071443d4a000d480c21220940c0100d442032407002c10303019080960500540d80c501c5601c03260350042e002480c40114a800500140d9000350000d426942403a210400e401c1c0f400780e00740c0f419004200030200401a001800490746058803a03490501c807002a030a01007a003c0c840481058403e02601e0300ca0361801c00c43c0b00c16200200101c1100d11310700d5956451440c0e001c9001c0e812a8000e1511510125403414819400390480750b00d40c3c1c0300b240ca9030f2064807041d01100c000d02280d52040f40c00c9112104400300b002030103501800c0d44038009a0708412a407202d40340d10800c038280d030750307410011621010030001c3c1014000c05200301c01849900030640752043c1400b075480140b0308070000c001160609503030b0030f07480005441d070b2070380f0108900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 667269937 1250 667268687 667268759
    0x4060803031324060e100b13050f040f090317010b1c091a0702010c08100b0306010810091a030d030e210d0203040303090b0f060607140a02030601 64
    0x103403004849054200d062918241c1c006a081d0703c4914240b02c000d018521400030441401003650600e0380455514480b100030f01804803082d480580091041124161a0a821500c0c020b03000d04070b4030442e440303120b94031070051003501d03150030400742c440c0302d20702c2040713002003d00e030240540e003a58082647d1404400004140c1030030140494000d9550552000811b980070200303000900ba0114007200d209070b031403042e2035545100c070081e540181c0c015000801d02a43c2800020b0840c000204015000c2080e8030003000100101412660858020718090b00c041d03440d4000c1541b06101544440c0b241d903e0100030030113440080c05080e041e8942107054407100c105c444d1040b01551092090051903401c074504103c2410400400d03550080700306200103050240d140580012a04121015408241c5481c010010800c1e03001082c3e900041121000e802810804089022406102c400500600c003410a100c9010700c200801e0981e1a8000d084802640e11050719039040d10107410003840c10a1100c02c21045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 667271187 1250 667269937 667269943
    0x190f0b04060203040b0c0a0504121b060206150411030109110c0a030207050906032b180902041409010609030b1302030a030c030201060801181502120a020c0615130c09091a040608 78
    0x907c0c4995100c0c2d0403c0e0802104d5400c142109031b003110014030085000003040d100705144001030a460300604510f14144450f10351501401a5091140d403070300036200219000e0070203580c15100070510000301001000c01c1042688680d0041440a00c41c0c0c000031000c06030300080714419508240e5843d80c164489105040e0354030aa849000500c5c01c1030000903070140713008403c000c80000c1c507142070458107107000005071954696400400d03070355030005414004101003400181e07011806488001941d890800e004001104902009140c1c95420002c1190304070300b4032b0003140e01034006007582c3d42c1190700c4c070b0080d2050489000441c055400d02c080003405100601c1000e139646901201960110745543c1c03815402000000800c80e030715030900c80040c9844c0b0a4800520904c001c6200517a90814100384a00e020340040401c100704a241001c00019101d46426154140007042c022660105141060300d00803119000822031910302070485000034001000040c07607500c155070400059494411080e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 667272437 1250 667271187 667271197
    0xd050316150e1005040302010213140a0609030c0e0604060302040203280204080c1908070e1e010506070f0f0204020d02250503120a0e07170d02070602190f0b04060203040b0c 76
    0x106500043c07071000c2400c0c690b411041d8850320920005241c580c2d10002400d0500c502c0d08204a00e10034200c1154a90070710050740c8000c0d20103414600c3c0703001c0c0395980d030044441340c5000d000c90148503080407c0d01a25550000d41c050341d401030044d51245800c1540e9251089113032012600c400c44050085001c0882e4030868040d56034450140010008074010b120385110041c07546120f0749489000051074040c00d1001e20094581d152800f20907040c4048056030808846000c0301e000000030f00100065a204000c841e0401d48c0209569003480c0207082854490b044810040d4005000180740210002194014140c00c2e29048075a290660b03031045680a4101e80304005289a004208018200c48909070056001171100400700d610850314a440b03081000c554000240e81401d03c8000d060f03170b0000e100a031182d1080d0f10082054524101d0001c0d528a002c403000c07501c90800300e03440018003030340324582080c15402482006603401c1ca85050320081d4402c035000e4031075410403000f08441800031000c9072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 667273687 1250 667272437 667272461
    0xd0e0d090b04050d080d0513120f0c02310c1404260a080403050c040f0e06270a12110a0f20090405060609060a030515060d05031615 58
    0x500300307070810b802d201550802003030940b170a500a020700c03011450705015440c4a0851444041060115407522071001540301d40468144041c80c18030116840d4400c4082d00300ba40c0440e980c0407103a2070003400310503400400b1043c0c021400b03006584580207546400c03030004142d0640d14000c9003103140c90302030854043c40c002c5c034003d40f5140c40000c90800307001350800c4c10312200c02d00b5910040556070720440c85900c25841243c003078200e004030000d14a0a8404d110a10000d0f1703001f40001e0402d21502502c1d030740014510540320030155540308005104040c40044209500d0403554807083d24144000b030240c951152600044a2070078203c0964804110120350342d81c01860710740702180030f5036142d81c00c043c0c3d00c103d2035042d403000ea50782427280d84101c00140602e0007480a418a0305054080c041007000007040c260040081c008204001940041c16040d5a1807015641244d5114280054002000313081d02800c544000b1030285500510480d0200d503580c13041c0030010700f0b910203078280c2c01a14446a0b0308 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 667274937 1250 667273687 667273709
    0xc120f0816050c03040f06030b040204030203191b0b0c010f14220209190b09010522061a0d050108120f03040f0c1412010902030304030201180b0d0e0d09 67
    0x881c00481c84904021000101402d1007410010b45080c1e0368516007040d880804858411201080016014401c3c0d0000c04d4082d80c055242a0468010950301d200c0c00004204594510038036009200703a01064216016202c02d5204807150358038000c1c2e6050300500ba06070959481e01004011880e2588500d0800d242a503580d001d03556501426a1500209022010031404103038501d83c0c01644d441200304d105407900a51034944406c00600c0404413169490300c2c6014150ba000140a20b5a81101c2c1d0040c400e000d039014606c41303034040320107005042d40e81d01c84210400808030202820395940c1c06070203c250b000d1810416a039890340301c00d6584220510200c140342d4104844030042c102c03480210780c424060550207810101668640010420a84c05640703980c60303e03141851140382080c0c0c0402030b242c5034ac0003031011450780d8000984030300c00e03440700a05005501004203840d034804100ca2008181d000034480e182c1d10389000000c041c0044481303501e2035024001c02d00501601814000c0141ea5840c446 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 667276187 1250 667274937 667274941
    0x8030a140c1203070306080114150103090201020c04110403020d140d0e0d0210020316081b03040f21080a230c120315040f0e01062907031e0c120f08 65
    0x400c0141d544003801213010151603940205000d9000d00401c401181a441146c11902d805003056181c41c144220440c10981446000e10142c1c0e8006028075182200712800100c072072801030310098030310807544000c0d0000c00600c40a0103201c0c2c8591a01c45074810b1009030740c89018034240489404810300c2c1007551040342c29103200c01501b0110a81d0440084a00403640b61078400700c55a0541114110200d400c1440020f00d82001a41682001200d0030341400450400d420314a01923060080e5000f08640001600103c00d1707000c0c004040c0e41500d0781c1120b542c81c1d480030b0182008259141c060428112408038178400c40308240807904443c4028580790162000d100c0312500914140c1c40500030811040c0c4414645407903070b980d84103101e019040c040000548600001905003990b00a40c00032040840481c40d40c40e82e9034030ba50300381c00c0e000024540250f0300d444030b203425a080b001c54004a10320003085441202080d402a04107509a8000e401020040103001022610503105015076400a104100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 667277437 1250 667276187 667276213
    0x10506030f01091832010c14280c02090f04020f09070e0a080a060608280804120b0a06090e0703020409020f041103071107061418040608030a140c 64
    0x21151042004403480000c407010a074850701e020784200e000700c210310001044101d507407020054a00c01461820170007031103031228560000c2c020b143c40b04108a01884002004100040550348407200014025482c1c00c442d15003240c01081d502c2420822401900c1d0600802e80000281246511699008002c5004022104144030198a028045d0001e1000030b140389416965500c4a0b003000c0c1003581d000345103e00d4103080c0070f070964601d607100c10000d070048580c1c0903c41c1c20150a849034000103180c0702200038034501d4002218031603944542510142e80c1c0540c41001b1054901c10300ad84001001801040d49075503180080f0740d032501340c400340f0381d210307a40410050516030001b0f040180002c01600e100b04241005c1026100700c180142e038850030000c100b11800f5000000384003030a90740c10040c16403d04010003c0c001c0007009900d413421090208050484024611082c0c02070b41c000f41082c0540c42c0c0d0b884166669820021201000c150b15182101c1400c100d0300944224018840040401c403141070303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 667278687 1250 667277437 667277441
    0x140d0f0c2406030816060b0a0503030a08070207050a0f030b061509040905031c0e0d020604080d0506040209040e060603100e03030411010c05030c15010603021207031a090a0b09010506030f0109 84
    0x194007500030349410000010402003401351004c9621405155014401850114101d030440d650940c810040b0100c148a2600c00200762241040c1c681000027003900c0e2050141e2038000d496116943c030000700350010507480038607440b54085030b1180b1502162911103004102440c0c20760140007054540034000392103039251a400505481e402a81a41d242140c0c1d9200300000d10341000c0ca2020080d203e400d00c00461504110a140c100f00c10302c060101400d1542d0750310560320900001403075143d00d40001c95203680d20f560440303040d804000c000704094490050020303152201141d50b58820301070a200074000031003d018a408818900014516540e1181c0d1155100f80341c081c4100c0c1002544000440003030340400c02042c0014100300148100c1044070041d03000d0782d0050304000101801401403d0240780401c2401d038010303200f8200401c103594000d15042100d00340384001907001c900d0005006540d105540a00c10390207007a1403503004d41c3e172160180016880103a44510480042c0001000607044335 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 667279937 1250 667278687 667278743
    0x1020d120603060204090501080d020714042a171b040b070809060309031305120a020d11030a080306040f02091806240a1107060c0b060607140d0f0c 65
    0x322a0014007152242c0b507003400c0381c010303420040000342c0d0f4200501007500204035030741e00c43c48244005d140c002d060580303100000c10883c841c9070041c0d0326000c5100000c0c40060006070074105005140101000d940710003082c50000070f5040c1c0610146402183e26084680c1a640030300c0503549205142c240307020003400340360303004403000c4d14498014080c241c55641c0d040e0040d0b02071245000159110390343c21546103045c42159028502c1051400300b0050002c1010880400151301107c0480e6500300e42c0c10246000c4511800c6258907020b52105081008407020180d401503005440c100320182c1e002403040224440c0e1200308c4d41c8100d540900300114801800c04591048011301014002842c8807090714900da070004000b80003600208a0910320399004010706100c40d65240140741e9107180074400f030000740c030700b800141801d0100c6c40062080e444403070440d10055880110840c4010400c010346071140700f16000e40d80000e0a44241b40362040c0b149400d80207182e040070403030400c03032240c0b0380c010702144130 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 667281187 1250 667279937 667279967
    0x90907030e1e03040b07260304020f21030f0414090103080712110a12170622090803010806040302160303211b12060e1317130324050601020d 62
    0xf0030400031911518000251550078801c06507841407a240c0e45c446424400c02004000c0000c0303041c0f0803c80581d880100c2201050b1060303904030800324607842c074001020303103003003c4816a10000034849000c100c3d00d8020000c40340c5000443c4010041402080400103080c440032705186400c1c003a030004105003550450f84403005007010002d103d00500c2c01810000701e000181c8501105034200012316400c011110490310241180e00c085181c5940020310900c0110030f51200c0715061030040700e1a0350035502041109400c2000740d9180e41c1e41e0308005a032541d040b84c0850043c01a4035010b0f151007034141140e42030fa985511281d03249001d00e1088107030b2100040814212030340b0380964000d215043c0001840d10721483d030303d0351811245030703800703100707807401a07000d0024000071104200e048100098030a10071036201d61541030112000d62400c1c1c940c060760310400301c040c880460010400c02d5860340c45106050344030010045418646c05c5c1012034004550041c0035030400d020760003c2a10a0f0000440841 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 667282437 1250 667281187 667281193
    0x114150d0f030503011706160f0302090d0809010905100c0605190f0507140403110d0201090b030a0524030d2129030109151e050c090907030e1e 63
    0x61a40c407242903584000d0000e401140000005000404da014403000b21441c02500410b16410950742c402c1d052260062010100000322808400081c420740480c2c0602e003000b85001d010305a1418414440c0c1d002110880c0401c507007420000d0705013072117440034107101c4441e1282c81084416481d20b46c041e00700140440d03220380c2c08071313000c146260080c4640b0788131100c4118002103610346444058503511031f0403074840b1407030000d11003000003643c0d11010070b078a20410f4070a6000152248016500c00d409a001a090080c2c0801004a007214513032000344200c0014010b98008240f0600d80700345850741031045509a0000204502c07100c0c003548103100d20362500c0700c40403450258940c0c80f1080b06c070f03526074006030010200028050316490308100e20742880118000c2140300a01d940340710343c4034078291060455607282c101004800c13000c1c901280301c103542d02d50144502c3c03400c841d80c0c1c0403651191802c240300310214404280c0c0d403031003440b51115603402c1c50001c02d03e0050b0080c1d1040c00c5d414190a058540c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 667283687 1250 667282437 667282459
    0x40c03060c020d0f02070b0d1802120604050c041b0818030a0207030302060a0c09060c0614010303210507020c060705100c0906020715080c0714121803011415 69
    0x50264812039070702811a07809010032001540c00185100081c11080045611143d82440108035150442c2c80c145289100000d0383c0040c40340542c040325070144003039880aa072032040c0241420100301d0324801c61140c1c007926030b1402200f0030001240d0740c0c40c9600400c506046590b02600b802030ba0442d0700f20034401c091401110240c1e0409240d41d000b4150400184c21a800410800d50100809900f14440907020700000503604801807540c02107101d02c401304264102c240781844003a03031050080c00d440b181108400d68603401c1c0075020620813000c80300801801034010b03c100c3c0c0140b158501400c410350151980307030910000c014440e0010a4141c03814000c46401c0c080c6030b50580304a4246061039182c00c10458070340300c03000c0e00780001540030800760180341800128bc0360340301c15000d501c10881c03400c060301c400d403600304a00304080c401040d0010b40f01c0c1d200702001c5141400090700b02c00f00e0040036501d4050309142410b00f60303480340b100541c5800000d00030840c112103e000e46200c00c01c0144c0148031070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 667284937 1250 667283687 667283693
    0x31b0e0d0b041b0b2104140601030c0f060e0a0603051008060a0903020c0a06302c07060c110f0307060512011a27030703060b1305040c0905040c03 64
    0x9080c00d450071111032894480f00c40c1c8440a0291102c024901214901d0034412100b4112000c18420510380070a21785190001d0104011120400c003071401c807408645642d83c480c80c1180d0105124010003005c0041d81c4000a01113100c1c4507240301c034603800f5042105040c500342c000d07800382101070000d03511030001c0113010803600f07010440c03103100310030b2043d01040d483c401d806e000e4100007108001601070501801b0502031143c0007204080c40320700f2403020295000140c000705821039902d08042110781d04100203d040607441605484d0a180d40200e00301d091818445220780d0f4038243c4c494040850036004044000c103100c0b04c3c024000190250191001e100b00000007400c02001f40c2002d00414400304101d584180d100c4c62440c054115a5503001e0085007290034203810f4011012900c4a191907617000481c02c81c011220305000c0200035040701c9200f5200c0c90408042d14a24903803901441e403480c080031101103a40101405541c00c0784450203400e00380700c1c21a01411005100382c039002d417000800000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 667286187 1250 667284937 667284953
    0x271101020c060a0206061503101211040204170d091805040f0c1d0105220b0d0209130201080906010f030f080903030f030103051615110708120415031b0e0d 68
    0x100c00c07a1340c2c084c00440c64001c0400c101201c48680100c01c81c6002e2040102c1c440912804005550301c0c0c0060a440703887c48d180405020910491464006001240000b14050003001e04403040a140003070b140c04540c000011108a03c1e50320801e0350030710205144640e0b2810a6000a400078040c009043e9420f20320384841c08409401d50090602a01d4101e4080d1a4401c0c5404640174003800c0361000b60300c00503007240302c80d5080138100c507803c0a41d540d20540e410399039840d07540049640c0078081d2201e030311300180340e4851605103501c02e80c0030480c8100040c509603004035071039040c1c8e941c0c607140f02d40107825622244160320155404840c401400c200c054610350381000601070840350070562503940d604528000e410104a41e249244808544a052054107100c034942e2420030518980070401009844026284c161503501060340d9000340181116118180b00003041550410a1019a25210440214200c82c54041c0110000012411600d107461198203090f13440c40d0024907000c140c0c41a901d070b40c44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 667287437 1250 667286187 667286197
    0x60305160605130504180b0901050601030b040501031a09030d050c030a0c0f021e010f020708033c040303020f030a09020f040b011409010504080a0b0a271101020c06 72
    0x2665502600d0300450514154608001500e800d140031801c0c0050340b4041000040c080c06800d00c15a140d0201040d250f40000c84000c5840d001241c0490354208001d403140240b80507146980040d0420100c0300c2d46040c05e003d2181200d07445602e0015407100305105072150440034040190324007040100c1c952041c180d01519014440806440f030b0740c0c2c10400448001c842d6400384841c1880a0188500340154021440d10101e0710010300d0000f10f400000b103900d00514003442c00380040c5201143c003d00303000a0070043d51050042001140646111030300d6942a80f00f81408610480300c2d1000c10b805400e6410714064006209040150a0941d4145120380c2034100300c1340740a600d0703030b11100315003946010b991380c6020f80b0301980c3c2040110400c500080960141040b2a1002d220004030429640d1240084170020b0188005882d0444001d1070000c3c3d10310300c20b980075840769040c00341c4400001440618000110300b160445694510240c3d140d080c11400070900c541940170b03140d00364003e40c4078a80140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 667288687 1250 667287437 667287443
    0x50607120e030a1208010504270204060812210108190201032d14090703020114220e090613020f0a0e0a06060311090f060c0102071b1419060c0f060603 66
    0x1000204c40c40080c200c02c4140c1c4031900c5181015070020710600040045000070458070414400b1981c513001040180107e07501c005428469074a500003c40010320141ca1740d07081030600000503c9001d40d001c2c01680007030081b07100320b4000318502201040a0700700751881500c10b050105110715050384100c102502c3c0c0403600b207070f40140d000044105d0810302c1030100d4911a81c0c00140541000d0000710750b2041c06000c000e060140c10030540030040d1444050f1031080403c80e440166070840c045110362760503110300c6150f01e0b031461600422109030012030517611520052884454003503582e0204180c401c3c203116900d1304541181300c00320306e40d410001c05500c682d9411030081606480c1c1500207040701c2a202001c04080d0043c00314103d641c0d074902403000b5001e801c41d141350703e947c5040a02402841512801802c2c180404034880418082c000c0c00301c2100c80781071003a8a280090000d200c140020100c40c500d00307035646403083c403ea0703000345003000c10107003d40c0b403150b2180e0307040c2e580c042140c03d11380013a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 667289937 1250 667288687 667288703
    0x90b0a030c021e0606060a18081e03040503060c210103060b181504091a090a020109051e120a020301020d021207020f03031b0d1506030b0604050607120e030a 69
    0x801c051940412840e80703810900c800540c0c0440501120980b0703404050011849402c0000303403908032900c140005448080040503001c9200c1c0e5980350207544199580b2130704580b00c403c2c8100d0520020210640d0102e6001501031700040d95072014000807903202c0c0c1d1100d410300c0714511680a4111f00300001c41d01a505c141c5e800a401c04140f404c200d140340c0449140001f80001c002000308043c5689e09402c00c1d0341003a200815909014034000c0e01c045603104086900000350000c00c940b401002074510601d9000ba00c80c1c0105503240d20070b2102e51462492010315400e20468211483d0400078107c404401206040d00c2880d80c4a50019003664001c0d0446900b554003c01c1e0003120742c10400800da001030349070008000c0c3c0c800680c2d4041e00c0c4c0c00003c00008100102c6c522004d08120004100c669181840c00100408070076904038241046840c000c400020345000124295818a0b8040300d040d81d40c01003499040c65006e59444449000900c07180d400c001e00c44902c03400d162010040105010303c00e0b01d035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 667291187 1250 667289937 667289951
    0x5010c0218070f0801270507091a071703071b020102031e091207031a040f170304120302040b0d0b03241815010306150b03010609050a090c02060f07090b0a03 69
    0x8000c00130001a00b10b00700e284034418009030102c0d0f5038501c0d4032080e00d603018089404d50300c800c030585282205520420381c2c40350b1481c180d00c070170000300010108c0500c1307902c3d0b81800603c0e1580c0802d803808210354010105158280c00036441d0210311151840f80d00c144126450100c103c8203440030b0a240c40c0d4034809c0d004011032182081d142000001c0712600701400180500f61440d15100743c1141c00c07a0b00480a11044800301d010310071582201c450181d045000c0c0c0c1c0703078600900d88400f00740c1c4c0202c401b42d030b1851010010200c8140301e0300841e01254480403000f414002c803003100c40c005003035500c0c45550511941a00081070030000700c00c0c402c00030280c41500c00c5031030301d43c4640480c50240ca00d00c1c0310701d40146200c524401c170545800790559401c80c04c002916181e001400051240e15004a1940a004000081c14035170001c5c04905492042c0d1305040c9560303981400e00c017071756120802c40b409a08070000240d00e62a4844005510034890b143ca442d0566039100d103a40d0a40c004940380c0c0000ba15061 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 667292437 1250 667291187 667291217
    0x9050f030c0f0c060307080c04120b06180c0406050c03040e07050705060a02090a180905100e1908070809031c03060f0b03060a23040e0d0f1805010c021807 68
    0x541110949440c1c090f00312a100500015000c1c4001031170032043c40708490100d0710300340440003038901405e002e8180301e68484075030824603070451081b82c01500c22680e4521300c503000101e0000c098001c48a1401583c10700c3d0824a0a440e02d8104034008441c0384801d0100054507a0026882c9000d0829500d17116a6031449081c410b082030303002044040c43ca03004125001c100c1c1c4640408000f03ca90315030100e9100483c0b039101a016050890026040d44203004003051540d0305035004040c103101210441d400031582880350603000785000b01c050641d038810f00c0428003081041c00200301c0c0d444020300b900ca00b0050502461a101a40c0c01070b00d00107692000c0901c03c0c50880c0307459001034a194200d1130b00350b1400c80001802c074000d80c000d80301101d11542003080c0d9403950748000b103030500c80108144641785040886075540c042c0d10b2102e2002922520301d8a64030741c0103214503d0f4104070200b181442070704003401920006c1c84403000301c0c0c01807860003500d0028862140e9a038009c40159454240b02c07980c841c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 667293687 1250 667292437 667292443
    0xa0b04080316090f090f0e06070e03100603030503040b06010903050312040b07030e0307020d08090a090b1311030f090a060e0d080109020a020a15061710240302010c0609050f030c 78
    0xd00b41c001030000301401440444a0201e0390f004555081d040415420100c406500141480c0b10a0b00e100d40300e14014051030719048a04402145016001c84002c400c2e01c406d079005031461484090045501003002c14041041008203a500c03400c1030518600059403079984501d15070008480f010404804000e2004111182e1030594001c40e451074144841510f040c0160307142d00c1340c0c1c02b001b4420a0f40742d940c0d000b0014040251440d0010040800700100e644030315201c0500b07203803440c030f612812818540040d44a103603c00d104035079251482c0c90341140d540111b6041c503220041e11321240d80c451078401200264441c080c1c50340c02c10052015101501c20584083c0550750706800c02c400c0c1e14010b000d86500c07103500060b9041950740008140402d10900417010303004101c0341d08400c08400981191042c0f42d00001503510a2044544e0708200c3c3c0c14a035103a1441c0c08040d00005c3d62800004041000958403d4401c0d1640314042c803c0014450900e544141c9406165000341d1070300d0308003080380d680446080c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 667294937 1250 667293687 667293721
    0x1031a090a140712053103030b040e0f070506040e0c0304081c02040501111218010504050d05070305160f17010219030506030d050f09190f0f03020a090b1305090a0b040803 75
    0xc00c6e40860b200c0390032001c150044045a0442480d604114042d4060600ca5003000c1d504200143c81003000b00784c0f0000399900c80700520004407071481020000105402c2035021170b4119440300f80d43d8074060300e0701031103c04d4070385c00a0416a880c50051182e00020005501710510060004000599070b528100014152100681092015410682d80542c240410200311402090000140340b21104c00e000140c03418001e036008190062222241601048000588030003941d000303408071102d02c030110070905154509405516800500e403182040382035a8900d051401c08500e40015041c80b84001389201c02e00346568040700001d40320740034040f03903042c28030040240034400e24107245400c2d918200b60100e0301c42d074820680940150b1000c0c400700f0140a101ca006400700140c0c82c0c11540c0e850b44070000c1d40e005400240d110309504000010601132610944008030b40c0500350004540500c04004001c204c02061442c41d4000c07000c0b141d002509030f43d20180f1442c41008016100d040400b942158040700e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 667296187 1250 667294937 667294951
    0x19170d02040509010b0c0a032f061f03030f120915050114060f03220b01030606081227060c0f07090b06030906040f060f0f02090f01031a090a14071205 66
    0x201b11385010b507003002c14060b40b0075405042c0702c52081201c5000b400c1c40d1310820000d2000880c42c08520103454008609a801105800c440c2c00d09005c1c9091104071961862100070041074051045840d954020301d0140d40010401400240703488d40b54641c0407640d04059221a41c07140d07a00c006004c4c403140c0030510941507100b502c1c26820401d084901380301c98800030b801c0710301d603500c2c10740c1c2518030350243d251450f07069901c1680b15655594130700e0100301404035030050741030b0390044007011103c6800c084156003103480f82058160000303c02d09031faa218000c082c00a1508902e00f08950a03118104004002c01040b401001b03001c002e1a2452090407200e4110709544114010410f00400140c0001d01980203504500c007270000c9034107860184018201c030a030a0701f186007041703600e00340140c490380580b4010038103a4005503004156001101281c62340b82075014020222580c400007030400304a110f80c02115000001042074000f503240350380d00000c50ba001c000a4a4001f081c4081400e07004040d003120b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 667297437 1250 667296187 667296209
    0x1031a070318110609030307200f06070b0a1d030c070b0c1f090507090b0108060109061209110607051e0c09010608090c040e0d0f0e0319170d0204050901 67
    0x800300e00c080c41ca0642c08020300080b451414001c070b1a6104400c5542d690b030700074104c0e070380e030700c640e203410200c003a04c1080300c040c0c0c6445000d404070582011056030b140c22000900341440c042150340d1b00c4000d01c9004d0424800c1681d10302d10188980c0f1410090080380740c1c21b90065840c0d100c0d00000d145050300681143c0c4284405100c60101c0e02000500740020b9941443c0ca00340c0003030b10100401c020500c210340500203200304080000c0045140c0d0141d00002c00a0342c801c1866a2000015a03031000d051007200001500f0041c020903107002507015405140c402c096840141c40711200040c00780d0410a41600d15800c00000e00f884288201c04143c424246c4101816170781d40f98200050318500144070316002d01000900040035544213001c521002240140100240300c19104260365410400070610040b903038002004407050301440000001805c003d0041180703103144840d40d141d0f1644140200e40004800da00700d0032a038503a001601d20220070010050f00d451030402002210f880c180e021400d421 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 667298687 1250 667297437 667297451
    0x30207020f040209151908060f0123090310050a0b100c0219050d0605010e0c07111915020303071b120c05031c0f0605010e03061602031201031a0703 65
    0x20300c0c1c108444055100c11034006032904414004600c1c0c50a110080303d215400006110002a40714038a510b1344240365038031403005543e8401803120b01d0a101400741d0110305060008401868040008000942d10400309418403031640c0c0840d14018540d00b00086031a01c8004002c0b81180034070810700354003004c4582c2c5403409900070010304511040c2c00040d00810304c40441610840958009000400024140000384151070400c42c001308002c1c0500e5000d008004085250f80b210352054514007030300303c56959010902d0204100c0f443c400a2945d4400100074100040d02d140b40c1212850f11082c3ca802850703603460940c0004201040a858990f0054070902ca040085802b050000080048609103c850b608550420328598020030394448603461810762004030661aa0b00800805031441e9428807002d91190019104184501101c0350180d20000c00594043c1002c00c5550008541d03005807490511810000502c0f400241c20a071003000f8141d0030680c03501080071426078082c1070b91400b08002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 667299937 1250 667298687 667298689
    0x2301090c09180203151201050f0a0b150c12030f040308090a1a040204060519050f0f060703050307121a1801080709090303020f040e01170303060904020d052d0d03020702 74
    0x21608040c0b03000142e6804800500c401103000c104413076001c0010085928101ca505410f0301030032007100c4c40985440c811021410000c04e80c040c1d9200760344000c1c004502c8094200345450b02c0d03001030070305540f180300308000300700d44e6046607006500480c900740e05a1198a82401c02920840d80903040c0350362903001c00d25201c04200481ca00d078a442c100540c001900c0d07121400001d001e0400c98005a920068800c0d44900600d540712000c0c04943c1c2c20744900b090107855100700b0084943c0301011940181e002c020410000c1c0c458001076a1012013810514041d00782b82c00c9600c00c030360102c07164619440d4402100e842500c0e080c5045003003070b840d58000070b01941c100b425694903552144694805140c640007905d04040c06901994081c0c0c4201031504d450703643d85c40b15250807203002e10039100c480b0101720285910b004048201ca00c0f0380f0000d003045485890b41c1d0300b44100146d440c3c905842a000300d40d0407807820340d1a16203d8090240411641c0c1103842060701b40390400ca101120207040c03602c100071440c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 667301187 1250 667299937 667299959
    0x30702060703030b1815100c02060a0818010509070504111e030c21010f0f080307031b020414070905040c0806130b09011205072c0702012301090c09 65
    0x1d03407a414940801c429802401188554142c50101c2c1d00c548078140c04c000751400a221064184601100d18015200041c4021755088500101c041d4105008000c0000300341e001d080200e4000704416003806001d011803200b1421034405441d10401604003039000c020310318050007080116000002d03420f10b050700d504140280029019030a104441e0040001600807114109484800c211440c0c0da141c00c50108601c184100341c05d0003041c020761b42891011800340010203054098411450040d0f20f060031a40b01603500c0d11100704011618084407460000680b128010141100f450045080003810020000782ca13a140541242d0b0140d803900d420801c407282c2c40703a045900700c10160303007443d840c8103108042d5001e060b8403860550442c40e141c4c000140203154502141140b4054420340307100c0b544a60700c0144c00d0200010004025010090342d1608443c003100094012100b4000081c0380c003000184d26003800f09a03c1e801071000800001004001c10b60302950b840d000c00c0b4a0142c400604000d40008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 667302437 1250 667301187 667301197
    0x2101e050601180f0512070b0f09040b0406030302010203180d020706030216050607090305010e0c060403110a050a0b04030203100908121305060a09060c1805061e03040602120903070206 81
    0x42a468001151903a4003546211031850541140121074680366240601a600180b107540e000724010340381c0c48402e01c0080b8804007079583c00d100c00307071521055200e075070503035084445400c1d403099860840010380e507141e01c558401503201c1e80016850346840d80001040000107007904001c1d8126410540000303a01140100075200e4500300107845044000c003902208120309801002d0713200712005e000340d131b60700109400120b91144000b4004c80d0b1490a545455080c804038031a0010310601c41403000940c44919441c070410084c2030202c0003035403103002652150150b4022444c84134001028001d608040c0003a080c2589680402d00030102c8554170030005203e00040c100703e8400312030108100c10b0403850800b000c150003404541c0c4a04114010000400714140201c628901c2c00700400265401000c481004c119065100c2c0e070428900424021213a1055540c0b40020a45030b04030b07098040f5000c0514007550103408011b2b1034120f1031700442c0c0810006011400b5680c018808000141e54000c210340c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 667303687 1250 667302437 667302491
    0xf1413090b011a0c120301231507050a15021b1605041e022101050f030a12020102121306140c1602040f0f0c18050112020901020f100603030210 63
    0x224000e60082c21400413805081e10203841c40c000c5216180d01d40312060091410f84003a210b0480c00a55140b051403198034a0710007680e00071032400f582000f00c2caa0000506112401002507030340d0300c1900c1e511002ca8416030101b8418695000c40d4502c80038a81800000982c2108070082c02113845820a010a0402500c0713940d104948510421003d084e502d0041802081105015515441e40500c600070202051000c10f0040c0c4071000006100c1c174000c200c4500b00100078010308468003a5481d00d0500c0b070b00f00515401076640801c48021102c0100d4100340c07041844103000e01c0d240c2c100d80740036425217001c4140d500012007000180030051034903a0803101907140390007420003922900c0c40880c3c00b401084111014a07440d1034003503986030a4540003071124621030b03560605220040c51805e036101020713016190026180c01c410900380822a402007140c1e500500440300c40c00c14841c14146070206824015034800d40740e00c010400c00d50108103504c021000b09006001d100c4401004140c07190366180f5038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 667304937 1250 667303687 667303709
    0x111c1e060815041a0a0b01140711040e01021b07050306070207080601212406060914010302090315041406010e15010507020d171803060c0405190f1413090b01 69
    0x800c00f00b1084139800c070b4802e211250702c00110b14000300d40344001d166410f100341c08603101c001ca024565504208959109500031603108034007480c401440014654804002c034190340c200182c00382c141c07045240030112501e180c01448994108410703d801c7c04409070408065500c05101840070703c13004181681502c0802520344007074808494854150710b03940700d0183c10b1440403c840540b00115600c0302603080ca140b48148903e550300c60044800316402d00c10b01c0c058620a01701d109180d131281d00103060440c03000b41107480c0c031001c010040340c00140030b4404075554401444030125000050204a0040c409801c10002c50f10382644201a46d41b108910b4604016000a41c041107564840740340c06095080344a00c0b003a950240c007200600e5000410384a0306016100c2c42c5841d901d000a400b501c40c14910a0140c03e0502c0d002c24810061034440720340c40114000f15020070051125032600c40188201007003203902100a9003404100065403029080e2107003401010f0007c510045d08690448000390b0320 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 667306187 1250 667304937 667304941
    0xc0e0a0f05120f1e12132c070c08040803030112051902010203040303120f0f1d240601020f0604050303070806101413051903290a111c1e060815 63
    0x240c44c141140300c8001c601c9190080380d0074109000d541d48800540d02c3e003a1025003849801010754400104980240800c02d0042e000280d2300f03842084040c1030079208903030042c2042d468003419030658101340c01084008004054181c14010304003c1c0304903003504c01c201d000004000c0c3e00001e4407485640000380c144042d580a80030341da1380740c1e4045a075807a2091000c1065000b0082c484000c2d14159007101070400c280243c01d21510400b14180c1c80c030540d0882112281520003609485042c001800309042d806118500caa0410092040602ca07601c01e0014681d070785010321014120b8039000e0032060140d0a070b40302e52080342d50080300042c00030799103d01c13183d00e49000140c400c2416041c0d80105800020302e405003510450342a24060030350f0310422040f40c07496102013401250001180c450301f4045252804661030300c07025800380030300802006119281000d000140d400081401164100d0599120303035016000d0609030030107032543e030145010f0286900e404826640e40c109166142050003d10340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 667307437 1250 667306187 667306243
    0x30b090907120f0b0907060306080f100c0915090801050115020a020d0c0f030c0e090c06042102120d080a0e07092a050c0c01090f06030c0e0a0f05120f 66
    0x2d103000b40c607138010600c01103803610100040d114940c0d8824003003c00d040c640d021640800100e0710003990003101004000601083c0071010140200c00351038001c0c040c8554000c01c10300e003c03c11540c200f014030f0700c03545000c0e40362504007801c40300d0580c04000b60056184a00b03001030b81c04240e1401c0039404860300202d403504c0d03007000c3c001d11540b640103006810070017900008214103008a081101c6c1006031100b4160b680c0c4007030340d803103a41d001e466940c0110104024016801412130420071112114000840c0310705075400715650300319026165401d640919481c0080ca6030000c0b07090351100c040c0c0018080c007540c0c8100203544040901801600580782c403d0b5011984207908403580006400e4418501000801400350156001450102c1c20340030b0200c442c41d6035402429414103c0e002c030110312550500c1c1810490050002495010411159140248441d40d8051544000d001007400421600380b900c4108604058402c0200055402070300c0b00e05400c9070701142103442030024a0302d00c007061003050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 667308687 1250 667307437 667307453
    0x4060810180b03010509010509030403170409050c19020a080f250303091a0103050303240a180b0a1202010503070203120906061216061808010e010c030b09090712 71
    0x81c010484041003007201401500681e04407000c03884054000300116118101c0c01402d94034205d070004806c0c0e00801c001c0002619210b010098001080c07030140c14251510713486415211300b42e4010180798000300700320785a420b41c0103002108000d98001071210020b036035503102d200e0103100e03105d549240d00481c0c1820703807940b400070710504044011860300c0c0741030040c079020340103190105050742c05a0352807144400b00040c404926043e250840010760840d520303410111489512001480e1810f1810214003001d62524100d481c041c0001c030081c0114240c090b45d904046aa42070032071032003080e04030810041541091041030340c0079028a401560707980c80b244141c0ca140b0a80105000c05c0040104100c007903100802d0482c002c600881c0c072800c0450b141410130390b41d54081c00c0304000800c2e5140f0b0401c10b0f1800f40c05808182c034030011a2281165032900054219540380c1041c4c45035035105d240300c519080d80340c070500062010440e915042c0d070500800b000d503076071814001d1000c0200041900d4040c0b000907 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 667309937 1250 667308687 667308689
    0x30e06041101110a0c080115120803150d0506010608061005041202010203092d040c050a2a0b01050a2403050c07021e1e2211040f03030e1504060810 65
    0x440c04451480c03e0502c5c02450411061007240c00325481e000018850400d854410421991b038408940301c0c0c40d03c6619060f4940c0c1c0042d20f00001002030101804060300c48048e041c0400d8019800307031032250f240500c040c4c0b0b101801400f5a115034914098418000d80040c103440c1510091095518400c0345440140d16610440001344d03400454407040d0300440c0140e81407062081c00303040749402101f00c5041071100b540c1c1c0c440d4501d07000c100f0911084070306511a4114407004012480c0030545c1405440c0054900c0e40401826942c1c400c41360014001d070308152040b10000e0011255005502a0f8007c80c40401e40006001720101511307000840c151800c080140c0d0003c9800800b8000d0600002035521516107407100018050748190ba000c40d000343c0609265240440060300c1348111940c1b082c021805040c0c0c0d8030b140a9056078070032600703d05802200140c009040503101c50030762642181406030010783c03034807000c0344184024100344080503440700548040750414141050a61541040302c504a245 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 667311187 1250 667309937 667309967
    0x60e1e1c150e0d0f050a0509040b010903082a0610170c041b18031e0201110a0605040b0a0603080d020f0702031c090503061512031e070c06030e06041101 67
    0x501c21456401c1c0300c0810820050416515220b28140c0c0384c8009850364003c0c1d10046021450504c1004040d05040d000b42840c210145002a1413a89a1b40c4080b0366801c44d031a440c0680c03580c3e000350710071001004c10122a13001484020122460240400160404103005030001e441d0880400004d140c0e0400c8840d5010300c001f4000d01171444178840300b118142c0d590f60340300006003031700e110340b0320015002e203c40050b0f980003400c20801c4490303041750302d200c21a0306404a04000c25844413180c0b420003489501380e10703807041d41c4c041203e01785410700100d05034010704803840c03203890403004100191802e0300300c0d51107514145015881d0b4861881e003d000d40110740000e5054091040442c07801d0040c2c030901c83c4910070a894511406440710309140d520742003243c074046071001030304546456141201d070040000481d50101c91a001003500d10802c0d24446449154950101246020801000641c11030140607589010880c090800482d07070380d1001c000c2d0004e401c10005410b8a101d6921500c00c4644d6885 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 667312437 1250 667311187 667311191
    0x30302070c031a04060b0d050c010f300b060f0307180509040506100b04050a09020d062c070e01020a031121042408040602130906060e1e1c15 62
    0x804440f0032211010704503802c4607407a1900f1418001858501c89880c0c666030008005d144a030442c000660349044002c003a00c050003240320190400400b20245a90481a41048081103003a550307040c8059403051818039200b28400d1010035918084042641d5000c50b2034500010310000341c0000120905843d0031054204025030100000d1000000720f42d401014401f92030260700b07a1301c540f0005607000398007420f60710002095040001450076005890f1144500b2000181d43c0c0e51031842e01b2084080d2a20038201a4004040d0941c8444503500c0740e0380b00c00d10b402e01c0007400c2c0040780000c0d16044a188000c0500980c1030141010035020005842e0001817220707454141d0704003001903a01ca800c60310031006925070b4170a218007248990315400c0a030011507240e00401e600d880c4e80d14406500124484452080800b03c0098203c2c40d50141100405064a40d035041044c1c003400c0c806102c441c4824402d00f2a07400851a0b610784603401d02130403031008120942d4194106107030a04c0d46507004105056007038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 667313687 1250 667312437 667312463
    0x60708040b04110402040b030c1e09131a0d12090e0f0a0c0e12011a040c090e1905040303090201030b10020715020c0a061e180b07050109150501092304030302070c03 72
    0x9048a030040c5028800070040d80b038900301800003a940d61080c406415044582041c501b0301c0ca0308103070060072440500088144081c000030004c140b10a188800590354033f09100c2e0020030150f00320300100041c0c00c45001110030380c071702485000380d0030344081c04400e58540d032520204042b912459264003421401003481d0601c00400f180309002e80400c1002d01c0e040900000b0158040c5884e115048440c44a070300d41e050104c1c5040b4a000d40f01400a0031001c0309540700200c400407801d148200e500c243c0c071a403000500e2a4160000500b124225507002780940f141e00213400e065a000565801100d0710f050700d0104202c240384040f802d041503006220740090320b010380414019002800100c2c100440c0085600310222200100e550b00c107451001502c600682130140002e51207035004014030b80c003420000c1030740c90b00340d9150340e00d032000c0c1c00c05c0240107940c450040c00383d90060300400042082c070650700f07500705800c80e80241211201030001020b05600003040003c1007040b0005000454029503505100c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 667314937 1250 667313687 667313701
    0x30c061b061d07060c111012020708120109090b010911040503120403060b0a0e01120f08160201090b0a020303060d11030a05010903030501061e0c0320010e060708040b04110402040b03 80
    0x142d90b41c06018041c009010800300c0c410401c18001ea03400000d0000700f140c40c50103100080d0010004c1a0402501780070001303051100340010000070344608526a9a0245200d203a080010180c10090420b82452611030115914a0750036040d150b80a4001070040c04d0960001003a00c901c1c1c3c0255094000c0d441e00b150300300155070103481281e0050a05000a003905010040c005010340241242d4a1914006000781c44035034881000881c8200c00020089800c0c0d1501070303003508540d518100e610082c985490031940c2c4800071500800c8411102d0703040c0303101090041c0d01d901000700540d000e1007031941140c003482112241c3c0c480364080941902c0342c0043c2400c106001c1d0540d0002a40800e041100008409210b82110280b0f481c9080e1a01400444503038215440f4812100039002c20209070034800c1c0c2040a414140b000190090002a00c0300390120700354102040209039505000340341040002007011801c41d60f604c591f0016002d09681110400280240156041010035a2010081002c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 667316187 1250 667314937 667314971
    0x906010f08162f01060e310804030f1203020a1215050a03151103070c0b100e010b07170a020a02220603030e030c0406050f010c020102010b0303030403170c04030c061b06 74
    0x2050003c58000d000d0551141041501e10301c060310513186a0b100540312229005c0081e8403400c1d141c140000c804881c2100f6160741d407480d00640c106840ca05250f440c01d40811103008000411401c1c1400c1c00d45c00c10001070300142a42682c400313400e1b107003034984008640c09007042c8103990107088000c1592095076164208172800082a6460300021485e018811a400c060181581c1c80382d0050760b04d4004032070031950741002d184c0003d0301d0128441005500850b40c3c0350090b00d9507010b0706064030016203501090070640d4203c04c0000411070309501c1040340702c008541c0030800c0c00b0307803a07019540c001101040e00c40366501d03490001608410207160090210400d507010059801300d45003107040b02c0a890542041108032445072140075445508000c3e241019400f07604a0548940140000103045040401181c20760380b044508030001a400b1854080090040328000d8200502d480001d08080c00e50f903481084940328043e0105102842c60424103082031100140f400a0b8031190a208180d202e0f009012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 667317437 1250 667316187 667316267
    0x110f06010608090d030603080306150d0c080610180b0f07050106061d011b1502070510090b0708040b040602030c0903032b02070f061d0d020c0906010f0816 68
    0x1030f034050080e98156244c464000c5100740c0e60440142403a548800d03041025801c103040c003145491300140310220380080c0c184241007813131004e07403120126407400c64100402c0424004c13444081c403201441d1101100c0d0840203000c2621031081a81ea500c40b03050718841054044d80b40014055030919001090683e4008808001003001c03c4081c05080a80340040d0b07100710b114001c0e0400321196651384d001003050110008200060207034014903000c01601c40a00781049041c450f14100c0c1c80304062020428140f11003a4041020310b4a400781e82003a94500107210006800035010355008008a4010138044080f15055440213007181d544848800000d04100c2440c200302d2803011042e180103000c3d0609001701c411107540b06082110301c00040e502d00b001464000c0e00300601500f03152062007c00340403c0380c1c85611026800811204480744200010080d0040501e410010501d024129507a00900c0b115080070514001c0403d4006100b002c80d0060605100c03c1940250310000030015840a000b0103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 667318687 1250 667317437 667317451
    0x209031006050312030906190f090614011401091e050901081e0601081914030301030305070507060201091a041419060501170c0d03050d05010f050405150102030a110f06010608 77
    0x4003061280c5140c1201341c0002c943c19403180d084100010307000501c402549038030610b108400902050006940d50480c0c0305900226002944e482c4c40700199211040b10f5401481004181019038003030800081c414030b079901c280303000b0003074001c015040011070030003c1010b0040034100121035070351400b200d96190450000d485e180c06403000266540540800d4036410303510310700001c0040183c1c454140e283c03101007903819280213102d13400500c69003406100a42c02507009542d0542c540c0a6401c00310f040500e0780c1c1c403140940e85452400800207000083c050151413042003200c1c001c0d50f071420400d4403001e55000005048c0500c95100080000c1e1084451034640904402c000750707a26602000d480f07165442c2d1540c11580440c640d0581c80c680300603100c6005101c1e04c0c0c22424052000606c01c290344003072b080240001012401405207007002e100d07071503002c0c500c0340120644000040000c1e4491041c44176580410140c4055440c1402e0108005461025180111903041d070351170740000d200110584641c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 667319937 1250 667318687 667318693
    0x507080411030610180f0c020f10051501030b040914011505091b03071206090c11010c08150406170d030615080c130b18010f0908031c02090310060503 66
    0x2003110750500003100d41c4505034102114403034a0034204036040100712030b9600c4501644514099000701e20a016890204200c2d800510080d04e03141900e60034030b0707280c000700c1100a2509003044400c5000c462081004c0e1170030b0a00084c0c1225503404a8054100600054010440c40c001c2c603201d010154130508a00110030441350059445034100a4088820303551380c14841a098020540c80b031480b0000d640041e6241000c10380028500c000f04107640e0b059200d031750019030b42c0c144028110380003103000c0c100119007c002c00c40b0840415020705400ca000d0582c1d10141e521000706070041d00e80f40e01010140000e41d40300c4840c548825091955a1003050080000904003900020049160109100d040c000c43e200c100c415030b50300706482003980110036401030f44142c40d00c0000e000c8a80c5001400204030700f1000360300a0581800150038690100c8070304041160203841040400b10100940c2c0596802a1000b03040200e030b0190440680907030303050b155150050102c4894100c105070b2044003211400d0741070f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 667321187 1250 667319937 667319963
    0x6040209060a0305030739061d0d030c0501020f0708091302030108030708030a0605090c07050d050921010902180103140105061e0307090234031e1205070804 69
    0x9002c40012280b20003480303035100380141d200040340c00440c164050100528003c0101206010b4038540080383c25903410750704201c01c1031048942c0842c80402004858240015401600c1c0116007800701f404005410007120160402c10807000790110b40074040200801e90b220789d200d09160b103160307110f040124800c0c004c00500098051242c02500d040742c0390100910305119640e01d0b2000d06900090065000d181c0e1842c010a00b552028000da025031000348a0b651109241e141461400542510541c00c4c0101070000804a90311001c503401c264003800f0a00030913007800c003a843d000d450387c1e220080d404400e0b90340441602c10f460a1342d904880c01540c6a00f5145000d08a080c22204151032160f0400300450742c28181c550500350004c0803042c09000c07100840c0c0e4407058001260000003602000b83c0b0018012000d4002c3c0304008050400ca00c000c0d00401e070202d59000d41856180707008403400c19100d1860030805401071480c0510fa00200405000619081000402d2103404807400c0780d82e003c0c00c3c25 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 667322437 1250 667321187 667321189
    0xa030e1504050d1b06020a0503092a04021806030412120902011403130614090d05090303071b03050703050a030318020901061d2107080d0815210604020906 68
    0xc0528040d54214019051031141010100d5945250192038841c0190011400e00003843c05d1006090780032a6689130b0391a414003e02c01d9007085044002c1032406204030700d0503e040280034003041c800e50301c2264016a11030898814512201814404642c050004400c11040c0b01000c01c01d00b10701d40301940c6007000502c00c4c60000c012140140c5000c0c1c0002d228414000c1601c004900079608034500000c510100c880503664071090707034158003031007040c8201141030204400782000206001d444d5030038190300384108080032982d40d0150b00c0d4003415840101c201005038414004e903100146401c0402d0750704454680c1003075541c0e14043d05048000a1506014000707800c01403400d00c034403030750003030900b007141c1d2803d0030890300d0b580c2e0075607080f038154241d40403020300307660b603800d5054454403141e402ca5205d000c805020f0f00301005540b00005d19040920014551503200009a6000d90340305e060700c0301a030310f0b01c01043c0c0108000810741d0100300e4135450305001c0c0d00c002803068401c5c0d100322442111596400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 667323687 1250 667322437 667322473
    0x71701031a0c1611012f0111040e040206070f0c090507180b09010807210b0f060f160516030b061e06070206030c09180f0702011401030201050c07030501020a030e 71
    0x81180c0b000c1444280400d000500c00c2202c814030042c0500d8802c0e10400d02551b1800500016020704e07032042046941030710984002e0140e1100050b5020460341414601200d070b42e0b211100a000070310800d40014410704010500303c1c90140f031a00720010200b0151a850710320020b00b015140003000c16400020101154403201499007507452000482d0309101c084401513902800141840c01813040142c0300d078005450741d034014142e075440300a01281c2400b400c1d0500c2501044588824069142084044000c000e00f00885030786142e00c0055038581034003030900340d050540e44420400192445640081408425040781e0300a074011140b100519240e1241512002103a03030b403854006000340240c0b005032800c90007031580f01e00848049840c08a9000c005607800040312150100310b0280014072029203600220305510142600081005600b42c071100213144c1c80504c4000e0401074002203c03015444140021802143d20034000c0d0f4036420450b40c007030040c01119043d480f147c4a07001036011190303420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 667324937 1250 667323687 667323697
    0x3031d0306060d020d060b1203070c0b0301050d1403120709030501050702060405073602071e021c030507141b0603010e0c0903070f030302061012110603071701031a0c 73
    0x610843d201d0341d040e4240981140c945030300f07440750b0380d0b101c0c809070290b1500300150030b1044901c4040c560baa240c0f4034000c00c84c192140c1049000e9601400144210780350243c60501503900040f041150041c2c0d407089504d944200700340e1581c074038206070602503070540003c0e039074040e04d10620003440a075903404003c83c3d8403207044030081d1465028100400c0301e0501c1140224081c040040b0f1402210050000380b070358040041c900c4204c079a4001205418480c10040803440d071403088100300c080340030175000615003070480250141480210588081098011011510b159500c807200d60001148001100d85800111282800794010035428100900e084011681a00c0e41e010301e100c9603803511028100d0640000c110280c0520401d0804502d00f044062480020341c42640142440e2a01c003180c652000301e150b0100070414644000328000031343c60340d4100309100c4180c850380d0303c950b200348045610100da02d4000c80100e85e008000b00c00d01c800701c0308403500707250803080300d50054441c25040c604e68414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 667326187 1250 667324937 667324939
    0x903020916120b011b0b040c120515060d0614040c060e090f0c12010f0f0b0405030c011d0d0302010b0306090a21031d0c0f0402030c0a030203090f0703031d030606 71
    0x10250b0000d200c10660340070502100c01898560041101803690a1040100341e01c01d5803104083c00800003000900d40300c0202130402040b0350f680001b00d076a0b50b29601e90102c03481c105103100d9240012203940701c05090191468203d581413004100001054000300d0382580c042d030b900d899a04001c680035000b00707400c0411f00c0b000b40202d0526030701c580d0010305c0b401014000ca030b0024810001c5210011681080602804001c1c01e4400943c1c50072005444080c0c07280c1c010390f040325051208100c150b40115528510190a00f0f14554100c41080c014030f4200b2a0b065169020300700e044845c09065055010398403884054048030901c4e10384019081d504d03600e030b08000300b0068010302c8030103181c030f41d000c02ea22070280242008228a001c200d12644040c03001d01184010368084500c41c2d250385096407080441d098252800c51035400c0185424100e13103d410072a409058000002c545640800c01c0348034020341e170480a480c0d102c0c1c1c80f4a0300410702401580f4560180351480f003080c140b847c01048440c001c0314 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 667327437 1250 667326187 667326197
    0x8070806060f0705010b040c090f0806070c0b06040b060a02010c021203060d080f0c190302060a0c090b1b07030503040f150207140f21010e03090d03030e19030903020916 74
    0x102c07041074a4591021034111815501d602000300580c0340c50184030b0341c6002c2c5441d01d80750541000c074071858641659000301d0b542d6101030203011032503800c00814204241c100010b40010703950781c008070380980ba004a529411440005202d0b001650650011041c000d01d41d003910240103860014140b5400103a5510f0b5200900c4440c1f40001482c460081c80c0e082000f9100b9800c0c86c00d56140d003818010000c81c03510213074000301c031050100740c1e05010481e88101044820051811203090040010300580904603020350700007481d41840745041c018415010503201107801c525140c1c40e00d55107903003091113644c0c0688010440480e172014025040c0601d109140d0080c11210303e070103049021a03000c40d4207980c0120401d4104101d98460300a00c4d100000d01104006850582050590031116210103540f40c0360001d004a91090f074428075410060740e010701c0e01081034409114101d0400414824850b0300e845810290010150801044401c40c0e000f1107080c4801c0d5030303e0303c0510078600c80c240300e035000079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 667328687 1250 667327437 667327447
    0x1020c0c0105130f030c051201050f0708060102030f03150a23010507020f180f06040e0705100201060b032d01030f0b0a02090604030609060509011b12110301060f0807080606 76
    0x94030070b01c00342007040c0c0c0044015584503616103080c0861213540c0c1069441410322542803280c2c0c2080440a029110960000c01141c5840b0312a00c0180f00301404107801c02c140500410f01d540e02c20016100803001305004144c3c0d0382000b040122103100c02e20b202034012110340c4c02c00900c62144c203130394030f80c80885588120340145082004540c55400090100d80c8a01d010010a500da07c0740c098280040394501070002150400c16803c94020b40002c0201e8441e50424a02044846c0d020806a01300c543c16101c011403200501e1040e07014103c00d411240c080c420220800c86503807480c05d20341381c0d411151100049000403c4220f00203c1d070013400050f00413109480382c100010030300c100140c2d1028030000e00605003000d0320f0016810ba801075000b83c034810348410003201440400e100751600140180c000b0020101e25800c004100e000c601d00c1300c41804030b0046056480c0380d0580148006001540c0300320307500c4d81c4640b0040c1030b4a0b000c80b5a080003c103030a00003856940141451070140c0e50007442c2c9130800e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 667329937 1250 667328687 667328689
    0x120c0509061e130315050a0614010e1302120124140705010f0606120f0b0904020910030203070b03091b01140c070510031b02010c121a0907050d0b0301020c0c 69
    0x981030b646085502007040290400002e0980818400703180309180e400c030b1105040d00440c0503070340c001c1c0125125610700345c0104114241c030044118000c1080c02c0246000d201280000c05440b40395641c040c14074000203001203040c42d4102010705803a8015046890312000300a64a445240c0d6800303d00032600c8914559203207500e800140200c2031090f40040313600d184000d0f14800361007241e44040081108a0891441400c0034040e210710120030250801c12507240c40d00003201c8440192010f4044c0d03001401280d100c02c0186a0301c1d0185070094119101555101c0c100200e5620444d0000c146000b98840103900c00c9a01c01c03540710802050351409130401642e82c4036030956009050703809552080d0600054580c4074420440c0e440001c17900e001480d5814a81d080070103214484e40c020840e403426811400c4260030484845d40000e0480b0000b1784203500c41d008020221880540c2584086410b040001c42c0b070f440002010321101c0000d09210f408440d4080c5400c1c1d00a08035444280d4000c0300d91740c482 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 667331187 1250 667329937 667329967
    0x203070503070c29060a140a0b03062e0e01020307020102120a03020408100608070f0303090e040206161520040905040c0f0902070201032313050715120c050906 70
    0x96074000c2e01c4c4228110402138401c5a482004a040049500c2200c100200c81c039003408210000d103031709101e50310b20400c2440080c1c211070560141c03410441011004c12455214800c2d080702400c00b00315540d1210b804d00c1e80122002e0a91a80e0200054010511410300d51020058a0740c00d170b03040e0010000112200e401542c0b6800114940003050350130303c4002481c100400104d50090601103001403020305141841c0d050201540100350301100500003000041d80c49908101100c0a141410f4191f481d01d01c0024028032407003914070000c072a0081103800b4403580c160a000c0601c08c04008110034a941030458100240610b5400d00c00001404108002e01c0d03503801c0707144c1c0a8800c000b040d003403d40701c41089403201101c1c0c0040790f040398081442000c41d60140315201c81c8006400040e8100e41c513015080900d882c0050803001c00c82d6400e882e0303004102c02082404c0140c02110703812002c44c1d4a9500040c240d803d04c0038540307030f850b0a10081c2d00c4120b00420443c0c3c2c10032006011146030003001c10684503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 667332437 1250 667331187 667331207
    0x20f09060423040c080708120d020706090503030f010f06020c0d06060807380405010f0e040629040b0909130215180306010503031c02040b0f04030213020307050307 72
    0x90040c2d21a1642d00786440031004104850725030b694404128145400c2081104c1c0a036001981c840c0e0002d042880a8000010740e40050130f003141038144c1d00c0c820b05212102a000d03140c401000300e4200030f1a0010040e01101842c800d450a05d0308520340daa80d02903408070744106200d09005138120a00d4641c080c18548c1c00c22010600420000c00d010b591440e00134079140030741c2e00c500c801968076680c0c003000d41c4541f580c0300c2d00c00c81030f0b103a2216820394140240d84070b44035500c034190501c10428441e06440740aa0030407281c1c03020050040040c647d544465141011a00c1000b00300704084108035a02500d81c0001e860680e44090034050820030700200740085200c024001c0a000c2505880e000c005070b48103420000c208180c5500d207515030b00800300d40c00584c4410804a0701c2600f00b04014807442c2c40c00020b071703000540c060701242d119100d00c12100d0b000740b00710b400c084000038001405510320182040280200d9109030b51045080b1071881c0d5030012070009860801c0002d00403c00f0030f1400380b040e004c0390 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 667333687 1250 667332437 667332439
    0xb0f1014041d0f010b01021002070203190f060e030903011116020906060c01050720010903120203181e190309091d011b03050c04030f120c050304080307060c03020403020f0906 77
    0x1404001403004a514140742c8550f0305005a44070907a10b225564184100342d64150b90b50000d500304006580000d4480540c964440036480c80300503030703105100c21030303c0d41040a41c10003010003144039a40030554880d8401e00d100d41c0250308050054902c0340b03d140484140344240072860f20045040e60030003500b0b0a0240085500c40d00034000070441c03840c203226080c05040d41d501d50900000310300139a01201c3c00003040b14022a490080f6410100703800403400307118014480001070ba603503200200d5040c03443c00a0019030040c410040c0210160303d0140c1550b1076001000300b1507090401346481e011340c0312a02030001b4002500b26100b0458904260000552800311800c0651030b215000c0c407150840780d40c1c0b840e0401c0c10344240b41460340103402d0300c01e85401000c0090340b18a01030842d2600201101040401051074003e081c10381c22151041c2c1200402c02e0f800400d40395a940c0ea95502ca07035030f802c404000e0392080c2c604520100058082d1084400b100c1c0d0181101d140310301e001c030030000c0d1506e00600007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 667334937 1250 667333687 667333721
    0x101806020d0b240306040e1501140112140a05040501060f060809010f02030907090f022b05060f1005071a0106020f012a0e0f1903050118020604030b180304030b0f101404 74
    0x11a448c000301000b05020301000088003540320880000148203500840b410503d0038500100d1035024405800d0360344d48401442800b0401c2d80f1186402401881c0c99480001e11580091b000300e000c0c0d500800c0d00d8000d402c9030303000f4440801d00c000340004912080c0da0110813584011802c0003040410b40003000840e0984000504141c201d0b600035202e14024004c2a0700074003041190080b4014034403800d500090103031075030016600b020300824603c0c801e4104c03a805014005c60617404114100c08032a002c50340410242005581d2582c1c060740c3c0381c10780c282840b059401c0c514101225441c00440682c48009004035549024107660181d032140b040c0520141c01825002465150342c8503513002129000c003d0b115104041c4c43d5092050855403121600b8031030050704001cac403016a070b681050b2400c0c0c84d006a440307070503601c4588556020f0114000c0305e1032a40408940001480403090406100311000c00c654005980d50300c400391714500301c40c0170351044010501c01d46071b0136013032541c09000808548050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 667336187 1250 667334937 667334953
    0xc0210050717101d06030d0f02030f090d02100810080c0a050103020a02030d2a03060506071205041a040312020f0616180b030106020d0908101806020d0b240306040e 72
    0x103075084084c0743c656000c0103403101c0510040781010412003001580b18a00f005102180301c00081d100c1c402c620240c4004080444c1141155a40d00d0105070459401083c1000901160300040c3c041e000132070341e1580088a541d000240c3e8007005c14102003082000700324510060900006400940045503184c04520090040602103840c031f1103080c5a041c203603512030b2188800811610040e00640f01c080b800c26040410070800c5458040030b81e4040f9901c610f554444903403454084030140942d0740140c28094101816420350f04140c801003058070301504406000410b4680103a0766003642d10400e110390b62260001518600fa030032002d052b00303a1035282003540142d82806a1660400c5508125030f00c103000030040001c15010081444403006074180910702c203207003180e0305072a030150f400801102912a0003000415140c40301202c00720360b101400b1900d03161240c0541c40200085c1c1021800790000300400c403503082c5d10807905103007610310900a5246648000a00001d00f0103107010004912400309 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 667337437 1250 667336187 667336199
    0x304030903060c0c060501092a020a051501140d1a0a1805030409062106050a020f0d05040b061c031d090103080c0628020315090702010c021005071710 66
    0x52010103c269529201051098182802101e034183d001c0d0b0076040c50174500500c0c0d200260134403400909a00c1050040c480340c810280c3c103020303120100800500401040300100001186454140c0b4504074048030010044c0b02480210441400084d0040c00a8400c48170380c0300c00942056888046400040303103804c1c0c96040d020010f196880102d52070f030800320341804001c0b06403040728020a0034441f00c25106000c050703100c6406e86a94009081541c40d0000100f5221a0350103e655007410b01e04115600c0308a07246e404010300b400e607012240c5080700000314101e41782403042803050b2441940124401207043d43c007550240e407041020040c1660000083d40681c2c2d81c101204c0c000e42c01201001e5a86042c2c01860341450801803d8a0880550000403001c507160314500e248881182180143d9076107a10018210039000301c00300640c0990400100301d046503040d00140c4030340100707400311061155009507030001d44804440100001d000f091482c12840d5407807420340d411500d034103015070007240c42d20307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 667338687 1250 667337437 667337441
    0x405040905010e0129091b03220c081b1c21030603024b0307061d0904050312042d030801060f09050108071b050601210c0902030403090306 61
    0x50050b121240300200030859148210720f10000b2071086860b600b01f80350017138408010000d0000340c144407a41c044001899400900384c2c035420b1000000210703506100610f05011803c101c0d000d124a43d0003a810121004030140e80810f8440030001c10856450118400004a03c4210300f42590f002d13412210400c0d82d412400f80755104031a10303070782c081101c5045005004020000b02401d0305d088034143e400c980c41d21180c108040b00586a40c803406c40e084443c41c07000c2e43c062601c40520f60b140c05540c01c0010300c1c6411280c06802d0790f000c00e0302611803d407100108600700e5030898029055400800524032141648511154480d101e01c021141e4018100701288134020400d00d16100c1038a202d180c4010306800481c00d50040c4590300d0404945094140004d0010726a4807131181405040720102d01d85500508441a5260172034040c103400b0840c9080c802d13a01c0b5804c0c4100380c0c03142104c480d0b240b4001082105100115000f41d00242c00c030307203072244403002548020015010450304c62800b10024a180c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 667339937 1250 667338687 667338701
    0x605090103060212070206040525170a0b1005060906030a06030b04050304140f0102100908040b0f031803211302040207061b110a0201141b03070311060402060405040905010e01 77
    0x41c600c01611a14246080c44d01c000c009460442035601c440d00300000200001850f0308124814144520000b00884000e90010091f400655152009240e2841600c0f80050f807581160700410094079151283c04041c5a010a0350284c6034208504120490050411030010b54100886880c0003850658a03111100e02c6401602c0c2107902c0d030000201040303440a103050044260748101e4088454410b041d0020f036440c060a80c420301003540b05d000a206022100c1c003610010110f02210076581c94011244481c42c0d80106c59184aa440301644442e82c200c0c00401d640d505420340c4201d900986000c58400440000109400c40340c100c0140200c00503100d83c005820301510600c40850403020b411100389402480040720341c100626502c42e0124150002072a040140e0282000003c1e11a0310f00200c401d442270152286000c1d580303030a0741c0c81a00000004008040c040c0d950251024000096207803904403d40c0c0c060b5200034203200500144c07400c0e80c0000750040c0b03d80c00014824005180e200d00759030b15 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 667341187 1250 667339937 667339943
    0x222051602070e010b030103150605030f010212010e070906200703030302040501030b0108190e0c060342010f0c05012d09020d0b04050709050c130e1b0901030605090103 74
    0x3200d041801059010020000540840501c1c0708143d070604800d1044c82c01305107c05454100000c02030b81d03120301c0c02c2d0b20882c090107014040d21070343e5481c8032100e4040c3d0321a10b01c60401c0d4040300000140122640c1c0d000e409515a984d54440c00d51410004a80c000030310780c2261203030030b50f11a1245441c40208060380c0114442e8401680726403900c000901100d0102c41298140030b500c00400103841503030b144030104405062030001c4c0c3c4052b5425080e141c41c0d050f800352900140c001003071248a1054101018240310b84000990580d03000c1161b580c0b0450062020200c1c50a89a0904d0015030080480c04d21542c41880c06060204d000c0e12600d007503409a545c141c4503a90300203000c4188400b080c0c42c0c40d143c020446401e008251096000c00c1030f60803004030182a5001d90000305080100a02400c0001d19802400f070000f800c0c03401d4152156446080d2640c0802c43c83d0900007401d0680c1002d1354440d02a130280b8038911000d04060460030760140d00e009040581e40c14021131700d691844000c038003841c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 667342437 1250 667341187 667341211
    0x30f1e090f0506280509061209010b031204271d010e010e060f060d12030b01021014040f0204150902070204060b04051509130606030c1e0c022205 64
    0x110308030500e00807880ca500054025441000120722041c3c40b4000641c910413900c00311102d602e20000216038038020051800d030301c114009200000070610203080b50081d44660001c20080300e8030001c140d40ca2010103907c405400080c0303c00c00c100300c3c2c90322045e840b9281d502003480c05000d62000c03503170860f02c82c806030003035242042d41c141c1c45207070091003011140018580208610030035001c2c1d480c0d4610000f0000d5201c00102c00010312a0f8496811002e15140d00900e4058400303070100c80034024028003126280184034074141802d0405090141c4550751030590710004550316030783c9448084400b600c800340d801035240da041c3c2e22440c2c040701070074004001d150b2005031280d01070720402056640907403211a440d0b000b4070052140e81e64240c5202084100200e2840d5198244401319201100c205841c182451a1003000980580c042d040136a00644a0340c0d600601ca000307550044038280316860311000160854140401414810300c1c1c4100b03680300c1045400c1a46004000c5010ba580417205801d07144 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 667343687 1250 667342437 667342439
    0x906121401092f0109051e0a08031b12030408160303141501140f090904030c021801051315090f0905010603030c150209090402060a0302091302030618090a030f1e09 72
    0x1000301c4080f48010030b00746441c20f9054503101c00107940c040c404071002d140520b030002048403a80d44490343d0b401845150247d94850702c84252107445071201d408000c0e110300600071040c1000303c06000b141c0c481e40c2d02c03550007400e100c2c201d4a00183e0545100c811404d042e82c40322003032400124a80c105105001059000c528620202c00040c03420058002021088034180f0201400c00610b40640c3c1c2103160680ba440744030355450804803466004a4400f0f904180c079801c4030b282076100310030124103076901624a224401303003041080c4102c2e618001100d05d11024401c3c203000c83d500c1c1e03800101070040c00b4203021541c0203154407141d00b1520340b644201c010854480d41a8204140380ca02500d07a0740110408600703050702c41d0301284462070b004000a115000002d08020014089d42c140c1d071100401030700c1000709158001c41400254019550f0f14032803013200c8200407411284000041c40340806034090464100d55070b07001d0355524000060b070390a1180c403c001d030790031406030300d000304000c8000d03902ca1140d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 667344937 1250 667343687 667343753
    0x106050315130b060d120206010501081e0408220801020301051c0c0303050f040819140a03140702030c1815040614012003040609030c090612140109 65
    0x4003000c21012010384501c1410850030b2201e240419032196000158200349a0300c16000803044501c0c4003004264241d50f452104040c3d6000420a05a49081c2c885c1c00c5c4170384078541585400c0c0401e0300000b60441050000034001401e44014101c1c0c6c6031000f01c2c840310071803c01d038103c00c80307031568128100d203a5010004010a180003000c60f00c0091070348101d080400c800e611402d80e6090180005414010009407016009000741e0482d402886140161100110b0b0b201d14075000900100c0146c0381e43c2a541182c03038400e480410f800034070355815110f403840301079504aa800da40d0031000d01603171305005a04820b403c2d915020a081103c540c80e003403404081c0b80c406c900702489080350207441d0080d46861000e01c41114020b01004032402c09003800d0f142400340c1c00008103030070b40c0603c0b5040140400f0800182c66904034001c003099030720034025006260340310810101164464802c3e030890240c8013140001180910001c0c0c80603100090000c00c28100503243c4a00c800e1540c155840300c0c100e110074000320 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 667346187 1250 667344937 667344943
    0x7031a060a08030708071505180f06071d13020703120e030405060a0e0f120703052119032903060f19020a0e03070902070311120a1101020d060801060503 67
    0x3104404403612080c140c10b0001c00b5940e07004101e002424201c0000300038080c040000725100d8050034070f800030321451800c0314030540603d0369a60f06040c503206040d000940854045207040c4590000c0d540e01c0c03289900c0860b404548200d900b0407540040d402031812074018168001824501c1c000e0f02d802580c0c04c9100003450403100411618142070300188400e002e030350b442d1001c035400c465030f51038185900d0022a0004040103c0303180c0055001e00780030311990301c0b00390218281040b28003460655020b4401041d0070f2f200d04801080c8412580d40420104100b0909521446074030b04862900250281081090b000d04440d45103032180c286c95100201013161070308221155016016040401c51410120f510342d224800e004e8036022078940214281d07115602ca1010101c44100003012600c90641da0071011000398080103059000502414a8001c0c0d00000030f1003452082d84e241526180188154040714200d4a00180c50309554081008005040c0c06001c1e48014011440c00003a0035031600040601e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 667347437 1250 667346187 667346191
    0x21207020615060904020306042309010c09080a081605060a05101202100e04150b19020706080c2b0b040c0c020a09090305190504050406050f0306042307031a 69
    0x10070a081c5100b644a01d4481000369400034109031000b5880703450300d400160140041d50306005010704002e4108886414801030f0700d020b0b541220080001031101e803c125280c038a28098030015030300c82240400007036009001004000003840d011400e624907a55002c0c01d02c84256208000c1944820a00c400404142802c10041c6017040d00e1011201103640443c16196040701103001f48441207800010944543d0841c20b0068001e00511884a4844244070342c1034200100d1494079006403082d00b0280350002034582c00b079802c1600e03840040d50300c3d001d8000c440e5002c140d850048400b41180881c0e044850500034032408038a0102150440102050008543c841b00c142010480301d03040c554056280d50b0601c2068400400004c151207a0b03608090383e40d03100e05030000946060305c1c981c3d040d01c543e124001d002a980112018050207076240308000041062450b21a0302d0340150011900049014040080c00b0105282c080310381d01d552654503040a06a40c015141c03d41501ea01007180210b41d104a9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 667348687 1250 667347437 667347451
    0x1c150507090e160f210213121509020102100e0607120c0507020f03030f04030803180106061b03090e0a14090102160803190216120e010e010318060212070206 69
    0x4a8910741901c00415141c00e03c500326003480107441d000043c561007452584054420a81c0c1e200702c50303519131034000082d030240e10140e41d1126030b540e000c10000740007c1500850303500900d03c0c4588120542d042001451030800490561040c0c001c8001c0d0100b01d0f005000d010501080a8a854546204003030f100c50620014131442c0f0f45090384406d040368200c002d9512440d0145d94006400f102100824510320400605161801c00802d002003005202c0d001503107e000d107034141080319215040801d00740d4089026200c04658111151004000343d03a11100d0300c1806450301424103035031a603c80b0a403020030703620881001c1e143c1a04002081c0907148458004480e4002107280004014180c03203101410380004082060000c04151545941c40c480c000318030248c8400c43d40c80c880d00004490f0b1f140c5c0c244045981103241c4214003041401a15101c0301494183c46010000c1d0510b001103001344609011100841e035403100a90210700540302900201000785000d0482d400d001e20f01a207000030040803030f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 667349937 1250 667348687 667348709
    0x40608070309051230100b0405030c011d0901090e1e21282a0210050403350f120a060503030706090201080718051c15050709 55
    0x40380060f100140604004881c412545c1c1c4a601c400d0b040e078070300c00412600f01c50030102e03010300c400d0f80b101c0c400314030340074201c40407200000503a114400741d0503009910410b54190808100425594040d142614004055208400041e140b5000281c07091b81c003070304a10700983d9500c11070380300801d081240a0303046c94803030b03281c0401c0c480b03240030596152200022044509094620030304a40d842400740c41410001d0824841c003c05d21034100d403000c040f03404142d00003c1c0d440f810000d030032002840c3d0f4201d20b001004554bd01800c00e03002e1042039205c4503885020013504220020109401e01188800d6a1040700484800d608105403c03c9403844c4206030701c441c8a040000c0030043c50400102c1e1928600b14545010306e076140c030a040c0080c01a9486681c060000080d81800c02c01c0c190300002e40c1034400d8a0303004d080c2d1a4107400711400c2d88445c4602040e22403041c070512903490a040c0c00207814071043c21030b100382e00c40d030f684425105100e8074654081503203c5080c840c03011b800c1030700301c0b0140a00041c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 667351187 1250 667349937 667349951
    0x61306032d02131a03160815040c02120f0408010b27040302070b0408010c08010b090f0904020a35280c081e0106050301020a0e011d150406080703 64
    0x80001004044004200340700d50025100c800c0700070b034a6201000f000108680d000c1c41e401085003007aa0740c003c450800c450140d017603142110ba405443d02c81c0c080d040c8480c2850140c86884180001000ca0320300e0001503102d052403016105c3c6d03000004010811890040715111482d0640c2d40c1c2c255410031180034407500e070030b218100181180c4442c2c5441c6100c20f005596050b200c0b403c080e0b0800200c1c1e0400106001e001501061059054100c0340b804542d0307941d9124182e030fa03040f004030381d0b0103140001d5a002d86881010201440d00ca410207030480d00003028001c0e0b003550742c60042c0b4000384903802c0748091514110009030081020341003c0d001e03051103018005e4942c3c501d2100390100c0301d5031004400320180c01419024001d0001801024003004011652611011805010a2020344041500c00d60a0032004120350906009480c00c4c03080f661904001280c0303c0b0300541d41c1503010b40c100c500d1000c40444a071000c2d03486050004515103642c9000b0b0340e0b642007c1e0000c003d21001424a07042c941000c01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 667352437 1250 667351187 667351241
    0xe040212040b0a060806070806030c010f0e100509130606090803070f02060319090c0918150b01050c07030b010614070f2904140c0a0621090206130603 66
    0x400a58403503840182c6800c5a40c0350141c040040045401c40b0b0090b108510400102d1600055445e003d0a402c03000c80e2010144071004454481041108100250803111401c08a0030545000b070404d6420341080342c2011012008250745891200340301241c2038640d0400c009075900310701c1c41783c06092076002a40c901030468079000040c0046e100b000f405a5400400545140480307003100503103144010040c00060340390305002194070200e014200c41c0505c1c01502c4488007281980d014000c650254005c184800800f013408010318500700d401c3d05010040016105107581808071034051071081603061065410000d008000e66002651a0701c1d5540c10404440820310301c5e5280861103600240c40e000d500d45103119060300291101c403100f00c104801091108120352854004520400002107884400e00c0c04c08210004910344103a5011030744110b0310310302d80e48407102d074004a501000d0f400f0034a00b805030b001c00c080e54081701c000202d00302c942505008050381401403070140040000071100046000b5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 667353687 1250 667352437 667352467
    0xa0e15010f050c0718060519030501050a060819031704121209110d03030b0a12150504200f0d03110c06041d04210c060b060a1407030c05070f060e0402 66
    0x300403441d412490321000b05d0b07140465017020f070103443c0180501200d450159051880d00e00c25010464495081038000307214021144500001c84180500038081090b01c5008001d10302c80041042c1e0804c21501e140b0202562075081d070b280aa4410840301418a43c285030044c255842103207094503403401e040070400420202e010107003040c2c10031650201c0500780740c501a802040c0322034101d42c1090f181c100c000707005604070341d961049a01a0440c040045050131700302045510803034004003445440c03082d81e2506038501e402004c034010060a0b000e2040140c9000468801f100c0364204c001481402000190071002d01510454800c00d441e0750341003508003001d40304600c82408640746a030441400250500800842d806028860303107100e100c61009110b0000c040800200080d074402d8207020404c182410024203c680b4042c0544d943e101d03500203e5a42c0322540d10180050b01048802c22051020400600c8204000c240c81a8900c1f1098517080000d03141a00d401030312072040f071040c003c00023150403070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 667354937 1250 667353687 667353689
    0xa32100f0810090507020d0822080c010204091103091501030203060c0f0f071a011205060c030910060f06021203090c0d1a0c0304020a050d0218060a0e15010f050c07 72
    0x509003031125544804003005040d07400e0340140c3c107590500080c4010303290007250050181445544030b001c1c0e651020320f46c20910502c2c900440c80d071107501c0c1820000c9045038001d40f0700c0e480e10300c0025140c666039110f07032000d0b01e540d4030241d402c01d0400070034480c4810707023084500e09400600c0301e070b020150b01d90740000352100e40081c20222001c00000c0d0785126400d10500319010002e00501c1d054581e001e904000124248641c040c1500500d1040082030316642d0030031441d07045510100800342d0780d0333898841034038642003d005080540f10f01520510629554005d150107041004000101946404e000a20f460080101d031480703d20200140310070a900030512803445101a14040781041d1503180009501b550035540c079002004c0003060062040112004500032070007100d914144603102d10400101c036112100081d4402901c0508105140828014170340c004d50040100c0b075095036480d0f003002202c1e811108800503a0990103021043c0da003040040a010318071f450440c0c18000c070310061950751042 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 667356187 1250 667354937 667354967
    0x30f1b020615030a0c0f060201050105150702010e0d151b14090f120d0305150f100c02130e01061703071e02061c090203070801180206090a3210 63
    0x49000b14071141d1410054800340950090030185450f94580121030303241c40c0ba005050041d420000001403034905005001c001c40c2141e60f1031032500324280d006403800080c540c03c5603007080d40480703074101161410315503113043c2c0c1ca95140840c0030201d0503107203030180c55240701100070b00114070314840421001c030007070b55082e4109488880030107161100240101b2144003a030200c0b481140a0051501d906420480c0201007510b11480d05407240020040491162982160000320b040c3c2e80001141c032030b800401009002030100514080c800c01003030240c55180c3c10200803603444a4041280c0f0202046946031442203601850404180b59100c14400e0790380880c500940980300004015562004101e0b00c0c0c101e1419100c90303030303c591008064090303c44801d05a1083c06124400101d022042c051030800d60703606420080c11044540c01c10000760030444080f5088003c80b103010800715000d40840740b40c58007000542c05210714008030143c030484a43c00140c011110b542030b5074003164104080300e92080e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 667357437 1250 667356187 667356211
    0x190515090f0c0316182a0f090e0a1505060a020307031409240d09210315051003091728050a0f030209030d08100f0b03070509060403050607030f1b0206 66
    0x42d000000300068403541500d0300030301b403805921700c0c5c00704140c44000030144240d450360000580301c90342c192910300140c80740d0300075003040b50000f80710540107510840c8080004045010050384840119a541e04442c51000141e032000034140705041c0c10409a03240c4d081070000b058540140d40000c00d158801051001042c002c3d5514123040c000d0503501510484840f000c01040544410f041600c01000035801802030b4002c22079034605080e111b4000e0954500d000c400d042d00d01450001804803000b107a56140e810542d0383c2c5c1c000340011f507802d114540d100c161000c1641c0c031050305212a0201c0080c107030032404030942080f9400901904a001e48190300901e0a094181c25010441030f4003900ca250480c07075150003140d90048115400c06501402600c070b140d41d290b1340a450b040a03003020f1002e8051038030000d100348001240309110b003001704501308015002c18101603690362030519245007507624a0110380c4640c129504584281b00c1c0b16503145000c80442090600707281d0203520742c040038040c103203644 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 667358687 1250 667357437 667357469
    0x7051219050a060f060614030f0402190302060712090609031505060a0e13031d090402060a1e030b0418030e19051002030903060702060603190515090f0c0316 69
    0x2070306002d0a407200d07070081c1060100c408207886940c010030840c0a0341021509400500d8900381501c42501d20032541d190242001d81ca40d0f03020062041c0078038482d110341410043c0c0100040c0c54040250a5403441482c0c08003141d000303281e000d4855075842d00200208081c5800400110302c032103284007946610510009141d4445002282c1688400c6d004030000034400014000340440409403028603a0090750351318030041e02c0716006003a0821260000c1c0d0301820001c0400c02614054008000404031420a001e42030014072080e080c441e22080365401195480500c2c40441c14640285001450f0b454030001034030803190740c003401580c0345980607801075462801c001003c0c5040040c00c3c000c2d020052000301210f0041400039030301e5118a151a0080c09814041600d003800040d0130f0340100402800303000b04403100e400132070300c074428401c05480e40c2c4903c4990051241140501c21702419400c00540f11202c00e121401c2d01c1d03c85d42c064a68001e80c40640e075401c1540c000340c90401a5a03042c28540452 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 667359937 1250 667358687 667358693
    0x180c030606040f030f150204051e031509151b04090203060a0b041814040c0e090102120c2106030c010e0f030114040213020a05032712030907051219 65
    0xa01660b0803c0640e009080404800c4c0510342240030011449800001d40707403c80305d05504107038001c0c0c0c4956504040402d44841d031070035917800e004802e0080581151740c81c40d020740015210441c1600e401d100350b0400b0741d0031401460200d00441c0c1c4071580b0300701d5004000109107a034619214a10441c848907a0200100b2059038550800c800100540300c1550380b030355115505142e880c0400041800d0b218a0009407683c00001d41240078030442c0c10050022840e440c010b00182c110000038040704207554200000c003001c0040c801c40d1030084061442c481d8440c0030705905040c41e6445503a1581c4020601c03000c2160980e800200340031040f100b0701e03106032a01030001c080b07006001c0c100c0c003030759055013401e2110a00040b48a09244030b1030007203a68130308030590304590800303e01c1400600c0d0001141003002401849030b01d140304460f00b0000c003410717081e42010a00030381014201c80425130f00c040300205200b000d030020460280a0b0600b02d4004c200921881c0405a40322a03000c01300042407642c105040c18 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 667361187 1250 667359937 667359949
    0xc070209090c041b090906030b011215050109020702011739160204140903090105160506090a03030b0a0e1801020c070605040603051b030402151c0f0506180c0306 71
    0x404040e00034814610841300881070a003680000f58001000f509002a02c118240102011284c01c080304151990070034017030b80c0654042220507501c500c04000d03410380080c400d100c0d03e80240380000c401a1603408510005201003420008224030401c0481071150440350269186d140034112006542c0803000c10004d0700705940041004400000d010641d0410507400e01e542c00e12aa2003140c0420a02c0d0b184030028121001c02d50300c6030b05e207500901a50303d8a5014070001d007800f0350400d2201010001b56030f038252508004440c0d001d9203401004a580400d0f405024048240c2011a0400100c2e400c0521a42100100500785042184050a1448289d400b0350403141404d45041c00d0700c040701e4270f03840054041e5009109030340000f40b4000010300e904140540403e003c02d51406014595129a000c01000d100000100340041400300605c90303820003401060308000448801c0464101d104c0c680f072102b2107078020b103494042c1c2407080f02041c40304000303003c8990080ea0008001d4880d01c40c1c4002c601 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 667362437 1250 667361187 667361203
    0x8040312141005010206090303070c03021c03020702190b070f060b090403080106020d0f1e120527060105090414210421020616080706091b0e0c07020909 67
    0x104949825036103801c910716011440d108030342000555074119681c1d40120380e103460448049070326030003e101181c420381c484c8015405982c041d10403034060034031240085108030f003120360b02c1010a90020740c4034110b0078032250110600381c01681ba1509180b40c818504501e100d50000100b1511100d0242020002d0b80c1c1d0191540b0040940140000c0c0b9161402a0882c90b084c040d1501611810031280c02c0e45201d04601c1c002800f240c0da82e00249a41c1030040c03481e050149513804203110003506506803104031423051174451002c1240187c2c54501d4072040c030a4035580c06c2c4000c0d40c0c54010000600203512000e0500b0f401c503501c90b0440e00d84031025640b6a041c041120025404a0302410f405c4070640c07c044080c0080d128030110a4164508071041c500a42003980070080d0051010702a020114040c0f1030690141030181044500c2c104059550004031605450115040f10f2084c15001c9144265030400c0090028861610500c0c00d00d40c0182095010b02c0000901c502803510000d002c0c03001c1408103c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 667363687 1250 667362437 667362467
    0x30c051c050618060c070c0501112b03150e0c09060f0a0804030e0102010c080610090801150306050f04112b0b160903020901090c03020705120d050c0415080403 70
    0x2480c909210030b0303402e1004000b0703050b0b443e0b900c200d0001c00d04055a540840b04075030780c416240f1020501c0c0c0001514820803000c603130406409051000f10429010107000e1054503259000c20a042030007001c003808072860002c3c0d0060740501c018041c01040c000c045416081051071108a44842221001983c01d206c1d03614000c8610300c1c04202d803030b104ca4100044078000e074425280c01c0082300e040710049089680c50070380d2600242052b0003140440c20452a00305cad041809103030050400d40c60380f106d98255410000c5241e46201c2000013042030090070310980e500b01c0000c080a01c40fa003845e882e24285103040f80e030040c0c800c000e90581c902503441030b80074117062450300c408c1500741d224450034404039400f4121821000e04600d40300026446205082000c1541e900410040c2c1d10303400c101c4400c1c024015a55840145942001510041607003080086210311402042642e540c928030b40d02402d4880c0500031000125080c0002d002c4a000e07070300c00141c0302026140ca6600d603a200e00b01211304030038041c0d9007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 667364937 1250 667363687 667363693
    0x7050a03030c090e0402010813030315060c06060803030105090a0f150e040c29031305071205010c080105060708030601030605120304050111030f0a20010f020c010b010306030c051c05 80
    0x14004068142c1c10081d2084100e840e6007000700d5440f48080c41052040f03c000780000c1500b0000fa848014051302e20b15414000d107000508140b20101101009000b83c01c100080b44845141600b00111802108050306540d00a5825945040049404180c014002c1005113889009905440c140e42d40080d0700d0b005074035001c4030030305d9030f4002489144200345c8003658101600040410966201810440c82c2c00f00c000b0001c1071b0080c40d00c4541d0341500050440121041180300060100310300f08000340c06441004040885142a480c1441c01c40301c1407020307503082c80701c0040100030607034440d0b007030310101900090300b04c2d940d0380c4940041300100b40c590041984011040008001c14800201400548034280c072445c034101c0b503030444140d4038061054007061076201000300802040c494041c02440c0b441d0011658110702e410900e403800c0d544e402e4490701c4141d5004c42c400865103401d0045104c0e150302800c00700075240c116102d0100c4038445011311402204c03280e0304400301c03d28017000031040f9a044070507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 667366187 1250 667364937 667364953
    0xa020f07060e0f030c01050f0702060d0609020901080a1401060c140a05030d1410030602070804031406040b01050f0102060a050601020304080a0605070807180501121404030e030712050309150705 85
    0x680140c0840c06458042c0f042840c002c2d0182c20005203170145c0010584440d420190000c43c030368403543c042d01040fa0000028825200c40074090300606000d040b40e0140507845803e0040010402c0c00c005040410040c10402009070440d50014201d0564001c2e180c2100402d94034181070710300700d5601c0e02c403507aa442041a8101404804800707840c280000c448140f081d03800b821684036014800f628485902c01302854200300160311030740200420b0344200221814265662149402c00581203d1401c0c02c0d0484800c20040298509480f4050801128070005440010000030359402005100a00d41541c45003c034403140c0c000c0003900e005118480480d6030418042c030b0404e0242c8400d07504a4081402040820103a034018034078800d0782045d22040d915000d103008011150381c1190b102001030907580d01007100000a40056941c8914040d8450090040303203042030603c1c200050344180703443c1d584058401d0016402104a40100300101c545801440c044a40c1d0300d824410782200810a01c90810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 667367437 1250 667366187 667366199
    0x9030602090a170a0c14010813021c0f120302030f150a05100c050105060909031c180b060307080607021e07050d0b1603200d060906170c120a080a020f07 67
    0x300481c4544c815400750400c0740c1d86889a6140ca000031042e1b901049455001a0740d0480381149512894001810000d01603641000f5a00c1c910b5808020b8030801c4018500100344181d40c10180e00003000e9240440c914a812101d0000d064406000e0040010010f098404180e0b103028000020700001804e000d0907800401e000b070200008120200c50390750921000682501e0403139181e41c821003170302e4051032806c0c41380840c0310089800ba803444404150340b0215040049040108200304511560360181c0b14140f410401d443c1070007940c0026100e5010004112900e0b6011900110501c100040301d820140e001e8121f9081c0700286d0405a00120586801070038007241c1b05601c0d000e1280d030041c2484142c004403044050b202c1d49400650201c01d250b40105009074070400400c8000d8020500154241d00e401a400a403182d591082030305400d04941d4401d0142c0a000384000700d103088440f920106581c4444e11307110341340340342d01a1070700e900801c00460050003400010300f25400582580c4001e600c81b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 667368687 1250 667367437 667367443
    0xc0307020406050a0e0f091c09051306031707030e1509011704022b060e0105060f120d080c0f13030c0509071709030c01020309072409030602090a17 65
    0x42400e9100e00c1c10070710300094a09210540000f500d0003991303c0001341d0340f19201c07400560b00141c5922124410781c80810120031200071480c4101c003c07643d605112528010401c50b40d009441007000032285010300420004003111301710b00303e02c10a800e840341c450040d82420b8800155500d49950041441d100c2e066181020800900c403d140980b150099900743d108194a01c200885000390408103c0d1820041c150740840c2a00b1300350203072226994220b41e00c0d510081030b500034070002c01850391180140101031424094102014505840c001c1d024411914a182c1c2c5030894a50081481100004039200c121500100c0b9403840603140388135510484040000c0c401c2d41c1901c016101c44110707400c080356525000081601130215a07458000340ca01c000e030380920740e0401030702c0c0301c119200030814450032010a00180d44146168800307018814942081041442044d000c504c11041c65075501c0390306507401000b58402e50b03401640068482000401040403941150440043e03519880440c24042e4000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 667369937 1250 667368687 667368697
    0xc041508060a060e0702031206040b04180b01030b0a02070305041a070c0b0a032d05070e0a060809010c0203070209010909021c051c090f060e13290108060d1104110c03 73
    0x800381413111356079002001ca03101d000c0c20301480403a503c0d05000c10440c1c64180c00c915a0100005c0000030b403c0741c40720800017200c48500c001c50b03044442d10010410303c20b42400700d0340e000100e04011f500d00410b9070741c0182030b0300c40c50150505404405440c1041410344c0c8080c1c0e207005e0781c0070f010070b9070f0b45c1c0d01d0b0318112110350044480310b4000380c100440c940c004100c1a43c8101d40c1c100d601e01101100031508030400c043c1000038440c00410036a00e00a000955846900000500c01500c03903c41501300180500d0940b40c0380360202c1c1c1590f02c00c000d00c500580b101c034140b50440707902c0c40d40040c00348002c3c4002880908c085020420201201400b40284800814860803c0c41e0104105407100547c640a42d5a1081c510400214442c000400c114140c041c0c01e4444441c40c0c0203100c072903240040031406089a40d082e07076007003660200c3e00710140780a07080d203903140c008902400e040805140100c0011551501110000c12a220201c981c0700551280e0700300d00300b41650306100303030345400661500f03a60740d80003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 667371187 1250 667369937 667369949
    0xa0621110301110f09010c05010f0e060f09072918011824031514090c1c0c030e0616090e09120a050403120c0c090e0c041508060a06 58
    0x160204110081c03805100300c0d0420800007101c0c0b0b044c9100480c0c000c203c0d422500712141400044100b02001030310a1113805290248040c000038005591610b051a040d001440142141c81d1030b41440041e101c0058100211441c40101650890722030302d0055404a0f41950b4007510781021510540c2c01e407410301d00040d60042a6100c4003c101c0608a02125034403a22800d1080d0b020801010340804098000c0043d1583e90308001c03480402c1e40c1c1a415098110750321000710210070b1442502513181c64440705070031070307021901703c0c3c01c100700c810003608103480c48801c8086840c0da41056852060094011707281c691410300aa80d010b1410307650f29103508cc08612083e00041d40d803d40440c003240e904240c0c60050620340020201e20080a1918409a000c005400c090280070f000000c00a02d8054244039a1200f42d0380c0c0c1601600180f8004403004000d0304107050250170000c0c40401c0e1540040c01e210300e002c0860700400e1023000c0c49042c5105150680000440303005003003c110001403507400400407039030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 667372437 1250 667371187 667371203
    0x20d0803070212030a0621020a090b0d0b0109020904140c0d0507140a020601090507030c0504051912062412331a01020601060f03050912030f04031107080a06050a0621 73
    0x9200d2100c07c501603c0000e000b50b10000141c420f01200315154132880d62000c02504041c10180365440b1a601020260302c88c01c0c08640000d020901801c040c0900341c154200c11050383c0c1c11303080281c0e5a100f5400f03200e440c07846d0365139a0000220310303500c01e500e44102c9420209120781c1e12100110020340b40c80090060340c4509040c8008030385514845c1c4034132110030301a030b80c40350306003401c10040020046003d000d0504401e0040000702f6a02c04824811420611031440080d01001c80f90f101041800d520051700c2c0b080303401c02e00030014a00e180056020150341310003100f00c0004445811a101d40341202040d07076241d81940784100f04005944601203591074400c1c1d40c4550014040126610b80003405400f0015400d091010110750003070700314a80045190040d2181030381015903400b490707007045814034031400c4c00c3e80500042c140c01c122504900342c1344101034040a41000c080b01e5640c8400700e0300820781a680c1000840c0d0ba0764541c481c0c005008442c0c00d0412620b0410035220141c048501709454901d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 667373687 1250 667372437 667372469
    0x6071e0f03200d120f061a181801050424060c0b130c050112020405060a09030201120509060c07080903070303051c0203070818100c03021312020d0803070212030a06 72
    0x44400911540002007543c0c82e0004102c240e290503015105c0c2454141016460f818040b810100c1d440b03404407907140c141121500c0340a5042842500440122014020b480090030540c03181031151680b4152501590701203011541180c01c1207184101003280030303030520944000300301558030030007200b1081d000e445e591209884240100c04440c10418001f02a80000b810402055024203a40380501c00c02c10360042c10700365541c021509582c0f15003a05000901582e42c14011517800c807a420100c0050400108901d02c1d11120700341c0d07201c90180014221721800b1516a04001c2440c08542103100302409448403280d80c1e03c0c002d0b003250400200e0140030310b060074090303a400030144280c0e84580201d82e540b118a4a548005903144406501c0c290254014000758950080d214011281d41e07110550b030050b6501a4080341c00300384940d41e049014900c1440e4000d0000da03888541d640042c03504040c0007030b0750383c40b0400207034940420140c0c40600514040f041224810301d07603010608880380207030112903203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 667374937 1250 667373687 667373747
    0x170f010f061d04050603030c010504080910112e1e0b0102030705060402010813050d09030303060b04080a0b09191101020106050a05030d0f0905120f150606071e0f03 72
    0x1076a0742c40082d160324a02e690200040c80c00350000e90704540e0143c10740b441c0072240800e05007911012502590000c40c00240071806082800071402c441d07440e8a04450300403890104641c440007010b20001e03d050030301714075081035202052165003200c0d01c01410040c03c080c8804004562110850b0f140b01e0340d1404103050b0f155400801105c0c011035022000d4602580c0703641c01940c00d400083d0030081184895081c98001a004016406a403201511103c000700d1643c42d00805440c010342050201d007805101c201310b0042d001a0711244c044d44405c034020303280d4400002d64542550390f81c400c01507000540c00f80041c8508007030007020115017039000340102516882400020016031046c60341540c0300c6041032150078404d44543d0240700f940c0c5000b9800c3e60f5500c000404056242600d81c080707802070804c00ca4410300400c40481d00700c2c2411812032840c6050700000e12940180740c4080e02c0c000009040042c44909808a01e00301c640c0301e9031604d0722504505000b8040d1902d0488407010345522040b510754 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 667376187 1250 667374937 667374947
    0x6040606090e0c030c130303080412140a2105101a0f07150605030106170120030705071103030a030f180203120a0915212703170f010f06 60
    0x15030b02c8030072509a0030f440e90006031929901c01040028248410f029043c100b1640700156030085020340d44001080c145814a10340318a00703401d015082c0f2901c0280319402160542c25900c08185a0070040460b0107405c5809071034140400307585504a1a05081101d641c9690701c12200358ac1441e0718034189a514401402440c1c41560b500c80440c041c244003100000ba000602644d0180c04070030081442c56640340407030f0960702c1c59001114024400300c81c5151659003489040551140a950a1910500c44100041511002e000380b020404001545002c0c02800001140c6403c0040c00312503039240c5ca0140200200f07030000f01d0321144c9040014050000c8115065035024540007406080d41c112808001d0520f6802186a0b109000c1001d100240040c2c0e004400400c00b0360300c0c0c580c3c031000011000c40c0d000c801d03824003410b94114a040f09101900b018030000050880c4c01512012260600d801d080d20111400030303005000c03032445420040e41c82d0031a40e206040b507042d003604500082e00c0c0e09003a54 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 667377437 1250 667376187 667376189
    0x615020a0201080a092103050a1821110d091d31020a03050a0b01050306011401031a030a030f0e060403030804060c051b010c02060c210a0f0c02060604060609 69
    0x10000e054400851041d2400e1745c86868034611032a5068080c20800354010030f070201041110000c42d503500200301c4110041d0049022100c0c0c4000e030840c4c3c4640f503540d00c19000c0714990003101200d4051050800850107060103651582d036000494140b1482803100604010582c0284000700c03403040d12180140400d044500e0007031800010a00140b20800d0030a00c0940b02101e01c0304001c005403440b5405a00c80c0317092000950701460280000c0411810903426548041e40803900a0b48002c004002c1d03800701034800342c40c000007460b000c00c02c5042005000c001410100d5190346c14040c0140c81003c0681100d09440c003030100d40c0368800100c1d0305408000c054001c0b48400360204500e40000303000100e5035444084813100740d0401c82d042c92160540003000340312209515031641e5540c2c81348941c194041080a900900101840e480c05005404100100c018004240c40c071b11001d00110324003030001d0704016141035045004020041c04840000d54400090b03c40354040c1e882e042000c80c60300c3c0700f580c0e610 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 667378687 1250 667377437 667377439
    0xa1401232205040303021b10050906010e070c02030c0a0e040c15020a08091906051308070b0703030c140c070905180304031b03150204050108150901060309110a08010615020a02 77
    0x61000303107106075000003801005100b1801c01d0b908020040e0924500725171a02d410200c1802030076004140e000030300803201c003d444c80031180e1248004100e01ca15103c04103a02002500e01b00c0700c0303000d0610211f403809002415260340f103070300b1900104080b843c01084a1280d03004421005500b07a441a40c044003851200100e40140c103c5440e150100b0100002020044005845184901c601c3c141c0d568040c0b205400000c0001d100003903200c44080441d500801800c1504040c0c2003252400342182090b109401c401010705403108940d0003018064039101089500e0450241da95028002055844003854000c8507540c0303213044003003003004078a1000c7c5541d0319203800c0194641815600e0340d001d0840f400503c54550042114003000007a030704081060410740d030000240e1940d00b040c001414a00c0020120310f1100300320a200b40342642e8805090b4119510350400064500441c1401c07102d03540a40e400d1600801d50b00e50010340d00005510900440b5240301e600707800043c5245040b40c558043c4030020b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 667379937 1250 667378687 667378729
    0xf050108060705090604091113090c0e011b1208090d170103321c0807090522151a0c15250f080109060f0e0a140123 51
    0x42d0300c242c000e500800c3c0100004000340e08266441046509481d854502011040c00105c2c0003ca1004000a20405050070385405d20980d050100010a50840a010f5134104260240d10074040054210700c440d203290003032a20549508049005070a080c42501c2d82469807280103840030700203200f81082c80c107000c0801039034a21a482c648950600d4030358894200d4040841d00b000c04ca00c10b03115003403127100c100d005003d041d0305464400d8070302150392000440001d0003001020000c400c0d40c030007404019a50119450402d03c2480031440b48812002c0080c00d869620b02103114016000d0000e044007101c4c0d94005070504d01c0444100b00007076000780110320050307501001300a80b4000c0c5200040da4440000b9541c40419003030341d071b9040300ca406240104030208100000c850710700ea500850646c09803082401c1444000d24190441c0e040c00340074414044940b881e80080346032609140c0149917600407084440b02196156035040a844840c0030f80b010744455490041d050300d003044003480307240030400310174 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 667381187 1250 667379937 667379941
    0x1501050f06160303150602072603090111030c03070606030627030305040302160605071703130209040512040807140904020f0904020109090f2705061303051606020a030f05010806 78
    0xca0b52440506040c120141901d89000c004815103110b81d017401088985d0040030341c18545140340721509480560111800c43e012803110f56100000115560301d0300030300e0403800c029001c0c204c1d141103000300340551501b40000035081081c0185508004143da0203020b00700643c100304010041d600200d100420700c00c0d0240e400410100e8080c0c1e020542c06802070041d600350360b814200c501c105002a40210002c518041002418070608400180d6241c1000c8200f901e12f080541250844c1200e90200900c5119080e0020301088005d000c98401c01c0072103003925460729162111a9101c1ca058000e20060711003503140c001091a01591250003140c01504040d24880a042404500c180082050f818015240340000f003d400c503110b580c4081c1034425000541109481c000d6103c190145010701c1c0308504010040003080021030403079002030040305801040085464182c031603008109181800880a96294092021a40040265032483c2e0703002c00c0407070408010042151400c0c020b6031526804440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 667382437 1250 667381187 667381207
    0x30b031b06160b0f070e0f031c050c01050c0a0809150a0c020f1515030a0206030121060204090606080109090c0303081e09010b01020609150f040206040503010c021501050f06 76
    0x100030164018403404280e81602d480e1180902094103469081d4080e45500c104103680354800e20014a52200700c03074203500c010004000035502d071210061041003a003080c86100c0350f10700450460b6030a0441e50020700c45450300440104241c1c000d0000003010a8103003002610401000c0b03602c040800a803114400079494068501c001000007100d4001503100712030041661000410021843c2c00c100e20003a18240f80156075011003024000c552070103940603600900041c0e40345000d0380c8c156a510b02c2c0030700340b0421200c00111100d101240260880f8070015010801c04c078150400030544005072113141c81c90340d9903140c000c03c0320b652580c05804d4234811101840005d1007030409540010700903442d00d518220904c07803141e18040c107a80c0c9220586d07444031401e50550b010301c0f40130742c03080c440c1028200548030030583e18400180200307111034480f18400040c085544141c299000741a001c0c000b00006000c244002e5510044a10701d412154400070001a00b86440e08100b2110078003d03000d1400c0c110502 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 667383687 1250 667382437 667382449
    0xb0409020f07050a0b1501020f03120a09020604030f05120703020d0806010216091b0201050601020709150e040501050609060418020105090a0b030702100f0501062f011b030b031b 78
    0x48400040c0c01d08004010101c0d0041100100d018050046204c083c00c0103045003103072406807555036041d50490144840441004000d5070482e0a2082c0740c80764542d900300c0e02c0002001580c40083d4810303400f140210910084006206030703148100c08940c101c44a04500da0b1240c084c4a90040c0103034001101000883d00c100300c141e40204040c011107c0c9801a01702210100400c1d030009108640c0c0d86004146207003181000f9220100580000c100174104080002c1d151030f024010360404544505801e9030303040c2c103500c0a0703000b8052400420312904061170414044c040c01c0d00c4030b91185007803202041c0c840c41c19200d00350321010480901c0d00d4070b8030b081c0d00550301070700003401c6240c1c4032840e5140004c4030012400214802d640035030103444048140e4511004480e50700490f105414640001409041d030420250035070009202100c0b0001a8050b41407100f910b05507002c61a41c3d400c00351a0030f80e0748601c40e2940c0d20f800c21b0791401c1c000700790004181a640c07001c0005100300150b0195123806182040c1e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 667384937 1250 667383687 667383697
    0x304061a04060b0a0201051f0e180610060807020c2103040b0f070c0f08030904111306030c0f1e03020a021501120201080a020304030906050a030e0a0803010806100b040902 75
    0x16840003045006040000390840d00d05500c41d103040c03030340010001a005c0c0d0a00c0740550000001140000d150100c10904111340480d00484600214903004100d22240f10044025940d040f030f0120350581ca400c04980a03a41918030400000c241403001040c441800842c9041c11407101802c41c0a030f00300f225540400c0c03650b8950054941d8081000045003890304c40e401042100c40b0400b003666100003d2400f07581f0124182e10601c4007240700142440300380d801000f2100041c2d0201c4002c1030003868118001001e104503d48140c8a01d110500054902e8058000e9202100f1645544032000c580c440152400341c0442107450054900307120484215019034054082c88006104031250070390b80503660b010280d0281c020388420201d02c03440f0b00031983e2084402e035114446850560460900341d80141035009140100780c18050701080c2411001c0c42640150a580070300d20407208022170b2400c051582d54001c0c052400e45d4015140094010001c0710714000807560f68a22141c5442e1811604500035080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 667386187 1250 667384937 667384961
    0x9060c03060d081b06010e0912090a091d1c0203031605070203031c06150210050a020c100f0b04020a140d02070b0708090d03060506040302130608010903200c06030406 73
    0x2c41119107002c510204041d02c444000c0c0c01403441e00b2202c900300d1030700e0802c05901104041e10440f00f044100c42012070b40700050f10304400d0958407440c001000a6280d0041d030071401840d891b003030b00d0540058401c0c0c0c144840d85903200544414144011103401740c1d42c00c043ca90000f6074010000b04041e4801144007404c5001146080360070f15045900007410740e800200302d440327020300d42451850f5014a901c1400010310710343c801552420000d02000e9110094100c1a0114698035400a14140c070250115010310640e101a50b41150707030101541c1c014004091440140382c50100c8003540c1d81460b10880303400c160030780c8070700c43c18100a04960685510911000d0081d680038440c0d1000201407401080c084c54454441401d00c0c601445450315180500d2004000c0504115040020b41c588030212820b50341c040d01c4940213803003660101005001c00d43c1c0840065071a06460b0f00600d980050340040841080c0c50043e8134841c0e110006545050424040e5840307403040020400146040d4022820510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 667387437 1250 667386187 667386199
    0xc0b06130905030706050106020601060c0b06242113140a0b150f04110a05090a0e010e0402010914060d0b0d020d03090503070618060c02032505040e0609060c0306 71
    0x8040c0a40d102070307482500c011159a440456a98104401030003042d0240c4441c0c402090b042d850518020301200000c84050000c0300e00401250301c07500c1e80e1044160f0166a451306201c000031030b6040039400e0380170006050500201d0040c00540e4452811a81d00948643c501d03116001401d403160440c004081c03420501c0381c4108801c880005940c0c043c40b600c112101a00001110031601c140b149010154550034070562400034403941c00d5059005642200c2d100e031a0441d215144c25000c9000c54080b904000549035030351000203241c40725250014410340c400e070b03070b441000d40d50b420034800b1900d02d022075680d10801c14040b605450005a10600c0500402450355800280c190080390295601170403e0380050f145000501040c10100000c1740207145d04e04d048005c48101c42da04d4000340401d405031108108a1000d2081555810040d0710b80d0280310b00d0102c24074100003640c004501c1107501c1014016400d01c0e45440c9105c0e40812040c1c400e00842d00541410303a603810242120760300003131116500078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 667388687 1250 667387437 667387459
    0xf030612021327050d0e03011509050c090306090c01020c010203041203120b06131418040f050715031e0207030512180712061a010f120225150c0c0b06 66
    0x165092180100d0315000d0310140060500b0174900078401403c1404590080c0e05000b80400d0707802030b209541089a0a900c400a00e80d03e400c0b000a400c3c1c465825401c1e4544102d100340030030003c0105c4d107002d80c0f003026003c03103c01e055004010380c6c40c1d006074810303034010038542039075240820b00030820443c0c054035564002130016010b0380000c0c900d402602220701000c000340700c28022001070340344500e80c480c0101c45010842d00d010007819446040200700a0401c0d08040196040182c10803e0740040c0407005201c40701d1080c2004024000c05245a103011211b0003600c0002105c100b610032101070580654400d4a0403044030300101e200c2802401007202d50340d04c10341407104031a00380101d0000d03041d019405d11410025042000645a50f00c00e000c0290006440d1244660380003805000c2d1000c090900841806418520350024090b00340100030180b03403620b90410601900d00a004480d129249081001500340c82c0035084646007190a808a400e0318100008108400e5600b07901138001061006e0705c5d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 667389937 1250 667388687 667388741
    0x1050109060f18091b1806051605060906101203080109021b1c180602030a08090102070b01180e393003090d0311010b030d0f0306120213 60
    0x802203501c2094116034690580030f0f0100607011700b81c050710041c607116580d08142c850102804006100d410140080003036059a12003603080400d00c0b45070050141e0b250b030301d0b101d2580f540f078500860b40e104590344409004a510207050842d00f00703587e00355440b201c541e800c0c042618001c0d0b0202d001400d03035128102003090064010401c0030700c6100303080c0d10a0042c0c0c650020160021880e81394694000c540d501c003e1101542c000150703500040e45180c8889651101545035009118007039010384850301c61800407500c10401d1f045040c00c2245120108426078000361825140c002c0c41c0c1c45884022800c210406a80c401c18104039040340c42c0503003a03512074080c02c0c006181c1118000c500001039116840c01000360703100482074901040c0c40000355141030b910400003280b002c0601001014130141509521916000358080024441b025040322031551140c01c000d07100f05c1d401004540041d00f0300d0b4002c5241c1245c00e218144c980e0b806090100102c004404880240100105202c1c0b000c60b80c5201c1e00d04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 667391187 1250 667389937 667389977
    0x705060108010b01030b0a0b18011e03140a0e070302061b060907060f0c0f020402070c0b1b0c030a050705090702120a05040303020c102f0307060e1501050109060f 71
    0x28a1140700000e9a0030300a0009416545d800c00041d101d07503d46c41c0c0800409100e80c08544100266000c0001c1000c0c20500603a003c0810300407224031110b100042c000d0b0340b60180d200107075462110120701ca1a50700c1016a0041d50380702c4512000c0b0341c11054003080141000c1015103d140600c20741d514500090542144c90400115a020020303400018100f2813139402c10f405101c0107085207040c07006001141c0341e0050144060000902403580040e503075080c0104061280c002c0c0410608182c1c0d00d070b22442d010340f041904012801d0050052581800d81854002920300c2406d6102c030140155500d003c04100068100508400c1940940ca00e0381407800001c0c0e0003020041d01c2a16000d0b141d90541c240240380000424030300b400740c84000381c50901d45401a80c4015000110701d08a00e0042c022602c0c0c07800b9080c8032420b070300703680b01c046a030030100202e9800804080520400316000090081102e0340301031020711502c0d0109019480c01c0c02200c0c031820146100440d1400e090620100d00005002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 667392437 1250 667391187 667391189
    0xb0103061424251406010e010612200a03050108010b030a06091b1701150b0f07030c0503031305120711061e03010312200c0f03190602030403020d02160e04050307050601 74
    0x10f041e81940c003801013048803030b000b9407851541c0e0000c081c04d40c1492030064060324180224002c2c440d40c40800d009604d4680c0094036120380042c0c000480c1da41d0810100131030341043c842d40c0d007c64109000425085414460100c98250080082040314116142c60300100440c11050740d502c0681402403d144a011015200921102c25846075042000f0303096401c6424041a101042d07503c82c0d0308020313402130b84081c1c2d80f9141803518600e6840c1a18982555059820b0300014094003001c0300300f00c0c03040010300700c00e0070785801142902c1545541525a010030f22414200900d62046550506002d0401d080034041e1182d02d080441d180b0715103003039034012a030400da0082f01e40301d100d00081070180c2c0d4400b6500003001c0100070b04c280301c004101a220786860003865800e004010030541d8024030b0b6000c00100010001d00402c0e4200f42d84541410700c0690b104480541c0980b0944404984082c4002907241e0300c5144114404003683c18a0101e03504060b000d40241c07001d20003070040c9400719505018044c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 667393687 1250 667392437 667392487
    0x1f090801020a0203120a0b0a05010e040f0e0303010503070b1e03060307091e0c020a0c1e0515070c0807060504050409060b040513030311040b1804090507090b0103061424 74
    0x6880d5811440440305d40d140041c1414441c40c181040c484158440b0082c02050301c0c02400c05008840300f010104004020010031400100d0403c28900d0b03100d50007100a40c140e0782d0079001d4548042e107403040c41e02907109114000304018402c0b00d0100c1c8291001d0301950b00014002c0a8800950f61650752800b690134081e40e0361030b40c8003441540220f4958078440c4c07070300c1d844060000d8004030003a40c4030740303e60140c1803155244240c511200125034428100800018000052610040d03500030400943c44c0c2e0050b00f402c44011980840201c1d0000c0005800000c641103507071014a464208420701000d426461b4085501917250200c1140942e00c80c01650b1207851101150b5244c8003507400c0090607039140b0200990100000c100038840c007070840e401c0b02c4099110208008040c444400881c005294890001d0414002c160340841c0400041d00403002e407a409071b0b02401219281c045244024080600003a03010812696031368400b10703007001e141d045111034201d15040c44001a01c914062001c01000c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 667394937 1250 667393687 667393693
    0x207170a0e01090f05011b02060c0708030d060e0c041406071502090f100c0605150d0c081b0d03031a090108391210090c231f090801020a02 61
    0x142070b568840050001030015810f5040c9842c40d00c170001e41b12550744140031802c0404101c01005640307540c0c0c00c59200c0d0106004171071030707165038080e0301d501d9402030b0344012481c508040700041d00340c02ca0100e803030060740b040b06207614003850070315000006078150a100307800440500ca040d01162410001d004000131036180540c2d18042c2001f04844903404105152103800405004004541d21081e20000607070310020002c0d01e03888003117079210600003402c561644214441c2e2441c040040c445540f104032920402100e0040000301d40040c4a484038420864002060b4440100807070b00c82d0b00003c3c01410003c0504640700d00c07100101d1400720f82604580c84560000e810300b1252011440c405043d11101c8c0440c10400c140b0a030051000d20044120510901c82901614540e40b070a01005960b0200b912040040e0074442c9445070080c4054420f640921442d8a20030070501c034907a078002d440d80310041c003292040c0400440380311700030040c0c0058001c2100885001c501080244003e202c0184c1c00c0d001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 667396187 1250 667394937 667394957
    0x406090b010b03150307031212090204020313030f0c030516141015090b13021c0c020a14150703110715050108010c1b0201030b0d02030d03050117030c0c040207170a 72
    0x412a40c001c048004680246c1c13080320200b02140348124560143c0700079140c0000005c00d07442c0c059000c1c140300000a98058800018059560207104032401306038400e844202c1205c2408806694841049002402241040281d03040e4907030006c0600c0603c500c54071802403203440c50041c5c94130307105804003041c64107a0f0b00e0102d12001203255050760b00808840205000f4080744201141e0a404070020300306800d500850030700700000c4001c0398442c40c1002d8401c100b10801300a03030000c0d0b40c1c3c41d0032501139880c050f120b614041c9401c00407610424000b06422034203110340300d0000840003071030041482c0e0030321241440440c00044401680c200d55440f44180490254185004a0308551a41c0d0030581804401c04011451141140000301d0007502424005000351102011603c01d2000040c003d526000c0d0388a10300d4025050360015040c0c800a01020440750a0585990350741c3c41b90860b640907a900c2045c1892172407605400800095120300e0000c094801035643c084007a030486041d800100d024015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 667397437 1250 667396187 667396201
    0x112141503101e0903210207020a05040212040f02150408011b020c0a0e100b0f1c0b03031602062101060f0203040302060301050907090f0807060e03030c150406090b010b03 75
    0x24610b41003000d0340b0104210040020f001054a403040d9141d40354644811801e028980a22105079510b403c0c402410020080c0c0d4842078000e601c504012842194020400b01e13050a01788251000480f01082c07080068485480c0c4a4001c0140e02c0100ea010305a04092440a25494007500042c07502c1c0d030001c1420f028070440110005d13000c0065900310f500ca82c0c11620b03160380769200c0104581c40a900b03a050750329030800d00683c06c1900e4002101043c0e00181c0c0c601d203912014020540c49890404684029204c045000155039042c2c0d000381c0d041e882880248120705d5205800480c007480100418644420641e08035604203804030413030800b41c805001003207440c4c1c12a000015000451000d54a0241190300144040c00103000320360060501030300007140c00c2d019414010141034400904061980d4850810760b90300b100340243e400042102c840ea002c0c0b0f0500000359985000c8041c05000707010036824000034440c4000f48150361042d02c402007031010480301c00295002c1c0250211140d600c0c83c02d50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 667398687 1250 667397437 667397443
    0xf11070303050f0403021e030903010c050c0607020d08060f12060a0207050f07050603010e0c0d1e06120f0f231b0108040309051c0212100e1203060112141503 69
    0x503c801114050301080000103a030201c1c5103000720f070822880b42c0d840340100c92010310b103005407010a41c1642c40e01a030314424540042c0501004000d1504980341c0313582d5014200e03254441c5010b9140800c8021000c6103183ca0f18003490b070340c0c1d40000b800d030360140c0e80140307080c07072801038181c4002000550008612003444014029600c540884500134600146040040f40d11f510051141648000c42c0d28003084000f0b6141040750f13411089000d090188481007001c50195902d00400d400080e40740c044006040300c068002191007603040792020aa40e501a25441400408038ac1c04460407201240d2408401c3d100c10a141e82c0b120340080140281d08151075090102c002109145061044450421000a62120300f400686034103a070000340480f50034441400d0710380080c1000358414281c0d5445129104002003a500c0003044403000d01a042c03417590180d40341e501c400714220b41107404100240c442d5000b5a0b00c040c04e034044120000d103801c009901600070032001d40b080340041d450002c41005034a010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 667399937 1250 667398687 667398691
    0xa2301032304210c030c030c021c050618010608030906090105041d071d100c0212250f1206020f0f03010602010b041d0d0806370608070909020306040f1107030305 71
    0x2070510901300a41e40d02c0c0600b05102000000f000c01400b00030030404c5440b402603078135001c20381400303411840850f4942140c6400b0222803180b6401006007134429400414002c6108507083d40000c0c61070b040948080c00195409400141d051210400c0000390409007401007041c0900442e604455904182000500d8032105010703114404506a81c007409542d68132420151807a000d05020b1000d03051480805c00c1e0b00401448c200203402045010b03244800c0d444201c01e400c2c2c3c080c2002d298080e443d0449890450700074054204088108050040003a0071540146903810340c1015027410024a02800d02441d03109800c81c40040c0d440361031301c8080d8185401405030091611b4601011958607014069807481c802c0744d500e007085500d4020840d80d8031032140602c603120320043c00c2c030040789420f90030145d0280c4c010300c131980d070b03030440c0d100000d40314810100b2034000d40309a40c0b403031005403400390308401030340014042c03a61050b501c0c161045404d4541c0f14a000708828401d9040c1c8034081d50401074211440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 667401187 1250 667399937 667400003
    0xd1d1005010501020a0c170703060e0304050102061b0322150603060b04050f0a0b040207020603150123120711060f070e06030c0421051603020a2301032304 68
    0x11516802000810301e180c0d1006840d007d5109800d0412100702c400d1800d01d81e90720145c24103260030018103c010b80480104140d60342030b0202c4481c0d49880b401420702c102219010703601220f050010410b690b594800c0f0702c1020312480460807007415070f600c8030411101c4003c4a00589a5140070070010003034280910803056200b160100800e19114065104140c030050000401c681e440c0d585000e16a075690685c0c00e440d4003e0151034a9203044559221542c8502000c10302081c40569a68006280255400c1011f82841070040c184a8041c01b0104005409000303a400d115900c4580c58a0b1002000024811161030603015090700740785001400c404142500079000740307030800402003030030b210314101e40c1243e00c2c001d0f09507840c400d01c1003c000c2010710404001c14078081c400d010101d07500c0a041c0da0741036900881f81000d5040e40d4001c40c1c40706404016510401101c040d4000b40e241d8040c2c0c6c0701603001a500c031800034000184448007200382400712402c031042c48080b40102d80d080030840d016424000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 667402437 1250 667401187 667401193
    0x307110d031407032903030d0609020408010b1032030f0708011d04111f080402010e060702010e010c0c080d0c26030c07020607150b0108070e1003020d1d100501050102 73
    0x1440c4c000000304203171110321603490400781c5c00003902da203040048582502c04007604210064617010800040c0d030040c45500119800c0155801880c548500701d0511400c040e00d07600f61607045403109550603c41e42d090840e0074030300656060b124032020030007144104013810551845292034040500700e41810f80145070b4074921418003c49a0320407a02c40d5070030580040701c104280d540440008c080c0c1c0c26111080690034441c4003400c0d45c0325040b00c3d01500980c400d8a583c11071803008c0d8103100c001c2c00343c114081d0000790269841c44041d4041d0088003080e5000da1441801e0701e8031000114030b041c4000e144480040e6100c0440c4003845055411490180824107420006003203072600134000740401350100e640c40d4000205c1c01d0444d40c520080760541da0380114950302030b039203080c0d54000070f2800d215203502040e44040010181841044030452640300141240c5654500712002c81c0250040b00e0491760290359015601080c002503e41000c51001c107400400d50b81100d1104001075510603844181558 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 667403687 1250 667402437 667402451
    0x20c1807050f1303060903020609010b0d1e03020a050726030712110313270c0917010e0609060907060801080303011203021507050c010c0203040513020307110d03140703 74
    0x307601c407003110340a90500c81d03040e45844205000ba0322001c40c95000034071092501442c8405c041d000f19441b440303032a4210081107541105418000801e080c3c410007440302d03903074071604408945808079402c0821b00a1045502101c030340da9805160403055000403295101a07000000c21164903c3e180c01e000d16000b02550421141c0d6803440c01d0b202c0f140e9482003d1162254020626000800c01d45031100860008039004075030b03c94202480b40d01030b9110100c0c808441207030040d6219640500c125550555075140e49032850318491406100c440c114a0080b55210491080350300c00404c01c8a009111503005807803141420035402e4070340840d5901c8002071200da01c00410025002006490448050450790300756607510380340403070804429030070080e1600307078250074440000d9115020703003000c000f600d000300250300e0804801d0360707a4040d610038280d000301982c800d03c40a40040d0045e40e00b040003420408507500210002034145400a14200000b035a21881c0d040800144588a904880d9030704040001c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 667404937 1250 667403687 667403701
    0x2280f2303060402120a0606030303020432041d070305030a080f0103111005041509080705040b030a060e010e06010e0915010b071407050d05010b15040f032004020a020c18 75
    0x40070000e03c040c0c0318541c4141c0248108505111581010b03a0081d002c1103000d4813460050020740060213042e110b0500b11039404881070103e0640d07400c4c03e0a440d6000c03121002981044043c0030a034055800b81c1e07405c16400010202e04120360805103114201540d120290041c0c01402018011300c50b40500710144010030120703c1f071100c039a040510582d99203203031031400708090700d052203a64028030040c01c002d034001c401036500c8803001d41540d6503101540d80a41d0303203d0070041030340c50440c0d00640c55004200603100048030359000020429008001181d410019043d0609024090340140042c0e01d04c03100700041e1079000d0080005200f90140c1c0010b0bd5414440c040805005801e401800c818400c2d41880d5181d00c1000003100030100107040f8024100503150481c060b10020803460300404204540955040c001815581920880c5080032200e510b56205c0703c0500d56031506540480b0748126019807940c403540001c1013021880e1700204110020402442a501290b030403000823245024240044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 667406187 1250 667404937 667404943
    0x1805100b070f020603161106070527060304030807090801021e09190803040801050c03370204140f0d030f12182603040c0302280f2303 59
    0xd640c40540d00a840d0403491400d40360010207124040c3d40110b020013003000081054115402075407a0313036103480d5240c003461145a43d9000944180c00032079000d114040109902c0d540340c040c641000308102076200c0c4100d01156460380159010750001d0300000401581e40d40042080c801040900003c40c500350032810185000701600020501900c00081d210440313035a1010348100c60200c684048005946e2180000c3d5654000d01c41c4201950910000540114481d010b6034030406440d0100855005140c0c1c1c0040321350980128607100c2e409521000c161051103201a10140400084440802d600b00c0104110300c410910014070543c0d602c0318003000a5030000b0601c850344103904110324100304000495001e0041000d510108030000100b00e000d22800300c482c00358282c41c0c1c0700c61030703148503541020045600c01180c001d0100070288004100508200000600140301384001102c400c44910704a101483c107903210410181130a00d091000c042c070071180c001c003100c02d40b503000621030b0060080780d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 667407437 1250 667406187 667406189
    0x150905090a0509122d07050105010605041508060306060118270b1f050d091e1b0e0402130e031c0b030a110d0503070206070b07090509091c020709090804180510 70
    0x948411030b040c1a0102c4017904290341c04141c0c4000203102940e101d9000a101e074000e071050450020f65030340601030b464001c8440d1402100c02078040c0c04561748000041d1840040d043e40319561500380440083e1108001803400030460000c144104885070b0f507007030003003503440e50703010705109a015000142e052a50103042c041c6010580c10400e441d47d0404c203a05004080e201e8003e008040b16824402040c0e0f24542100a080c0c46004a0601003032a460800c41c265070f24000c95a0507050540894094500b40c9000c0e010001d840740081030b000e804034055815500091511030062803d81c0052800d1007644c0190310094000b0303070050510400c0c0d52a02c101b909116a11280a00000e01e640c2c014488148100e0310495009010360f6030750f80240c0f03001141c40c8422582c10001412070880802c42c2d15041d00d034603008111020081408020488501440e000c11030480810741c403400c0c1001a00a00074041e810507280940d20107615189044014550008181ca41e45130440c980403c0124902130f80184c60 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 667408687 1250 667407437 667407487
    0x60b0306040522050703140c030a03050c0a02150a0807021f0b03031210030c1203050a05031003120216090e0d143f10150905090a050912 60
    0x80b605440d0520503a0321075020800c44031491951032000e50030f120300090040c003284e101e00c411a1031242c20441c502d488044d00001141d040d04241c206e100424032490290080031806000d40344981e40c1640051710000d42c184410748aa0350220703c400446800039142980043d007030010341400d8040e681304140b0300f52120700a0b20040d5881d0310841c260f4408000740d410401106400c455a070400072103c1c807091416200c120380c050720004011402c1e0136440c101c100d109034151a104d00b44503072000160f0340f90708002d12400e0301d0b4514001c00004100c1ca9003084008000c641c0103030a110064108209071100035401076005a030514900410048002981561046e21440c1c481e152050b100528074181c45404000701d0103080700c02c2001040710600e003c82e14010a0014000e070f100a40842c06007260004540c5101680c201250420030721128498100c0c0042e601d14240142540304e200041c2600030541b24103640c1559482044120740c01040345a2441241b100304a080842a502a00001c1070020580c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 667409937 1250 667408687 667408691
    0x3230106120608010204082a01020d083601061202090402010c050304091b030501060c020a150509030a0506040201090b13030305090103020c0a03020c1e06030109020f0f070f1203060b030604 83
    0x10600704960354004005000c9000c002d5503a00c0e6a010a030b5a607000d48003a0b554800c55a2002000036001d004040814800c1070f0045c00056803100c0702600c400c0720040c144818007058820741e18541e24a80081c050304091180c040c0f030100f044c50849400c680740e54101c203c00c80420070000780903980b03c0c00380541c0b0950929002a20b01c2c042d1502031f0031800303960f000d100c1c0c580c2448020780c60200048a180c3d000040c3d036400300b21680e621401202c01303c0850101a42003020103505001c1c9045e10b11841c075820406040c5549444c5007030000c2450310820141c10785003600b269060000315a403041015006015002109040c60720303100090141f00510701c001420300000080c821140c0e4000e80544000c0000d1100341d840940d05401d0107500d1f40503212034540700300c145120b400f4a000c18104c1008040c0c0c4050003003070440e800c00309520002c0d0305c1036900b40300c10030b42401500d41801e42c2d00028a5460301c034810b0600800e040349401d0060182d1900391030b0602d41002c405110304101e50050300d030702c03800450b00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 667411187 1250 667409937 667409957
    0xc0304020d170703020d090608040f020f060a1d091b251401050106030203090c091329010e190b0f030d030204140d0f030c030e06120703230106 63
    0x1c01c140d850907002001c0c01032501a2580b80404800a410094080c1d0240c4910104005d0100d84503035450180602042d40000424007107102c1c80e00103220a4809032102600b9030342c0d0300010300c0f150040d00c02c03440000d981c2d911100064482130b0b450f41c5029429111340f8203a003402103d10000820501d2003810078840400d440c01c0785220890380c10b24444099420140b000030904084001d010f00c00d859004a43c00d0100026000b8030910849110b103035584013900c44c6580c003504100300000e01406000390680700c1c01202c004500c003040d60303c03c15400c1001d0407822900541070840d80240581c030112104142e00100000c4440707610801465401020307000407030440400024481c4840070003203a80501c20f43d610a44c00c2c98040c0c3c010300c103035140c800104c20707010840c008000c1d01b24036400c0000d20b0401481003060000380240007074030346c05100b400d21065020760000814a15000003940d006600660320510503802c0d05031241c00e010380300c600e0b0700b0b0004107000220a4510b20043c411030f4100045021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 667412437 1250 667411187 667411189
    0x41a0607020d050102130b0912060c030109092424140d061b03050a11130b030c070f0804030b0a200a0c0c0905040b13050607050901030f09060f20030c030402 69
    0x41160300eaa6000c4401043d411f440e07801581d49500400d403040d0094030007064100407114000f4000f88250000780c4c085245070b00300034508005e0004610211590000d4548a410280c0c04220103070781d03c0307180c110024103c6032548085c3c1c2400102c900802071404448002d20110200c5d0300d100400c0103003501e4000e4030101d035241601c01010482812088030440040001805903d0307007007580680707032001c07003800030482090380e50403180301392a22809625400401003200020f90400385500080044105080416640b555034548200103070455a900c0c0000342401000900d20841e50840441c00b420800104115001148109000325604010b100481d2003240d03184030321691410603501a2020b40c00741c3e55410761034003801094408403141d185d12000220204e107481d407070724203042e04100204035a440364003080e1110340c401102241010740b00c1c4030005480741d180c014901428403074840001d1592080d00e2500441d5220342181200810540740d0607030140880c030640340c0065200b05169902d4850348 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 667413687 1250 667412437 667412441
    0xa0b07081603110405060304030c02240d0f090209090d080109020a0f180f080a05060604020a05120403120203010308030f09031c0f06050a0b041409040b040f03020a08030a0b041a0607020d0501 84
    0xd8802c2ea07020300b000041108042cac0c0200c8240c0400c1c800c1c2e0752100c03184405c070b1134024901846070074208181014025100300148a41184c8902d051164002959200903004542000c208840140e03482d0300503101c07507441b40d50086d003007801044d4046c011410952043c01c01000e4019081648041044000b00010708600d803801110091040705c0d00c0240417071759a034296491300d0b4107000c213a84034000e45000403580d0520780219030340354005179200d918049806417000c6040300c018205070104410b6400e481000106403005601950181100312788900c0c04440807034084500914001c1c1c3d980084c003c0884546d401e03906420382854094010603400000f000c45030003030103940d001d994007507104840020211a1600107006130b602040a1060a200f000c040c81100e5200340d80007011071a560002a0100303540300d241d220528030920540d4658091070302e814605400640d42000e54654660f542c0c8506e16052094000c40c4101c6c51050185140550000c0c44a0098240107070080c150746400200308103085d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 667414937 1250 667413687 667413689
    0x10f1e09020a03060801050114060f0714011409010e07060504180b0d11011701180e03120f0105030c01030e1c09080708031209060402102f0a0b070816031104 69
    0x4a1411511104000340080c0501414032905c0b480303500c0c2100100d0f851540c883d43d08480303100641800e00d450781a00200c401c41d8001c260076a41400d0035418516503900138011030944000314903030a0800c2c01c00760001e60855a5002c8010a2076000140c20892141c100e0180d43c00c44103000001101c444071007400030040c0c0000c0352141c4e403120210341d18000b0050b0350f072544140c8090030313031f07500301e1141e4200628200340000b8001d0015190a03040c115401000c0740d040454240314a4065a05107a0036a141c001d90401c1a11065522040c400042c403590808200500c0350900910f0144401c030b8030034620588440c40c0d1000031825049104102c400c2d0707401206120001c0021104403100266981c1d038140d1660065000050038001060204040420001d91540125001041c00103424003207001640e400701c0c5080c5c45005182c404121990030b4007064401d000e2800d605000c1d0030040000d15200a0810b0000d05800601900c60140861180000c00c024115051810002461030940e410381e860390240e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 667416187 1250 667414937 667414949
    0x607120b03100e0114071b03050d140f0c160b10030c060509130902101d0d060509010f0903090e0a020d0204060c05073c0e071805010305010f1e 63
    0x2d500364404040750141d0020403a401460003c01c40c0881040081d043c0c400e007070700d400700014941010640c0c01400c1d0400c421507288a0304120303145c154812400e00c151401c101c0c21800f0fa00c1050104842e801035004040e501071500e031301443c9003802c1280c41c5004005100405440b6034407210000324201001c1107808080d41e006140b01d80c490303560b41c030010115400410902d000f800703201e015030381ca407140d800361844181d0300501c1310080c058150011110714a0200d0340c86e580c1040c03040030605a0f21303a00c1290841c0c44c0250304c08191407400c04007460035555084100032200b442c04a801010030381c0403551100750303198102142580d0b1510503000c4060300501c040000303d60300c00500080e030b0940000751192500d100703000380c0c0d42090f03403800000031001e401c2d0210380b600309484003401c0415040c16050040300d00c0c0d10407900c0400c0d4541070001c20701c980407520310010604074185e2207031850700d040d0800e00038002464148007560412400030409112842210000100310000182d80b40d4003c8041d406441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 667417437 1250 667416187 667416193
    0x106030212060414031c0506031e030a0207050f06041505131d1006200109050d0e0a0905060a0302040906140708060a09050907061404270c020a02030607120b03 70
    0x20300032075501c0d140e110560f802c0354000d0031400213941000011050780c000c40048000010748519400a40c000ba1400070702055050081444614843d111049003900d80900d020040d5210038540c0c001034a07050071703a000a4490300c0c42d1481680c0c00d54030b00040b03d003030340e9111600e80001580c10501792118001e03002d4030821400c440f0740100303031404c07405003509580800301d450078015111040082400c412500440c0300107010041022422228001103103c40c4186000020362201e83d901c8040c20301011100c11400201000707200d42c103030310701140310030094400140c0410150400c0800250b804000b07120003405151610160302c148801503104e04421130b0350b565205820314102e0001080c0e06c1c0c0407200640300d40c0c41c3c442c4c045000b01c02c52152501c210450002481003c2c100b11065400d400300c8074412109040c10400840c00c4e68521010f010700c91030140e031019012025000784c0c401c0c0e0740c110021100315030200a011002da5030000b0310f540c1020903814150f02c00f980c0803280c40050220000741c540c040c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 667418687 1250 667417437 667417459
    0x513090501330903020907050c010207110108010f0e160908011a010311160f02060c0706050403200f0409140d020c0901060c080703050a0e09130201080c1c09020301060302 75
    0xc00040044403075503a0034211141c01420000b08042d0000d5459516001820034070782440103060038202c00d604485641800c030f080040189015003680d100ad04e0444001124814404403542c01c24011405032422804a03020282418002c03611082d004000c4181d000014040b00006801240050b024001c00380090100004041010240400402e6081d000a2030042000410714140c03060380c1d84101c00398601c134440c001584500d44040e0340c0840590340400c0403c4056002082042058002d0040703848450301c0300c0c030703500300201250002d1100d0b1044a50b14400e400c00750b61030b140800e21007481102d0000c0c1251f080d04000c036000c1201c521440d040e01c0781d4560010502c0d0001840c03c818607040320106c81030b03a00e6810448409149c19401491020184001d0b00003a01400c05441c420b002c82c43c080790741c0f160003000079070b90500c01d03245031260101440140065580c0326000a92101a05200300c1c644040030384a0140040240c181c099210342e1982c8090440da02900213000035a00200146804 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 667419937 1250 667418687 667418699
    0x30f0d151502060f101202040f020304050f0f1f150314010b1504060206061c0b0408070629040f020403020d0318090606020c21060c19030612030513090501 68
    0x100c003030803070700005880780341d002072203c0c4000c0d00120b1264941014450a00e032404141000a0001203401c80e13010751074415500154074140701862280340900700401041c807411440c20b0800c2c0002207000b1254010340800c2055000903101e001811502c4400050b0f94648401c100c0d81038006c1b81c00040111010301d0003800341400541020075503070003caa81c00f9255003540341990042c800c610a640140e0413141c0081d0b1245080340618442c6202c80301e141502e6051036450080020341200e0845580c40e0115455080c400d9134800e0154000303417801180c5280c0c1704c52420504141c01d0150703451003151901e421810591091b01510019580035100764605200d03458043d000c82070162034901c4044800c1070010700f1035158001ca100b11442600603114008c0f2400502c404042c0c1005010003c0781e80306c1d00003d165a042022600c5040000051a25070180f038120962100d8800e40403020941003800510106141c00000c0c0c1901c0c1e4941030040da030360646040e520703c100d0554040d40000d41f81000020399 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 667421187 1250 667419937 667419959
    0x108010b0a090212011a0c10020a080603030918100803030901020c010e0601210807021e1003201809070215070c0b060d0303020c03130302180108030f0d15 68
    0x8018085910601d803039210039400c001c90049071985160030103044010000b8805c1c441c0088a00c0384001300c460310f00300343c0c0300f180d42c40c1020701a0607002c0707180e00255000d10300d030340982c8480e0019011009186811003641c005860035a140011301900c900301004210440c0144c40c0c000000d1001d40140c0383c8a10f00950403d000390401c04844015508140c1302c80701504001c18028142d614808520141d2080480307104102d603580c2d00c1c1211015170400c049000b41ea120382200107a031221034110300070110f010081c00000c00001d80c0c1f040516050803492a50440921030b08200241d1725501c42d600c5089480c40c400e10800c0402c21190028000c00030300c40c00a6001c1400540003034210b0902a180d10344031411502401d00a402030b00e2590f240010405500d401291002c1c034900070f280242c2414190304903282158010340400c02000100d06080003107081540254440b500319207003080300c5624220b01180c0b01c1c0720308508101c0100c0002000b110026690740021904d032201c1301640c030304544660314050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 667422437 1250 667421187 667421201
    0x90e100507050c010e1e010905151e2806120602130f0f060801140f060d140a020c0c060906091003140a05041509020a060c05072312030a05161406010801 67
    0x21002006e1000d00d0140e005014091700035a214000b807100f41e80e05908001d40b950040c001d0000c4456a0081101000c2c0284070580201c08001729004440c0d80c011803096080c0082141900c2141043c00c1000424410420303021590f07002140940d6440490b03409a0311010641c10801c207000d0400d4010400000b049141d20540b80039454004440c0d88541003003080c540c644a15a902c0402e62000d40c03480d0034504058510f0104040d40400c00150807800da40c811035003119401c0d41c1c1540400c0481003002e04002c4600e02c01d005030361451810103d0800326086100344881940110b40d6000c0c00c0300407a11030380c000343e0700300780d80c400030340c25400c2900700b91003d010700f03031400e5407400108505082090050312a0101040d402400705800c1481c00005031a08244404242c489010b03003480020840400f244200b070100e0000c2a9100001d68501000741da400e050070648810317401032100c8045160003100300d600d2502c180e02020310300c08403440c0c140724010400007070101b83e002d01c0d400010b0348281504211 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 667423687 1250 667422437 667422463
    0x301080609030c07051201022a15010e2802040e0f24040c2a060e0d050301090203060a090905060402030105071814211501090e100507050c010e 63
    0x502030740c54004100381d40b4010192800100e80045408100d145008a000c110011000002504184800e81e054840200c030072581c4c80c100d0440414160512824002e40c05c4441560011481e507504203c0444140782c00142070300c0704620204003000d1020754642134000030b0070206405660310703a120840144030442c142c40c08104410004d0115004190f0345601342c40d101d0400d142a1010f01c0c0b01402c00001e0b040c01202081800003001902400e003188118080d0165054401161481c681d032501e5003c0b6043c2c22a803080c01e130010011051880d61110459046450740000503840e5218500003d0b0750501980c00000201d141c40440001c10402141c00d502c1940200c00070482c80c2d4800d1425142001d40b2004100c40d080741000134007400381044520781c11060050300c401c80381c20070032134403c448860034406615260711250300e14540a100582e542e0140645000c10310191900902c1241e0750304611405911403a11000040c040501c01c40613a50704510500080c0070907181c0d10005074032000040510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 667424937 1250 667423687 667423693
    0x70209060a03030e0f0a120f0210030b090a09060b180f010501030614040f20030103120201090c060804110a0b070b06100503040f11060a03050106030507020d0f12090206040b030108 79
    0x18045141080c0410202c1e60540c54811040000c90100b01240d440d01c6201980124052000310340d1080c82800101000d200d400709a2078400d041c01005071a182552403075003014140000101d0a032120400b15411250719400419207401510303040c0090f108072002a600b10800041c03a46d1200d4141e6261401903084101455040e40c03100c004400b0740b41d050086c03c10f82040403c0790083c0342003e034801100d1198000c0c0010748020441280b4440b9401d490780030f0384044021005006004049048901100e26400208100c031116503c01d840013046109213000d10101900180600440c0c1a0781c0034440740c000c060807243e03600c03100d070303403580e5081220140d62410b0344900180143c146480703d103540350250348131903007556126a00d104642005140440d488210401503c2c01134480c1f2000d407040460945003c40c896050105c001d088800c002c00400440d0700c41e65484583e00d801200c180103050252508191100072078803100042c10700c1480094200000041c00548544c08801540c165283d900a07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 667426187 1250 667424937 667424941
    0x130b070903031107050618030a150207021801180c031d01150504050606040902090d1401020415020c0a060e030c030718050112050606130e1005090d09030c1a0708030705070209 77
    0x440c3c0e20942030184580151313040000070f150a0282d0640007640070000c3c02c592080c0241d6440d203cac10649041443c0116030041240403c62410b0800c003080d101d9003e40c601210340c504030005400300d400900da401010741d2036184007242031081e000700c00601d00c0c2c1ca900c00400c2d04010040c5000b01411442d400003004804000724540c81c103805190f0142d071006000c1d0341054146103415000317510200340c40340e10a0b0802d47d41e5000a5240c4000c4e0341c040d41d00000141c07600d1528005807118642030341c04070219013001d46524210360f0341036150800d5883d140752400e501d200d800080380c61302e40d429001541c1440360f03800000703104103005c03403562154041540510199076600c9100c3c0100840384001481da800c6400081ca07141000c0f00c078511841079440c804500320030030301d802c1414004002082580d89484900f088032050003000484480052440d1104505c0c1ca1078030f90200e0741d0650b0280c15180c440b82100700ca008503651081d9a040354100012550b40d050403c0050300303940c44454200d02030404140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 667427437 1250 667426187 667426217
    0xb100806070809100b011d03010b0a0e0a0b060408030d0506030f030d02073f140313050c090606071410110307110106031a060a1502030405010e1e09130b07090303 71
    0x3076918500e106840e440c880c0d987c0382d110083d00e1001c600d601c130707055035a0b0000d50340e0596640c5450401000c64803211203403814650240d0017540c01500b812030084d40108810003140e50008201c6045003003a07500040c0799150000087d003802c04100d120b40d0303544800b0500c0c00800200780c0c000e028513485500c0300c00008103200001040c205445150300c12503c0703810440f0700301c0c441d0b001024481d048030745811800d2031003029000b8503540094500d1102d04080141900c1005410000142c580400f281c00c01014500000022650721900c08014400c0c080784110b413203c8902000300c1c030101d14104409000f11699815100c4441d00b04854201c00268600d5a41c1c131010300600c2200140c85d04103a02101c940311401600e241924040c10310354000103040d1001594031300c080c15a4001503401e0f0b020b1582d503072428000422264400e40540d2240042a007086125042121500001034046e128881166526600c0c403540e8048000007030071540b0702d50f0801150070f900c4400301c01034030b103c2d8440d01d0107910110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 667428687 1250 667427437 667427441
    0x160b090c0a0909020135101503060506030a0c0309051209150310090e1c020616080f15150d1d031e0d020403020a0306060302091803070b10080607080910 67
    0x500041d01003400341c14003d0046c034011012a00311200c00f0207440d2040c10f510904100c074041294003003015800420f0502080024200004101e40d26240a1041c503003064005500d1344406446030040b156103204007512140a50001405a80c01c40180d5150f03460081c40c1030403035406103819620408a212101d8000c1d05400166405002c011640840c51824440048002d01d0f038098a10340c01c0c03041151a00c01961203c2c10506003050b02e074050103017401c0902c00e43c0e09185200c0d00300001e10500300200010320f210014031a5100c20600c10640d840c2114001080000c04200c250401c510350001c3c2104c212801c54020030303265400c20100c2ca10000300d425405469008107521800c604881c5c090001d0780d10344600151150610700785c80145000c2d600e0b40041d42000559004a4a80d41c80d13041c1041546403000d1800d03800704100d010000b2901c100c2c4845c580b01d00c10000014880001e031350120b00c080001c5041400642514821501e8a003450b4201400e8001b04031040c840a2040e03094a6035401014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 667429937 1250 667428687 667428701
    0xf0301110705061b1c06050607030c0c06020a200114030f01081c0c0f0c050a17060705070201050d02071e080d0e0c150705010e0601170f0105010f030602160b090c0a09 73
    0x10340911030404d20398250051052841c01030b848100741d164180447c045d650f402c01010075034807a40b50451110410703c0d001208000302da0124055400181d41a8041103d85d02c550198162007211200a44c40540c01616281e012200d5100074000200401200c0200d0740c950301c2c1684e00c410200c8031000300500c511100c00145000790000034004525040c0095030803103a1149580c803441d03188124648031404140b2b40d145603448217030600429050511000c90500900390440c0003271420702d25200407500060002d118084010902c0b50b40050801c080c400000c0c45104940c1e0800718843d40000b039410110700a42100d4805000a4a015107001c0d80d030b0800901041e0103900900300842c1441901d01111203900700d0541075500d03540b205000804d14106000c80c40c0a030909511004400d410115058900301b4030b0b508030f041580c0340000522140341c2c61680780c3c044940c805800760380d0314200c020001c0c125400d00c0700204000180014080ca18034003081c0d034080b810064496014280d624000481502c02e9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 667431187 1250 667429937 667429981
    0x8070e0f06280509071211092808010207060207021309120e180f040b011e0e0613110a030f02190f1815030501060201290f030111070506 60
    0xc0e01032800441441c104246450300c000d20b1002041c0c1d50300c00100362498022a00e040c00100007080d2021219214400c003645419a88441802c01222001060000b21191184413600000d80004100c6115018490016042d01c0d00295165120b510b452030203500200800c07440345114441c10500385440e4428900d000341c2007c2500e2400b050850f00b61030681c000070f003168202d07810742c3d01010000c1d50803586c140140343d011483ea61501c1c01d1708001c00d2841040c0c00000c00b03056071000c070040d40180300c851001039501c14424a81c068071030000181440c40344c00380c0c40d0441c904080c0102d82d4811488041c0c031a00d4a10340f4103010702c0860030000130892045c0c4484168110702c40641800c07084c42021000340091050031f104d0003010405404a0044580c0d41c00b040c0c50038071510301101020b5250040600502081c00240b245454145161032240d865075110302e0311030314a882c10b541c1995003807410f00a840e400f070002c00174085035102c25881a03100720400d44443c880d00d408a18100030101070b4082c1d13515 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 667432437 1250 667431187 667431199
    0x206040f06240e01090e030304050c15040e2503110d020a030b13060303030b0105181302040902040603020c011104030f03120212191a06040306050405011508070e0f06 73
    0x15076a980004040082d10248100ba09a0b808260800807040c1d01020f002d0a400e4a001585001c0c2948103441c20000765616070b4000780203100000d8000651011190750898a03002c0722003002c0b03e1100d40303000702d500507810120010284034601c08406103440c0002640300f1810190010904103038240c4140c02d00e03880c0001e608101035510036041d94054040c0c04282c0c98003140500155000401c04403c078030101d80741c150b45010030420540c15100368112580700303092440c2025562054040340060340801e95016151810101848080d1541103801519903038004648490b01c0d010000c009400c40076020103190300c1c0c951480c002c02c2003501585c3c00c480e4002205071440d6041e81d03084410340348500c800c240c0e480e003c1c400e08800102000906104940c04811000700b0f111120500d403d5070750340303491022a42041c80301c2c00c002c0c0e115501103c059a40180300803e0544031440e1150040100c41240c086052a4440c0803400f400e0120795902100d40c2c816020030304d43c5610745104100755040d10302c070354004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 667433687 1250 667432437 667432463
    0x50904060e1902220b03070210060f050d051218130908031b07050706031a1503130c0801140103020a0b040e0105040e0319051c0603020d1e08161101020604 68
    0x1101d0b0020702014040016283da084101d01d913200301c12030581c00c00301d10203d01008202030194108961549c280b074461042c0021071504031401c50706541d502903d1b01401c41c2d035107654244803080110444400701806075517607030702c82010401c040400d83d041007032060350001d4103094041e41d81e0149006030b641244a85181d40c031811000103402818034240b8544d0306d800e01410000ca902400510000c0c075942e1000718000c0d8001c10010b01401c1c01071000d0348118000803240c00232070403100543e41d218a41480391510110170b4105155001000d5009000640c02c0150340c80030703180d9644a042c100d034800e8030300d00c03140b03620399119160074015409521100f080d0340c3c0041000f442d10360403650782d03d19613005581c580703100f01c070b030801d00921240941004104001002c4c912001007402c2580062010305040040d141117500041d500000c683c1c01a1445142121205d0545988110080c1c2c0303d80c0407440d1980c0d200c42c06514411080000300c00c0d00c4020ba1943c4100c038030350000c2000385c03180e6032120403d0005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 667434937 1250 667433687 667433731
    0x2010605011e0f090b030a0b040615080a0f02070b04120e030f0c060306010504080d2c130e0312041506060c050a0b07020309120f240103141c050904060e 67
    0x6014841403c5041000e465000a040d83c4108001c0d801139030b8000c004104c0010702414002650295400141800d0b00d1800ca060349aa101d0591508100c1034180403880d405400d04d400042e001c0c0b244090065008082440104618801e000034410300d5a12a6201000248101900c0f14480c1102c4050744c4c01074851240030f45824001598080710505025045c541c80c0d032901d500c0c05035a070a4407c0031901d005005c000c140ea165400f00420070350901e003901182080f0300840c0d03940c038642c11070710492070716090110211842031056074103440d482030741d9441614207814007880c0c06c2034120790029180d282c01004180581720b2000c0700042d64100000f41504041d41d9180a0716440082445086000c10f1004601c04e40d50707500e142d50321103600d82c0185800034960800a08151101c6510b10a0045904804aa01503500c03086811281c20400000001005500046c203001c0502c580c6025800c401c0003101c001c0350020058209440c1c2550200840303901d0345603d12400e01c0a40b040264202410150010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 667436187 1250 667434937 667434947
    0x80304030f1416050c03010c0509190911042d0e0a0902040e0c03010e0105090a081c0525030b0303190c020a08010e0d0e0d030c1e050102030702010605011e 68
    0x1c08540c501404005404000c03a11035400c4058100b0b104400b0700a000c041c42800c0100c0700302900114002c00c582054a58060114428200c0d146e0041040c20900c01c1c80a6001c4980002803180b80020b00411004d000090310700c0c1e0003070141c419031400c48444620146440d00e0a44011021f9608012031035051000254181c1001000307600b08030384401c90100140c566014100070240c450004082d02c104420405d820b451404d1000c078540d130b150000f00300344054000f40d031030034090b00581016540c840d03d01c000800d205e100c0c800720b001c0c10701b8070381482001c005c1050030140d0399640d6003880b0050342d1030340d9044040d14481c41d0891380c5070740700340103003144c002d02041c01c60f41c0c1c41c1c054213002c03001d40d5030366000c200313420300e00d62040c96241d5540c80da5000e14401070000c80c4410080e8a0300140c114810000103548444850000d070810034480c100008000e99041c09070500c00c1051002c040b151041c0c50102d003c0d52048030010015420580c000901f0350103002001c1425500e03483c0780c000c04d07404040403a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 667437437 1250 667436187 667436207
    0xd021f080c390703050601080f01090c05060a0c0c12030f05030609040303051e04140f1c20030705070f08160e09030f0d050a060e091510080d050d060b0708030403 71
    0x1120300c030b00c8051a40141003040001c0c002c500c51005030240c4d41c509942d00d800c2c02038803207039100c5507414401154001444520341a0603030714100d481c213407540140c20b01290b8034911544010f01c00b04042101203030201d81d202006440710300c26600c829048000c4c01003180c6d64001990f150703401c02002c40109002900075041942c0c000d0302c20350700303264946807150381c0402100291016a0700e11800209400750303840521001050780d010784000c1034074807400b886000c0c11400c150114410840315032059081d103c1103140d44412911a001225121681828216240c2e2420702c121800012802c10001d411000802c0f101a911a070101c0401014500701001a03005401045075400740002c1000845c00c0c0701104c0904142c6485203800540c0c1d141c518280c2089078010b4200c41107184884040020507400010702808200c40030320104201e4440001b0f550030322155800001307203405001048014158001c01401803110b4082043c81495038805125100384142100030f0a0120200700282c04640200807540d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 667438687 1250 667437437 667437517
    0xe1009050c0a1511031e04050f0a0f1a090d05100e010507020a0305161a0405010507030b15090a0509010909030201050a09080906070c090204091406100219020d021f080c 74
    0x2a243c001c6c581c0440c2c041c1c20a01d83d0025422202140500c5181840172401d5940c0000380c9000341c41604095032809031642c4c41c81030400070302800100c40100c1c07650b1025202460805032000134109014500140c0b40c0e804859031862491516801842c280e03014042e01c2c6c003480703840e0090f00c8040016142240d4540c0f0140c08955001d51001c200d40c000745054501c1660f408444030000b1042c10700e458424203544020740750104150810221080f166240986c08464590544070903950701c40e0440440ca40050980c804e580c048510b100014001032107030030003803103503200758000c10944e510007600c28121014044003903e40c960900c02d00390142003e50041055130b000300440b81c4160b59400c002016031740140c11a450340c94555420510000005065a0b00598111902c2c0c6510000c05402591012201000144108202c52413000e41d01c0d0301311409e0f91142c002e4046010248000781301503607858680700340301c00200b18a0000700b130800447c0659015909142c0a2104c0d51f088101294890074180401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 667439937 1250 667438687 667438693
    0x50913030507210f1e050306120106030602030619120b18100603140303060114030c040503060c070b0f09030706050a020412110f010512040f060e1009050c0a1511 71
    0x2010100d40f20620892014107206848040b48103001c1d401044010304140900601c130303007a1040e1044103058031100d410341d5401e1506684940c1c40b4400248010303001640c401d401d500e40036000c014400c071a001103102c1d50050702e040044100805000312a00f40510409030003061820541c3d00017928001c8007134100702c0804032100800000c0c00c103141060845190300c056282c2c0c1e98020810894000858032510450001a40c00c52400f00b00203460002480300c841d003c1c80c000000140d48070f040d401500c0140a01070120356241c035145507448a0380d4011101134421484090003d40c2100c06c0340d994074407448126001c0e50425030300c1c1d91600003400001d0140030b400e90f000e10002c11440000f075000c159a41c014082040012400000d00c405583c05401c0300d41042400c21180ba610b417598035040303410036031181400546184508205000341003003620381049004480c00590f03407003110b030820302003940100141e41002c00814200084510380d48a2003002c94002441c0001142c0502c0030804200075490903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 667441187 1250 667439937 667439947
    0x2030c0705070b0a080f160c0615060c110a082802100203120906060307060c06090618060f0c0e240c010e0c03070b030f040602040515040504150509130305 68
    0x7840741410541e400802400c6400b00c0d1545449500c1480c25802c007240d030540304011304013000402d80303501c0b402c03544a0602c200140800100310440d0311086107d54051001030595072a81001030058203268415502d15888500ca4a0180f600d81c8040084403040c40080546e01d4594616603220740c6c0070403003040e41c5d0010746110009602d82c00001181048030b07901945e071387c04107001000c0d07074404050030001c2d055004508224094400055100c151034003800c0003108400d4a140030006008140c00040000b400d00410900c1c104901c44405c6620384205000d000d00c03107905411004441030b440b0403200090a00c4412021030601c44182d05150b8005100c01c0a642010042e042c40c0f42d021030000c020301d030f54403030050341c0052060207044000c0320120040e122a80c5020601c40072070102408015a41540c83c0100d0100282e03541118003c04001e0446815415012145071617604184541801030b800c102c4076042541c203a8441da015220024a460840d403a0a8041d196180c4000422002c1c0882080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 667442437 1250 667441187 667441193
    0x3030417040b0d020d0c030b09010504090501020d09060b0114130b07151a0109080708030d0e03130623070c030b070e0306010f050a0f03150903031409100e07051302030c07 75
    0x400122401d460003617038484034061107500b10f503100c050715001c151400001c01803560b02d4404080c110340084070003042d06500c604005009100f02c1508401c642c3c900354a000c00c205e41a0448100343d8000d03207440b50110b410440440306881039042e1001e014040c2d2100b408014940005490380c2030065420420fa10f12a42c9102c0848000c25048800400784080103245503a00511032009800c200010381107907854116240d6403402464440300c555512044080d0140408000380d515203000044c04140c003655401c0007034000307503e000a18440400da001c280d10028035800840340103580c007005404400c1d18588540b601540090014420440010441d0b4441da40420030b40b0701034580d0740d03280c2c410140b60000f040343d040c109500c23610400545007020000324070749000c5075441c545505070100703600342c2520f4210000e00460f00207050345800d02c401e00084c0640001c003020b014001020410404040e22282581d44903244606c0d58088c003080b098401070003598000e10b401501c5652000e06024a540e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 667443687 1250 667442437 667442459
    0x1603060e0709090c030921030902030304181109030a12030f02040801141605070605130609060c0306090614040f0905060c03070e01030c0e0105030711011506090b0c0303041704 77
    0x1885580015082d004140240c41c01881034040b843c0741e0b401e0030011a4000e82c7e8499826070b600303030010241d5800d40744143c0054020f4205c000156402003d40b90345648a405908413101a11070003142645050706106200c080e180440e110014020300620304c1c00c5460783c40e2220825030200c4502010b81380c3c40034100802e4980003801c0500b521100102e505141e10b1150410504024241c3c00020250000c035901d00303400c1412140c200c5d80124002c200c6a40daa40035104002e484103005045615112001051004691004000c0c1580b99010310bd00c56842c003000041e00e0710b5024000703118100003520f41c000e2801794025540c5e0901c0400c0824440c00a4413180d041c01000c60311101655000030401116542c8140c01e0f0440c60002d083c00c0100f0303090554001d0050b92a500d02c14140100003003c200780a0181c01808143c040c1030000384031a130050000c90301b03d28024411080458003034070700030a0116080c0282c440b0761810304011811603903141c0f107848041055014401c2e01d004200004919903040e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 667444937 1250 667443687 667443691
    0x291b060702030408060f0417160f03050d0b09240f1201060515071109180703050d0f080906060402220602061909030c0303020d060e010e04051e061603060e 68
    0x75006503460394940b49000782001001454403071103102820400c0001200c04013044280c5458421894135040340c80b20054428081d02000b800e040250a0707070000b003692113801441e03184034213281802000340c080b05010000d401070f2802c0c4000c40e421006114900d03000085485c82810061a40c036400ba80703c03002c036507240c251903d01e11a41e512850203102d02c1c24071340d030700b85000b44031003030100d01e041130b81e13240c012000440140a6205128410105102c08013404401c45140c1f0508159070b4107a9480c84c14982d20002c045140000c990010000707550030b4010b03100e05100f0507401c8040c00090307030348404100095001e103842800103c032036040808171480c0858940d0240c0340a80007401c1c1410254420322215040280444030301d030a0065540000782e004109a98007a41418096103070a2040080d502501460b0811907405c1c50540001584441006101d400341d4010030540d11240100b02d8a003100441c1211240341d40d92001001c2231b8281039844c648104031015140000d540c5440b2010144035900c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 667446043 1106 667444937 667444951
    0x2d0603060f0901032603090a0813030b090604060f0b0a12021203030901020c010609270804050d060630030806180f06040b01020d09050f0301060e0c070c291b06 70
    0x54ad0410318003540d84007494441d5881c0a0a0883e61100c1c02c440581ea0071b814450f80001266040c850a99181006405402c0003410520500040d18866604a07001403e01c0340e01203250b8024400b550049441c00c002607a50a142004030382910600c1c0c00c041d02052800a02008402c90b0b01c80345008445c6498404c1e494101d5800c0010050050340d010940043c14044201d0400800d0b0f848402941c2513141204941011284184400310301d1104050381048080c06100100c2c2c02540301c16844480144806020710b403044030030004c0182901c0e85080d00145806101840c0740078025805044000e03c0140302c3c1c21401d080013440021144143c40c010381c001c100d02107050300c0070b410a2380900309180241180d4100f00407031889681c8011000d841c0701c01d40b464046030341003a0080e80101032080e451030b9038035080a682072503503d610404000b2174003410019507041c421800d0040e1031107001 = true := by decide +kernel

theorem cover : BRFrame.Cov 667266187 667446043 := by
  have h0 := BRFrame.cov_init 667266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 667266187 ≤ n) (h2 : n < 667446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
