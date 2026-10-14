-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2051
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:32:21.936829+00:00
-- url     : https://prove2.me/submissions/8e815324-63cf-42e8-9f38-7a21d1f26809

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 368705035 ≤ n < 368884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 368706285 1250 368705035 368705053
    0x13090b1015020d0f030e0106080a080309210f030405031306020c120a081b1236010c150905060c04050a08061911091c020906040c05030c0714 62
    0x1455244581600d1030750610280c1401e41490a03a6078001240c00c01000071168004a807040d13120760b01426031004000e0004c6a200e0395038900b0f80c544043c9140c1950751602c000107009016008100c071700002440344040000c0709031214000b040500650740c202c4168400040000c08021007441114240354101c905101002c1d1103010095903030188042503401006075110156400400003070090545500101040c42c2030241c0030480851035140d4074200040c80b64080f0090800d140402811952180c4044102440e20f403c030842c1c91030501c80b0400040240d4050040410399105640000c0140c21542c4000240060442c480083c1111000a40680280c17411310010341607400c0100120b078822100c56a010342c45141680d2910f1064911303070300401d142070880c0500700c2c0507000f0003502c000525400d410000440003146104c8107660789591500c2102e8030020442c81c058508a030440400e440404c40044000400b801d1480090312030345150b10701007080c000300241d030f090307039942c9003400300503101409 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 368707535 1250 368706285 368706301
    0x903030e15031006020c1504050d2306160c020d0b041e0b0f0f0f1609030c0909050d0201020a0c06020708040f0305030c010b041509150e070c110409030c0213090b 71
    0x340c43c1d002c2e40c0b00502902c0702c00380c1e007071030052000b4017403014a40440745070900c0d00c01046681c1c000070380200c0b032840007484883d005401c1300300b0240c203a21403080540460325004248241d0642810001070500410098090240c4c03030312182020351691012a0000d96151030504540a55070100580040100082c511040003a400c06981c00350326620440c1d081c94031400c0f1242480703182110140307c40540c620000c2c00e030003a194041c180c03202c406d0401c18600ca840e03443c0d180003690f59400000d0040d8440020800b008410000010707450340604c021403e29148440041c0215800d0f030b00507003415004108039050240c10000c8a00905209403010400b07076480c600b40d52070384c20807248007072070703501e4003d4070045030526000c1d0007c00e41440f01c003c100c0609080d03a4000401da00c00c01078044240b484804907601400d09555400ac410b1a103449088004030720306a01d4560031940301ca8019818550f15100207a0800c01d42070b81198116802c400120400440c02e00801130000d01800d143d5464051000740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 368708785 1250 368707535 368707561
    0x6120e010c050705151302100c0b1302010f020601060203040611070509070305011706070e090a091b2603180d06061e06050324010306120b0114030d0903030e1503 71
    0x628812016100208a180b8441885c10b008803000354403004c4241e142c900618010880da400ca00c0350f41032517030301c600f0f0700d48407050084001c460546006a46103000d80640d0382002c8605000300e0310388000c003850b6041c400e00a440e400381e44038840900000110080f01041c1c14440c050242c84040c10f03070012841d100390001c0181c030080c8109075066140307544d55080f59102180d61842200e0030784074500c402141d00e05215180ca0010284681a5503511032440054144400072030725080c100768000c181414150404035007014550460907071081e483c84200c242c40080240d0f4412250645024142a0540e005c0b07401800c05000051a5515000d404122404000e42010042020101064071992103840540765448151001c501c208a90000400100080f006058a603030041c5030120f42c079507a0f080d5000740d5802c03040c4103c1c1c10412040060100c03041300e070a80040c040d01200246188580000082c00b240e0a9010140800c12425105c05d0070740c440080c00484800b02c200019920b14002100e01c02c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 368710035 1250 368708785 368708797
    0x60a05040f0b12070308040b09012a0b07020d080402060d020c0303010b03040c0902040b03040204090507080718230708091606020d110c011b11031f0c02070b0406120e010c05 76
    0x11400f0038940d540003092001814005480d48100401d16090816451183c84e400c07540d030040c100305c040440300150014103030203150207520003403018641c480585004c42900d1002010401158001d849116119622040c03180e0000e40545d07050b40e41c0c5c2400104100270384265100c0a01c9403000000001e201009540110312441c001c804000120741c41e028003205901c224440e480701c4090070b0000c1009481e180d030150614510500c00c441c1c427507640d40e0071a81000c2d80b980c0040418001e81c017492800505500414940d40a40700d004c0210b8800c00181002c1c0c8034000c0c1a032400c2008190009400302020885007100041c0c03480e002e0078a555400009545035a0230144030002090354055084042d40007843c2508403005031107407441c81c088100b0810140d40341c0c400c1a02c40200e510f680400ca900c00f4840c0d2081c40300004141129803550152020550f00c45083d41001c550040108204100340c034803e5401b03a82c41850084200c156010480001d000c081c0c10200301d95185c076220314405074000c0b00a0003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 368711285 1250 368710035 368710039
    0x20f0a111e060f06060f0910020a0501060b34030507054809070c02010203071203020403140304031101050a032307030f090809010309081c061d130308060a05040f0b 72
    0x35075103034020700c0031760300449032603042e001e4081c84200f500340f9004a100d4071483e07191044802482032915018259030b441e521820240700d00085c0766541d40403100c41419003050156400d00b0b1040e01d1000100304c00410b482c080d04202c0c010641c101005000d10006042c0703001007000483c1981a0100a6144a03081022100381444840c1e403000c0c181c810041d031286040c005003611802c5e82c3c1c00c0e5040d541c6540c01e580803811400100400c40001300800104441401156401a111811880c1038102021f001d00e02c0d100a0703006002c10030020b8100000345400c417a080c60201e0310354044a40a40280c600c00d4200a004440402c0442035071080c1d402440c42003000380e13803d001d0321021800c240115160b801010344120805c0000176490b50181e008689170300c0c071a8803e0303481c015042d00620528482c0424845003640c40380000c01180c092542150308a02c0e950b0913400007810111203540442c4e1034110000c050001d82400224181d460041e8000105400b800c1801608000340c543e83c014000407031694 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 368712535 1250 368711285 368711311
    0x40902030f0a0b31111b0106080f101a030a05060a15060c17190c2105120a0b03030d05060a0f1a0309100914060a020f0a111e06 56
    0x480d1510300780c2154040d41000298019440a013490003c0707120381d08950001541d515509040c805200b0b00e402450724401e0a085401c249100d51000ca00f9201d49078030070034160f4801c818404009001140c0b02d02841025600040e018041701000500414100d103815807501a114009052080c0420303814421884443d003041400b82407810503420441a014102c00156140c1d240000141400c00706030300e4a28081c2e4940c01c003142d482c4074031409040701c500d071030001d080280f0000c10050710501101e8400c0b035100d4004031000244000905038018125003083c290b08910108aa80d8202e40c003501c7e00c0003020342925600c0d62a49034080103000140c5109000f81840c2c0c10004686050402e05819a011900502c64900341012440103903003010f40340725810b00800ca000c84400c2070710301c50b40100034480c06180745101288245241010780003007845a00c280100105a01c500207002107800c900510b05000a010b00000d1105143c200e01020401d120303441d0000700c00c0303902030024003188a0345071100d0340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 368713785 1250 368712535 368712551
    0x60c08071e05070b0402030703020d1209060203041a130e0c0403200904020d0614010303030504060507030921090e01090e1b0303070f1401141501091d060105040902030f0a 75
    0x101c0420009041001c000601c107200d00d10015582550030750b003040c0010200c074001d5440b40c00151040d4441c0740100e07042c02e502c91000c0e584c240c010348031100525050000d5401c05207090086462561004503040c100c00c0c0000d40d6801400300e01c07804c1d13000741c618117420100d54640f8175640317041c4d54000d0009a9143c402c00015800c1d610356850680d8840002601011040c1c032240d090141000ca582011103242d82c4400c00c0580d2010901c3d003450085000ea6400b04860415007081c4e03040f0390014120400301030800e0903031804141d0f40c106030b101c1295589150122520380520460341907081c1c0e0040180020a00b0000500c030b0003e82005540003098010740d0011a08450700c2c42c10301c110b040100750107800900c103a501203007101c1c480c6201c03940100e0800c20b41c035500034001c90031540440303031400340c0040a4040c4044850140020f1021070300a082c032005d8241070000c0301c40c400d0f0030901d4440c241e1100500007040d6911607002d4400404140c01c05540740d060845000c29204400c4807900301251409100c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 368715035 1250 368713785 368713817
    0x60103021918240e0d05060a151e2304050c07050609060121061d061510080a0b01030b100f02190f0b0601020c060705010e0705010207060f05031003060c0807 69
    0xd0f030295401e10b4994003c4007050481940c4801d03261460726071028403403280c40d021a1007404a54031582c06c40308002414000c0842d08000c3c0f0405800c01c5211004049006945c0000543c5290030340f251040804c009814820900e450780303980f0300880b60014108403d01040c0f00000e0044d00b800c1d0f01c5402503c002d5620000040d54a000c00d01c0740904c04500840c83d4460f07800318a042e9a10746002d4040801c003202801e1034181c001e90041880c4034680d0103541002000c079440d0f00700f00080c800031240c20002d100a418010440200030b0701a2240c43e42c1c5444140b1142e000741c1c4080709240016206c0c1d05044a043d40240041e000504410094000c1020941481c203c1c0304025000a42c00041c0d42c007105069110310022000c000e0a182c10361003411201800c5913521400750611700d214a00205d05018101c03031440c102611039211505550042109200498003c540c180911342c4a04c0d210743c490b034070800d18000301141d560001d88214600503099014552010340b061081003640c603800704400320009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 368716285 1250 368715035 368715059
    0x61509060403061a090423010204060e041d120304140703031403040606050a08030d06050f0a120c0306021201080d09030308062106070f0f08040218060103021918 71
    0x10895000d04200720500008407641e0208940008040080c00303044d0610000c100020700680b429680500300c1b41e4140746a030003110040398070513200360080d42400e00d80800134008a1003000f031a48625240c90509015000160022040c00c42010031a400300060a01d0700c2095402031340d06a400084c0d440880c00c401000044840c2201da05503203900d16000b80704000001c170f42010b403003110003d450f143d0000d050b58032240020054080c4a005d190384031001d00b0414202c9031258040c0c1e00807508001d00c045580d96000c00c440440c1c680c401491540c011900d880500c10f101500010311040c030102e0b400004010b4910f08074180c40d152001c444003041407107001d403504070040c03100a00080d08540020007500f0112180c04001504140c182078007111240100c0c1001301c01c4541e640029140e419a0710560b0344111070042c84105801d20340058105500459034107801c1e41c0d8590055684100400e0150b4070079030488a442d00100401c8584a801e10b100901c15800403000d0750104192a00110355031030481 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 368717535 1250 368716285 368716297
    0x7051c0809120a111908210f15031005040308010501030e150406020a0507050304031209050d151a0414010305100614270703270320010e150615 63
    0xe141d55007410144102140c0e0044041a6145580604101e00b1140700320030303041042e41845020000d840d030f104000d00c2c134030003807441d8500007c843c07140e001c0c40b000452900d00c064011044000c1307540c00c4070400d00400d2810f514034902ca2521441c0104101c14542d0003020103045e11026a8280804601e00b2140c40d2b17240c0342c0f158140d6a5100c15004a0001072542c1c1c0101a01000d03230800a0510080e51a12400c0d500280c0c42178032a20105040086465070060180c0090481202c200c49200050f480381c583ca10b013403031040440c1c0340d03454441448260f41c3e03190320420741070004d00034403002d103000c0c00c1090b1904080c0310444141c0310f1103801d440b0040c030b131740104400d540111102c00106400c280c100012142000350301602da0422410304121703e40384080706488bc04181d1008a480d003280d24015440c40f8803010840217440b00ba041c1840026401142c01c1c26000f0240142200c1c04c041440e1940188a03074280301d180751141c1082c5405504421084500c02d200c02c0b500b100480705084900c1100344114 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 368718785 1250 368717535 368717563
    0x50310050c12090f0d120e0304271401080c0a0e061c02060d0204030c0819020f01050703090f0f03050606121504050102130924030b01120807051c0809 66
    0x344044444154848607569000c903c61040300c000c0e54480000a003003100c0e041002000408a803040c007100f201c64002c800071034406000540c0b0309407400ca250014000c9880c6030a015030504c408510035040b5542010515100020104149580d249d904a40c5c80c0c206528a900483c0d01c0840014044a0b21610303901c13409014054002490f28081400f02c403070310929080ba03004005100240c4082c0d0075101420246104009103266542482c501c186032504a43c2008056001c0d5983c080060701c840c07444c0080d00c00300f8281140ca54510b4a4162541951034010248060300d172000003076195a00d48030701f03048034090020b03100d60791225810b001d41440d40e054594600e602052035030300c4c48482420b44e9980903010310001420410000310f44181d0018070340c0400703951501d400e40c3c0400314a00501803030140c4031092200340018599507881c44050700512034501d0f08078203550070381d0a001d84038080b9140181d20405a5130618110300781e03454400440a1507a0002d0b1003000040c4c105540003031840030105030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 368720035 1250 368718785 368718787
    0x22109011104120f0807050a031103070c1401050910021606050306030d05031b13030c0605120613060306020c07090e0a0308040609080d0e0f010c020d120c020c1306050310050c 77
    0x2050701c1c4115040b03c0d0481114102010350301040070036150b00143c40c095110314043c1941c08800c0c28020064010b5421140480e0410401400011400c040000444108242c1240342c0b890010043e5030b07500403110b6a641121558090080303450780401c062144120b204503001c0401c1d103410080b145404200c03900c1d07070540d1003041d254a441d401040950743c046020302190340b4613000f01000c2510380d003150848120680740b00c0810300800c2200c036803001c042c1c40715144c100d0404400c8600c0d0243c0c2d000151030a8045c2300c4144c0940000031035508658003551b00701c60b0a650f40c090410015540b10030a01c02d07903e00ca0300d0900c800c161a40045843c141554040d960000c45854503120f000081c100d00300d04075003038601000302c4889000f1501400441c0044030000d0030444044401d02401e4880f80705c8068110f4014511864515811613000c200b21410701d000024501500b602c260b2802c240031034010703030010158040b10500f01a940220301910b90a8054a00c0c981c940140003095403410b481d00b8032500c81c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 368721285 1250 368720035 368720039
    0x51b03040620130909050a0206040b0319090812090c030706050309010c02032d070b24120a080f1b06040c0909080405010c0f0204050c0d18020a060809030d022109011104 74
    0x40c4d540000b0a40e500940940b076118100d40d0004d41c07554010b070700800070204084108400f80702140c040d01d0b940850392106000b10400d070350b0f4145c2c051240103580c2005107844808a4002c6008102910103524090b0499070410744541c0702071b2031900212aa20501c0d802e000401f1003240c8003000380c421a5020520450265200c0c642d2100c22050011400d6a076400901084002c9503c40610a02894001546040c1c5102040d80f142010300704110a9000300e05504440d080317030000140b41d6083c070350041040c9403a9114109064000e00c5492004c00079003080c510080040301001c034646015038840e01c440e00313000399154a54001d50301014400f52560900f40410015540144002c94220748951800368080720319500150448800703403102c28840c840480c3e01446252944252000c0301c165800111b64004140e000408807001805424100880701000c0340030030004006030341c2e420304240415502c80c095030300ca94030040d020141b425141d22503038000c610440010310a076000c0f00c0e80c2e84011842d0038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 368722535 1250 368721285 368721299
    0x1005060a05031c020f0114040203010b040e06011814011508011512020313020a0f090608150c090102150c130b031915120609020f010f02060703051b0304062013 70
    0x1881c80410f11056003d1070030102603a02c000e110b004d114400c2d070440304070795040ca4014503007100c600040071070259150400e2051f4142d00011250304541f01d041d070710540102440b8150000d00380d001d8444044c506800000300c0c040e510103050020182c01591090803030303070b61846489401200d406100002c259141024000c60205400559011049000d40072260b017181d4045900900303164451845841807182c03e000c10103c4e80683c000811080c8024805650003042070030711010042c265507100e030000a640c9205900034482d40892210380000c256103071501c0400800c480e4002c5030b0040560f6102000800c8500c11403003560b000701640740031280d403409030000400041c4090312143c501d00404510000303403038480c550250300c400c1c031580e0b000c640c51000748140031040000c01c40e40d505010110301464001980040c1655000005e40b60205d00c0c0c2d101e500b00b0b415a68071041910000703800000c20002880a81d801c41e0312034130039100c09003280b43e450b0a9058120700410f4901c948104180340100050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 368723785 1250 368722535 368722573
    0x31703072c0613050103061e180b060c0a0b07082203140c0f010e010509060a1e0c0f02060105010f020c01120e010510060801080a0803041e141005060a0503 68
    0x60400440920464241c410000b02d007500000c00d0b10740d016182030b00900041d40d040c0100390080490080c4e600390a0703032100c010044000341b07000e214250010072144070f407517003013540140c1110f0002038400c0740e6480302c2c02c090b10707105c0d28144010780d0791880c030f48041902c1c14810486588038425042c04c030700056140c50070b510850700c2105405d904007c0014103c0d41480c091000500d00c4040c181e006200d0120b20400d03141c00e40d08280c4694490b64501010011900004980d00760700070003203200000c801e80c0d1200c211a41c142860503001038070781307009280290580c019404484030407040e000c54400d44e03a5140112224074190201d48016041001a280e071940560500103070913107540400300d140201c2c0c401141c00c580085440d12510f000c1c01c2e100308070b096007001105001d4440580038000118071502c4807407607444050300c01840052209146090025600d607640300da2030b44802000f08204842c44501c2d90342007480c510108503072800c07000c5400d918208000100b11680600a4401159195145107030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 368725035 1250 368723785 368723837
    0x73005060403091e180b060307021e03071e080d060e010302180910090206040306230f070914061201060509030c01030e0d0305071403010f03110306090c120a020d0501020403170307 79
    0xd02d031b07101c00c004442c954492000c0c40c840d00306035000b004e02d210540b0b41c10b400f0107440c0031b074240703960420407090011590030b0045c032610550003501018006118a00010584580c1c10030300d0160b8600381010540c8814101024100c0340200d40101400e1442c900f6520300907815220310405a0100280d598800e10076013018075a0350000741954106a030701e46440c1c040d02d01c9540426084484452140900c010380c00c0100e030030030410300020319180340000c000b074264041801542c1100c00c0180f04000241d4690049811060040c0d00c0003c0d1560f680f8005441c1d42c2104041e644a8040c0c20a004119440b910a0151640d480e60040c144c81900440a4004110180008003041200c0b20b2800c1c80c68100c4009500a01c5a0303411131400f1850740c100b50745078290340c01816209820040900c1402180011120401a0101e411007209040489407601d480e210500c002e4001e01320030015001d00c14194003800c02c5a0007055030070b510201080044649200444d280740110301c0720000d1b80d0100e1520544d00b00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 368726285 1250 368725035 368725079
    0x812062e0509060d02041a040e01211406011401140906030a09021f020105010509010509042d060b0306070219150915090201020c12073005060403091e 66
    0x21070112850007258295020820080e44135070001000c221080c3c030440d40b090600102d40810b0b05003424009419503013803040c450001d000054802c903440d0940841c04418010b5800b402004061664070f1440e91103110912807044000c44e110b0311408035500440300303042d04ca0200c0400b5403070140d0400810001d034101500110115581758044030050300d17201300ca080964030600d070404c0c441d05d0560000b03083d102e058100c0360041c20f000300100143d4691b16110b84e0002c0c1c0c8040807800c6031702500c031200381041d00001606070106a03a00d0103018028a81e108100c0c030301094003929030b25950720b0816039035004a4a102450000070750498004203209809036048110841c10104188070707c1d1700e51400b10740c1c254500200d1290307501c0d81181103603010000d11100400581e58680c517401c0ca940d440f62103030b0051055200401250411642d003241e1070202600e840420070f1488243c01c490b06003190350340c1c0c040310210089100b210f004a40c601059005220741d010f25400600400c1c1005460200c1e404d038410310070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 368727535 1250 368726285 368726287
    0x50118091a07080114060a05091002010e16050321040b0a11031b0c0108040b0613141f090504170a050d1407020c09040503161403070812062e05 63
    0x115076014a000c64050200350b035548000e54107107021440201100368030305100b490304209000c0015048411341c1d044980484098001c3d81120409038090a00c1800322800e60180f110080207145080c400031040d28002d4084031451290301c8500b0750108400a0305162603c0184000c01082c8e0043c2c00a008902443c80c10b100c9990201c2040e510b181c00c0360901c0d0704100c40f20404414800c01c01c02c881c8911041c03d00c1c0001141c14503443e40e201410025106030b0007181500c804800c540901c2e00100490a2440c1d200304461500c10450303500c2d82d05400103840c105001d08800900490030b4001c1d07900503900080e000010f104c00009016840c2d001240c241d0600c0340c207200342500c00b01140300d01d20300c000c403540c144001860b10940003401d1440140d4071078803c590702c07070a00c004524000180c1e03044600d180034503e0554094100a80014501c403052580b5102c0043c0c0c2c4420040f040c8040d110042000f8000352045e2148010445680480d1085414411f10002c035045421440410744136580d060341402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 368728785 1250 368727535 368727563
    0x2a110f01060f15020f010609090218040201080c0903280c120b0601080a0b0d03090503281209030f05010c020d11150a110a0504030c120c03030302030901180f0507060305011809 77
    0x2d1b420760b07040350b001c000c12030395070144c140640c00d00c00070180e403c1c8407d49251049207003513400603007406409440c007401c004004c181e02645490802950400f08000400403100c1c3c1441819005c07209100d4100f219201a8540c0014610300d100840c0281580d05c1680300565030b42706001141c64220041c0420700d402d44883e10150310744c039182e02440340c1c140680d58101c105810502418a0054180c81308207158070111071620303010340d40300845d424a95100030071941c66502070904662a00a68001900f54145213075041d0800c4015406003240138840c1d0291001c496030307450b0075160782e80344200b80d500130b8123302d1220344e05100c1c04030560780c0304c014101c00007040403490901c03014941190400b00003107107002805000740b000342c0c508500200110150100c40309a00c0d0346400b540801448010141030b0040046401000300303400241d200710740440414200704c42d5052026440b000c42009549600031040042a150b12034016030f03040c0d80580d034a1250b102e04550342c010007010380b81e006441d00b080d00514 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 368730035 1250 368728785 368728813
    0x804020604030c08030a110d0f0c080403050d0804290a09050a1704031a101208070f0c061d0306011a0720090a0b090103062a110f01060f1502 62
    0x1000d005803134600d00840d200e024008014044a40700e500c0b01103142e028001040049600c01d00d070b0590a9200d00d4010710380c49003490017203050300a42c1c00044c61401855a02008607911140d08d611681c01000c01480c0c0d5140c442c0081407018004009016000d100000030b07081c00d0142d000400c417240306500f00d03a080301c81c9407107a014062011809200360b20000504109003c000c90600b0301c0e800c900c840325007550506a40000a00b0703443e102d818001413151803c13100384900074055455040e00b20f0309013050030266140140003000a4000c50010480e1100f25191602c951160b80c4640540540100000e908001c41c0d01103213521549401d107807407401c00010f400514160380f200102c80003441d003103000882e54820800340920082c04a802185003080320314141d6503c0304981d04407a004040020040395420001024040f284414003011780b41d0480d2221a5030300002c900d441201c00341c15501c41802c5010001c0c00d07200c003071003070f070300480385ca82424031101c0030800d901c4124454a00448042494200f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 368731285 1250 368730035 368730053
    0xa02060912010920040605061608130b250b040605060d05100b120a0b0408250b070306090b0a090b0f121f05070f1d120303061e030607080402060403 65
    0x2012070300711000000d521310181003001c00c02d442e0103048405101366414007010403601e01031100105002d00320902420288034100d01203032503281140d100842c0320f5882e012584c016501100784110760024540302c8100c804c1070b441500c4160366100d240e541180d102c03601d03010702801d4040e01c51980000407000c1c480c00558108180c200e5050301039004030782402520100420403400e80701e007400581100522030005200440030941c440e0f808151592120158404a00002d9240300401c5028410a02d20010710145400300391140740241c0c0c0c141b10742519495004166845c007400d0940100080d8000c0c421140950080c09018a018280c804a400c00c240003901e442d8208850ba9400d40180c1c48220352201000010107040031348110911050902c104000c0800440c0c3e4010b0b820000882e82854800c111015450f01c00c100080c84845051401d001d0700e52a03910035a81c8912a008005c402c440c0e120b000380031496658001005400709a8a806050300c401800400481e4890030800000c0001100e9034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 368732535 1250 368731285 368731301
    0x3020d091b0504051e1e010303050c0106140f01080a02090415030501181109130c0f06030501080d02030703051c0903030605011106060a12150507020a020109170a0206091201 76
    0x145049010040000e24a00340500d1904450f01650511042003410054521407006800c0c002c40c02032400c0e80d9902040d03401c4001c04604456060341c4200000505074481d01034250655083c0007000920342d5102d80c00000b030806200c442d00a4070400c03866400b903008020603913101c0e000e00d0000d443c04112800180c102d9400ba5110712005030f01401c2482880004d1280704039015030f6810342c662024031500c1d1003002d4900b210081d4030502c0c8440c00a07035900040d1402c0f4075229440943c20349480d4403a601001d0808041c05005c0000c1e2801c000010b0b607200001744441005040e8019601d4501c554a089940c0c0e8401c0080840b0b81c0c480ca954044e903c03143d445a9440c4500959000445070f0900c000100050104119403203d07602220900400760784092088013140c1c1d07540b4807900310f101545048401034001d55040941c20f842c0404202001e6004505183c641e4400d80c0c5003102e45403581d124000d070121290341d00b030003035200808100060500400800600000403d074002c000806d40c0c016007990408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 368733785 1250 368732535 368732543
    0x40f2a080714090904150e0615030304030804030303020c03040807080703151b0e0f12060103020a0503070807060c03031e0902090c0c0a0b0a0b0901060810090b06070f0303020d09 78
    0x484400014194040e0394290801c500389000d0011051003400e010243c06000c02e014030402134600840c04210142d0031480040c60350741005c1c801c0b07001c40604680c0394142240e40f003107000e8810100343d2061401104a8045c2c0e540300c5802410030b03003191000c4001b900550100401e0b48001c1002044220741044a10000c00e90640113090490541c5403145520919a040d001180d003070919101c1d14158140e944c03542264946003030360b00c110030b420005501400c1d501e92150091760310f503840d00110502191440c141c038029900c884509507582c0a040d9104414802c40525400c90017051064900c200d81080d4071030300914000c1000006528502e410308104816134240540d940b55480031824450740c45980503c00d03101c09400d1034803d4030701c035403140b41a02004004060035000101030781c0142d0300c000d107a154041c040380695a100c4202401c0c0da101620413414903080f007400000c1c40051400b404040c0307500540b81c8c50400629540b03109920304402c4040742415000d11084602d00d2039403098041c600d010b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 368735035 1250 368733785 368733851
    0x71e060213090c021015090218120d230708030127060501020a030315170d02060903090d0201050706140a0b0114040f230a030f030f09080705040f 64
    0x901000080c840341d0a074018500c2d64108202c0071074058000c2400303103404015400103c1c1c001c03d00c0240200e4085207030040c0107a18808501f405500301507010b800401d1000351140542c011b000031040e690744004481040008034000b04060f540c1c0341480000c00d0f81201403510700d003001c5c9507583d0312249800076000104002506400c07466085141d600b98100c682000c3e0f01009030909040000b5110313400640003605054035240203081790401034404030010407180380d1844039050451040c0392100e00140006c0e00511030310300030941506010013212502c800003040c201d40495141d006443c030f0740210b81c055408a5503407659224480b400d80300c0c14860152058000742e1407000b0070026050000c0700c1301c0400015024841072010f07079840e400c00010384175409244010413089500803002d000d04446191b130400203c060004c10400007110707480c0740600c691981001c0a01c080012550001540303d24111a401502c040103076090a80c02000c002012040109800c680d042100c803000605005203c03520300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 368736285 1250 368735035 368735047
    0xf170a1e050c0d021e030708030a03060e0c0309030d05040219031202121804020333042904020a02010906110304060501170706200105040b0402030c041808071e0602 72
    0x200078400724240c0001160410520f03411500410321440c44d003620350582070b4103041800050794040114000400c06179003202e81e1000d06100c0100607003000e1050803e0300040d400480d0fa00400792003034912800b070603001035041c591259000000f42030007800507604050b0410043c100c0c1682440c807200554050510072001000c007040081ca081050b8019214242c014000c0078072580e103440801540da101110003503120385882244c4145a60509181518130007a826529404983c502014103100070444040000618200c11995000e00c260b5141c20400d50320130300d1080341e1900754040c0004141c3c07480006040b12543c0cde034400c1118003405010422000120400c410040e5502549024100540d03141002154a11103160307620002d00664041c01444139442440030002d082c11400c4c480624024090303030400f0304068603800415142640240151400c0001d581807900401440f40d0034280c0400100056071102c5419411503102101c0390004002e8440b10241d0103c51005c0b4240590001aaa40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 368737535 1250 368736285 368736293
    0xa1b0605061f09090509030423010305070504031511090315010e060d02090730090c0803160b060301090506071e0e090406090c0e010b0406030e03040f170a1e 69
    0x5182071028820b031441c20350204a0b294051542c004460f46000040340c039072a01c42c0c9050031405660410b01d00d005050520343d4130741001213503102c40380c80280ca04000744d0303c803800111010311403408042e101030300b114004a5000c070240c1c4204030f1750600500746400c0c03440030350029040406510300154000b00440c018030009940c07034681a00008201d0785040e82d42e0240c0d0208401c01c0000f00042c1c1440f03c0361401d44810000c84200240e07441081c0e1400c20483e180c030481d8401000424419240e00c0c2c2d01200c041449034001003154151040740048101403d002c0d0b907120450223000340100c1e015504c540c02e40c00022001c1001c42d001d4a12504d90f8030b503036900c01060030700000100c106001004070f0356824800503141d28000700d822540000c40883d05030740b01d086ca146884401d41c0300807072844d070743d0b0000030301070b1510406007050311036555081c0149590705801a560b40100e014244a0400b07910741000640008504100036a0280303090b501691115280d80c080a1140c100c0007030560004101d090402c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 368738785 1250 368737535 368737549
    0x12070605150a0e2d0103140d020709020a030f0903022406060306090a0902030a0b1605031510020a0606090618021206060a02011e0e070b030c0d020a1b060506 69
    0xa107900015054035400c400003414a45544511801c0540c15400700d102e408210704030030080206440300c0d88180c24600d000348400042440142c031840e88003c0d44408415020440680154055006200300c034244050748000303510041804051560700c6203030f0243d001c0c1030302541c810607009070068041114540d00c18182c3c00b080038611849042c4040c03c01034182d03a0f030300039260440c90544000d0004d41c1c0308500c0400610315910b003e03504d4030500440e0403c000d44030380306501c85c0380b114040e8086416110b00641c1d80780402d960300c0c40c00c0c8109141000040c01d11003010160094144125071051501d038448a046410980020784180d80b03c8400b0311603280740300d410b011100c8424408610704101502c0d1940b0041c80030340741034410000060b805860910035000070450500c002000300224090b0a0040f0081002051034805809469000145003e200f001d49102d5202c04030f110b89000d030f4262001e0029401a03200000f40721001810001454000c4102c1401501c501400107441c10001c0c100050303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 368740035 1250 368738785 368738791
    0x70503010501172116060902030f0d030b010f08010b0d1b050706060b030105180402030c031014071701060c03050f040803090a0902030c070b040501020d090309090e0307030c0308070e0312070605 85
    0x900c4042103115907513594008203c801125a11600e00c3e0f11326514904403010748841403002e0350501ca141000c0f0075145c0c01141003c1e41c01001e49081200c10a42c1c030054a5150503c0c0c0c0c0031001c0390f02000100b004001c03800080c100c00c4a040400103020700300580d608816455031008000181002c42d00d08200300c454480c80c0c014007800500b00c0d00750b601d404002a00c1040321400d01500d8210000840d0440d01e0402c07107040309c401e00509413400943d5205800005005142c4025401c1c42400041a48540a4806820110014410002160300302a000c1d180c008209101f1010000100605400307880f03010054006014100044c594450f40441006042e215981001c0c1540d84100709200380305015408440c84158011a40141c035034031424110700900850010000482c105100d0904040c0c2c00b102041c291062210b013001101d0244c1141c681e00d009020008020a240304850404039001e10400c40c1c0c080d1a515200b040c0951301d0010a00b44015415024840e00c0041403441c1002801d014103a8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 368741285 1250 368740035 368740063
    0x607020d0807031809050c16030c05010501060302180f03120a05090316090e011a1509090f04020a060801030203100e0c100504141e010f14072d1109060307050301050117 74
    0x481420198108205485018a030987e15900f1239041c00c20140224503000d0a260010002c00182d80c2d5031a0140107503010310314110584000031a000998645111040072402d006401010011000070040444e079100320a46020312000740007000841d278007003126800e001d10102520b20030038601070204058074610020200c299042500140000703c50340c50740384034083c0031034505010307c010100390f2109200f00e100950300304508c0410007403a881a03004441c062842620a8600d03141e450a08032000c40007804003d6140c0c0040000c0c2d03120056981000c004d5106100170769036240100030000760703100b41440510303000c2400030800300001d408158001c25100c2e0161840c1041c0081c00c00c45000515240443e1810b200b084008066118803a0b505003000e18021070b14540d03180240c2c100b203032040d80306252044840c0509410f00010304c800c07c1800b1520f40c0d01c00110003c4161017410400507a0b8010600e076014465100001400d55003400f4180c000d040582d0040d138500300c4011014100a800c040501d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 368742535 1250 368741285 368741291
    0x22150911030d0c120513080c0315041218050d03020a03031a0102060621100b030d0c03080a05040602161109060f060703030209030709020703050c0610050f0607020d0807031809 77
    0x1080641d0030601034250954041000182c8108011041e40e0311b004e554a00c030180000450b0218070303184005443d40c4110421421500070981d1b0000e007c548020444004003462002e20503440c407240603a141301c0c00b402e07000048244103901e41e80072502880b0844001d80c0182c0c0200720341c0060640602c42c1441c0450b400c84100c02c0e031813107540080e5403180060403a602074038003450559404207000e01c1d01010044084244d44d85101e4541221002c0c01040c40e4161003402450007400d00240a14440c420841d895110712619940f00384010300280801030050303c04903020890b40c441d02c580c104e213199200381f0810450070504040c1050014400e8014222030044248a4915696a9521003521295075062802680d11040320340403d080070040e0744179044032400031480c40101340d08a4081c1108001c031800701c030032a80d40c201444d581d4405612a4036082040c102c1035401c075003003060080846500180410043c90001e580d10a07441d400824194002082d00d0490001411580008001800d0303152081c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 368743785 1250 368742535 368742553
    0x516081b070b04110d050d020d0306050d030513150c051009051e07080303100e0907030312020f1c060f0e19090f05070308040611152215091103 63
    0x803001921400703501408488100c0c00103020804200b4000302c4110015290b011006000d18125079180d0907503034040050300480d484411024802e114035421a20000c1c12002c100500e074500351340c581c2c8911800b5080390480c40d008103001d90841d685c5100d010f5540d9900403144041e0900d01d061030484000420024100b01326680442d40001e0368070341a506c00c0401400380c580310002c4c10b2a0803440d40c04424140808420081ca000c1881d420301d04030382d0b0500b918034150362002d00701911000c3c81d0000a003c181015006181541554041c100d2580500c40a5142610317000e80c2e800282c000318501014140c88d24401d001c0d00c520903056000034245590005100e00303040741d01120345680000c1486180396182c1c002e609000c00307041040415030304101a10b0041d0749a082c00c80d25035000e4061000414581c1c00780601c224000603040d641c07034a01611205030754843c64442000e44501181481c1c2641800c10b480001c11001c603000818180c0350740c00000d42c000c00385041611010343e2900c41e84031390400c03c0c507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 368745035 1250 368743785 368743831
    0xe04030512010618080c06040303050c150c0d0e2b05040801060803040501021528020712080106030501120818030a15060f0611300a02060114030d05180103020d051608 73
    0x48d10142c0364541840307915010880d404a01c0d00505601070310030180c6550912640c114840001c1454406185082c00400310f5141443d64036001c1102d50078010603030100a46880714280c00c4460700c034025160140c07070150b40744582400c0d0381d02900700c0c3d90b558100080c02c2085680400c200700000c180544041d40710328100000001d24818803042503034520900550000301c1c40b181c2d044480007644070f03003100c00f861903c1c0001450603000f401000d01092811001142c51900304031101c0d84180c1c88031103545400d04c00850b05014040164200e40c144c8a4084c40000082c22243c503122200d801e4040010b032549010010a60407074294022402d000340c0d5502e00b00c002c00e02241001c1c20900030301a1031001042600c10f6510001c4500e400b1400010120300b01c0045030740401e01d54126555103c402000c1308032001056202c002078958000851803c010050120024120940c2005014100181080c100300c02910a503402102c0f44000d9407a080000d800d5190040945034011005c1c1000c0005c1a040140c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 368746285 1250 368745035 368745037
    0x601050a0e0406050612090706020303091b0d0f0f030e0411180f12030909011a0301050907141b0f010606021911040608030903060c03040c0e04030512010618080c06 72
    0x40c419003040004881990180c40b50341045004001c0a800d556175810480e50710b846150b000e940a42e054081c9250008429100000781c90090b4045005000f050450404030440d8480b81c07010250080340c80744801010900360700035030715418054160780880d1348680c44c0042c4003542142c81c0310310070761030140c0e01c40452b04c165003910a02d4901a02d4040c080301c658001544409200313240c00d074411111103040300d87d598080058611080182c88601481e40c0720340c485000060103851010755014180010401847d049411a40040042c02c1c95010021030f440c405000350300108581400c03031840c03844c030840c040c010061408000e0b030f910000c210050810308000e4a811524841d0448075015008010038030142d0350454600900c01401040300b6507032005101d4694010150350751290040d2000200d0400b51041100e1107250b00c03001c0018000d05103507006d5403034180a0001d40030000107014a190290186d1002e034060181d035294945080d42c0918044144400743d0030501c0c1d00c4e0440000c452a82c0c6a500c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 368747535 1250 368746285 368746297
    0xc080103020907110a080d110f09040b1c120f2c27010807060809120a050c01090f1403040303021c02160905040b0f0f19020c0718050a05060105 63
    0x441c10039090f21205012900c0e41e00881001c1903a026100030b031420440004001c041c0207200c0001071100c01c12852400481e03000d01130b41d03103214000422140c0000d241c00d50044600b0301c00200401e08500001c041850360000da0101120074490840e41c0520694100840c65491041860405555468022a5480c1034000381210490114100c0148000d2f5951104103d5015445a00303800030350170804403a404175800c0c0308144280c0207079000440c0691240b41a00d11820007040284403442c540e162818196100184000400c2414001c0300e508020070302589190728001c2c514200d0310021070424424044210815400e40c1d4001c00042001a4010a4080700495a10b00021040300c801900742d080c45400c6250418980c42c0d41c40104115000381d10442c041da0198924010355910000e482d50628401d45a002003841004001000c0c2c61140c003811245508881015003450342282105187c48150340004510294550764105400094441c442d44101145001e108a090003c00686144110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 368748785 1250 368747535 368747539
    0xb07020907020708030a021507030c140c01060f0e040303050609091917040303090f0f140618100e0f030109030e0d06060b030112120c020102060a090203010b040c03020304150c08010302 81
    0x314000901842c0280240c400520b0b44000b070b290388003413036400203480ea09110f00070384c04c2c804d240000c00c00c40c0d0301c6880b50501000740c07901ca614103000c1f01c20850300d0580184005103440e42d00c610020400440352030880005010011200c0c04504161502406489004000c5406400c5060804c044004000380030f000b06203a00c0794148280c02c403400c5c04410b0800d4261500c40d4200005000001c0603801054442240c40c081c401002090300c0b035003c0309102e6001d108a0502c203421105200c080d10344a0010105040c01d0110f0f07500f04040140440c46912840c0f800a0110310381900800c003a04022481072403004044000304000707880c1c4d9030b002c0e0420000c45036150090003615000020018558011006040c04045a030344a6139580d07081c81d44400006030071038400400d464000300c1c0c82d0152005105c2594160050b00441e641c8000c2c0348000c1250580580c0d1540d2202c06118581d00d80f0b1140a8151002e560b01503960f1400b400d0001c040c5c50b200c40c0b41241c65151800d0000041c2d070181c82d0301e041d1307541 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 368750035 1250 368748785 368748799
    0x90c090c0f0909040506061c2d0f150b04060f0b0a02030c010f0b120a0c061101060f0f090e0304030506010603050c0c01142703031b130303081e010b0702 67
    0x6041d18100c1a0152500d1160008401c030240421301c00d0001d0340510507001100e0300c0941460101141c2c0001d01409030042500d41e00101140301002240c6070f0701ca800302180c03547c540d007115544a4084010ba0131009581e000e005040701c220441150040e840e200c6002c0d6014401d040c9071a07188151b031104c2e4460041e0100000ca660f100b41442402141e0032a00904020f1103030603240d5070440000c0c1940540c00d4450b09120103111003891010035017200040c2c01080d07000c2030a01d030120991380c03c0c8091080304519540c0701004200302c00c03d440014080c0240ca0310b000081810000c12400f03c598034032a40b40f03141d20038001080000c100250480c15928a4500462a80c4880d07082c0d148902601c80c1c8802d080d4280b1061000010030320700d106219425200c040c000400ca081407002a01d400d0520303026182d08100001100d0074003000c400111641d5102055240140c411801c4403a90884d401c01c8000501c1601804001c0350100305500101e411602800841e516114040388980b0034081e000b402150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 368751285 1250 368750035 368750047
    0x3030711180c0c0d0f021902011b0c181b0507031701060f0314160c02030708031224060403150b09150307080c0a0303050711040603120206090c090c 65
    0x440000d642000129121581c074103051506041c0c0d40c03074101e0318480c1418854403020101d080e1081900d14a03084460b00603160f1580983d05220795101a08000d0341840900d100056201030380b0f40b14075002038010003000ba0301d642408203095900c444004104645401c0c1540014001e4074183c0c000307a04809030030040e54030f403001e02d42a01c10b40c40506139502d8000c2e501c0c0002030455001400401111855541000306498800030031203003d070306980111801d01900040403c560003131f58291100d500040440d16195561241c0914641c841c20302410b1042c55081031002c0d140d091066103070107030482c2c2130f4150001a0440401d109000700c0c0720107864641e000d154102002c40c160f21440b01400060000c1d405490007406420010f074468403041d0191080d20760000d40144041004404a031004280524403841c0d134404580981080000361610750b50100740724481c1e076441c4200402140301d2203400800407410140642403100080000005420114844646a4030240050b6111601031005a1901c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 368752535 1250 368751285 368751289
    0x20609190312052106061903111b010c0305090d0c05010b03030307110609030315011b0c080c12010e0304090c18030b01030c0b0c0d1b02090c0301050a05010906020a060c030e0312010f120203030711 86
    0x81405001407543d10001c1c0d102e003072b10400458007600c0403607000240700064001e8411021144101d40c01c51098104616441215100706a0503161900030300011078101e10302000030341554030558034403001c1114080c84e004854010300c070159100503900c018504501d008240207020103020316600e8100034095070311100d8a40e40c00d051801841e000f07020186c0705919031121990b00d902d0400114418000303007603100050041401240759078a41c8030051402c091410405c00d000c3c22640000800b484500d02044128460040c0100300035805820215202c0d495801d2401420b240780e0080b085a4034200020b20380204005041e00700c6040c14604013540b201507044030103611a0703c43c0000c0d440b001100500c101d8210040c0a0340c10ba520841c3e21030b8200c1e0f5141b0041d031b400f1280c1e01c40c640240c0c00001003100828801e910030311100005040100b4000c00000038541035038040703411007003000d08d42d20040c442b02100c3c0034113001038829901005241030ba1a00001d6890164a000405040c0c600315401465 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 368753785 1250 368752535 368752541
    0x6070c090b061204030206060f0609010905040f0e030c150a06050f010c14030f041401030c0906080c0d1b17010b090607080f0c03040602120403020609190312052106061903 75
    0x206403c500c0c40a003010710303000392104000e981c034a00c04c2d006c1d840096042c0c40c1400485101c808142c680c48030f8030b80382c0300030b000143c42c0240346101090340d1659030000003502800101045150301004d09003c0004005000b010309000d0700c09a41540b80c140c0601003070303c80c0e104442005409003400310301c0d41d030546850b802840700900031102d2030102003615000400200040c105560444400701c2e07046400c0c0004408582021b041100080d060078000c2003514010707004140c201461940d5207141080c07018894007a110046021201c40740e4843d90b8081740c9600590340d00d1607281000c0c50100951610103501e641d402a280d80704e120308800102c0c441004009003c94a0140d43d2005030b6031580320114041c1d40301e420612500c4003600a01c44480c000d44101000c440959a0041200d400c05000500b40702c0300f68034142000034070f00c2500d04084003280341f400270034890350110b5881590f28480c4d03d88050013902880c842c100d04035540f8003480025030740d0741c090743d45031003410160250901c08c0400c12805 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 368755035 1250 368753785 368753797
    0x71502040f050f0402031023090f0f0a060501091403030702091003030215010b030a020a05092d031f0b0a0b030703150602061015020106090617060606070c090b06 71
    0x4288005000900640803881c101c089880c1191640c4514002e0030500c002d0348403c55000c4105045020140100f6003440220f514038403561111503290340030407000c0b84003c2401e890004440711074000700402e03e620300c10f000b68400440300c414050b907440c1c10006011380b18503004400241401009640c4c0d1a2810010781e0410b40c0c008098942c50304007960501030b0030115000c260010b02030042c507460015101c011050482c2e050b400c0d110301c1c5035646a0108025000400303450f0030410200100f61382d0f50754815810308910007180c0501740340d8034281c43d100c45c41451241898000d400480d821102c03840c581001d0f501c50007010341c010039000100f200003020000680c005502040002c028848099803540c4015405500108000c60290b1a000c040c2e075500c000302c880c54403c80c1d40f80c400340000001c000c02400d0104040c0000b050301521f50072241d09541458004002c000c0c070380c00d0b055110000802032281c1100003951443e14044d03198850303080b08102402480c26098640c034503025151609812980 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 368756285 1250 368755035 368755073
    0x108060d050102130302190f03030503060a030b0907090c141209070308032d130f03020c061606110f040e04150905011506090807091508010207150c050f090607 70
    0x15550038134054080160105020070b901644412009880f00e02c25001200e054991a8005444003851654101c90603800200100d80040c04504000001440c011540e802105004060107400d0706120301181240e040b000a1010000150f00814406900f81c040300c00300500f504100c855a5641e00d4200e1628220380d0006080700000800c03c14040419040c144094500d004404540d01900151a80c10307041610000711480b6402103900c000313030204007c0407440e8880d0040d04d12000400e40004c010360443c001ea0b4541c1002c0050060811003a8481c0c404241004843c581c1041071501140056020f03d01a0300845049500403c0501101068900070840036607400d01c0a0314103450003502a1010410b14000f618680c10003046403801640040113464112000740301a034a08000f50b070151222026020701c81596003000324201c01c0c01e000902c5928002c095845200c035001031603800322280906010708000090044803a186814022102400c0013151f219444203410b003000c0890310a11a140a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 368757535 1250 368756285 368756287
    0xc180d05071d1005040605060409050a0e013b3403030c06150b0f0a0c02030d03060e09010509032704060e070f08040807140a080c16090e0604020108060d050102 70
    0x702c07071041c1201c00500c503003481d55040340000da4481c00c1c0020b0f40e1280c040c45070300c010144400e000b250402c0d40815844402940c01140128090740b940b4210303040d411000703210b10781d1010303100c007c0f058055822202481c1d0301c20014400b01c1841c0803e461b0558102c0350410307d540320642c12842c03001d25940d5454030070172034814180b880e540d02c0d0240440072140e0044400c00c0c10316420100e08428070400e0b030121181903404518040b00a1000700d11548200e0400051105003500c06d8050b840030404070f21050410784001030f1035401c281c100d0391621401480600503a041c242040002e400110645085101038840b890340032502088096510000c401c1107074110703140110000300001d402094a01900f1151540701540208030402c8403550342c22036000d0420342003085000c000580100300e4503d10103103101070743c01101c1207a44070580c543c004071462602d070f4484d019025840c1c1e64104908000c040885003004091300044205441d108000c2c001707814030150b94002245510f035802e1502925030701000031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 368758785 1250 368757535 368757569
    0x51513050d090f0503030319050606040f0810140103050307030f0e0324070e0916092606010b0c1c030e0109051617060115020c09040f0b0c180d0507 65
    0x500b00300a5100d404000c01d0b004400180f1801d000c03085078020030f815101d00020301145200700340580009440d071504807038108400103180903040c956401614101008e0803a010f04810a075059990110b81d014580100c1c80c010400038500008449520780d0500b080c180c4240083c8080e980131102501c00741d0140200d844013542480c2400360184048018604410542c40b103490480b41c0c0c2d5504088640c0100b507203804104240301c80030043e039450010386046624503031038440b2010380c641c5054590020400c0410b03518521035042c803a00307000d00030b07085407503003800c0008900a5452080d21005d41d0300122001d04c0009107440398020000b0441010000e00c1f910b0303814980155204030400e032090400f41030300d1012801d81074611280300102e804030001c042c40c1c1d080c084032148141c080100b802c25442503084a103100d0711006c100b6486903000d2403000610040d80c3c10450040c8200814940940c80b04000c400c03281841403038138003910345081d035507141c0e486110f1400c04c1c80c00d4016044044014844224 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 368760035 1250 368758785 368758787
    0x110115080d0f0201020a05090609060d0908030103050705030607080a090515010f08150c07031107090504080426062205070803090a0602031204150209040c02030c19051513050d 77
    0x380140c40030081da01c82d18140380c403000072402c034040d070148800000d0302000a940300307140150190414038001007910b860b12600440d414201c8030518401c070b036601c1020004106010091040c04018501980a082c10b440c0921006116901c02411904d8080e41ea400c0c903020b002d400c116000380caa1424821500c1943c550401e4840043c1c0c51040035a18801c101003880e002c0c03443c0104501070105000c0030350902883e554207684080e0349403801d0746a8401d0580c00108500107005550040340208103083d690303030401d0440c051401c0c41ca404d2050351040d0903040c4140c04d40005200b9070110840c100c41a5050b160406500320014900380074100f446440c00115007040088020808400103d400700c9a69030748000690302c0e4050303880380c14481c044d20400103001c03070f0300300c0800c900d001881e06c00149171145204c0010102c0f800441c5110059102095950602100300308000340c054003000c001190030200c0d51070b03640d20090040c805501303a04200c00320700103104815040c080541e1104c16284041c0040b032b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 368761285 1250 368760035 368760043
    0xb03150916030312060603110415020312040c0303090501081306050711100506100207080a0308060f040f06030615051e01020a08072004090803070804020609040e01090b091c11011508 80
    0x440c4d410034500c1d0800001d01d6034002e1207005002d0109aa020381003515208000c0b00102d600300408003540000c120406000c5603075604184150710407614007400d1429801c1c002c00f500a01c1d0042410700060405010006001200c1c0c04031103648500f003c0745c90b50b6200d50442e8040c10300d192502440c4500d054501d020f0406130010b6100f000305a5411950a1110340100e03a620164400c0e4a181d0300702060000121f0320070021281d0080001c8d054000c40807220011030103d41002201e0750855a40d00c8081c401c010060207070300b904a0040c191608014180b000203009145a210030700886401c240095150380d00074403501a003107401800b01a01d480c086d007000c040c1c10800320115281401507920440007841c0501c80c26502039040b10801c0d041d6540e41c2d209488402c0701a0069a2086041c010200d90340d43c0c2d07000d83d088156083e000400c003105d051400118081001d025031909030004c2c100c8154141081c0300d2140d81117004e1031b0074118664120070460061446020412404000310004140f902c4000313 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 368762535 1250 368761285 368761307
    0x1061e170438040510050402011e090b190306050102010b15090a0308030f04032601030210170c0406030f02070210080c09031905060604060312140408070620010b031509160303 77
    0x1c4c0070b407503480014281c00412503204850081c04640c100d6840c6694548102421007040d1150829001007922017190700c61030b81140c503010000000402e607410105e03516019040042c4801e00007444440308810001e00311054240c50800c6103040070843c3d003210307a10000c40800a50f041610039690703007421043c98044c623000320340540100f004540b640880400c04110345041040c03030442140981d003164204041d014060f03407403a040090290403001d42e041d007891554000e50320405170581c0d80d403400002509860450b100b41019501c14840d03080036884441c042182022a842c042003c0d55481d8541e120a00410702d85540502c510f00b480d0700c503407000e4888030b802107000f10115030241d50741c60100002d5920501008150304050441280428050341c1010305401014020b982400d0311841500d252038902c0e4812000210740c1616042c140c0712802e0941c28212803c07009001d80040705010903030318074201c0340200704144010f000856421041c0301035402c01d02e40401600d0010303540c2c28002e0107a001d038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 368763785 1250 368762535 368762543
    0x20715230f0f040602030a0207021203030115111203060d060903180e040c0302060a020a0b0405160524090103180b060a121a041a01061e17043804 64
    0x803408602a4021054814411607015000c82c0e15540e46540b400080e41019080d5540300c0c2d000c0c01002d0060b40c07030740041002107502c03030000e40e2258034148a0314285000b442d12041480110141618491808034098041181903030b115a0b60b52a02d0740032941c040c20310180039124a0ad000c0d003160030580d001e1142c420445850500610392ba84aa50009002a0a48008003001a81c0c3c0003000142031400242a2000c0b181c015035040f0043da89034141c25000844049410344c00c000e03110880d04030102c45010140030251b80540104a80c10036202d030400d405544210580720100b13070718010340c1c403c2e004519030014120b044204d0380032510b0002c0b0b81103020380d507152240d00d62308004103003480020707106c241c01d94212920302004500c61041d40320100b00a8425034940f949400140081104281c4542c000d003040d5a501612200c426078182c20180003c40150403c00ba030004551a81d12480c51039800c150002000c4005022030140b09007600c0c00c1d46a03010041c525103018139503c000c2041d086200c2c07802 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 368765035 1250 368763785 368763851
    0x1021207030605030d08040c051207051507020603040b04260903010516050d050604020f0a02030a020c090709050f01120c11010e030901050f030a111602010e01020607020c04020715 79
    0x15503502501901d485000741d82d00b560107034012074495880740b00c4041c1c100e4016641850415100d002003542408842450701441c6d01440041107941001c00c0200c9402c0b600382100c40c01c04c01039034002841448050310151440610320701040c180401d1381c3d0141024040300e184010251030b80400c400c01d07504a0a0700b11b100754a4400002c00380c000580301410801e2142d650036284c50740907014100145000b80050344c200c0e80c20720180c10100000f0300100701482c0d454005544801e642000280350030f00180c0c02500516200b01400780720b0303802c404400103490007111507410107000500100c940190030514844058104a486c1e010507070401251081090500000d02c0380240e48022203a40e44100c2c5e003d01e00089040042c802c803980058080c5400101818012450303401c0741c45002d0854003c400b4040b030010b05150b40710219a0480c895260808080c00a09140d140100000c5c1d215000100c9442c011900040d00008210001401d02c01800c0b0300001081a5000703c00311501a1700883d045c81040b00b2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 368766285 1250 368765035 368765041
    0x1206010809150a0c05090307060201093003020c010e0a1b0501031a061b010603150b090402090115030e01110406022109040f0b0301091109010b0403020d022e02010212 73
    0x1d008103a03051030a44210354801d064903001c140708024980040c40e81e040080611401083d40d42c1030103c0300042403141e0020403040541c1c105610410340c41d4440d403d00c2411700c421a810b0300440400c5000404035030a00603224000f0190311405044004003202182c000c42c00d4207020095880c00c540691040b060381c145019031108010340031541804010a145803280014030718510b1b2040050010540b4040c0d4441920100d07c019425101305400031245054000c0000b0803941d00744c0b007844420341003100c401240e400c050b00400c021402c1801040607442c4260b81a840702c5009401008001070404020440383c0c0480c400340c54a50414069440140a03074403156482030307103602c0003c1030300c19030094207440e0a044100b004010a0072901441c102070b03c0703801100003940c0c2072040c4030380c4a0003242800140d505d600100044403070160080c01240703c09000500260700e414803040741e25541600e8401601d1900c00c080c3d1080143c0c54101c580410704400a000035036810740260411201840a003c0075031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 368767535 1250 368766285 368766301
    0x180403090602010e031206030c090a0f0f02161502130605030604050a1415040f2c010c0905060f0409110c0712150207110a0b040512010203060a030f0c080312060108 72
    0xc0c52884000010f40d1050280846c042da4040301603802000081c119051034000c0008200d5001c021611482825503c011070003483c00a402040005440b200c002c510b0010316109224403c1c1c00c20101411284400100d1a807200e42c0f5030440c2d024a0001c0f1404a202d40c0c1c69500800c554400ca0700b45014500380008156103001d54020800070f03103090210306225a585601881a1043d280ca0103035000307031034400001031896944aa417030380440c1c206841180141c501d6075810710320030f1229260100e03031622032918145079100800d042035038811591185d0381d182c050b00c890300e14080c60b00030101c01484e02c900400313081400310052448550040a440090b03075134003044440d50b1649000a890021900b0b03005c008440d2607801451041d00c60385110308254150008a100c90510703400407080c4035400038003441285003040d034403119070980703500035859440d00802080d00c58035903110040605001402210802c601c001d107100181032041c0449031120012144540500c5054443d01d0110305c400e000316450f5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 368768785 1250 368767535 368767541
    0x2120d0606180302030d0c0302010b092401090b18010309140109031413060c0204091a0907090e101d0318100224060316090c021207030f030b0d0218040309060201 71
    0x681d0010046c110341108104255500002c10904400319541e80303540315800e6954a407110f00620b00210009402400c030380321200e0700007000b80170f141840030b00e5270104425042e410031600f01c401c9030760040c0d1900c85c41400580240408510060945244429401442c20154418502c0b18002c3c0d4544051140d05044007165220f04040d801440609580612125006a44a10302c1c03510240001400e840383c1e40f200d02924820b005554280441d20040c4900100700f04030000286c104644200180d0110a0166a8400e101c0340d0030071000d91911a0b5142e0710034600c00d2181d12503603400c140c0c1d5568000390000b0340b0b4810741d14810340c4948903416030b0040540c400100d040c40300c2e2401c6645849203030110b4803200980d000030500c903490300c035554010203003414001c1a13500418182102003164111060301a041c006c10800c2c055410300203003c3e5401103540525039031280c440310304000070a2100600030a000e1900c40e440a9004142020000071103404400c603c0c0c801e502030b81e54010016141e00d0b0803426 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 368770035 1250 368768785 368768789
    0x102030a150807120c091a09060102012d0204030b0109051f0311090c0f0a1e0c020d030302030a0f1806050601030b0a03200312070b0903030408030106030c02120d060618 74
    0x1032640040e109100305006120000103850060240c0c0d0301d0599552140d105440185104881d9000d09404003440c5003481c0d0006270f04941c00f400284004c900c0607507140701c2e802504040707050905000c8880b101c414850388c100c3d0007964011013004a80c3da10383c0820000b810f0140c688604a49002c0c00d801803580c030756030303103081a658040c285032950b000c1c079000c201c0203600282c03041c5900d04080003600d0f8800d4840e00104246074254442c41c001101150403c815020714075840d4043c44032094100380141c2d940c3c03c0311540d81c2d80c50300300180c0729140c8260b06001050f100c840036444a103448400300c40d504282200c400201c0c0703d010705001b95a203c0b0011004d59103513040c510b0304041c2c004000d10014844010440c0c014142490382840800f0b43d00001c0c0c40c0446690a40c0355080307000032200244444810f5042d807060352000214039506199480100a10052080500300343e5a40c4d483e0780c11a05c28460541040c600e103001c540c03200100e002e2100107080764401c08000c24140740085590500130544841 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 368771285 1250 368770035 368770049
    0x504090b0609040c0801060f03060609050c0405154005090105012307060603050f01090b0c0c150906180a02130b03030d0204080a02130504020a03021009050604080102030a15 76
    0x103801e48451007400309840700900100d51120b58104042100e180911031300c4001c1c920707030f4000e0250502d1410100304450540e04286881800c140800c01060410011a802c641c070070b84900040f41010749481510b07001e51465000b100f00326001c280c403146d03d0078221101c10542a444495004406901d10394486e406114154000030790303800400c07266000d80c0410342d041d25004001c0d100c815a03240100055480fa40c4101d4080d03540d058140240002001041d0030018040001c014500b2651922003624030010700460140b030001405000f520b905000b400103030084c4000040d141d007041c80c5050313100c03201100c042030800d851030100340b40c81c480080d99055264000d001c86440c482c071445001d025207004815203405100400c480c2d901c09403140700410041080c00d0260101d08241d20412111101c41e41d0062200c0d800d00c010b001c05640d90000d07000031681c1c1240d1030040c0071103508040d60b0340b28941d80907552040011600081a88042d0011846803030200420095480994030010300072045000b584 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 368772535 1250 368771285 368771303
    0x20105070e01140706020f0406030b15030c090a05030a03121a010c080a050c071409060402180f010905030a030c0506010509040302070b0906040f0315142404090b040b010f050409 78
    0x1c55000f0054110101e41c901c2160307281c80302e00d0301c03840c003641d1000e0a00ca090a00c0041c040000b150300d84600001100101c07544482c018084809844600000d0080218a074002500074801e9503201010802401c008d0240c40e00b0086034100546170000500e140c03100b25040003015840c00c240c103034640e03118003c16155034501d03410a407900c18032030b0050ba00740014404d0401c011400340388100004070013000f4148400025031441c805221407468050316040c001d500500140d1300c01e5401c003681a010050558540d00f501030038400480d030102a5900054045c069800c4120901d94030014001881c1c2c0124101c3d035203642e83d4001c0c4407082030111005001a0003000341403001c0f641d0075000380a100700090040b07040541f900300030840c1c44280d510841d421000103d0120102c581c0d4042c0388100c24100c03c0410440c54940f03513180d4000c580c83d08148014030014160b07000ca0307131694020001c00c1e401c2028140c9900c0c1900c2c1c190700d502c00c2800f420745c0090b40e403071002440d0715150152550903036100201c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 368773785 1250 368772535 368772557
    0x60b21030d11042402120a050a0507020a09020f0903070e0408030c161502190306210f060203040c06080c09030c0d050a020d06050709050f0a031101090e010f140102010507 75
    0x100400000b019032101000800001610b560b40880810861207800402c8480101320712002e0f01d802e9a140f407100800c113082c00030100300c5400c030081e684080414100701e550f84441d4800111035034840d4110020442c40070640c2085214060f000e0300c1070706419421900c0444c2c0710804001e4006044070020105a000c01c0001c1c00c41d0f20311320142c1400b60500d8442c0102402c030741e8418070100c8405800f0900c051740403070703030f0000308a4821004040040d181010031846003045400d825400b54103c03421020ba48540751081080000b103a04d41c43c0745d42000b001c540340c0c01c051800200c190507610948002810300310100d16051070500032241c3d252002001011120012028450314024020040d280c41c09001c54000240c0c031036130a603406240c424480010340b4503218902401d604865046540520031500c1021065106d41d5150025070741c0124411040d0460400121090302054103c00d250314520741c000105020460741003c00e03620000c40c0185a0f00314240120308880c070403a400e00000324500c0c42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 368775035 1250 368773785 368773807
    0x80402041b0807020c06040317070f0f0803060117040f080a050408011b0f211a090a06051c0309171c080411041406010807050c0d081e090303010b0d0603020a03060b2103 74
    0x50040ad0f2107440c6442480c02d880d11344010f01032004034151450507002042001b0756070301c030a000e404540003420700703945401d090300d0310303d1404420320008100d4580028281e070301d58011402c1d10001c0003840c00902079400c440d4900c4000980c03140190300414141d0340c0c54aa1107009072000905080130056544800c49140003602c0a44a002e00f00c54220240440031540c1d0b44074207004a124900007a03010501c5440e004c03e104580400020f0905207186407507140000a600420100450b40500021412400c0d404462401d261070301c4116488800200e0f031074110f2035000300550344503500540c01c10150315059810b000545030026091305d00c0700c0c02070303000030304960007190900e030020454900b0038100203184071083d00e80b0240043c240d02051100c0200140c0440455000244c4441a000100181498000c41c0e0b0b503030106000b000c04158012402000015041d07000b44011600100000c010503903c0c24908010210300c0125801405441c4500040980003100d03480c0c0c40350100700852515000320300c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 368776285 1250 368775035 368775037
    0x9061512110409020c0705010e220e06040b01032a090207060902060f0706051503190305090d0303061502010b010206072a0c08160f06080402041b0807020c06040317 72
    0x120140640d95101ca003018040c06120240001d024051401640c078a902e1400f00d19084044c5c1c070030b504024518500c1d0100e5161280045a44000000185213419100c0c072802c0280c441954040c41c984145001c010902c032200070418102ca00904100d5020b5200740090409038080b030011085a5041d480e01b0000c14400c1c0d40102180c600602000482d608298000340701540302808607900354401050b01c00c01e0000f60310032503800966484003100145e0402002ca40c451158100b20405040340c0c0b0700e45000e141c00b550440e070390032100900d4a603401500e45030180080c0914020f400c64a09464911a00c10f4014400d03283c48050503001070040ba6115101240c038804a10340755145052103050f11104040010144505c5900c0b8980031503040e8200105146449450aa240141a00380c9001c110781e40ba81c0354003601b507503100d01c0e185e0426515030002c100070380409002107520742004541015102c0c0d0110b44c640c041c2d0701640c2540d8210003100c00b0403c541c00303940805850b42600400d1440d002e850b001c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 368777535 1250 368776285 368776307
    0xc06080402011e120501140f0603011206020c072c070203030708040b0a0b06070807030f09030b040204020a0507080304061b14040b0a02010e071206231803130b04090501090615 77
    0x4c50000a586038040844056400c01e174403e06103d40d02e1244525180703440c008800c017441d0161595825589440085110f803d0807001c05080980c1c005000040e2400034010600075001c0208140141800355034061a605051050f101024440d800400d80b10b074804000c84c2c2c000c0140380e9590030507440719140c803d82d100f000346c070720b880850307441810300450340b10a40948803460180030016210512800e02a00c0003401e41144420400602e4003400001d03c00b100507074006130141c80060300d598082e01c0a4a09110300c40d4041c25056000c0100320400250350004003805002250f40007580c0840b20081d5501131110b0700280407200144000d01c0f00310001c01c080e0900040d80c3c400450b040030b0142c0510b00740740e095085000d80b8030100d0021010b01405c0d000c5d0380c2c803422500003030344500c0364800700400c00d10030b01900b50100804071940800d4800300420640c1c03150340c0c01580207140e4030b60724034901449070f1113440343d58000790504000044042e82c80c07050200702c49441060001410b03c086089481d0301c402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 368778785 1250 368777535 368777537
    0x1006020a02090601260a050601080105010207060509030a0f0629012c0a0b0d0507021207020d03120e25060e06070602040e010b0c1b060a120204030b040501090c06080402011e 76
    0x843c1074420002c0d080441a100ca02c403110050100e4103000340306ca030907a240107040c40e061000e8440104039a9070f000541400f25411454041d444d4140200040e0800f90350700c40250041981c41207810901c00c0c941d0007811a080140a18401c84020309588043d002c089403102d808200021030010200d001c80c416141d440c04c000b0b003610481000304002403002040d9802481c000400440c881042400d28854503401040e503000401030345020003913070744d118404c01c10028084d04880c0a09010503001d102d1850203030344190000d001d1000c14074103282d030721814550384840f0f14240b01d1100080c003151804403026185540d0760f00242101c09410b226280d400410100c4002d60700b00800078030644505252800317410701e0201255039219144d826032416004030392820720410408030310703440c994442c1c048580c0380f585401c050408410100c2c00e00c1c001c1c0190351024251258040030841042019404815028498284485060380300d40b0b04035088031084130002d0201d12505c03483d040c0c10000c004061085441 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 368780035 1250 368778785 368778797
    0x4020901050c060406091b05030304140d0204060e150111030a0e010c0501020a0e0a0905190c020a080d02090a0e070203030c03220c050102100e1908160b0901051006020a02090601 78
    0x52500e019240c06030131a41901c0403071303403008400c0c1040454203501c40304181104500c0d9804d4241000281c0340e00c03403031060f8079070292000d1a16405032504039091003582d030010010000d01c2c1d96903041c0c0c500301c2c00c115040e10070023402e0038000c8059030003150071031079014440e0021800c0c00c60b50003003594010318903c0f225051222000d80040051800d00040501c54280d5443d058981c0d010814444200601d40189080700d082c8020490340c40728034116060724840e041703004194204001002c1e03042c6600c407800549412000240000000302907002040c40340e0b01941c48aa1042e0b45100c121415034098590340c0c010b80040000c0b541602c0d015001d5504542c01c102c001c4200030035112100b88103501007104035240303102030104019541e0103106c40100221206d400388090000f10307000644881c040c9000d415610a0702252105200c540c0e0251000d441e0300c905c441c0c1d40b075080f41c20701e0048008100c500341100d42c00c1a0016942c4010751801108a034010340017440000165801c01508400c010452810800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 368781285 1250 368780035 368780047
    0x41811040f0b070c1401020303070f0e0307060305190603171317010506041104050a05061e0406021f0603350315030118120518061b1005060f0402090105 67
    0x1050103002030007003541a03000b43c0d480e809840e00300c114a0301c4d640420041d80c00000400401d0760040704480d44040315143c001004d00328040252100400c00c007603240c05100e1180c0219180b078160384007a002d0142c50030315201d8035201812160a40300c0c1404014030350070a90900700c8603002c09102800786d5400803005440c081ea02c0b440341d030301404500c03c25000940c0d1940d042c0821402c0c01d00c0b4206070403d1018600c0d142c0750070301c00400c0d0020f03846d03c034050080800003128840700708003a08140c0000704110591307540d26500c0200942d0f40600c413120343c2004040702040500b90955100c1c140880c1d50200004928044101d48261109140324001d2100545020956001c910910055100311075091604681c50501c2080c582154000445418520307510300c83d080105010f280c0069940340c0340d141c45a038840d40e1002d0078298004540d204c64120401088183c17101c602040c080104070001c13802c441e82c0e68004440c0b5026a90b0135500c064101803a00117240b41801e00d90010708184006040603482c0c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 368782535 1250 368781285 368781299
    0x22b051303080a03140a061a0702040b0607050601052701060327030203032d06060a05041a0a14130501030c02030909010b0d0c020d1d180a09030207050604181104 71
    0x20303210f5000100004c1e03942c01c58840411a07840301d80c1d0085100b40c01080341034105442c4040716050402543d405101c003051900c11552140c000c2001d00002405040e2036041c285801d0b690f0310710a0050900c149440d000c1250308103201d07025002c6101c404d0481080c0d6902e0f040b010780080c000290400308000e0001680301600136420f01d100011b502c25802140d0f03d1404112000b20320100561105071401600d445511040816402c00d401543c100e0341e49076100000c0070292514419070f400b65008290341c8011140c0010b040c40603004180c102d455620410458000c01b03842803207541c0404040c00404601400b5551195009442c00c03011801100e25003a143c0c0c0c0001d4101c50241d2000f41840c400180140c0160098054104104171600041180e030f003580c071001d41200801e1074400b84407060801070081c00e03901c0c40b80200e0668a821160314460070400c00082c081d15040c44140c0151049102c002194101030702260121a110b00c0b17190703140078400c4900d0700076060051190601c07000500c0041065 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 368783785 1250 368782535 368782537
    0xf070c0f030f03050108030c03030c03070507021207031104290a0b0c06010807050a030c06030513060c020604030806010e0609040518012a091d0405070b13030201022b05130308 77
    0x3550080d102c01c05800b090a07802025074005800c00d0816420502140c40400c4000007901e4002040c0c050407501c0369241c490454040c003500c14041d41c01010001218014000407440740280d078000c0d840007040c00025001c1c80b00344c41c0da01da040c000328420000e03889021140d12180108060000741682242651200c0e8444107411650032a0600d400c02401041500410010003005007016198003404c50b01d152a030000d15a40f6205d01020702d62100c0008800c078032048000c3e03000b1a80b21100300088a0341e00c00c005d60711141110b084020811a40206003650301078618440b103004020030311403820b00740c5800c0c8005403402030121440d9480200c68090014828001c5500068803900480800400d901c00d001510100041c2202402001c0400744507080044005803d48401449080342c60303129480d04528016255002c80350801011403e0800e0130f0811008104403400bd82c2101c4590400d160158a8400d64000000700c01002d0114581c429000d2406030900c40303213004a41d80000c0d681c1e1100009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 368785035 1250 368783785 368783813
    0x103090f020402040815090d020c012607030506010e0f150c150108061006080903090411070b040308010807080102030c0304020f031e01140a02160611130f0302150c060f070c 76
    0x10320740003410140e2208640301b185030703440b008003001006000007103100603440d401958880e604100c021030710300800000c0c9000700605440154082d589610b01111700400903c400c2d00d80038001519182d001800c5d2400100ca040300d002d0007032059070030003943d880e040300b10b07404644640d085005404541003032a500e0511720b8001e204050103042c9a24003070b5080c10038002580c220744148204e0034240900140700000381c603480300342610005900c040034240c481213802058001002c90410004000405a011028034100c07604982113030308050311030030440d00340e00040b0717203080c0403030011700001d005440c1c014108a490a40074068500c0c0305405005010a101c0c808104216070303450300d00c4481c210011801c07803a844903840a0031400c20200130421801050a00d002400564032151a074070480c8508044648246c440507200411965030f0052001d07903116440b040e40301d0f03100540202030401c400070444542c801c9201c0542001d54a00d0420591408094600020811050004000a120043e141d80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 368786285 1250 368785035 368785049
    0x130e010e060f0d030804021903051906061505070602071a0c031609061e020309041d0708010203040c030605040c21020f19173a0903110103090f02040204 67
    0x240361400c582442803860710114103c0c01942116015004030703a00851a030341281d8100c95000300d0140c0004040183c8000381c202810074050400d561088000141440110510520050244c0c90780c0d003503070300800d02031119010007080c0200801d80c0090125801050072a2190180710f1855088000d07090320400c3c111241c2202c08400003e00403003511a0194194400341d40c42c20200c043d04041000300520616120096000c50b8031149107a01360090003030740c48000300640100280008058410f00b0101d00c0c609103203140c061094042510081070085911079900046c4003240580b5640c0ea00005000007030003624980c4400300d002c2031109200c00000c20300000c0c4101040002040c1c010450803032031303400340380e40f15100640d0b20685034041e80c1042c404607905000040c80b801c81c03203004a410705000c4000a6040d41010b03005025840c444100f4261000155002091003120300105030307050f080d18003000d0003182d16a180c029040d0b1090b0051017070135209060740080c2010983c0460f003660081c0e00050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 368787535 1250 368786285 368786309
    0x81606180b0906070b16141908070905030616080a18080f040308070b0105120d080c09030f0d03050910020703020c0409030e04050f090d080c03040f021518210d0302130e01 75
    0x100510b47c0141008010b410400340300d881c00004d030302407001460280d4020070620041000250f0031602410303c1500412018050b203005113040d840b2112074121070801603021030042c6000c03402501e26841185042c405e030354103580710400300d40c69007400ca4001100c1d204d02d40070304100203c001341c42440a4200e01c0c5c402e02d040072041d410941001803007002c44201c6007040d03112090b480c1c4225480548143c000d00300d001c25603a540c5010002c01c0c01c2c080c0c50031100a49101c4d40300058901589a8411392142910030b090302c00d031a00c21140c460036841655409001030340300e10940d8800b4030f082c3e4000c60650f40700f401d0034100ca003090f1004c070702a034008650144641174010708000b00102c2c103000c100900500c0d403500e045c862a168500b401c031030002410140031025034100580840d11042d061084103020380b490b06843e81100800d0010030010000e03074a0148160741040a108101e005811001c21342e58800f80c000345600410880082d0490a17111680e1a803000000802d5001d81c203615001e004200b080c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 368788785 1250 368787535 368787571
    0x2102060105100309051002180a180c141c1d0a0c08161502030906030c0306190303051206060910080901051b03070e011701081606180b0906070b 63
    0x40140402d140148003454182840320001070710210340140c0301c511190300103031142c8810142e4840c1800705144660880031700840401c030706210f22201c18000d0903046080c0040c400c110300031207000200100c1005180001c0c0300400d003102d175440f003407440203001c48400680310728a40002200720440b140506141d400450000d0140450040300c0000b800c036110060000054900c9820340154042c410007013108003190744c0074903075442070003100ca40719001010030ba100d00b042d000b15151039001fa80c07103901c101840c4da41840c10f548042c3d0000101c9801d03465050620780e02115810300400c0040000741d21980401189041d0340e03504400d03010700481980d48800da440c20504090864074082e0a0f008000e885004203002182082d003101e81c0088949800c000342e50140c80182d4100e100000401d03200e00f240e0700045480780000809914108400c0f12038080319982c0c4000f030341d0072121454121104ca00c94a01070000d0802d9000501600c0e0000c0c283e1071070170072030380c840c0140040301b9102d005d2001800c03015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 368790035 1250 368788785 368788789
    0xa0f020d0c03081c020a0c06020904090c030c0f08150c090a0f090903030e0a020609191a09011d0a0603110d02030901022812090f0212030a1416020105072102060105 72
    0x14034240000c9444c13007145021003981015064590385d00740100744070340000b8070384119115508900318895028a000812036181e190443c0c80b03118900480401c145d49076400180d9072400a0714034403151000b0b000050300e898403400c1c8002940454469900f100280f98005840200c2126000060a4008001030f1210003458004e0980f01203440000040e400140b00d070300540d46440032035208250440754007906150303854081c040f4941c40e5120000b00505880e48100e04c1d0b1090307000700741d0140240e03602064005407021040c00e200c0e12021050b0855211762043c001c41f0301035489117038040481070210b070500038800b8000060780e00485012903565004201c0083d0074a181d41c0c003a414840180343c545c042d04050800401c84107891000c10035003511001d110341030264440d103d0842039009018002190a40e18156540b54003282c2050001141104000070480c804010340b55009143c910f03009140401e0b80044515170400c0c1c10030703900c41840d00c074140b00b90810540141c0540c0ea00307030040c0445601d4417003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 368791285 1250 368790035 368790067
    0x1f020c031509101d030403210c11040f0209060c0c0a0806190f020903030d0507090902040506041217030f0103030813081e0f0703030603230a0f020d0c0308 68
    0x10501c21000c010a0501c40d0740703040403506050908030102d000601c408000a00c1300340b00709152215840703001c001000b02c04d00c108504000607901c44d4501d402c1c24003100354811942a0360400b8040e002c0c080c00001c3d485070385425003229180c44100200903003407541e0f82d00051804d03444000510500d40c4101d0141d030042c01c00c40c90500c01010a40c4c094070b003a183c0740c00f100011070381446401d40150b82d10500c0108201850741501c040d04009000c80ea00c400c0e036100c400d001040181c2e0310101240200000290410540c000c5401761031001d0000d41c20289001304c070b295a002c0d842d40854143c07411075640200041d0590255108041d0340080200e25451800c01425200014180004078880c605030900410740f03401c200e8808290500088400000104901c41d0074040c4200a03110f004001030840140b42c1d054000708240d902400c00f00d29119441581c4083c4040e40c200b11300745e5504240d40890116607151021130919001031b00400320100396680300325803168250400c0715035080c0440c1c26030310101005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 368792535 1250 368791285 368791303
    0x1204152d0509060f1f0e0906150603070c080309070e041b050d0320070305100e0610050109121401050705041d0601140706090b100518061c021f020c03 66
    0x90103002c9508002e1107140081d20000c10b50f019280c48144641c88401700d0240d464020a041101100c2d41d007804001c041d10380009450240c01d01e032524080c1186440c2840450b4007928407501d80088081c0d00303641c1c0a0341900000e142d45d0301401141d40025690000c0b030b80480c801c030721a050410001715410020340a591076500514010002d45484e440060b41080c0040ca0039420500741c94510103410060900d000d007140c01c01032550260344000171003d842c07500b05d5402040c4408c00d40b09165207800300c45011800d503101e40c9000540c140313800c002002e1035070b126408481c090f40015000003615140e0030301359003050b525203000a500003000c105190b114640300480101c0d8443c442c20074104680000e04803101d0030311020961300300050400800c0220b80c00041401e0303000e00c55000328503142e6164842c252180c0304280c099000361030940c280200748061580b24070b030010010b1542c0420321101c1d05070f280300c145089130001540c10040f0b4200c120100440074807e102e900404290b2035030414941024110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 368793785 1250 368792535 368792551
    0xb04090c050f0f07051204030b0a0203091e0c10230f0c070e0709090e0a06020f0c0a110916120903030b04021201090b030c0f0409051c0206040203070b1204152d05 71
    0x203002c240f0009d000022040e4000044450143c0c0742d071070341368181c0d040603400034003214000c0300c40d00300c440000c2c4081441d00c00003004941c0d501c2650350900080c3c1d5030151915400000b07a07c610302d40e411207100c4002038541030f4004000302d4140460309160624083e803581003280c01e40424000c0181c0264271220303030406003410080c04d020314200805c0c0390755100400d140041c281030300841e540800405010503a41c25000402c100c0c2d03040151418045125400038490790300503071040000038101e03124042350070380001c2c1c0ba644008415002c00c0c3c0280090081550031420151136280c440010313074807400502045041846c450001d945041039410032a215490300e540039802c40d2440034034035540e030b03e2544924501030301e003c19065011b1415500b80b0601c907042c03902102001400d80500c1da070000d6120300c264420b5003254502c0c4d44541d1404440d000d090882c020700f8500c0800140051200480941e004840c50340105245202651070f150300c1401c1c1c402d11200503c582440c003d0324255005958000f00c0c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 368795035 1250 368793785 368793787
    0x80f030301081c170402150d020d0606020118120504090204061806090807121b0305070303021207200a1802090f18011e09050112051005010b04090c050f0f070512 71
    0x11204000d403105158411840c2404d4042c1c00203025034491001040c612a4142c0f00c030b0380d891024408000094006010300440280f600034080307105c0d4014407e91640c0000801c0b00d00d04a0b03c00e9403440d40c0c44031501034400800400b84000204090a80041d102034501c42c1c0783d03042c0c118001240c80086503402d90009040161100742045011400301e203490940300c024903210481e8401d03040207111070503508540581d07400e007100008244540420540d05a034820b80c240d030f48002080e690304015026000000d0306040c0c3e040700e04180d600084445205079400586205000c0b691681c103004076584413500c1d554043d40001d1103585c18a4036103200031201208a840d080c90b89001031403010000c4050183c070101d1100718801680e54010700c0482c0006181c4083d007031200e50b03140c0c040e01c995001416421589446084005c3c0c0e001c41440c000c2c90306035120071014a080a103800f040d0005801da059107481842410851240b900c841030004091280c40320350040d58034a102d142035880c2c54940c090140310300b04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 368796285 1250 368795035 368795083
    0x6160209161b0c060509010c0203030c07030b240f0f0d03110c0307030c090e160b2a120306040212040803310210120203040311061b03040f0309080f03030108 69
    0xf0900070039505491252500301e4583e030040300140c604660030003001c5c0d81440003244003041c000f80002c100c001d49101c0d40034002c1035120000c605c40c407486040599000041d01050340c40646c14071003842002400010b04040b581900b4002007028489141000c1d80015492480103913202800c00803c2c000711030aa0082c0103803407550f291401c0d5480b06014941210b51620380e80300c0071070000c01551802d000070140030718030395940d115401220b80c4128000064041003880c60010780806009000c1510340580c0a400c441c074400403101003036403008000700d038040e90070b001d8100007940850060f80b1a901c031703808071036503800c1c1030042c1c840100c0803009100210446000c140c01011784001781200c0580d05442c288200240c507003083c0c0e014604061508078262003c0200410715901208030829403d424041e11030b60345480c40901d0b40444076014400286504002240005480619452400b8000d01e0031480741e80c1c4480800d814584c0009000540340d0003c00180410227041c09102a10f854590301805054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 368797535 1250 368796285 368796293
    0x90f0609031804090212030c2d03120a1503050a0b090c031b031218010f05090303040612020f0418060f050f0405040302070e07050a0813020f06160209161b 68
    0x1501c0780e003110340150348460419045491b02d20803410351021360425262610400004a541c0b4681401604080100042d006241031810b140c07810918103690095483c04108065500459001520303200000780d54180c0b0740c0114261181d148040c40c07054001c0c00d50008a4148041140e101812450b412f802c56110165031755000070707007020103030140c501000007203522400003403c200200d8004803490348002060508540040120036004409803a11490b401e0320446c200d034031340505518960158002c0000b8441140078190918003040940000f510781403240c014410185c0080e8010520351000101401c0c42c01c15038041c09024003000700549007100d1800340080c0c41c0c0c2c00b240344081d00641c0e1312404101030603c203029680290a2400c660741c2c1c0c49c06e161500400d0769120381c1d00100081c0821002c558075040f404210030708a900100a80400c003140b40c104241e5a000080130101d116201310241d0044c0c072031001c200d12a00301c1c905e0151005011780c074090400ca220b420f40f8400e5122350780000c400a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 368798785 1250 368797535 368797567
    0x80601030b0c0d0606090e070306030804260d03090c0b09060702060702190605031006110709020f0d15051e03060f060f030a060906110a020705100512090f060903 71
    0x16504403000d494103031910011000b01d480f98489420105050207004540350f42c000003202d04907004198005119626154104c044035040e000c002c06130242004104108445502401380642e94004d03014201c00c1e41806c070500d010200300400c008a41c481001c4001d11074000322000040c5a0120540e10b0071031403200180d04d6100d81800244941070100340e010a54880009440d01c49820442da11480b945405014000f60000c0358440340c0b210f40090007040b03ca00c2212114180640c403401007420743d00f800c21520294014001c8100300d88802d005d0304901440c0390040c00d074000344170004000d40034100300920000074144802007400d4400301e00310010641b40005e01039400380303504e00d82e00c03455101d0b480003410203e0821032999051003044030900038000d5944c41005124880c3c3c5040201c01c0d0034008034140b501441d0907180142e008505c04004074100311410240700c01d420329105103807000d00130981c00705c2e00c41aa03c002d040c3c0e000303510168880000b0460301c1d812950440065041102009014080b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 368800035 1250 368798785 368798789
    0xc100e10120f0e010b060901082710020301090b01050c0d0804021c03051b060606040b03190504061b03110f0d0609020304120e010c0c15021c090906050901080601 71
    0x180a028880501291150030050541c0070401801d100e0303441d54aa840c800b41854a201c0035140d441e24007040c690b03150a20845a8600040e100e042c1d1a80c0d0b0354140c041e041c14019222035080000d4105200d50500510046080180c1e40c08016180e5061415020494109103900c0b0f040c0300701003184401e10180010303400360400b00c070b03e40381c1d565a8880c400300f5034014480d99014811034024640200309070308100580301607211405c1051000e615445c0e40345d83c8203801d40f0040e811140420007800700a014500035035202070f19501601030012098049800c0362000c0720b06582c4169140c0f07055000928202c20103e43c0c40951a0620945000c800104094030401040032120800080d0300d00114107541c1002c0020401241c2c119168503141c00d2143d011000300041900084244008064560045856251840d041784040d0300e0705041c449528540400301c031251041d44110304011600c003009214a411034046940c5000000f445c000906094030055000544144140d07401403045100000302c10341 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 368801285 1250 368800035 368800039
    0x8010503030f0d0e0a05060115080906010501050403030809030c060403120e0105150d05010905030a0e0310050112080304020f10020d02071a07121205040f0b0105060a091403160806090c100e 83
    0x1840706019034616182c0345c050034006040340224000041e540c0940c2113040200c01d85a140c01c248e40d5510035005403244400d014880c0403440601003480841d100c2c240d07880e40034620074101d0340751000d440d46143c64400111000c07000121031610000c044462405400c898402441c024003542c10a40c0c41d0000003504030b81600c0c0036000c94001c07181405425085441d05541140507256240c603000801480450b4515506002e481521082e810b040514400c3c54100e650050494089003455a40c0380d0300c0741d0001d403081c0e0f4001016000268280d4601096607090419900246861000c41801074102a9580d0045058480301c503603801e04002c1150072903d8041d8013090f840d07400451000195401c03400c02030360042103071400d0204010021002060a2a5030280680700f405a03a11802c0024510036190303c00d000a0500750204120104203d111021100003000e030b032507003198503048c00c0800d20181c7c020080c50744104103000d1108000e00c500c00c0800d100355400801000c1307a02020f441c032110004140c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 368802535 1250 368801285 368801291
    0xf0b061e0d081c1e11030709180b061206030105010603140610091205010903090e071d040b1801030c12210e0406060e0102010506040b0f0d02040b03010603050d08010503030f0d 77
    0x104180e43c403400c0034801c80d485200304405040c0c00944a0458825140600e01914103540c0400146801d02943e01c5401c0355641c5c40303100c1d824001041600950000440f11b12516045210078681d80d41c1d0190080d440c406510082620308070f01094290341043e1710010615140443c1460320400010441d0b0f400380c01030303880d02c4101081c01c204850303203169035000c412240800341410040000641040500501a40d52084a0360300c4583c035906012055a01c030001c0b60f24000303803249028240340100051000104000b401840740710101c1c00c1c0304140c003860b0040003106401801044024003114000d082030700c2040464941c075949618980e40c40d040007410318001c95903400d03440d40c4141021565120090818840290b41e22005412240c403810514095420b11000480b541404d1180b00550780c8000c0240e140b140d0004144a05d030f00a0b2070040c0c0e04a500d4160010741c0ba2424051103000318030960080c0242082e2441c0188801c074103070041c500c280c1042100c00070152030003041c0c030f92181c5854400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 368803785 1250 368802535 368802547
    0xa050a120c0e010602070303030e2a0f04020a030b030f0303010506090112061a0304061808040b21090703030f110304050f0310060303020607030608030418020a09030f0b061e0d08 78
    0x124070326841c1540a8078100c42203400210382580d001c00c1c40c40480713100c2e49040c4000758003a503089031a080120003006162500018549107410512441c9030001d40150103004007402c4d00d804201607a201080d20000b20391110308001701030500b0040c0b5040940c804e00914115410280003030401c1c0b10300aa89410080604a00241130403203078080340080c4050406c1c14a0b5100d40f10015170213400844003520072900e050b000c50b583c1c1e84c41c120390040b800e41c00910300307140508140384015290080800000e100c0c40014030f40c4044104020264080c2c09480000e01410b4694074000300030361b000303601000410250780705000364900c002056034141d990440d0710340880b810907030100f4075140400511050950800300c0c004149034011500705d02800c250b40c1c040c400191543e16983c0e80e03125520a0600c000140c8050104003861a8040d010b4001c1d81c2ca0004072450740e9841c0d2010750070890308190740c0c20481005004092904501c1c3d042801400f03440348580c0c10210b00051466484500301030850a000916 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 368805035 1250 368803785 368803793
    0x5161b1211120415120c1e050f030a090b100b1606020f1303030327080f040321020106051507030e01020f030d0506090702060903190c1a150a050a12 65
    0x1e86010441c505480e1a5591405500b0b50000c48048031004150f40d22620060840d0b140284a030955884c0c43d5003041c070a040502e03071003001c101f03543c0508201007441000b41c5404814000d6010340d08540f00030440ca091410246510000a49180d0203040342c0b081c04c01803514028142c662003158240d80c07401c44841030800b000070b8842e0007560f5008020000e951409220761200035010b4a0003075a04104c04540c6070260040c0b0351100003040b80d8070a240ba4910f0014220800409010407540c0740141030a40d645e64101ca10115030040e0a403449006103444003103a0b09120f100000c000c21030381c05294000e1191245480d1040e4030340501000300004180d0032690007040f032411503400900450f55200c0029422074028181651788074816036070072011490003440019031500400d0900080d5203410b2200001c100c480c2c00355407030ba809002880c5418400b0034201049406120b03618400c0c00341d1440e0450341c40741025502e0703501521800c02c0c1c1d17a0611061f01d80a0300003041c0c50408660203000d12040c20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 368806285 1250 368805035 368805043
    0x120708120f0409060b03090c040c0e06160f051f020708070b040201090302190503100b0604060810030c030311100c050301090f09060203101502030315061b0105161b1211 74
    0x40012814241c4c002500071000005500c1601d010701610b421044107800c007c00d440070302c1b50900000300048443c2c4070a16003140108808904030300d00f00904a40759880f0514003911100554564028243e2315104d510f0494404443c60100c2d001145000b006039640043e6010f8824007070700c4c0f401400001021a4002c44400380515002001411a000312050b40035104d00d4a0084a0003800341e000c900204007481e00600c1d130141d600811741802c003410300340b0884410340000c0c99108807010304500000440c4090100d40041e50190f55030030b00000c0e501d508689000748589981522174034041661a010b035001e800e82e8195901d4400101d10000910800c401500910801525441c400014044121030600c1ca0108540c6020b440c410103804190041e230711380c00129030080352a0389020140c01d1514001e0003d000d00308100140c0708410315000c0c42e890841d001260360714244921003c50700032582d04100c00d09011214003e210000104035643d40c8080c0780780d80400024011004448007020070244 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 368807535 1250 368806285 368806289
    0x415030b04060906080d1b060203040201171510080601021b010302220e01050d17091c060e0606032a01091806140d0203030a18090606020c120708120f04 67
    0x1001840b44548511508000309494070440c4d025106528035404030a00038011801d0050000c04035801100640e243c803406544000d004038104035848094080c80c241c03503881e250240c2c1400c141d40d085082d1103018044034034800d566880901000804014090380e0004000d24428400f05427142c00e50340311130041e0b0281c0103542d40b05541210f51310601c1b81480035600d44c102254509054022a031347c1c1c1e01e040c4414080c0c41c0402030007038030b5682000714a00804500521305221b01030180321510040c171459880c1410100d02c110388080e00c49020781016141081400d401c000c08401a040d01d6103d284000003403c101034400c034241044150790841a0b000341d00840c003c0241401c0704e40482c2c08085507400400090050300c3c3c84580c0d00c502d031100c0d418840081000d4907805002549040000755094446d40d4088001080c4401034600c081403101060240380001d2041d60001c0c003032410410b00b00f00740d41c1001c0013410a02d85c0314240c2000405c00005050309640c45002034280d0354480060b40d2401e91083e5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 368808785 1250 368807535 368807539
    0x3190908070e0a0b0609061827161b03030e100c020d080a023402130f05090102130e090106030b01170c0a150e030339060405030415030b 60
    0x1808001614002d150801d80b0a40d680441082110202020442c3d82d010741c0c0c080c0b030307084141804400700d800c4801d02800e480341002442c1d1441201070b038203510f0500340481034000500381c420702031004881262030b1109800b5002e0070500003150450329004020400c08001408040d03c600c10108450014060118105c0b2418810711100084540195030f8480118001d0006a02c4000050b2070800c58030944000703c071030382031081c18201d07802000148203c101035022039104100001e0b90060751924a04100084070388404103145048270b182e20708070351000303140c1c14160f4010003841d006503415105c5141500c0003150b55102c0c076140d1507030050040c05075400c000c0880c10020008210142041104987c485c0b4840c01c80d011440004140441c001180c41030003840c6101e034200051013030017400c00c418002c10180840e400c3c2002202d24203a201c00c04102040900c5518034a01d0a1901419240480c11414002400d00d4146a659180ea130702c114400c40030100528080071000381d200e034000503d59400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 368810035 1250 368808785 368808793
    0x60f0702040903030e12041811161209090b03070b210a0b09130c0501030b0303121005180f0c03041e030e1f051c020f070308010f05011103190908 64
    0x140e10380139004103010b00300c24a135445030051429842e0f000c007040742c0c02d031080301400031240d03000c1003444030142c0860105038410326011b0299a0a801012400d8120b00703000d580e568a0f0f0545c3c1400192500b04290010741c2c0082c24548400c1003a01e0010381801101c03605401c0030b603509080740f0b8880204920403c0444408080c2e011b102d291046038202156503441101d500801c3d80360340700d4484e001001080014002c1c1c850190400c900d42c029407006442c000d0103000d491501c0d0303c0d0004610f902800b21024035107004801e4044c00035040a0f070032000005d6500d101c4010500b803c040400781d0f5100107210710f80c80900040000c08001c2500412142944001c85500c1d0101030752030050701d507000d14a03185001d9980c004065964410194103001160f4003900e03240d14100d101c042c0348082c2154074100f1402a5020054040f650350640001c0140e1400781c0d403447c00c2c035410301c0480b07040c44e00940e214a04002c0c03a0704107d001e00001000f2a4800000c2c222800030718182001c0658181f04140c0c050310079806 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 368811285 1250 368810035 368810051
    0x403210510050f100c02060d020a09090c03090c030f0213020705060a0e1c050313120503010f120c060e0f10020c0a050307080d0f110d050406120c0e060f070204 70
    0x1080303400050281d184092102895900c50b014044039080c91031105a016005201452107140580103100c2285d0003d403c00749040c903c00c0941c07003030764440700c45080002d03a02c42040041c850b140c41040c2c9800103d180a1205070801c1d2204218030b00580005000d04281958610440d40c41200000f0790400103c400e54031218107060007604c80700101c0b04101d01c60704050503508a0000491403a0304540c1da40202c1406200402e000c940b180c000070410946d82d0700712100040821051231081c0070300080390351200c0d9258145481c600380c1091550280d1000c079150f910703403c00101c5400803d0183c4400b4508101c0d24558080012000c4001021650f0004840c555004520f41d02103401842e0a800742d80c151504c5954105150341d4181610952204d0303080014082c101600c129621500300802e450040c0d40001320021080c113010400001d0f07000304a00003002c10056030002d006401581c09000208085421400054101e80da0716001c280b0079240000d07881d10303040c0c640c81510322070394000d0803c2011013 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 368812535 1250 368811285 368811347
    0x3070e1309020415150c06020d14040c08070e07050a020c0909030d140103050d0e0111060f07030509030a020606011404080a08040e01050a030f060513080a0f0e0f01170403 75
    0x9002007041c0e0081d81454203c4011005a00d1041c0403600c04290b1614403a5212504440c072450382001281c21903003c00c5003c4407e850303806004d11a80847c9805c4485082a00d803241c42f00700c46034404030312030f000402c0c10092544256a815403000c45401c0055480d5a5884220b01f040c006500c850b501900d00d0b4144078100350004050001b42e0740b415004c01c810344c0391203043c6c0902c640034071000b4019482010400c0350f0070310840d006031200300e060403c01c0c24611403041c010b080c5241202c11003112406902004512545030254a411000b8800a14a4882908002034503440001c0049050099501c0030004010000c0101e0b0f0041070408141c0c1c503400c0e014580780c0d005a101d0700c20213290205520010440b032410f02e464408480e4404500306240449948600160000401100318200041024008619410002c1c50f240c0001d5848203410454003d010f000e11812314907160041c00c1101660541d42d0700110a03880d101056080020145e41d01e20342228988414400e48142254003500d5241c04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 368813785 1250 368812535 368812541
    0x50d060e0c0409080d0b06040509010b0c1002190e03070902040b071a0f0f040c05040e0a060c0305070e04050c220603060e0402061b0705100e0a08060105060f03070e13 73
    0x18031248815141032600010800080d100807402c00b8040310410440c0461145003a4049000040050481401c1650303c00c00034040c100268007001c0301c0000000c0d030922510041c0030100c2c0c40207203107408505140344800400204004c80502c9403d010135030303403c1c030f005980c1084640014482c0f10300039075595486030248481508000400c641c116814000600303a0303120840994811129480405120385da2085c0b10001301c64041d0066031403405407c000300307140e15140140b0228020070402000e8200032031520790100e030700391b00f100b00425103170006102c4c00720303401840b0818003001150049115100d03000d40c3c0d403452040d051000560119916002032087c0300300460003c81d051703904c2c200800740c2c1e900d0448a074258211402503000d0400c03c0041ca0030940110400094110201104d461070b40b101c001c02e040c0c6010f03902420101c2c001e0000406a8039100c082c0801030520034001d4525545041d0219101d401002d072601d01403036010000800d01403040c4040b07042100c00804d01a0440c010110701001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 368815035 1250 368813785 368813801
    0x418091e0302070503030c1903110d03060e0604090b0c07110301090f0201020d02030903100903180e09070b090f0d051501030b0106080c031015030204120501140f0c0919050d06 77
    0x940604080001c0626010042c0e64002247e90050302000c20240c12071080b1b00c3c2505421002d1020800c1c0d000001c100c1005031041040b0b031a1400140a0300740301d040d40b0b50050007001a0711075820704403030100044414032001e8110124030382040d125049482d000b40384070079030103403260598600156001406500030720001c515001381c003a07880340003801c00100d03101c1c400d02018640540c00b0a41d4100c001c1c141d503010301c05aa0103494450820101d88038008407051040d0b01201902c40c0103414040ca242e402d004800080442280c0a8945824640070034201114010707560b12582010806606010040c0100399407441d00310b02400303283da10b038030340308540d030000380603040010705030038002880050403004603401400b00d0204044040d141c0341c1e8031014808107001d6002019001d00001030302300d4204520445540c030840c004a10090320741c504036200640102840c105182034030900c0b590000a00866104520030350740901e1040c68450380c19000801c07a0302c815041014000c151042c426580d0012034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 368816285 1250 368815035 368815037
    0xf270b0a140a090209090601030c1203052101031203020a021002031e040f030806010801082518061403070501093501021914270d0503070303060e0c0418091e03 70
    0x25031b5115012500d0f5600c0d03003404000d00303828094505104407100400c1000125110b40b501500e400b001c3d03414032104030f0000c03000c0d45041d00030070018002c000744442000884019132074112700f08011568002d5413060707050203503128594000003148502c0301001988082e8407440e62b0070406400c141c03409400540d036000c425000038849001081e001e6109102140c12a11824024625000c85030310880c00038802c1032180c3d0b85da0704680c4000a2240100309806220043c41c0300000e03245140581080c1303560a0181c80c00e2294101d00c6051055a0f0408035140c01c0e03403060010780c0079800804094000000302c0f800c00d8075113944807084e002c4070100150020a0b00e01c1c00034240002c4a455800c1c01d5074182800300300f01d0f452010501105590714030303805c0c2c6d1f64041c3c0b43d0305411110700003496000c907001d861000e038140c5807604000327050014540c060140d48001c107585843c07080c09141401103c03c0c240070700e0084500041c0950f40c01a0040030f150007000000c1d40090f4440c40d200e10041c03001c0c0102e648040d00320 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 368817535 1250 368816285 368816299
    0x3030f080112080306090907170d020f1c0c0c09020723010b0915041b0c1208040503090405070e090f0a0606140a0c0302100e010f270b0a140a0902 64
    0x801e01100c0518000040d40c3e001440905603103d030001c0080300b03100180140134031300c01e44c1000101c5501808a802d540f074840f0020745407181c06104000d003440a0845c0710f02da15841000c0000038421464440c0c00440c00918140424504900d1310501c035400310780c0801c2900d4004100b80341480b11194808100c00c1502007040301c080d2030000940c0c240c81010941036801542c0030005240440303100218010054004c2000a0362484481b00c1242c685032055948001948403d480c0100300300500c05000c0380c03a050a00c40c540d407805558030380e035a105da081c81a00481d1100d01040760113024000a22050308020851100d40c503107605a000d184008440c01d984050500c0b00c00038400d030241e1403000d100c4c0705200d81103103041810402a15241c041c0c0710101d0851256071441e551040e150310980244260120010580845000c0c0c80e81c280c0d2a83c40807038036000079490841d1006041d01480754003c035800b03801c2282d15901c442e01e04c03000780791940b501c0d03280d40011020041d15070441d03400081a10301c09c032400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 368818785 1250 368817535 368817539
    0x402210304060905010c0510050a090f11031e0a081b0d021612020f040b030f030a0504060807050c0a030e0f10020601151112070206070206041511010c1b06020705010603030f0801 78
    0x446d00c00320135450107000b5811005035051000c0301d5800c03256103e042c9100100702900140e407145001d2041c00c60545d040459400200c1c2d147c502480003000c2040c20802411011141030303011611a020000024018031000500c1c02c2e1400703800c4203000544008505a8801154a04001c6c1d1a009401c0300c0c42801200c0c2035000c6642685500120002030300580f00c0c0382c05500c404140002484c00f8003076a9414403a2044203c180102040107100301c0c031295031595140d41c50510054a1000007800300d00622600780000d650080d00000d82102c0240c040c50020500d03142040841d195052403202241c0005948909401454001608038120b8081040100c0c2c9204802d2007121000e41c100c0d510043c0b034008001d05a60b00c440c03103015101c0980002c15543c51f2104541c0000c05507800b551140101070f4040c1c0c0845a150340040ca10500e61089800a000b96071001900900744a02c2d082170244078881a1a01800d2183d1641074607611070303000000b00100c4d0740b01d00f0007404002c544200500003c51030303000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 368820035 1250 368818785 368818787
    0xb18011709030d200708390d0201050105180403180b1305030c0f130605060301030f1a190c022505130b03030703050d020c01110a0215010f0e040221030406090501 71
    0x9481d00d41d544c02100305040800c40d50b10325140358071410261000f0602c6020040c040800e2045511404584099241d03841703196942481c14000c00004e00340545e45400700411072521803c21440711402c240c0c801200543c0d452030107031040a1b042c88020000d0030101c0c0b02081c40d51002d0028400c85034545240c3d000c075a039440405075582000c103800383c1c00002c22644507200e42400050040c03448400c0f54046840d98444010030070720b801c26801a01c1c8403626100c1e00b01482040320100c00e00300705100c402c00ba1890545200e54901e900344407904031266807039250202c41d40c800c0c403e00305030029000c080314605200258411034154503020301407080b0300c08090600104500c5c4506600000064061414a881603c2c240c600344c20010141c600b154082100c0c000d0524280310701e88400403485103154840904100003403078919049d981032a01c146010050003032844d41c2c01403e0441b00c1c00c103084c56607580d82c1c3c13020400340542c04400030f1002401e0120604114804009441502c003240e45150a695643c40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 368821285 1250 368820035 368820071
    0x111507200106050a03030819021303020a0617160c0b10060f11120f1c090b07050705061909120206011d01150c050705060703270b18011709030d 63
    0x200b0a54051031032501080000d00440b47d90343e120380741d141c40440c00600001d141040e0390107080c00c2100000e50344011302c110316006400304050180b918006d42900410a1003030040302c1d019100c84212200f102a00c1c0c40315124010b001011507208019074020304048084403940c0e03c450085002040c1e03003020100e4140d12807038045400740000c500500c0c141c40b24200c410760a90295000d01c0180c4001c1088224240000003102d030301c11741c034220000700604070f428070a41855020b0528801c0110401c860404100002107050300280640c1e01c80034108002004000200030034040142040302c1001200c107916008910203040f641c10a81c210190ba407600103071000712000740608440d02d8481c2e215090701c83d02c5554001c59407442501151131464071100020b91541103c0c008400180307030039050701c08070f00c4065910081c1d2010401414070070390411203011031b5400b40145543c3e404c80c07005203000503a07200d240015034000608040000c01c5c14451f845980b280e10198050503140d09022141064030f50800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 368822535 1250 368821285 368821289
    0x51201140303070b060f060304030f02060f0c090f06040911041401020c06070609021503090c01030e01020f030c070804051305040204051614090a0e0f040c060f0c03111507200106 78
    0x2070140d46000e0099492640d00070020381015040020b0404508607922810010740c01580661a5900b0481d08201c4c024070b0b000009060003d04003101c42881401e001d03103802d07120070b1841124400038491038440896568003e0b035001000c03180c185030301002d620050b00000c0042d50651190300700d41d456018016030380c0304441404150807000400004021401e02e500640010740700400350540f000c401d44800340e6a40041e44c0000c4150030080c101c68030340d81c05200e4031240c4401c40d0025402c00c004140d00a0b86400010041d259191001a06404000e5400204c401401c00149942c0c601c0da440e0303880000405003158100d0040d0320342400702e2244c1d16030303141d541030140c1c15548803030310307440311000012071a00100141a0410110140440e030032802e612801e12881c0c0c9541800a546003a0030281030405e903031b52003441800f0505a01d10000795020210030702c225010f05111034800601c0f46050300c0c04034040c00400a18440c1c1d418042040c3c0e01a0407521101024a16040030060100003030307089070094 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 368823785 1250 368822535 368822539
    0xf0207030e03061b030a0f020705100e010e15040809211c03020903060613090501020d091704080705010f121e050a0608030742060b0903060a0b040605040c05120114 72
    0x41c40006e05560b160342150018800d00d10300503042c2051995200c1c900306040340c0c6003079074a882d0110540d442d0000d01c24581d40d9000f450041c0405100d403010b445030114040c101500b2020005080c5984e516807010801000c4031110084074450351001d80f01d0b03210b240c0480e50204960384042965405c0b8401c0c002c4e250500001405000c00d6100c03442008000090b8000c0c0c404103a480e04008000b003542880500b1206904e030b800030074001200d286c2a8800e280700407407110014024031090240c0300c00080e042c41a18800e00b041100904400c40c2034481e103040c0400083c0060420303180c540c484013040111214103076000d105006646552036220b0903078010b8040c040c2d0552050201e0000700b0141d40040b42110340400382c00d2100c20201407680410900d20071700040d040c1140525081c0d040365482040700410603040c03032508002d900780010792500340207014a060385803503030407000c880d541e164040c500421004100304580e148902e0080c01613008100303004070f948c503400700000300c51100c00d0481d0303220500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 368825035 1250 368823785 368823787
    0x20c010c030e040c02120d0204050f030d0507030804081318050a060b0901030b0d0c120b0a0501380c100605040903090509090f01060603090b0601020f0319030f0207030e03061b 77
    0x42c01400028000c69451604600ca06440982d54071810401840c0001200c10b000da60b0f2801c05007400715408220720307098000d502a03100d00728007560243c1521a80d6030704d443d0000325900c1c3c2d818442584d001e907103010024050000c1e40001c98009440c00c42c0c004215a80052020395251000c00c41101c45620404201c0001000200241e600c03d81c44200103001c001c124101040b0b5548800c54052810380107030000e014039010140500280e03884440d413080320014180710340d40c101200401d00c15034842c00811a001201d140310801f6546190403088458680303301f64845212840b501d551b08001070803005140d1070050045941e0500c0e000d51240141c064840c41c282d980303800d040c0102020000e0070a5200d0181110056007150f0038012000103191550b0040385440e0603040101a00341c02819250655100004580d1119804000c0c0c03600d103000d0600ca524042d11004007a000f5003580300d003401c500c601c005010b008050f004101e00440d2407058044810503900c030400e6100050036000c0c01e069101c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 368826285 1250 368825035 368825057
    0x813030b1b041a04090c0206040b0f0402030a120e10020601050a0b040311010c020111010f0903261807050d05060403031b0c020d080906070b091006060c08092e020c010c03 75
    0x25084a00250010711182d11300d80341c2c0d03c0c0c100700c0859003c00d28040050b04000144400d0110314034400d0f4001050b404d00c40c80e01e04003580020341e509242c4030010302e1100c090181e0350107030b4040c05002c080d16901604524030361100c0d25009403124005d00425100f0192040c0202e81160114255802d4036403000020189010141c015030300306003180c50483c100b1100c201801d48401c000c0c014203840000c00310011802c0e1100c0d1401501c000809031041c3d174068066140300d09121405240c1c184c01200c9000842e034040301c00b0110038101500c0d03400030758000724400804001c100d4001100ba10450296408100018024000c00703510200c0c141c00c500080d0182d0200f0340985000d00000e10303594401d0300a00c0c6410b4041d004074140e0307000781106a0b8204060410850020814040342c00d50b4406440c00b0000e240c2420b1010b003510784001e1014100b5a4081541c3e0080d0f242c0350b030070200341c400c100040b81c5150310010385500d0b42e803018038040005010790310904660354020b24100c418203605440e00a2005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 368827535 1250 368826285 368826299
    0xd05030a1505030f060a0c050c0c0d02040e0a0305220617060102011401080f0c010809030d0b0409050f0d03060905040201080c0304030320040812070305030c03070c0813030b1b04 78
    0x881c1920455526416690300010169020018100c0c65010030340a0856898810b2a1200305c561160610050260802075410b0880e004140c00000082c12a10b54550b9000760002c54010702c03c0301d02c224842c2c130414944030245070704800a4001c0d100c09408152403010031540405800119200f038001007003d42d180140510140e43c400c0354081c00600c00040d48144040c03480d90202400c1c0d120b0f0405411103101d03664036100a04c100e588c3e003182824050050b05001e81e00b16030360f100e5200540c0565540c2c0c00d100380d87d60707070321381108010300d0700681180c04100d1103480054441c1c019a0328000401d14009000a5170301107802014480c1d90141c4075040d583d41c58866916031640000c0c81102050342c0c46000c1c650810055089510b50308140c0030503071f00c8904001d4046c1c6407059449003008143c07020b0104ea40002d51201c100d03607001502c2901140c50b0789035000161011341e44c1003c0207007006400700300000c0c0b045d0400400c40480c0d020b4071000b00360343c8401c071601452201c843c0e0b01202ca1042000140000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 368828785 1250 368827535 368827541
    0xb0a0b0703110319030b0f0117011203050c010c0e1201110306040c051303080301050102010c050c03041a070f060b0405061c0201110a0209090f1204060c03080a060b0c0d020607020d05030a 82
    0xd50845003603074036061301d5910b0030a1030824a168000803e5031201007803100c0c100070900c1c440540d002e0801048000600403800c11001051051400040152400c0f00c1050b02c90015582c0458540e4000d010b0700300914000341807010000d2410303001c0d8101d240c0d07415091005010303052503c05096602407840e1281750610003c0d08001c0704802c240b0030100020107890b01e509200780002e41c01445000d0b141d5041c5000242919062500781040140038030880c2d01e8410701008840884100243d54a01a83c403162043d40c280901c1c2e001411f011440294002800031135009000702400484080000e50358120401800080c07a682c404101e031a20300b4542c00650080f031031544d91201460071510310640b6503000800341001282c440c001134200c00402041010100304079141c01c890280c0d024205802c1c0315005000c0501d417180a01003201001c0400e2003000b1035408140603010004d00590f41d541012401c558035040c016440740140b160b01c4c0011a020f00c00320300000c0514156035518616100d840d505030103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 368830035 1250 368828785 368828807
    0x5032b030b0d1b03201e150309010c0909020a0e12011b020c0f0f0d08031504020c0a0c0905010f030807050705060304032c0904062004090b040b0a0b0703 67
    0x240c1e401c09650085850030341c149444a0000601c020914158900a4125000000355241412440e1316034295550b0300d400c10b00d100301c0e000310710b00006c583c01d00004241024030114031992034000000d00c500030340c3c10740140901c016641c50316035003e0390790704143c82284100c44450000945405485e4510301d800d149100e91f0000d030000105460401c4442009180012240080507a20030511465a03003407045011a010108a4401d000b5642c140049034003481c800314014860780000000030b0050340388400182000c00003401c119110500d401070302e0b035141c03100c2109a8800c48001000240f00c101400340c1c80c1a50f4000c07141c0404146113a807010030640220400311224003e4080210300340c1c0b980400f030761055001e540c03042c0c118485020701904518680d41401c80c22100420000c840342c030748404a98000d0750040300040c0940d1900055140200950f0000d00000b1340020001400c00c0e2075001320701910030456040000044950802034000511701c80c0351031107441031150344d000c2409402c00c404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 368831285 1250 368830035 368830039
    0x6040e0a152c06090103050c1c050d0c02180c0f090303090316180c1403041a010605270a0306020306010c0c150912020a091d010e0705032b030b 63
    0x8202625810200b0203490074002d2081149000b0002d82d09408480080b6900240240d58070601e550464581d19101d040506203507000d8082c60144c2100511020341910216412000340c5101030b41008004210107000305080c2e115024209180414a00f03c000350380c02400c50356201480d141c40554400312a4001c4502c0e26818082400500c0700c5072004d004441074603048200d4075120f10304141700c0d180c50040201551445910704082046c41c65001510940103910303c01d0b0003170f141c2d0b4592030040c81c1c002c0c6140c032000409400ca070000079840c0d0401e01034940c0c05605440c0c9021034000e02e02411900c2e80751400540e0003646030004001051039035000316000441894046041c00c815180ea07049400706502003281c40300c11003a01c5a400d42d0050f00074003e44200034151452800c1500080ca52492034000c08001a0b907a50f01200f00c0302e510b10002503d120b048000b071000020140b0415110030340c1c3e1080358024013a106006042914414208103520090300104081c000102c204034014840d20100c04e07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 368832535 1250 368831285 368831321
    0x80601020f16060f0801230402160b040204050106020d170403020127020a09090807140705040c030605090c03010e010603020c0c0a03080d3c110c0604050c06040e0a 72
    0x7403002a03062100258803561016001c1c03410f460518018800c00310050140c041110440043c0420154a041180c004290400f901a10703140c40e400035000b4440c80139200c0b6584041806e00003000744140703451344107600803034040040ea81d8410302070782c44032011400e05000407003480d5015402e260340394003a40c0042c00780c0300001e0140d0907121518140400541c0003000243c5160403001185072013810b007405404950340600c944003c0303079681c0d049030145690080c000c07418000c0403d80c260007009001c005001c010310900c500c02034210090700802060040714096200f880c0000e007148c680200f1a4121100305103542e009a10302181240250041040d00341140102c900f0f50700355a54920b20040034601400f60650b035041088100030440b160328103100c4082055407084c0c002084071186500090020650160127644c822204100405504902c41c01c00d0710042032600c100280081e420348107611840c2241c0b80c16410400300201402984624841805c0c0c68000441094154000f424103003100c490300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 368833785 1250 368832535 368832553
    0x2031501080901090209040c0f0f05010f0c020f0306011214010207030c150e060c212205070902210108010902091b0c010614040f02040e0708040309031a070e090609010608060102 78
    0x1b0701c0b19141605d00f40c0310900d94610501111100c080940c00600d0900d8140e206146030000181031850024541402c1c00340414200055450328450703112208001020346540e0f46c0c58000025905c50440e01c140c4000c0c00c910302c0c400c4068814800c99141541544460314880c070540d552805121a82f207809400c50344480c00c1141c0d4080822686006441c9008003c0e210720071240c00c02e10010b1000c11461403101e400042c05105008000c0b0b11030010140c00802c0095002e60400c10301e06103241c1e00c1f07040030602c001009a4201c4c2280405020348903003c803120420f90382d03000c8140c280c0d2420a406588250100d011511485450030444000c00d041080d890070541c0e503007443c500710342d4181c0c40307000761030b108580d111a945018031406d15a200c1c010303c1181810b0a1017240e000c1064000c08010500480301c020805150245e0310403c011680011607030488241d00c00040348040090703134083d02160400c01031060500e81010340300d101d114007500b240042da280c41c504640302d200c080c0c031017810341c0110b08035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 368835035 1250 368833785 368833789
    0x60b1b100c050a0e030c01080a02030a18230a150902040612060b0a1205060f070e0a0306020d1107082a100b030f0111041818150e01020315010809010902 67
    0xa01d140015030b030312140d807168030b0004080d00c03501d946002540300303400c083c3c01480c90b0780e040000207402c03201020006889654181c03c00005081d01c80026060614610310882001552441035500f82c20b00c5451a01603d84500c1c11640d980b070200008288000d8440540100c02d1242c0c01302c500680001e0001c40c900e6910120845400c01010317081c0c0745152500c00b440e080b4209046180c0003444a0b82c041481401d460700c5540d200c00000c1c00c10b00d140c3c990000403800c498458104c0b0f40b40c1c001c004100781002d0f075591178010000c0d840303505130320b200c9410100840c1c43c2c0401c01040c0c8201715081b070111842c00b28007041903141703050300030b524804802a1211020346818104044d0400100b4803a0005175503000790b04240c600315100b00c0020480e0b041c80340e5045d10060100c1a030301100c40380c179030451262450025074800f40098a5181441070b420707003e03003824000360b00da0844100b6010b40f82000000c48450400c4d00340c0c03004990000708403007070000242c1154400c0c400164441c05c0c407000020f5445003a40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 368836285 1250 368835035 368835041
    0xd0806030a0f03020c090411031c0c021c050313030b090303070519091e17030702012f060406021803070e010b1e070506040213050f01050d05100e060910060b1b10 71
    0x1505823402101151f221445003010804a4002c07561041c0c1031100e91000c5c000100310504120009000d03508032919004091010000031783c0050f03000c2c0c1075a84420030003036040c9050515100950304042460045442540301104407805260a56142c07480c212400b22528940b80303808801c00c0800c442c804000400b8000031a45a0f60384201d4010450b00501d011040038005008041c21003240d042000b00d040140e0300a030808003140800781c82d146c4490310f01407103c09921020b602081c00c50099001b000204105039006100c1142c2150003240d8410662040c9075030b40300b95000384002c507076200c2c0040c0708060398403000d05001c95414400d002200c00d90041203a03140c1069004036500e0344003a05000440c9054048124601100035041101d03240035084852512018402ca038050a4910420010f00c4804d200c082d200410625091110100c400c50302d07651240c003110000041c3c01140c100700e0b41142d05020302c008a07488000c4107401e104d02d001400c4c540c02c8291241424a2040300940081c01c07040d80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 368837535 1250 368836285 368836291
    0x50103050d02010f0510050d05031b0a030f0503070c03210e010c17090604020d060e06240d051005090304030b0c030105150301080d032f07050d0806030a0f03020c09 72
    0x60250801120550010f801d69015002d0003070913a041c02e080025044440e210241202c0d011034084c0c0e683c41040c1402070443c4160403144441664107041d14059200c00507154400501c00c5c0d4680e0f82d021310b42c10007190180000d4403128005103040b40c0c0310010030b1103403502c207074600352500000d1000c0704004500c0341220008808040241d440341e41502841c0e400141072500c581300203000c0126458500d0740b1907201d4000501c02481550030428030000d020440d0300c103d40300221501150390320304010301d050b00b1a09817001c1c41000440c603500b500b4050b092214403940f4440e4004000c3c0154141d150800010b03180c0148001201e110601001010885421086000b202d065004903948d50401091001004d01311500000c07040e81040104140e1400080c41c0c0b020104a240003c4d1b4207a80307140c00303080c100c81040540c1c1d8200143e5800c1d020781041400070301c040b921650440d04c401824100a03142d2407001c46446515412403c0110089079424002d40411b611a00c1904c4031100b4840004104400607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 368838785 1250 368837535 368837543
    0xe040c180806011d010f090e010b210c0f0604092406050406020c030a030f120b0a06120f0e06060d0f080d0b030d03110a050d0b0301020c03130f0b09041d01050103 71
    0x40401080111001e071140c0441a11491040c0311315810300d2040141c0d261a445000d000c0365551012001641083d4000010074a0091001c01c040c3d44081403c0c0c00b8401d2010703401038500a00c0310f004a0362800500c0050024000381c006400c007407400c81c049000300114005906030b00c0000e403952100070482da882001400b629221552180d0030f1103002450000e02c058464020341c404503000700401d4202c4d58240d812401c500e0121403a400802490000e044400240e94020900c0300340410b0303054101840807130002c5101c00400c58205504144821344d8082c441314250750300141c01080f0182002d507118003403d405448011410303100f640d031700300e840d40c0441013215031130303503103a00302c1d00340c1d140900c50441094030924051081e454000d03603100e420311864400c4c0091044c005410580648107420040f80c11200030001c5486002c40e245441c0ca0b1760000c142d1801a00403030318040b500c030585a00000a5a0f0441c45c4942004850424000105a83e1103903a07541d06540b01c405040714804d000e407074061403103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 368840035 1250 368838785 368838793
    0xe012d1e02030403170903031b01020730031a0405090f030a0c0308090f070b0d0e070b032e1202180412030f0b0618010c080a09050a0506030103030e040c1808 69
    0x1540c00e00b007101740300151859440c040208082286a5000010b1300c1c0424a50002d03945504100c460740e600a1081c00b0b402003506014000521013a155802d40003a84440c04a046803003100151045044070508404205044d1000140003200e003025071109a0000d818821901185048140d4a14580000c10b80c07100045c0031108000c10160300a1795150004c0068000f082d040c20a01141c40e1070341e0342c900500540d04c101141c201500714854201441c0380c42c0d25000c1e1840c00d40c80f686e0800300e550003128401e499a4131682050804e048584070348140001e5082c00c80030303040c24609981e610b0200c0d0764040ea40f0043d04041c05418580e003012081c01280304101d035050010740c102016095030005000c8202d927030324140041c00c20362106421100e01404002c11950501150f000607110032109180c0a0001c04000c06c803140003c2c3c0026400c0c0c1960000c540c40c1489035a01c0c404c10886100900000300085c48124020b20641801e8000c000030b501c840c180078bd401d0452a44103040d003081944608003580c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 368841285 1250 368840035 368840039
    0x8160c03050102031506120a050c0405100207080712050607030c1404060e01031b1709013b1b01180302030607050d061d13061404030e010e012d1e020304 67
    0xd50700381d17800070b1041950180d0421807501c01c1c1917122400140101c0300c2ca600c600c0041c8001080d10115005402c00402520340e070500c0100003944c5a0080c080c080c0d05216205000c60800d142450300441c06a004004040d69580e4100440141c252202c0420030300500f00c0000602c0000c41d80a8405001349603039001c031080c15840014140e5200d401c00500a08205d04400d60b51603020409503050007025582b021207841c1c030213141d0300400c42030f024400400d40810f076080e9000040f200b402040504040c0301c2005006000c16140c031000d080c0900c00125080041c2d805095004030044180c1e400424000c20705180d40e900230038100711007100c02c40000740c00020000c40c4140030344a4030300500314001c11030842840c04a0f50394280640900404526036403841c0e02030412001c0d80107000c0030540051201000c2c10245400f40c07800684030b0806000c1141d000800b4220751264118140714040507030401e001e1500505080c084c0001c0504410410a13964210100c0607152450700c00700d036a15078001c43e0303224 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 368842535 1250 368841285 368841301
    0x211e02030618070603020a0e03150124050915091905130b0a030b0c0d0e0c1008060906060a020f0109080408010c2303070e180703050901060b0708160c0305010203 71
    0x181d0092142400010b101d142800040000400c0015140a8100143c0e03480300407000342c52403032102200316414450319540d05c180011008241381203501404569420807400460360420485a81d540030000303400f8480b400280c50460512102e50070b8030a40700349400c0e0050040f48801d41c2c80801c030403400e1f080d000d042005017440c840405148980100c1004160318240006002494900c00506030800b841c0101d403940c0402402c440ea14003034410100026403520400a841349014400c0c81d200da1000c04600c1c031410b000318030262141400608041e010b40d00d590810580d604540c00c07070b204503c5440c2441c20813910034818410710741d000f02035803911a840e040045082d40c4414100408100380708004020942c1070590605a17005000c030500e0701c96403181d0045940000300018154017611002e18132001d180c0102040d4000ca040e0354045c0030968403100c4041c02d0700c9075407060442002c8100134080100d400760000d00500000001c0d00043d50403039407104000d86005402c1035a4903540041408070384 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 368843785 1250 368842535 368842543
    0x711012607020f010207050c0d080f0a090303080c0921070b0d0608071a0d0f0908030c0310061107090203040618080c0d080106080103060905010b1e030c0910211e0203 73
    0x451a1100a5103411802c2da2202e1319030200040c109e01810703060f03408004000c60041aa48444188015192a030044400050601130180700540100b44c0100c041003000d90210101e60700c125001d0318003848150340001704000c3e0603d40380c402d55240500c0c0c00109070306143c3c90003080340c82e4003c1c001040f0703c1e0130310140c130382030000550200307606000b1525020450141c1405445440455450005410030502c0c0c412014100c0020010680c250020402c2041441000a54080d500b290118442c0c19125001079076080c000c4003030000264008071040040c0340058008541c40b900c40c0d500440d0ae00d5145810301801200030390126610000401c0701011810100300ca0b84880c0d6452030f0602041d450310b84041c002c400c040c0400b80001e0b884250381c5090200075003010f803d04401034140c20b08160f0300c0c000c02d0b26840c1c80d903803454884c2c0604443e0880501c0c1050589000f2a181d80402c0740007491b00291200c070500b180d40070a40304410381d00810100703044c40d03051246924460105d0000a90903c101814 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 368845035 1250 368843785 368843803
    0x12010606090503120307020d0f030b0402070b1e040302060a15120803010812040509420a0503011b0e0a0f030f140109030f1107051207030b060d0305071101260702 71
    0x1a2540c140200101c039940050540b40c030f220359040c2702103a1441e0360750483c040d009180e56a80c1203400098180f040102c0c0021080c070a16174207048001c00c091a02000e01008410341d00500140d104202090b00143d00350f1102c151480307041c1102950960b9000b54040e901141141a14410004401000720000c20b000341000c180036503d80350318140c10320300080c2415030040c110020705003a045003040c07243e03410f00c50410303d0040600d46c41805240da201c0b5030303020280541464000e4082c400c2c00280f130304050181c010911a9440d9101101c075080c0b10407225140d49001c8250301101030403000542200401e0b4000165008102010783c0310000c0c20b1511080707140760590740c6580e00d4a010640402e90001011813901c60520f008181a1001e4000901c2c0050381c0e00101da120f56001c18002c09035034001049021070744078021003400b90f03030380b02d04011011108400c040d0100d00c0401950002402c6907980c1c880407001414100321040d0f25825070301b0100103248002450400000a1200c520340400103508 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 368846285 1250 368845035 368845063
    0x162c0d05011b1e0912060e031902190305070b04020f0d0807030305160503181204080a02091e1503010f0c0c03230a081008160f050103050606030105060912010606090503 74
    0x200035541590b0013001c41c0601e20440c2820505460300c0000c0054640205541ca0880403c607078580350800580b440441c3d2420154000d4484c0e0000341051008541c50381460035050307241c0d1800c0004a854184184030018022a4011980015100b05035106100c05c0c3c00309004003c901d032209014034024080307410103808080c0792072144100841c450384c0201260f912000141800070b0804048652514187c00102d21090420000c03078041100b5400055004800e4001c40b80340c00c00d6100c090035a440340c80c011070a120110706000010740000c0c1c00405040c100c1e00f015000040c0e48680650410480f075545500400146024101c00141640801d6250904c038604c0e0b140004048006060074862182c0c008040c18086030800054400100c9507031a00285080001e03181038015071700d00001064014002c1c1405e090032241c01050b075502c00d104041c89a5005800c807455039080c0f13801c01a2680100301680d0307219040319840342c0c840b4000c4c025140100401e03252101c02c03600700000c00d810140c2d1100011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 368847535 1250 368846285 368846327
    0x408070905091603020d060f0c0e0103110408030702061e0a050405040b040c1e03110c0a0c060201090807080c010213140a05031b040b03190b162c0d05011b 68
    0x6069007080043c1d002200d030b048580c200103001034030b001d00c0944201e00c07444100700d151200d950441a0040d040600d49682660104150694500d2181385030282d0b009080280d84180084401414200001c07c0d02002500c071048407640000e404403a2603028561040014102180411880c24580110569407008a505100c1c20091040041c805044150700104940d26507040190460090303029811400d418003d1542d681d1501d12000d81e03400b0a01c600b1242c480c6181c00003e0000d01c10301c640000e0503440306040345018860780321101540c00400074005255800c00c001503002c03c2d60034130310000700034811f88200e800c070b1034908100c203095007580f005000e5000f0a518050503020314103034640c04101102d000607141a10004a03240031a1141080c00c0002800074040070b21003040300303040c03003144800300c8242d0b00390b40c01030201d5170604034481d4040c0c04408900104c03034070b600d105580d17400802d004d03021010610f981d80f145425038a9070030113420050ba0048041400c00d6000e15100045040da000d10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 368848785 1250 368847535 368847553
    0x403080606030a020f0409020a0906020a050304050105030a0b1f0e0a05090f0c09060a02010204091503120807030b031b04060b0403050d0809120c3f07050102040506040807090509 78
    0x500420001000c0320710400c40040011030036107983c1d040d02c4007040001d50850b103403600c414903000250700c01c001241c0881c3c258540000d0162000406400d081c0d03105024608240c502030040d00e00c0d4101414038681940c40d25a0b8040544a1801c8021041c441d52220710103150301c4200076044030904489039024440103078042c48a03481d141c801e1908581c05442810311541c81403a0f202940c02860007259020b5400a40340014a50540280040d103842e1401044103000026011180c1030203848020b02a001c400700340d0004a00503100e1a50054440c00c001c240c0c440c8420019042400c2a501c071000e51202d0394050032541809d204100c060304408004a02d400c1c119110795580e105503079401e8082141d20300025041c010240050340c8030280f41030802d0345452401d0556a190b22101300d000920a8103001c810080312113400c01c0b00c041e8120301c003071030340351510001d0f6285942d4050350303040c1c4040d03400300000691901c500004000414500028021890500145000350b550151403002594404900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 368850035 1250 368848785 368848787
    0x90a0b090a0303050f1608030405010e0c010c0212161701060512031e07170306100c11040e0a02060c010507081003151e060305071401110717030d0203090a02100302030403 75
    0x70700c00352900341c1407040d00c854103c071203050385114440e600441038a08110000810001c1c001660040788500004e0104490b400102c958400c04107040b680081e22a080d18000340c1070003100400c1c3d00024401b0358200014148040405541c0c5a0000715104195481088010401e20030600507080032542440c02d07181401c4199500d0252444140c03075240101e80c4c1c0001301015600700c8040f40c0d40444124445402c1c2c1c4180d440c04d1300704440b00750185250318455a010351252260018882e030100154400020301400d00c401070481c00b41020301d0784241e1050a000d03a0b03e82c1d0240024100b1200080f5141c40d015200820114003d402034440400002090000540200e50a0030200080b000000c000640c010301e02c0a20010302ca4a4490514110011082c803002081d40015a85811080c40c200c9000c00011200c00b003241006054a800502050002042c5072400d03d81c100e40e04003c0785e0501d10080b2988040344c0c41070311500c0340795021203610821424010740301030308101d90b03003021411031500381c038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 368851285 1250 368850035 368850049
    0x315040506060f0c07080f0706081509041205040924050a1a0d110703030608240f0c12070c050706080f1b0f0d020301031a040807060c091505090a0b09 66
    0x480f40a40701c0c0860079010381c1e00208031450003804203804442c0040000d80229480e01c815004000000b1034001c0058561600341000e00403020014005062136642d82d01d90424030346010702c0610030130808100015801c6130790b0150300a100100c1c0503d005807441032070112006c000c0c69100a0098824120800c000494607145040c4805160581687e841441c04404000d08000000f815848808138642c81403540c150300c098191420841168103001d22154911a04060036030044400502d01000602640d000007803181c010707080b02e40007400d00d4403e001072140400c0444d0b803000000c84e2010040c0500ca400c010b0740000b07101e18144a502270234424444160018000d00981c00040c2c002a09100c1840c000304880c80a200b4601e004d0710741d14a004e074900698020b11066031000281d0009400c035120174140c85010790350109240345001c10584d85d03903024090074a1000700340000c4010014080e00100a8480c2507000d03a40c0b00c86c1c3c1ca102c2503040107010000ca4000c000c540c5018820108540c03100d076 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 368852535 1250 368851285 368851297
    0xb0d0e071703181503070503092107020111070504050f250c1e050304090b1e1f03060e01030b010501170709170708031b1207020609010e180408031504050606 69
    0x10100c07000e2611a580401c0c10485480711204184c0000400c1105060f400005580035010100551300281204002100034452542c1e001105210401160005602401f400544040400d040e141226550030000d000c4a00440d003000d05054038004000400e00800346d0400c2d80010300c2244400c004101038020007440f04c0c1b50300280200d800c59100c43d03c030211f1100303600e80b095108044943e87d50300c40c9149005060250103c07401120440d10700801c8031840700324208801d40103054076581c0462401600d4010240030070b1074040c50f6076110049089900140c2050181d4001c001c1420f15515190005001004000d18030104a0040080c80302030f1b5845030000b01220491458100034800550740903003010702582c0550224840001c400550503181d8070b0420650300050700352000c3d403160000d083c2c140e11031030100070341c8400e00b00050f04d5558004e144017021000060a4840c0c6c00180d15a100c3d0105d0b01a5015203242c40c01004000350380f000d403503030848050b100303440620403420700601094090041d8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 368853785 1250 368852535 368852557
    0x703020d1407020d020609090a0608120702090f071e0525020a0501050307120906050403020c06030108030307030915050a091b050105090f04180807120f0e12070b0d0e071703 76
    0x502015010756a400095947c00f0400078038404250900f21640300040050348200000340c09440100c08a582200041d141e02076000341594030182e94004004025039401005a0b00344a41d00641c07402031008030700f807144103000c2c94490303907558601110703000319040000441081110300c41c402c031001030300c581112104542d42802c0954032629031010640780001416441d04809207841390b4101405a07542111340603500036020b48a0b0074011800313009c52031009019100040d8020408251014840c1d402101c8403400b4244290251070707401d00c81c60640390103880c000d17081a10b481408051050642c1000c20302c1c181c6914229182e031034880060480d000303a4140754458407034200300844036160364102e940700c80b000300c1404204008914011000c1c0e0001c24040d40d140248410240700e903401030203003c8042c6401d4481d0888914079000300034426036030203403c038440d01800c0c40004400e107020016040e9003001400108414140c0c00640d885d010b441d61200c110345038441510b40441001004035003110002d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 368855035 1250 368853785 368853799
    0x10090f0911090702032203120503040201020316110a080319020106121b0504050708010e0907030b011e090e010608120412032a0320010c0207380703020d140702 70
    0x89030f40580c04c5001b01102005420700340389640c40c499500000d45002d681c0b0613000c01c42c145c010400100c8484c04216402400360303104000b5038a602c000c032040d4641c0303c1d128a03204500801040082520060309038089081030744042940550703423840e00c07519550f04c40a0710080000e14500040c010203049003440113800f00c040180001c103000401e20401014243c042c2040c0721500302050000c014003424840d58400c610070700080341c2c209030045941c0302240d4104403102540e9081000441c0c119104004e2101c442400da0400100151203004000c8003605a900000d1101d2918440c00c0c245610900c00c503104901c1000305220900600e0b1a081c50a1380501d091020541003070750740150121040065030600761440051820141d02036151b100360811031009500e403a41c81c03400d46080e0b4103070780d68110150300805c0081c00b08440b65100e11180ca07a002c0640e202c10128a4104404842401d140f501d0340c182c0002e289080c181c0400c01a88070001d1898483c82c2040341a02900503400f9001000384940c103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 368856285 1250 368855035 368855041
    0x2060d0e011b020610060305010b04030b19050907050a2408060111010219030e010b0a0512010b150309120406080114040e01021602030f03040501201510090f091109 72
    0x2100354441d410b0b01c0b800198524900c2214000655110740c01c407410420490514008900e5510030700407281261808942181401e00315a81d91540030401840103041507550900d07801d45040c13030701546009a00003c082d200103814501172101c0e00c08180c001c074515007940654030ba550314150007a034504a125280c901c21035181d480048524100400c5001019800400c0c81e06421203040740703111018030741e03403010840c81603046407160980e21880c90f09507001000b28410170060a140100d40419004003000146400b140310020340b14000d102d0b540c180c600b5011003046235040b410002c0359800310a03000c0e0b01d81424a0030800801842050203241d43d0000141c022070031640f6503030004400280c0140096455444002004180d0001a80180c0c428811840e2004580b60080115000c0c2c2c0d00607513485501450000c0c02c03454102183d0700c50416441000c04001b080861050f2507800790507500800172240380b4003080d0b607007a92614000398210b00c0c135044140001403070a6400300c01c9d042045d2880c082c0d81d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 368857535 1250 368856285 368856311
    0x5010201140a0b06041d090c2d01030209060a0206060306060108040b040f02060d1b140306011704050f0312070f02150f0718060509120105040206120c0915030901051302060d 76
    0x20207554054606c0c0031896003100c50381421040307814400c003415821a0b00d150b09080402c0f4000c1410840c2c03007482c0d04102c660681d040040300310040300600605026242c106d4180120705c0c581d20a80700000142c200000380b101c04d15051008030b8200509203000540c9052546804d20081c0e0081c10041441400d28845070441d2926420b5031101c050000341000398524150281c0484e0f48941a00c0f00090421200e0008503034000058a020b00d41c103a441140b00000c8091580d480103010348165001e03c21003035100c2a44804000920400e20b010f00120349604204e04080e04d910308540075441550030424a0242c2d1403e0342c200d46030f2020620850700002c3c0c55440d41a600400c0f50401e02c0e00a81d20f104000c00c0c01c43c0c218008019900c0d050b500d02c0080000d001600b0708070755081d28000c0d4401020803000e100389584444143d08024282c10451034183c0103400508048180120480035880200c200314207464203200d0310b0f03403000c0000c2d0750105d070080a07400900ad42c4a030340e00040405640e00614607a003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 368858785 1250 368857535 368857537
    0x506060906070510091103060a0507020c06070f0b040606240f050a0509030d0906230a03110f03130213051b0a090302191a0c0304061b0813030c05010201140a0b06 71
    0x10b500c3d0769500304603244490800d506c80c2e40c1d1700e40c80315000c2e10882002c2000c042040c0302e400d20803d140d9024001c09010710f030410200da40210300545180c01398507490000f1400c070302085400303940728110004001c2d140119900d0350755914100312030311880d0103c85400780b6400c01503c3c2d074005a103107845650b803607505105403181c0c000c81441c00d41512401c005003580c141c00240714070949a964894081c00103142ca00c00c004020ac009400512610030f000c1811400d01070b411024884840c00b11701c505244441805030903642085540d101c40c040114444015070030820075101000c210803009114030726001400031690003c04041440c84480002e060f030f1b17400d11403590b80024590091140402548140d03400203649000c1c05180d003121803a003030002000f6400c4044403103010170400614200340c03404a0640da42400c0003200856164031000c00c030006107500004021828200b4801030019045003450446c0b80c0c03854110074150380c502400c0c21030400320000e03403580c0550107840120764150483e01090721 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 368860035 1250 368858785 368858803
    0x5090a03080d0f0f18140319091d07020606010806040216031205010f03020a06180b04150f0305010f0e15040c020f0c0a0e01090b041d03070507050405060609060705 72
    0x440040802c25441050700e5400c030103a9104241002c2c00350006814100003221a082d0a962001c0000076900001a01130040c0007068800c800c00c2d2401d08142d090440460030039010f601d000685880303c10b00c40c0c4c1483e501203903001c0c0362900c10001140352a4001070b540e03281c0509801e043c0010900000c41c2540c5540403a9041000f680d8040c0c401c0441f890080e14186412040541060610001240019652100001312034000780314036012880c141e41581d034008270b402d443c510000841c201051203c460030082005000b0860b000480034484440103100314540e07002c8008240c14100104400d1000c800c608042d00c3c035200e42c04802d5256050f08903a0b440310342020076013003800c1c8071040303982e50340205008822200e22010341d41d4080343c6004201700007507036010790b080d0f000120b40140940300c03d60f40203820203440a0000141c1d02810301c0704d000c101c5648901d00d183d607480041d03050b003040801d004860007032000f907034280711500b0700301d000a425000d0321030402d000d03c9001c0351150900000b00000f4213 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 368861285 1250 368860035 368860043
    0x1204060e04110408070311040e0d05030c04031b240e01030f24030b010b040602060703050403020f07090501080f0a0c050f01210b011b2003030715020901180b0a05090a03 74
    0x6610b035500c030481a02c4074824031054989150032007d03030409007828080c0e031005042000c090503c1c4204004140e03905c0d08050310100703007808280804030004540300e0000100c1c0480c0e2602c9040740d803400181e1944500c2444a481c0504480011071800b180c01200d00c4190318802d00340070a1040400c1803001c0103000c00c1d40451a080c0b2845034449030801424039040550703000e0b80105c041c503030320313041e00401d948214031410005a11800018910520a9120301e40241c841e1064803960f00303c03801114980354540e001500b01c1a96540100720000007002401108404200600040d60345d80d1a020100d000d0344c8540c0740201046510580584e205024140d2101010381c180380d103044030241e1100c000c214034010700d80410b01304481d03140f800c07441074a00b8440e240e100d404060f405001e02110140090140304c010303054401442410001441d01a42548404281000607212113007a80014040c4069029100b16920305003414410401902c04403a00703009541081950b803032910000c100c0708101e60f4400f130 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 368862535 1250 368861285 368861287
    0x105130b03100f08030a180302030f06060306130816031107240c0f020f01120c050304050d0f170622050a0605150a0e04090605041209081204060e0411 66
    0x840d2614121001d180140700c5000d42240302920b8800003650004103010f01c0d880d1354010b001c1000080e1081401d2140c0c0414015006c51166880d804070740f0303200b00508807030619004002000628101004000d9110759200d04420a0702841c0d10b400450780f00b942c00c41030440220015440905008916a20940c0a0681150321056441c17000c401021034a007030041a02003000210403045204146000b002d98101030402c0e8454104e80c2041491382d40d4030f1040303042c0495002c20301e007601d10911825102010640720140e5901d407510340710341011fa824600c1030a01105c0c0002034101d036840a004d9158142e4400d1a0019132207580004615050881039031800400d400700c43c614114198011074042d0503481c5080c85901c3d2210f04204030502401090000030300140000051148030322820314180300040d00009070706149840e0700060b640111001e54208605c10383e04907405501101400050511001608080c0004200c02100348075600c0b03a84200403551003208040e0355a6400031413814407500b045 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 368863785 1250 368862535 368862539
    0x90309090708040605100e060f030a080a0309050715050f130b1303050c012a030c020d0c0807090b010f030c120c0807090f030512130b0705101b1706010513 68
    0x60030300c2e40448007203030320320b040101040b19004250170b008262940203a1814040d0740e84410f001d8401a502d050316490700c11405600c000c80c450301c0040800b052555004500c4050300d08000d440c5c0100d9a0007600c0004c40e00d003e00440960240594002d8250301180664541200d900050000321640080c0c041680c001500188003061381c0902040740e214000791458810040010b40e4540c181c2105909000d6101408001205200c07a5008100d40310b030504601c0c0300c0d0a030b0003007014210f5000c0212451030f0010800d0003000000c1000c00c00800c2e4000e8140880c1c05007200007800c8035602800c460615407514941c1d0038181c0551150411090b204004209d201c1520000400c5c1d00b800707403411000f2a40f0b40d00082140c2d0b104103550b100740c036003100041450f02821400d03005030383d1291301070403840204100d007c0b0303601005c4001440b640740200002c0a5450031340d000801200c0d912099044c1c4501401032405c20903811981c0712844c0c0251010316110356450a0041e41c06110300c4180c41100c040f14100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 368865035 1250 368863785 368863787
    0x3040b0c0d0905040b0108070f050f04030c030303050606031306050c040806040f03030b1c1205041a0405180114040507020c310c081f180203040605060a140402030903090907 76
    0x31200c2041c4968a03640d4030b40d80c80c4240710440e25950003050000d1f4910001071100d60041440c104a0056440d01e44d180c02c40a941c50041c681083d0000c5a011007034800403c14590b05005990300084120f07030031843c608002e410681d00164101c4003c14040e21000001e0008d900c00303080e40c00500300d603c181c60188c0303007500d0110841102c91001720046881d103922544503040000000c090700030080c0009002d0040c0f9100d008240103074442c1107081240411000c2071900d107464064842c200c08170b076284d4503681840b040014076070750004464241034109004001081c103281401d0860310050303030b0004541c2c61381c5a0890500003100380f1550003042445406455030007030361a8101440c0c011400d07158110710420840165005104048001541c0b00c2c007045050b0994022082030186507600450566950403041c800036500d1410000515804801c10007441558001d55510070401c5540071645420400300d02c00000c08001c5050103180c1c0800003440840c01001100c402c004001e103d0a628600781388 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 368866285 1250 368865035 368865043
    0x30406020904060b1c0213120c03050f21030a1104080a0302011b0816020a0c09060501110c090c07030306091418010603210c0b150a170a021203040b0c 66
    0x50350500581c9002d500003107002c0c0324820b4821a84a00307030165a451001805807021f5044030400c043c07401c07124540040c09802103004001d20f944100ca0400c2024550304000e400c1081070100d003101500010865041d228070818081312944c1000140c03030302c0e500c80944950007018094048a0307950300c002000315158000144090303c80703100e580207200c1c15840006040d00c200050000102042007000441c640070002c81880388802c0780c9204881e04e0510545401e550a1000c2d8002881180c1d201001e10195912401c000c000c444098014528120440c01040c40000b00030881d01e501ca1340803c528040510942041c001090313003c805200958218000030b52103201927910042d03040c480440207262000600500044030740118800c0c00b0052062031500c1c2c981e200c088864104032501c2010400920034000301d034010320080456803c604040414014440041d0b040360100d14510540340c10038403000240342000300d50590307600252140c0358000034698011600130158a407000704604e006610002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 368867535 1250 368866285 368866297
    0x60b04060b13080a260c01090c1401081e0603120d020307030c0c050706030f02070816031808070b0d02041703090a090506011b1506030311070f050901030f030e040203040602 76
    0x540544290f641c4001c039545131401c0000904801a00004400243c400f555030b00014070a05400d034071300b80c038194400e421611600d500301c40c03200300714501703100d11004000000d980328030030300303080d102402c3c5006000050012095801c40c2100c1040008400c0c4d101401405000306420900b26145e607401c42d44000030790021581000041d140c000314042091058515000396504880a04049d80c00c2c40011006000d982d02d051620940030006800029030714402807815078032645003c0040075640c80c00814141c10b40c07545030211032000d001407096400c0400c03800d00700c0c1c515604441e6140007000100d00a401194028003540d5442d2266044207103011005100100e41207a2011306551a95000800c6036803e44e03219000410b00102e00700042d4648049440e130500403240c1040400e9080715140940d0704070f403c00c0300029440000341040c00350070480d01010345818004100003904100100c0c0c1d22240520020f0407602a00409034245405080200301c3c000c006070040d541d0303180c1414020080d41c480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 368868785 1250 368867535 368867557
    0x41b031d0a02181e0103081207020309100e0d0813060f032007020f09010f06080a09032115090506030c01090302031f1d0a0213050c0f07060b04060b 65
    0x90944140385600400c1d0181c0701c66000b0161102015645200c0c2d00710301008206400d4041c044c164400d0900d521010306000351f20031a00ba580d500301c03146c1180d1955201800443c20740d8001d10441e800752782c3d01d41103007010799a00e14169406403031400000c3c2070400040c81c0a40452400600b007035107191a005e074001911299200e1020640c1e121204a040765a101d00900e55205643e81d0b00e82c00030b8501e801813800c030740010f0260011118402c00a0800384081e404400ea003c00c10104201c0150024400355000300d1070340c010001440c05880c0540089440c001f0101c0e03040c1c0341c88230001411410350003203004440001c0e101d08025100e80c0d03003000905068038058424803070400e16409542c0304101003000e07070781c1c080c000c0c2001c51980d9a00c00005500201e4007c0c4880d190840d80190410f034507004c002d101c14000003402c4212090051003074007682403001c1c042c0d207030501040008940d80001154545c0101142240d5504c1c2e10342007000c000d001d12004164414107100700002c0b0007a240019002168003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 368870035 1250 368868785 368868821
    0x50d0503091c050703030509120106150f090308040909020d0501090507030c09020c0d0513091103070908030313110621040b070f08060621190b06030105090f06041b03 73
    0x41c10380c40603102d240480101194495007042c030000e407145018010784078010708003440c8050322820250941340c054101038690f070007440c858240240e1003a0748000c0640d05040c0201041e056846004151042e400350b01030305070300e5041c140c0031522030340035042c40c1305d40040007080b44007400c1c03070107035141c0d0840e100c143c3d81a01105000316020000303108549040c2c0d0400d000345400e0f40800d50540f519002800707071840c0100740580000b642c8050703018082641460030358080d0b40b443c102c0070207042c0780019049016154024402c01500400c0044105807003034100d4005d640528501c00040c4491060300c0d0101880c44c1640511220200d50740c0740140518850004548561b5583d11f00301d854540544510000400781d00c041a054101000101140074950f0030700790382049141400d404107501920518198640214844a420b2261051600c140d20881d50f252a42d4908000952004005080c0324a406021808506a59155444110281c0301188041c2d075007100e480019000f001c4c0e846120800c0c5503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 368871285 1250 368870035 368870059
    0x102010609020a1b03020705030f0105250f0810031e0b06030102090a1415040807080705010207050a0306020d0603060c0e090a05040519110d2004060e180304050d050309 74
    0x5164026540200f62940d80d601c600c010a41030358a1a548124064081d80030360301d400304403a2001d00161000072441d0703001240b10b04102c17100924402e01140f40b4049007000304100845141d01c8a52507001d010b1034a0028491b854141201041c01401e501c001d0140f9460ba400c070035200f1a0303030214241140145225252540c9901c00d06091748102c10034aa030000b605101440342c0040048041140c0b1009080426070748240460101d00c3c0c0e0241c1c00c1641c0c00d902c011707003c204aa8041046002410007840940b0070b441c03810000c11780108035400020240e5401091901103685260300070002550072500a102c054010030300a80703040300c0840d8044c042e14035000041c070020074070301a0074060399105004240d0205407890341220f1803d40d02040301c0340c0944402c008210713076611417a140300a01424943c86641c08d156400300d482c492a520302406141031040400094180c600c4450313000e0b80c144e0301d0640409090114500b58480c5400c06540042c01c0b00138082403203000400362010520a90707140700050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 368872535 1250 368871285 368871299
    0x7050f190c06150b0a03180b070206060a08150f071e050d11030f041209030b010608010f080d0903030f090b040905010312020601031e031103160501060605070215250f0201020106 78
    0x9007513806186108041000360b1040c17680300303901442d0a41520986108020100e5039162260b490950385400140e121500340b020364900000800010410200101145108001e00c0300d40118020100d0500040c3c01002511581c010000e05040c0e466692504c0c00742050298080c05c190004100030014902e440b0400e00c07100c4078041140d001c0c1460300010302d107943c1c8903a2040d20855002240b801080111940000000c0291200b030f4007900698407004002c3d818040100111181540001c01ca54840740502504641051030b180580380c0510709119000d031440b400352020200c60b84140005800020001111041c951145058074421500c000c6e02d081014000c82c1d55603028080034010302c0f40702074825084d92910b41d00307c6100d0700c40d06002d501401c00ba8025425504403010f060007000c0040503c504001d001c2c403800c4007600301c500341142000c840750041a1681c1d2004086d000a600010314079143c13041c00300ca90001911103d280b1071030010a80b0f4030504102020303400f28055800e080d800b24100f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 368873785 1250 368872535 368872571
    0xf0f05061f03020d20060c03040503061005010806211e0c0301020f0301092c0a03020f0106060906080a0b19030c0504060506030a05060d06050a060509090c01050307050f190c06 77
    0x140e80060800700d0070045505c83d17a490001200d2000481d41c01c000c0711070304980714030014141e00c078400c2000d107841b02d01c2c1400b031600f032803401081c000f004000c0301414417860380c0101d00590031407419541d84518005a61042001d10034000d6822101e00c9041c3d42503600c42e058400c1411003201110a031484001f074030040c18203134042c51844409001c0300b400107000c943c4450f0f101c07124036030070303c488445c03101d10400c0e040500d02070405d074500302504040024000e01d50100032005510522030300821845103032000042c1440340602802c41003062490101d0700c0703040329400244030941d004084007010840941d4802807000548811184c502140c080003030700f8134051066104903500603007141d10b103070b503140700d1100105030041071180d10504134050303c00860b9040c031400740300728841c06000400314100401c216030000c00606e5200c00d60b000040e000381c01e99221040da0780040c0e040c1031843d281c0c4502c4c958408203001d174014071500c1c606200301c2d2071001d60340000c00c90300c0d10b4080d61040048070070b118400825 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 368875035 1250 368873785 368873789
    0x70f150e120102070b0c03040212070e06130b10051c1b0f0210060e060f0f130905190803040b180a080d0f020310050306130b0a090f0f05061f 62
    0x45061140c46008a0811814891440c884103000614202c241e680320b00c4d40207000c0d01c140c10803c6000c03003000210b042c4400090303100e003050f10040486501d003669031045c0c032000400b664003484031042112101c00c60387c0c0054510580080c6920f011000c15000106560003000c82a080c40c40c031400780c50140c04992085070504041807440f440e98082900e4152030b481e0451300b2100c05c40c032440500c4515510f051058070054001c0c000f89007540d0401e0b50410003c241030090b13151041c000c0d010250b5060b981c030840555020082c800c0810300a425081040c2460001d01c000e0703101c01d0700e490300c034020030031044010342c802d0b8410680d000c0c56031100250408103000780744504255902020300c0901244084010301099070500034089801c409030304114043e070b04151080c103d0550994414400d600e018041217600108045262521008039100c000314000301038024286c2d10b9898111906212140300082d21060b08607444c10380c440500d141141d56900b0445079841110307440512040e00c07c2e0b101d022201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 368876285 1250 368875035 368875037
    0x5161b03021f0e011106220819030c03020a0518030102071509060f060308092202040603090b16050d02090a03080a0f090e0907090b03071a03071d10050d0b060309070f15 74
    0x8000d1f036481404a004200740160284648007001040000549000040402520310002910340a030203050280a46591084600500d8014041040026405000d440100c10034446001c594511032000c2402841150800f0380303004200401c900c4242c1341d940284104030300c503407410400308800822160446045000040a03070300c04100c840141d10300521825003401488a1210103a50212011000c81c1d01c1a8070070030210752901030303007c240f045038504154401c83c481d80d81c600201500c80020440e00c44c0386256280158003141100b201e844040c40b800180d940803840c95640e6000d414080e000c080800b0b403100020340a4900803884500709805240504103000041801c17605002e607050103044100000c0384c1502c80c10000050f0f83c0d010302454420351140c01e298541d282401c6c20020440081c44480c0844400c4030500340030540c0f6a120f89074a0007800d86440c50b195046036540300003038240c0601d07582e4000004021320100d00c84c04200c040444010300500144030f669034426001c0f400e11150644 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 368877535 1250 368876285 368876293
    0x61e090b010516051e0a02090109110405130b0a0e2401020c010e0d120c0c090504050a02040b011209060c26071103040b030408040e0705161b03021f0e0111 68
    0x64650080074194a016441343c0c0c02d407074881440711007418401408440f80c1606a00c106841010b60911141c400d0260101c0201880b02c460030469400c06885036104160083c1308040804002042503449550fa00304000c081d03000702540c1d41c03588107002c2c80c181c660403070400e008611a052540300c040d201145a2042e0003601c46000c0b00030042d2000c1c007100751482c1d00040f00100b10400035031902180060b2080c1ca4941d602602c2041c01c00320a51603040d00f0081c04a4a000c040c080070800020712007803080d5040320b000c202004400e004844c0b00455403180c1034aa401d11040004000305a005428242c89564480385415229440d2003505c0c4d15050100c0c502c42e07044004178106c284a072180481a007240811203140c10790b20110045503501c215000d9405140220b02400000003082095030007004034034040b82031080c040041007003d11840d034001e2218408001020a1196148804004640003402e0315118400b03034400414103910189500d001030000b07075019540e513002e245101c000c022043c0086c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 368878785 1250 368877535 368877547
    0x30b010c0201090e27030a03140f16051c06061101060308070f05070b0c06010503070509010b030a0b120d02101808030f1302060301092f0901120f061e090b0105 70
    0x51802c0300000d0000d0ba885c0011450145000b410301c02e242080b151500f0040d030703891005440080c00c607a08140e551500341d94440078003000c498010100c642100d1540c20307458001c0b0500030141d6082c0301350302c05101600101580f04040b0506640403004442075911120b1a06480442142c200c3c0c0050000610000041c01320754003141d1040e40c500c50082c41802100c881a45850002c1a960400d000301441b07684400014405400d080c4400f600910064034000381c43d50521221581e02d000051840c940c1958440d5500c6456403211210001c114440090381d240004d00c5500039100c03680c002410403400d0038000c46003010040c00c410451100d4003c0345060650312503002044e003a60002c6c1910880402c00b030800ca0140e5160b400540c000c160381c0d000020365080c449031072440d017040399170801008900c0700c0103000410164402c43e45c4600e002d1078101da64140120300c00004103140d000c1e11800624020010a44201e00008141c2e0004003012100f503c503500c840840c00c1e12011410071b80065420b000c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 368880035 1250 368878785 368878799
    0x6020d021e010f2406020703030e01030b01020a0c080f211b030405060313050607080c0d0914070b1e04050109061d090403030c0e01080603121b1507030b010c020109 72
    0x50903500c2454030003c41e02a079500086010b445050041c007481401212040644c4120403850b60000e12090025206151640e1000b80c42500d4103c11241410303141d42c4144066807007031122002040d40311222190041d20399816642c2c4854003458588203110722580c00301400700301740b080c00c0100c0f00480c005240038458042600b0b241406018480244400d103c08112550741d0405948240c00e6920f56101100c000c3c140203107841c00c0941020180200e410034001802c00900480d0301510708403202003210f440f1807910001e00d0129540310340301809000e0001c990740c0a4a0000c0144800c0c40c14aa1540e407040c01284407184907600c5248e02103400028100251b60040366003500d002601286500700103180c1340401d8000b40116805c400003543c0e04144400f1035082001e03c01028020b01c5d020704240340c41400f0aa8408043d170310007051301c8000c9007402e850150261102481d50a09082d41ca04040000c1544100b05050ba68140800d007408000308565101c0c0425480700c540594540f10703290300e0426 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 368881285 1250 368880035 368880073
    0xb07060e030d1107150c081807080604050106050315090a110409051c0f0e0603060d2f09131a0703060b0f0306120109020907140412051606020d02 64
    0x2101800180820450844644a01ca18582050140c0f44d5241d24a1400d4188200c58034903403090146404941c0444a6110b176031554888006c0030f8200200580c0c1c0221454a00d4a52003142244201010002041410341081e0202d880c04d400f1140300405400520382444005c80e9800a2035000c2e0180302c0c041401d141c81d8403000b020150000980584075103d241c14000c0281e1000182d008184040381019400151461204410320340010008000c10000f0545d201c05005184101d075250396010511480b208034a40360a001d405002007010716140c1c0544445200080794860640d00b00000c68000b0358a52085403280d0000021440403480186d00c60078400180092040590740e40380860081400d0004000402d11101d946441e0310300b81e810082c03040821003204240c0d0741072040020040e1140c4c030285402c07075030710b04000410640c075021540c924040e035885550040200e03ca1030082c400c000c04c0192488102c0e03542d90326031644510090b40d0390f000060100e0b005074410f0304500a00d10581d0b03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 368882535 1250 368881285 368881301
    0xd111e0d0c0f080d021206030c030d0e06041e1406070c061d03030a0215010b070b0613090602040f05040f0903091203050c010531020906090604140f19060b0706 70
    0x411001c030860300d8548464201d04003130086258005071049020b45070b021960740c00402240104518030019010a40700c3c00c0808442c0e09000f00c01140701c11941d0303844240e5000d4801000030740c00e90402038201242000b06032141000305042c0c00210501400c0c0401200c1d58a178001e8a6111458a8114211800403c4400011609d090f0303603a08030b81c65a003400200444400b90b4001c1440c043c0d0231000501074141a40240c1c0c0f180000c000200000380810b0b89241e00c00f9048600070344948075803840744003510a80c84010003613840000c011422041c0034952034159481950108141a60a510542215028040034000c00c540349030402101003413503407822000b4882d01c0c0a50501ea4a540c076a402c0d0340056800307000100c44103429522481c4a1920300040c3c480c41c6002d030203c6559074001c0b13560018081d0205005010a80c0041d25546490300446803400790f021550681345030640000c1812182614a28199118111440f08605481c0181c40a840c41002613910b00441d035a03d0000400e009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 368883785 1250 368882535 368882543
    0x80712020c220f05040b01081209150a0c0f05010f051f03170d05010e011401020303010e1f0527100503060c030702161202090a0204061b03110d111e0d0c 67
    0x228051401103e650084c9401786115081b113442650410400504000017403011440700072060109550658a00e6000000321000e01c100943d2204042c00071a4104e024940241c5102490300c20002001030540c0011829180780c0d00030062a2520381e003001c107000c40540030b800190400c180c14404541003d0070741c0000ea000400309441c200e0066907030300a55809078852619600d00130010441010091004020444244055491581003001c0f216158102130405144042c0c01402c12102c04200e403a9403018040040454220341511281101c5d403218601c00e0003500c0c074030200866100c0f0214550181510300080c06001103984060120865030001000c00d4114410544080d8015010010b400003030720403100c3c4000302d10300c9070050150f5050301030000040d07644104000c00074240e10420001d600641046e400c0f803000740f00d0808446d00c03898400c0300d110328010214118a0365130010060204c51140c84107031144071540101012010015031462000e41c1c000712b110909040c803030040550035900c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 368884892 1107 368883785 368883791
    0x10050f071106131509140a0902030c0906030711010b01090e070c26040816051c0501091e11100e131404080712020c22 52
    0x2a5020242450601c10752024140e50385034202d510b84180c1c914280c04060b03c0b42010181110032011882c04517a4120307000a80340058007003c005034000804403070070645400d83c008040e600c0104003907220002000300440301c1d500d600103180100460380e11803082e8440944d040d406c448035010401d061105080080141038554600d4030b5000320f152034101500b003000e18149641140d070803440b20000c901e1420407802c01c0c420001a1084a04402c07c0310300d007280000164050840c14054175130040201000c0804022904c101c0244031485000005400740e00c940354044416044007201d9010304100b02600140001d6148038000684115a0920700c400514030203000c1c40d4243c4182401550140c07030b812220030710365114021000da9000b582c59a0320702854042c0711580701800485181801700302c3c25a03ca0300c0092294200e070009400030060034100c503000c4540d00c812150301c0c170445032 = true := by decide +kernel

theorem cover : BRFrame.Cov 368705035 368884892 := by
  have h0 := BRFrame.cov_init 368705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 368705035 ≤ n) (h2 : n < 368884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
