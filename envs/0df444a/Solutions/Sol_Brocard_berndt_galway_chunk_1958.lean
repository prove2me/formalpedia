-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1958
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:17:51.495631+00:00
-- url     : https://prove2.me/submissions/1cb87640-9e99-4895-aa7c-469bddc3a8a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 351978417 ≤ n < 352158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 351979667 1250 351978417 351978443
    0x8030f0f030403020709050c190e0907110a0501060609030308010e04020609041e05070906090803031b280203070b06120a030e01020307020a1e0e0708070e01091e0305010b030a 77
    0x580362141d80000c10440071401020800300d4044000e2080c0d60084942020913904c5a0200054000069002207107400b070117680c0a8010865460b00101c55010b025841c1c001044045211280c1c41e20b01e11a00040155003410400316115500c01011800c490180d9a20001c0c0e980c0c50342c0f031301c1c801750040d1030194104100f0440800c40d402c2c1504100c244192001e40d48424102080e01d200441e0300035151040060640e030340c1041066071000784103000d0200340000d5459418002105d002e0380422001b10303000584045050b00150301c11024041200b84001400100303407100400003922584034010071547c60003007002188680c01d260000c0105000c0040040000d64103c2e01d00f40c40c1040001c41150452004000500050f00c58045282c003d015440c4886082c02d86000110398040883d00b09541104900e41080b446980c040100e54006c1341605101d60b10b600c58000407110740030b10350462000403200e180f5509070018200040fa040320b01880007084812400410151200603851002d001030300702d445 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 351980917 1250 351979667 351979687
    0xb0a090e060a09021603020c03011119020307020a0e0105190302032d07180c0c05120901091d070f0318020609120f060702010c020a15020a110618010608030f 69
    0xa601d822030700040c0a00c11059807a44648160391051210760660a6a0542c680c1007580400c041180c01c032044000348584162020b0704c1001d0300481000c6101401071000d401500c60007030080b03682032500540001e480c03585850743e480b50200c0a00c922401182c0a01418210b01c000700760b2141501d9008000d0024540b42020980d243d0b03008903001c5200c2002c046080c0c408020811140700180300d411090380b00100d103402550111401e0322000001c6c040b4001d4400002030000c24030302c0d00202c00c1032846845a42200040342c1003041c90304103601028a042a01c04802c005004945c0b180c3c4840e90b070b591000e283c04408500b950f52510aa16080584044100040c40c0203009007070380c0034014044280414514000c1460411803000b107140c690058070600c1a00b95081c020010418502d00003054481400d507145c1843c000c0080d0450b4980340d002c2040800742e88500c1c480154400440103e481d603060621080310b100303e411041b0039a5600e00200051500804002d803401402407501982c180010301e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 351982167 1250 351980917 351980939
    0x2040b0c1e0d140a11010606120b04020f0a11160e09161a0c0307060c09032009010501050c10110a031d060402040c0203120705091c0f020415170607020105010b0a09 72
    0x500c669042c0100c00309805d84000c424400c040081420b595030342010403440180104841c15050b00e1070085d401017244000c064407540c1102c6258006103000c0415402202601c2d0138007204072136a44860f0b80110300000d03c00726075080c50f4000d10031441076841060f02e40c403001d0382c440351502c51a0b0050b07442a40c0f0005003100b900180c800c401c0700e981568035141c61940c5090884000614038404240108014014048020300d4407500859039041400301d5403180c0002003101c80148155410004000b81c82201e014050185080090960500380800101007408403c95000200e507080028604081c00c03901107000312025001000c11000703001141c44503000e2102904421405d84198071041029810689040e41c0702ca20030ba0b00d80d81e403103482e0140041042030b203c4105a14001050039501d00e4800300c0c80504040800c564102c50006210540d420a40210040341d4458001115000c5116680c10404200544250b0316a0700810060382c80d61102038007401841508000100040000c3c000f5403001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 351983417 1250 351982167 351982177
    0x50108090304080303011508090f1902060c1b040507050a091a07080406020304090c0809030d0902040b060c0307120819022209020702090903041208070602040b0c1e0d14 74
    0x250054902d0103440e002d0241c51540203030301c14036400650207100110603500c00c1250350486901d01c0681007921074000d00e5507440880011148200080c0d0740d0000443d541c0300100d40c201d5001100303035050500c001460084802003000300c203010760b0410f40010426449081114031100094944900280c18000019440305aa0341052a000c404001a80204002e0710251000308030641c02141c2d0342d403c10b040603003a1044017000c0302c21300c05243c0610000d4040402550341d02c2028800c002000c0b40c0302d00014014080712141c044d00b0500000348804040300120007055107a0260140402c510520f000458405070100c41580084080b0107595980403015001058502100408185a0350131040c0055007402d855000c070244030b600040301421810110011a445020400914181842d100303110300c4c250503c0b1b000400107200001c850003003141e9a815600901704400169480d860245040d50b5030340100794800844d0010b05600e00d942100000d01490050311a5844861454100505045c0c9800c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 351984667 1250 351983417 351983431
    0xe0c09010f060c110409050a05120406212a080f09030a080703090b0c03060301051f0b0a0c20090a09080a08040204140a0c031802061e220302120115050108 68
    0x22a4250844e02d9031107001c0c5244050099000c3c00907401b852820781c0ca0b004814098800124044c04204000758200310f56030520718509205400390341d0034910340c0c0300900c940b904440080c1e00c191910010310b01507020f048003d00158440c92400d40b103002101c400040c1c12990103001d5070042040c949454414140340d07070001c249060101e11911150780e480004802111695035034036000c410008203107003d000e42900098111059101d40640701ba1400c14180d03030b4080c0c0342082900040d48804d1078441d05040d082c0b1500010543c0b503031084e82c074200b8403201303401e10122700c40c1d070003840466100501031054010301c5074044003482c90071400c41016520800c00030801d0b43c1c4984c0e00c60031b1540e52101c001d0000e100f8504090005001c462000c005012074290300040340c645500840414010b80303d11088420a40b103618502d404003000200101792845004030882e040001c80c034416170320780b4090300c2d0389040d00d00c225400101c1d0401c48401c0c501300d5580c8000004581c0701c0100802195001d480700b0f41e00842 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 351985917 1250 351984667 351984683
    0x509072a0f120503040b0c090105040306110301030309050604150309060f09030f1b0308040f062a1d09040b07050d0c050d1b0f0503090c0406090e0c09010f060c 70
    0x80010200d040c811180034007a140015890840350400041c0c54100c03107150201c0c2030150031414580c880b08800480101003c110207070025100c0700e50b81c000d409940095900440c14440303819003410603801600300380b101b1808200e5003c4045011314054058509944401404490b61080c0080c00c60282c0303580002500d80580c1c403008507214204a0080700000ca010307403550f400c044001c4800a1850403c04401184a2220004400000c1d03010b501d1680050b08081881550303040c038242a07005048660751025074440020a00d80c400001901c401c032a20b0094a401111021340d4001c800c071081440070f490350180090000a000480440c6002e82210207498042c0c2800b03100e004400456000b40c1119001c164007103502810350417180520b00042c541c05280420a030142280600341207a00c00200c01805030100009100600421508004500080050001543d10a0303440c0c020240d4141a60080c022303140c40c4001410400101030407140400c0c4596411784c40d22404465004030a401240c00070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 351987167 1250 351985917 351985967
    0x601032901140a21050601090611190b01080d05040b070f0606030b010b070b1012030c03020c060f030703050711030a1209060e0601170a02031507172e050907 69
    0x10648081e103c0ca140585030b804864070b1900f4a0030407600c1c9500440401802c0c1020080d4699002100e281110900d003050100d18540141050421300102c0c807503800d400c00095007905102c524840c0d07a040700c8002003612550004098103c895118a00400c2e11640c010401040000c044600494801d405a180000d485403240c0e91500030107030030303445010060b50100d5584240500c0c6400e140d0170200b00b5020f0700500f072800421803800070100a010f000c3c019040c0385041898028400740c0b41108005280ca075440026079103035103260700b0030354490700020b103000c00003000709004001030250155a54019800e0100e40c1c1c1c0c04032070086400c0e903091865134031156044009000380c0902014900601e014241941c10014404d002c1c00207842600701c0c6910080c05c40d005600c0210314802c0744e10100c0d401b00159520804242e821046200c0f50242c1890020204130b0301c40b0305425922000f0400300031080030907001480340c2201c80c00a00030642e20003a10f40c08035110601804103e02c0142905040c22519 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 351988417 1250 351987167 351987197
    0xf0304170a031b150f02031b071709190306021312020f040e070b03040c06111f0207030314040510062c0604060b0a110d03051e18030a02150601032901 66
    0x1441d107141e014074421b0340210902801c1d1207038241071906500c013290b42c90b007001e0050b16265000100c441248000a6001950f1001510750305070f41d070010180c61946810441c0d4074500764000794009c0c5103402c04403c00040c08903e40d40c0c4640001e2040350010040701608a0340320401c0000c04002640c043c50707104803036002900c01130f4040558400c0703005842c1003400d149444005441401d40b044d203a0110740160381210f000040238412003650043e0241c0041c0c0f0303800c062405800906100b81c2a042c5440c124003000700300400001c01d9101d000400300c0500000350b581c04a25100e0080c81c02d4100003002c0c500d20183c0e2401444a180c0d4401d10080022440d69035504021000307610a004401c00640c006d0501114540c0410807506a003900d480d0801c2315143c4410002003400f070355100c00c841c05502c0c0000c07445140c164161078016032200d00c240d954640b40000c02949d03910302103550161400858000503c19800792191111a4880024030f41070700900040406407202a580c950b414000f18407626001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 351989667 1250 351988417 351988421
    0x50d051f0e010908091e0a03082b0e0114090c04020c011503080c0708032a2b110303090703030f0c05070617091f0c0509030f0304170a031b15 62
    0xd401e0040e1400c80c1e13a8031700034040c0800070390301e207050309204680c5690341036845d02d441841e20202c075040141c20380c86604901170403220303092a034400141d9040600030400c0c40c400640c020b5800291150003044100c0034081e1007080d110301110412031503000092030130300a0a10780c009000c000032031000003503140070507582c081c015400e507003050300d20000c00f01d08004207480800c091400740028030000c41c281454201c07059807040701c00940ca0070010783c900c88135101c00c0040207080301082411007a400140c00d2001d400d00420303900440600020505107004e0f13108103020080301c0c00f03005520050000d05045807420b03501200c524243c0810082d07100e04e42400314400f0700c9200c0190843c0e50304c40c44080c3c0140328140251002500d0031200b908110a000f41d00b07512079451110080c542440400d00f4410500d0698007030054480070794060007120307602c04c8212000b00090040d01c0303184601050485102c00540d41d00c1e5409800200032444010080c0070000010364003a0070681306001c1d4144004002e915001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 351990917 1250 351989667 351989681
    0x30030703021308010509060103150b10030c12090206030f091504030206060f120604030e01020a06180209100305070302042a021b0d081b01110c030a0801050d051f0e01 73
    0x80066070109021082030410410030000b07005a000030b0000e030030009140364603101c043c0b10003400e40d1107040840801d00119009400b102000510708401034280710000781c041c04411035494009650303059021240820f511494805c035401078100c0d820750b0b4071201400310400d0b01030040502485400e0074951b0401e125080103101e14800c1d4003400560070035070f085c0550890400c90340d503c42c42c084100c070099410700003030b03813a44107800d45000f180036140600140e09007044404003030400f41c00d1000501d20500000f04074009148251020241c690b60409401c240b42c80900000700260064501040945496041003081c100e0342d910304145250303400d44484074200c4072840000560000036440c1400011000200c45854041d82e466141c20400c1d5034040140c41401c0d0541007104403204d1a18948000354001d114442280010560351005110b840d070752900035211903400680c8220012519080202c445024154030400400b07036a0508260000024196585403400c1c2d942c1c0d0000400348503090041203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 351992167 1250 351990917 351990931
    0x3020a0303090f0605030c0909060f030a05031902070b040b03040203010213080a02010f051603081b0304080c06010501030b01090302013f050f0f0601080711030301260604053003 78
    0x400c1d610f000405252905a0782c80081800424400c21018a10500454031005011101c2c581c2a17a6418006003030103091940c4513416102c0c0100007410020000700503d03a503a0180c4c8007031060010290b04076550388a034003801590010500c001c2007456181009190011310007000036040c000b004402a07419450f80d400850942e01007400c01055507080308400f10300003524a042490880c80300210342c121403190000038101728241000407080640c03194a6803007060642a5242d80c1d0603c5c0c01c1100740c0d9000740314082c0140c0200f200005083d8081d10828488081c1a199691440d2854005440040c3c091019040b0780985281da901c1000484448041c6000c10003d440d02c002100001d980448100600c6001001d014006005c20b400c1c2200c1e806521260910f0400c210b82c1c1d4190044802c80c850000c1c0c2ca1031440080008200e60240840c1500d0040782e10b1420b049503540502c82030f03604c42c002e0b42c0160094201101400e0f0b04c03903400602c0c041164030340900c00303141c0898128140306a40304850340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 351993417 1250 351992167 351992177
    0x504060903030c08040809060d240312050405220b0307060807260103020d05030f0d0b1203030415110405060409090605010f030b0106030b1314041416090c0903020a0303 74
    0x100304142d00340c880d8050248244c58108058502551041c400b0710903624401d21139400410082c0302584141c12031841200c90b584403024408030824020070a032254081201c0241030703040302006091040701900d040b18802440c0c6da80b00c070f5501044d0000000305c082521003042d111511614207446c00c101d60002030000d9a00ca00c540e15041000030a810781200407081001800181011004d00c90b100040c1900d40444400b281800c280c0b604602c2c42c071828400c07003540c2e10003248502030648240d0040380d071a6815106081c00c1c4619503001074a1344011100140744011280c054404040d072903000e11480c5801c00c8205240076210400a102500298054400561101d070007000b01b05d0300d0300640b4010408860040e000904507a00c800c148603050044c00e0402d56501ea19000e19500c2a0f12110101502d007010055030810314a17400d0300500844094a07250780e100080c2c1c034080c0c4005071000c8201c0744111491020340c14121048040e0601b5001c01040102c83c0d6404030140e0b03940140f00c0000c611030389075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 351994667 1250 351993417 351993431
    0x3050601110609070e2a090301060302150c06070f08240a08061506340c1205010c08071407020a03050102040b190801062a0605010b0d0605120d0f0909050406 69
    0x940c00305c003400140f031415148041c1c0e400e00c194038401c82c40090f080d503609a00c181c82e1403460020a00520300343e40041d6001140c05a078403084140c0500030000e0540000c1960185e60b01e1b03103019113840143c400c003900060205000100000c10b402c803585410980310194000000d0340e6400244054401d03002410030350041c8003804140350b203e0400301c07a25542660000d05116401922080551040340d50f905560f05c0e14a5007992a07460580401c0d01940c00300000c2e40703154660118000314244214119182d40c0b0b0200f2003503c16002e40d08140c41071038207540c0c0f812404900c41c0845001e4200480032030300101142030100000300301703002070700207001d402e003920303031280b101029078045000f412079583c0c144652400144007140e4000d400f8018130030814400b1a8210602d0901d020304480c0c0c2030040c0495180500200d80d900074000140b1404240800c103105190300c400801c01c5810110300c0c1c54040340e20958070900100d00410101d00700042904107100255078403d140d500b950004c50b0100d80f01903660782 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 351995917 1250 351994667 351994679
    0x60a0b0102010b0d0b34030e240705070f0f060902031504150203090a0b0705040f080114010e1e010b071a0712110702060d09020406061d010305060111060907 69
    0x225141c030f0100b0454106005070b800d5103a20b0351251001d082520a1050800b08880180035414800f103101c0d0500c214900e103e4400c000100104803038043d410b99805a40c2c1c0c1e40c07a5042e41d010040341d50b89030900300b0040c0d40d125110b041e0703a15440780000319151000c91074400040340f000c280811401b4003071980401c0500d0140304060800300c209085141e0b10281506000104158520070055000c1929005a40751903150301946400c1101e40001c11044420081200a40e4030001074000c440b0b100919211194a4603602c030f00ba5480d180b030f40c003020580c4a0042203039926410803590003418644030301c1d180e42c40b106c203400e965003801d8000140b0409c00140032400c0004030100900c0c9100d54800300718880c1001c2d2401440048100d000c88006c580355608800070a0152040307804890340106042d40d102d142c1800742d0050036800740164401e514000c1c0004009000c2c1110178072041030000300900061044d00150700a00b03000e05036a0400c01400e02c400c41140017041030324040c1004c807000301ba145140207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 351997167 1250 351995917 351995921
    0x40c0c081303110d0b01030f0807060e070e0907030f0b0703140c090f0402043519020f0616150f020307030b03010c022e0b04020301061206060e0f06030414060a0b010201 74
    0x4040740d1300a40001d80c0b00804120202c11443c19240e02c00c0f08000c2d18480f50601540070f006804001d01564a00f964480e03072108001180811070b98030500c040030301e94440020a403030f032003a80702c0500144151085c40000030024240c80b80d100300d950500196000600308010404601111174400303594000842000300e1900c4600b0842d21502107030150300c1c2c2404c01c031048440e020b295203d92900d8850102280321520304800d0f020990030404129100740501b0f000314041c0350300030f00c1c0c00d90248619240c000b03502d00b4914201c84c0840c1950083c003085001c140e4514090402660390242d1050303403280518000c9049000450203025181e030045660144e1504060071103084884110656200e41941d2030041e850446c640c2d1040c803103010002c19020440c502e000a0580c400341c40d9803003440080013081c8180c100c90304080002500c2010001c0b15103504043d0350080c04041e406038401c5d044c580a01e03182c5401002168094440e40c414803d00868007100c91600d942a20030089103510380091100f696424 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 351998417 1250 351997167 351997193
    0x20415080f0f1302091504020d060f080d020d0f0224040615030c0b18030607050712020714041e05040305041e0e07050705340905090c040c0c081303 65
    0x2510400c2c941d081c800c1244200704030041c8024001c80030b050004107414200c00361203020000282c07040d90f070740011a20b000010211030251021388910301314007182d03214001030508100c1810360018020921310a001b61032a003c4c1c0c000d101e0851150811440d869083c500244480b00044c80b038a0340e040c00d1900e41082a141040c0c4000c11444402c0c504001203500440035808468055441d580d0310303003034070301d02e5178800610904264151107030105020035294040c00524545010b5800310b1010803000c001262981c00300d00c14000001443c400700d107014501681f050701504030034480c044800d501010300c0015100111020307000300c0d402240402900c010400940d11000a21042c47d15150815021055000024100008204010401d90101705041000b01c3d00e128203074a01030221709a82c90400700c0f140c01d41014011052000000060409641c0034550003400c601010301842e21480d002d102c01050b07a110007600300004a20500041400300004140c0d03900c03001300d010442419828510070756940 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 351999667 1250 351998417 351998431
    0x50f06031b0105030a09020402120108060c04060e0f04020712020106050406080a0c1703160f1214161b09090c080a020a030b06010203120a051510020a06050901020415080f 75
    0x1040050140401012200201c24003d08140c4d44a440e030303801c010b006240304400250000d200280e48070008080300302143c1252600c10898910741d03141098179801d8000c501c200c802090140161021b00d00d0640240000c41d00c01510040c104a016142e00d01c0d1400c01107051400341c2d5507002c0c00d100c030b41058020003010340005001042c2c040002d58540080040c02c1c4104111a02d5141b00200c0303031401481106e0312002049158014100c89080c01840300c5504a4211800210a500512040c0c06001c2c0c1650f65a18941e0103030510450b1b0305800480310800d14100d54039124001e00214001c445640c10001d40400c24001850140c14500a01c241006401180d501e50000c8034040050791080c071a1800d50740c1c080307461062a200c1c03400503882c1d40207181e01215809d041c0c1d001c1140403070031076114a100d07030224948541040032002c2032104226080c0c040c040143c12031f4901d1004038001d81c0100360499081e00005160940e21415517007040d807428688400034180500340f12880c01607003182600304807 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 352000917 1250 351999667 351999673
    0x5072c10020723060906030708010e1609030b06030c041506091706011206020408120d0b040e0d0309030908060103030207060f020606010e10051e090a0603020c07120813030501050f0603 81
    0x1003445080442c800030000c1e209503001d440800b0b42c030b007a04c400094818001000d025a5264101480094102002401070b800512100c1002400a801800080c0320144141e2191f6041c60305688803e90201c80003010160544108580342510307450f244540301310341c1c0004140c0e4040d030342060780c020903074150380d880030800050710415840d0454012800306d04486010039042c01d4181c140c40c1c51400f030b0240380c0c410b500301e001d41514040786506005c000c0c00e651415041c10070001c1c1c2000b00700070485420001c920140d0b80050002a40e10740258030201803203019003420050155903c0c201850319900340c10072801038001240c1001000e400c402c20058103141d0340040e04551818100003810f07265036030001889100f000d03259808040c016400c40340101c0e015980540b030800d2001180f516948926583c0e40613505156000401620903c20b0340d82960140c1d02420303183d8901010800800714407101079520300402c008201c002a10788a00c503000710711030000030170245003c818100c600c0d18014100c90286e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 352002167 1250 352000917 352000919
    0xa0c140d050d180e01080a0221071802070f140601060212072319052505040b0109080d020a0606060806100807120212060f010507021305072c100207 65
    0x100042030070b190325082440c00121807503400100c0e0000030244da10074050b07101c01d20008a0960390100303480440c6030081d680080720000c402c0b05856107003a0000301d488142c01c0717903500340128080071600c0002c1c44038910300981800d826484a42a980f41881c0482e11110a580000001e040c14080c00380144030500140401c0401e81c1102c8041d4440c0903001820b1030780309018079401a050740c0603c0c1004100c24100c4a071584800003103800d1002c115401d03035203480303041030a0201e5085509810310b4491014441320540c2c2c94002400041c01031652242c0c10710040100103d00306004200026615510303038000c0101c905c550038241e0403101650000c20030071000030304000310ba8907a24030004581e0f005260090701a55a150119090910300700358054440c00003031448075a40d080c10240340181001c83d02c1426546080c3e005580b103100d0410000c2d0084000c58412000c8102540541e0303014a41d81042c070702c07a6450030040300404c40413454004d000200105a503501382007680c060f03440c414060008001032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 352003417 1250 352002167 352002173
    0x605121305030f070c0909030c060510060207060e040207121808120f03042a03060f090c1a0d0501150201051803160c0b13050907020a0c06050313050a0c140d 69
    0x74403800c4004200000000b41a44c10800d03520103202c024948080208030003000e034a001031016400c03a40541d201c03410b21011402070102c1c0c10304c4404541407074004082c150300d414026a850014038200c00c0d07205909118480c08075501b44880c0a020011750380e10074070200c0404580c00002101c3d040761405910074243d15403d0440d540c1210001644200303881c0c0c4960710391821104145c072000d8820318940c503140f04491000c58030140602500d10604050041035000100c0e50100c8841c010041d040e250752481c10400c10419030104030050004c00700e424038160104819409548081c0c1c003000d00005182c180c046629820b202d4250003040360b0b503070401c03540b92800e54143c1d13034028104840c4001e194000c5201c208494240610000d0584241254498104108051308178030365214440c040c1a880c8001400d00b403011400d204016802407041d4829420800112000e03040100b0b40c50184001c0a44540401c0702080b644d540c8910a002100803203081c40048614043c40144490041807419a50800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 352004667 1250 352003417 352003423
    0x111030a021b011b1209110111100204060c0c050306060f040f140c07050f03160308130501020c07050a1d0c0a0302070212010911060a050904090213060605121305 71
    0x20808100e00035854900c022441030086500481c01101c41d8600180382c04600044250011010402d440365200301041217009010740701c10100040c00b9032440d411004840d03004110303c1c02e0f41d108400c11628164403041c903600884c1e1160300282c020071001004070040160100c008400303010250301400144c10500b02098140c0960206207110380d0301c40e00543d01300617155020791851346034140b0060713090501c3c41344140d09900c00303581604c0a010740360031460281000821030f001402c0030312002d00c0e000641c0c2c0341282d505102410303100d402c03100c04095401280c0b090002c0e00050501101400d8040d29200400c502c14100d07a1100400641ca0500c4016500240107026804100b00e8401681c07003201120481c020f00c0380d01c00c000d42c41440100000c140b074405501c415070040c2b0a2850100c084006402c0210502603208400002002048082d5107420719801a00360144050041c650030b403075844d41103041c1e4085802a10000d8030114103610034021244903c0d0300a0f0018401d80c0505041d6280c00c1c0e1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 352005917 1250 352004667 352004671
    0x61302120403030e10020409061e0602060f071403180d090b09041806050c04090c080c0427110a1b0803010b160215031905160c08130b0912011103 64
    0x2050680c2c41400700c142d01307018400d5194401e18403108654a0344ca901c0040000c162500400d440078208800114041d015080044242c1c1c0c00360b0014541c69507809841980b2540080a040801c40040b14014480013100095030190921441e10090046803a101c0c0d03141a04c03c00c01c1c0020003440314020410003648108031070703038610250b9001c41c240c452920003003004001080010400c030326080821184c8c1c0d000303c02404c141e030038074002400703a07006100c0129007081c015203007002942c070304200030003aa110307402c203000c2c04299041511508807880030004040b200c41c2c04200300c0540c0300082d82006039a00004449400d00c11088a1503000e446403034010305ca0005010b0984600ca002906100f070004444500403115402440e00f42d044c170a01c5511701c0c054106031a035240701b220080300d46d01d03100007601900b4424803607842d640c00c2202002c00108c61288902c0c1d000e6a601004014203800c9049141c58000035155503011590349441c044144203060440a00044c400d0345840403542402c00b0082c100c030307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 352007167 1250 352005917 352005923
    0xb0307030f1101031109132702130c170405010e0a0501060515160305160602040f060305010e0f0c031b040906030506090d1b0228090b0301020702010e060d06120b0613021204 76
    0x10090807411f4001300000c0444800d4a1044690980020500904c1c5030300022040d00c2a034166100420103040482601c16201031100400d1040d4001e80700800f1500c402c40d0300c1030245001183c0d10405a0440341851030b41e04094406135111320040c0110b0401503100c01412030072800851501e0249151540401500a0014100007000581045246110440b030501c140c02c4a0210b41e0f4644d50501c541a080c0c80c1e02c00d8a011030300708000000c44450b1920440c1c802d0751020320328071107a82c502c82090b100c2e0b8070003021210166205030100c01540e00d42400351002d080c04da0400140329003141895480d10000030450070340359102040f2600059803000b884040400d60154841100e0b01d1403000800031032001e245c0310080320220310081d140d210344240000459546400800104001d003081c903003030b4480c81d540a0701069080741d210703200c4c2c1010001482000d507016000a1866103c61a101890594450656000710013005008080c6020300030035900368414081149440b05010304c1d000002c1c1c00074005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 352008417 1250 352007167 352007179
    0x1b07020916110d18092715020f12010b250314030901020315040b0a052b0f03030e0105043305010b070302070e090303190b0307030f1101031109 63
    0x2208605008190b9040e0303890441e02560110f041da03140040080341d01540355200e082d1450700000b891907040c40740d0004c00140e085280110404a80e40c0499060f600004076040141d421040e003000b8a640f003d00841c0b110a1606640d91000c1003242d2030350351043c4c0000020040c1000284000d02a60304440c2c00c0d42c50b4180000b0b42c91226043c2903a0300a010703243c031042c0900c00070411505120660095205402642142e241c1014003030a0000f1650b9052520f50840700c41d51003030202d4500129407002940c41361000650b2207142c03c3c0310380d4160106820882d01c04880924906c01c058050050001000014002b000705140030b48032080000d6407186504000d1206400d48104414442d1562070821040d030014822565503100800c010360060b18180d0043c0903921011070300c0060920342d903009a000100440c01c41d2542103400614805281410460b1692001d000640c0c2d242801000c00640c040d0303280b001980320505001c1f0850342840c055a041500c0c1c049502d048402c0003081d03030080301382030340e20b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 352009667 1250 352008417 352008451
    0xf06070f08160e0d1e0b060301150522200702130e100b030f010507080105031203010b03010b0f0c010c0306090e0d3504141c05070818090a051b070209 66
    0x8000c11758454450703c000c2403030700030148409006040034880e01980e0f007a0020080c684412000d00480d5506000f21035022408103406004404202020784000410381400503100fa0b40c15803807060000e500c0e1a41d0b80c070f540c0c085114815450726119032030743d12500c20824014075000241d13064450500d51510614281d40c1c1d800e2112544003003054002d0148804000c00460400c80e00160965509104052080c45a40c192003403659070881901e040b035600f1900d02d41581d081c0844408181c20400e54403d41d9030043c4903c50300c09000b40192580d28100313490004015060110010646170010011301c0241e00502030440042d80c482c80701c005000360250050704003000070b610201404580350303842041d02540e070244001c0c88584c04c80d1400ca83c240c14110346810a1180102103010600c44004000c9030050000c100800d8030b0500400340c86c0c500002d11003403c40000d0008942d500155242c3d03108641d200d00300b2a1700e06803c107030105001d400502031401c1403030300d0340002e0309c50364000c1c000d401500030204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 352010917 1250 352009667 352009673
    0x51e071a0307090e090618010b030304050405070c17030106030c030903050a0807030b060a05220602070e1e0106020309030f0319030b043c0603080306040507020f06070f08160e0d 78
    0x80b800c030140c81015072141c4a405c03c040782d242c1c2e506084d5031801d82c00d21103142d10000c80d00144500716a03440090b0103142410b20384000c0000404004002c40d0030f00045803003c1e000a00ca0754490450540e081250035100e50500740024100e561509000090600c3c0c41d181001183d044825640b040c1503070300d0100b54a907240d4a08401038424040711580104001c0750007450107805c400038082508140b100d140c0240d404c0d01c0c1242001541e03110720001b58104070001d000600d440706c04039510410440c1c403004020322944881c00c0d1500c0c26480040140c00100c1c003c000d5182c284892a04c40324044002d508010700b44402c60ba06503603528020061540c1c41b200304866481e940c010100d0007000075020445141404007051620b20804060090741c1540300ca841080003042c4106002d0765000400c0c0c500b10303030b210820302c4001e14024003003605602c14a810030070907103810002541700742e409681c1c0e02c100001c0e10401401e034140162a03084402d52800590400c6680004290310401040310400064410f0381 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 352012167 1250 352010917 352010927
    0x8072a1b0914010b030c1b060f0702060601090303050a12060f031a100b0304030e06070c0b0c10050910110c030f04030b01061704060f0e0a051e071a0307 67
    0x2140144280d65010410800c01031000c2540201c4030800014030640440c070001c18041c200c00d002d200c00800c41840466a808610700181502c107d206481103070004102c1d0529280071402c035009005181e01d0010015500d03414081c0780c4d000741003801c000c8141d42c215940a052405800180741c100441341d0b0182d201c02c04d864000308010204001440d42c07103900c9040140441e0a000440c044080102c00800c103800401250170080766141ca10785400c684071079400f111440503c240c465071001c400d12180c00418010550000188151400e840d40c0b240c60028883c03c0c050191824415589080d041180c80d04022629102008000c0800526100792603000001b45c001c1c00b940c220184030101d005503285c0c0c40d0a00500503a030203010340080c00da0340c8210880e600300b00f0702c43c1c0700c3c0810100b001040c0015840d07000240c000074101004507a01c1c00250006140920a01d42690796601048030309081d2056600258100445007002e0103243e410444221103121050b10002020900000060715480c80f407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 352013417 1250 352012167 352012247
    0xa1509050907021e07050312040b07020105030a230601030b0103060501020c0907020102041a03010609091a0f04021611040b0a05011707020c04020c010212010b09012f01090f0b070807 80
    0xc91a0516a03030404c00c21150b440295000b802d020780b007008030340c40594429100b44e40841e010003441c64585010f036401181d09404c09416410040e03150741c0002034154400d010b01c011314182d1000d2800d02d03e80280010280c41c00800c000f41810f14010040c842c03079a011034003078103070769042c1c40140c0c00b81c44240c01240244a580d01c40c104d5000d4015a10441840040c0194102c032215641c443c2c0b060344883c50302d4119a50505143c40b40c8151454100503810301881503801440001d00040c2850040c41c82c1e07440c4034041c043c04440031403a4150050151810b44103480d58008181e40901000d0305200c0040e2801807003030b11003601d0108a40004002038406c000026007964043c0040d921100904081c078081d4000b1005200012403c000204d00b200d07021050340c2d50030005954500c03a00c0854124900d078611150350f4005000c1c1641c2c482c1d20141d1003405801240e611400c45c5081100032400d01c10384003900031304070300100580c050610880d164000003105140c0c01580d100552140c0c0540c49a00000c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 352014667 1250 352013417 352013443
    0xa0807032901170c150a0c051e0d030e0f0706050f09040c0c02030d022a03070f030311060f060306040605060f03061603060807030c030f030c0807060501050a150905090702 75
    0x141e000400e151282c8810a1207160100084404081d0040104030010941003001c014807a000d1001c060064031036001103d10034080c2c81900c400d0001800c0030603a2144041404d0000c0e0700c5261180b050365070520922040b00859000f50100011a50312151144c050f8030804041220102d00051a6101c001c00ca034174400d40280208401d1242950142c07218160300c40a074420302800750081c80300c50021030f96640c4600d00c441c040c100d1285040100a102822040c4031f42c145c880c0c12000700e8030101c84030b4100060341c002d840b81b080d8054030310b40c0c003494100020300c1d00003045404014444141c400140c803030b030071682c010400320b450f641b82404107003001040d03c00c8079854810601841520042c020300000b010708682d030184141600e89a074266101c905110003020301d11107810800109200181501c481d5100e403821074284240c1380c8602a9a420100d82511a207698200401440c9005904807009005940c50403100e0440000050f202d60b0540c400d882c050701c000800140070a20078400c3d400143c2d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 352015917 1250 352014667 352014743
    0x201170405011a0103021e130e0c0310060f05040e0c0705011b0809010603021503040c0e091609092301020c0d0503010f0f0308030103061812020c09060a080703 70
    0x501814854040c041e00103a4801e903d21012401c0c441d9446030088400c1c040c00d9011655101003525074003076190340110401d134100c034160b0390302040f044032070600c2500940040a4180d12410002e4811750346002c168000402e020003010800e600d02e170400c0a035821030340600c0c1d1446299540d0032a0000703070302c41c000008165500c2c0c0041c0140d00c0a40071006e44048043e03179507170b407160341d25490400d0072601c241c000a54049010044800400c00d814000c591051088404620255075804c0b101e00d50142502c405040d074000c4c0c00032225000c803140020004200d4540c06000e41d0b034060f01c03071045e40c4041c081000b030410291609040100c5d401d4045915400f084070841c0c400c1809208002e1254000703024030300b07400c01c000c080081c040f91001040c0c2d044d42d4004410f14034507461603503010018a08100b00c00140b501e00383c03038100451321101c0301c01030004080d00501004540e0340d0400c200b4040040600c0d12880d616103003030001c10400102501038070f5201030388aa400841ca00107909089040c840410400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 352017167 1250 352015917 352015921
    0x305160803040312020c100e03041a030901140106080408070507270506030109020114160b070807022505130609050103063620030111040609091503030507020117 71
    0x2a1500055124600944d02c92001d5071550080f01d084c2c1c0300e01d00d00c2c074110341d21409140c00800c000c0d41c0402c00c0c1142d8032040782c2c6069a00c00c3c414081c040034022400b0300103008010884084428003031070b04100c0019038024020340c1400000b400444014001030315a0001007050700800c0b0042165002400484410101d100c0110304d050880c01a442c068003902e60405010603420304050051800301c2d0382c161101401a80705041a0340160440003142c0303d0410254000000714200e0f000481c01102165682103107881d28140180c50102a1191303840318100c4420041c02c1c40740940221030540d03800711140c80f444446205c0b0807000c0d0020350003660210303240100010030800c3c1c540c403520058034280c500700c80500402e0b6000c00e02d0200c0e00918052412402d81e440001b580d071030741f10b01e408500000c1c0d0300706a42105020a007100c0074451180b51040780000d0501c84150000c0b9130340e0080c45141c03400d008100d080790301107482c400c0611009052040100c0e5520440e80100081da41d0b4a4890115402074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 352018417 1250 352017167 352017173
    0x6070f12050f010f0e10030209042d061b0f11070807091a0303031902031003060212040303050c0405030a0b09030c0d0207030c050f1f120914100504030f03020304030516 74
    0x540b400c0c403451003200749107080003c0003071220070210b00c85c100303181e8904030440c0303940c003070015155006004844480c02d0f1a50181000b005094407824511503a4803140010224500782d81114805242074aa115107070048010031940220b505256440d54540000041c1c41002d17594a8801e803a000024207000700c0401003004009640700c0d001c1148010745094421080b2024140c99102c25a090450128050000d22201002c0d400030340d0000854402488260364030340341c54040707800090a14280d0035101050006065140c02219002102c44403480e01d0316240c580000e59901e080304004040001407000540200414019214450400403c2d0760300803404030300003500ea694600013190b0903030b00c600b4085514144a01d00c2000440c000d402d2084526403000d00075002c40100e024902001241071101200c04280c4c002c001751548510b445c4040410042c400d03900f05208000c040746024a031008220204c0c0c1d0020040b140c1d4802c6040041c0d40742c403a8101220144502c100005050580701460420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 352019667 1250 352018417 352018441
    0xc0f130606230301060801060f1b0f11030c061204020f03030a05040305071202010e1e15070c080d0c0f050f070b0a260c09040605090703020301030308070206040506070f1205 76
    0x61003640c0b81a400c1e4500d80380d00080341800280250000030300f0b101d0052260038000c2440025611090070801200104000040001001590206e0301280c1031007d0a040010711003024a907843e0880c05070401300e60b1103001c180d06014010b00201d20a1250001c2020340d212a10700001401c400b80c152565010682409042ca070301621088540d0300c158a400503000025000c1c403105954141d4500040718844410090f80d042d1491071140030400c3c0403c050620358500c41c00d41444040e5081e050303241c030440d003400042070b00740fa030090310140c1108090451559102503121100c03980481a110403641c6070416500c1d00d00704043c0780700140715910b0003084501800001d003110307034240da440c40102c01c801e4211181101c040009502544000008180d10303145000141640c1c440207080010100d9503003001403855481524401c000c80d50000c010300c14036910244203944140c05000a00e80380c105a03540f40c1e0380d0000140384c4003c03c42c400c44508560313449569451041300d403464081c80242081945419 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 352020917 1250 352019667 352019687
    0x2030c0f013e010c1106010f051005190f1202040b0d0e1e03030105091302131a060706090c0b0f0a0e011205090c1906080a0c02030c07030f0b0c0c0c0f130606 69
    0xc00301d403200c02d2408000e54000740c61410b0b10b02403a41594258a0107003449103044450ac205000d01400340042e40740000c500c141010f02c802142d564000c220b440c41c00107800301040c40400703010b982c01000f0600107000010202c0e481c1c015061400550304680e5481d2900701000344c22600a42d80401c40d10341401d080c004051410b8404c202c40102c050b4441302c1d06002ca000407500020340164080e0460110390500303030b000181940301240744861082440c00019035580c88018216170b40383c1d0f508419401e000d80446c04601030b00010b80410b19103401c1601e040c9480c0681e41a05080114403155042c2ea40d1140405200c03016083c41c0c10700c41e60400c00640e0f502c88e500c00c00428010301101c000b05403e003c075035100130111032868544c150240c84030028200640312998040c419403104005858909604000d01001103000d20250f441c40030251a12100900001d400c0c8030a01209015825030b88038003296034100d9250440d0850407942081012480450105059182d084d1030014001400358100c0c2c0321107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 352022167 1250 352020917 352020941
    0x40605030a060f123c060b030a020307121b03140609030901050403230604050601180b0a0605090a09020f0909060619081e100302030c0f013e01 63
    0x100085803075002c0c120955045125141d030340c0c40d5055207100411706a0020700c2030384108038030071400c06090032294020099903c0002d444d00314810103040c144282c91268102c8640d040b030141081c840150002035075070105025100c1c004800809040c10498186410031008202c0854611165501e0421301065201585a480c00780110400502e00c0c0c9000704c111058024140c4072030741407c1c290b441d05402a82800300e6002c07240f0b2918480c280382c03481000707143e200c0da00c01d0006000540c14009040080304183d50080c1401d4202001003c15948400c003100960f00745160803a1104100c1300000e00e00702080e07110951551000030601440f030f0f1004005e00210744c007601d1150b11511544140000c51107525440e40d240351242d003001c402c3c584154000368120070100211030402401c0c442d0200310f05410344a00d01024402d00c1b040007181800d010303442c151242214101d036885001d00c00070f45690740318162092840020030304005d10242c94056451000c4440f02e91030000d01003000c200d4000c01c0170070000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 352023417 1250 352022167 352022171
    0xf011407080702010e070f080607032d0e0307060b0102070b030420011206060e01090b030402030a2a0807030c0501030915020a020a060212010e060a120b061309050a12020d050f070503040506040605030a 88
    0xac4d486501900a40d900503802d0000214a40301c1200c1242050f00098426001e40b5215080f901502c48200003a0031424040c420002e28a0206800685458142d5200b2052410180104008107004042c3c807001900e010950390b07800d42c043d41c0102c900ca0360b0a510402424644000803403640d87c083d26281003010203807102003841c1d4a6000c0c2000d00c1c001140e0095160380b00081020001d80500003034410710001450507050144000c1c0304650344030340c82d00180d2855010030803c209022300c1800e400020702081c00c0401c4503a010351a04000d8600d2400c850100c640c0000b0720480301da10801c070032401d01c0d400c010110344883c0b480e56080c0007000d0038440c050310205160f000c83c13040e2078140c21140440d19402003000b00c0c80d07220b1b40c07906802c240080100e90701c40160303050702c0180c0056008295030a80305001424046205141c01071028030444030360400c540c006410701d11f40c130b41c220080744c4001140c131925584407021881c280b86141300b1600415008000446c0015003180c101000d5405201c0340744d81 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 352024667 1250 352023417 352023421
    0x3090810060911160609020303130306020913020a080402040c1e0503060907030c0504120c051809060f07090611160b03071b08091908060114030f011407080702010e070f0806 76
    0x1250003814200c0c0410100300710007600060790746e40a01c5a4038070290a4905100e06012803484000303c5500540d0104e400003010382c46450b01c0c032180300d0340041c0d2030021410700c0c00d1800001c040240c0108028001c0d65900070089243c0e018070f1101c0400380030742d9000b0007948000c00004120350030a0300c0c0903008a4160340803e8004d130083c040c18110034115a110703801c0518164110418180d1044150360110b10902c0200d2585c031030070704124009008662050043c280307100454a8504002d00c1c440d0040b43c00d00500c049503074461075101c1180d500d403500d0401801a0b00c4001d050400119410813900c04404c80020010241000303144940215140c5415003451140782d4082d00d2004032004040038003c118041403071902c05085182c4580c0c40c0d2111101e40e4072a44528034080c0d080e004641040807004558079585001c000d007440030300e4104020b201e1311142901100032001d020700000144401d0a0020715824400d50002c101e22071032004031060b05c1c3d9104800031a40109001700c080c0c9010b0180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 352025917 1250 352024667 352024691
    0x105040b2a010f14090706021f0e0d030207121806030f02090409060506010f090f18090501050702011e1104090b010507120801030b07030b1e040b03031210050306070e010507030908100609 82
    0x10311b03108130348094018050300652411518182c2010040120104c0d60300e00c481748240904010040c07511981ea100180c0d0327005141030031300002d40e1039480002001034940e4440c0c06a02030414460448496050100310a4000003241000c6d001e000101034006d407415800a043c80708036004107000e0003081c1c851700100003404004441003182401440d0518000e0802002002e44a00c45041210b0300c003440000c0da0071840d034401c1d0039a102a03400100503912215010552500c070840c0da1102c03045c18104002d4008581c8004240340110b2003900d222a5170f070060f407070203070b409003044888103039002101d91440d08070010058410b030f00a000542e0308203031240000728094005d200321604800014040e901c9a00c00d1681450024000644203400c13940700c0f03508486603103041001d0220800d07944070501051511311422407e40c401544030b03d11907403190040c0007005811003c5038110b00c0e03080ca002c2c0e03560101ca08060b120700310954080b40092003a00c45004040005a00420130345412580501c00e01c09220 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 352027167 1250 352025917 352025923
    0x60903030f07060204030c0e0f240402070302060105100906080606071106030106020619050103020918422802070206070807030e12120c1204170105060105040b2a010f1409 75
    0x881549c0c071a00b643d00440e040c00c0740180e20100d02907460025180342c041b21030104050340c01140088015a1091005016916100a0703001800c00c80703103048042d04d450210f0040805c00e002e088240500c0000035400144600c10460201c85800138144039500e50351454002e40c1ca507802c580988514801c0040e86041e40e0003402014120b81d0020910b100d1500d07410641d07002c0f801d101121890034400c4402c8242e15076440ca5103036003c3c41d480b4a42a6100a603100c0c0b400c03c03035914185501e1074104003420441030004a00c00380b40e0f00c001d0840190641d100300403256009102e4000080e5003d44085551810004104010f04511344203503202092100e40701c0a112889103600c81094441d04208100940c600704031007e405100c0780c5004956400310184461400b40c2c1c000d4125800c07810412115200c000403d01030b860f000130003845d0091810345002c0081d00140562070341a8a011419035a000584107a003419605498800d002004031111000c060742c02000c1c000c0708000c0d291098000102210408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 352028417 1250 352027167 352027171
    0x32105010b0405010f1205090c01140a21020c01090629150d0f15081e030405061b010606121103130b0603120a0f080603030a0905060903030f07060204030c0e 69
    0x5940303802d04080c1070500544183c1c003480750354410170412042d40100b0f01854040d050141ca02403002e451240320300380004142d889015a00310444c00c041103000c580030b60040e51041c2e42d40c0e00c0c90030381c5c3c050b0508944a03006807285840200740e80d0b0800c40c1c02424817806a10800101d00340d0f11680c0c0250b080303003242d0b5109101122005a02007400b0a00a2100104100514004d001203000041b644203074101078085402a2400b900700d020b001c8420b2001b40d5040008007644185c070070680002c4210302010707941e81d00c41d40c059580206c0002c203201e44200041c15407980070310300e010001d1210549580000307101203114022044928240080030b881c070988442107074081c00344140c41101071900c940310101c01d014040c007402c0d054420001c2c3d50a603003800c28060b10303105584c4ea82740e02c0d0b0340500e294020504c003000b4101c01e20903007041044004d12070304404241c003200c9003915029113500074100000c0c114015110b9000d040100020044204445540203200390381c800c21220311215142ca614032114002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 352029667 1250 352028417 352028429
    0x13030206040303150e0c09010e031606050901111c14071e0503040e091b0a12021e04061e09020307120203040f080706050901060626060f030a03210501 66
    0x20008103000c20302c26004142a4540d00f0001c0040564070240c0d16503100c4206c9074001c010902184a440c0d642c0d0200d42c2c40c6203400d00718010080a11000c20414103091144503500c240000010300040130390060f01002c1d90300052505503181c544500e10700001c508100965580041c8005054280c200088010b07108100d81208010f40340312202e8011083c3d100c0c4010095860303210501002840c0402c0d17070703002c501c01ca480c0300280c091900ca007a00782088507201c0030030601c1042c22120030310070040f2210071440400c0e011203640c0c89040010344103c1050081428581e04242042070119a8912140b40411003039075058028590568481e080070403404250341d0136000906807480c20040e80e5094015541040c00381500030401c3c5842e41c1c3e0042c00d07501181c0211402a2038504200e4454420b22505000784054140103d40c001140001480e010700c0340250a103040d50b990100345180c86510807044201c3e0040d0850701f010400e420040c06401c41090089100e5071a070f110440941c0103406040e0481d08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 352030917 1250 352029667 352029673
    0x150c0c0103150b030916140904030c060f050903070209010e060d0807080d0606170a0608060601200601030501021b070602030904020306010507020a030b09010e030913090302101103010e130302 84
    0x24481004401500201d00c1c018464400b4240101d480c140d0340000303500404401e00100417110500450008007441c0d54007442c986500321216900340d072681c0001d40c0e4419818035201c41c4100240ca0800c2c01001e05c80d01d0f80c0b1a0350325000400c03140c0c900010041071554000c80300202903aa840f4000c9000c04400c840c2c4030b400505806040e400904d400d000780822174812012a404c040c50000740800326403140e8401c90009d8183d102e000b4984000305542d41e0003502c43c12043c48424100400c4650b280340183c180e6042000c41602940030300d144c4414600100410400da0b051035940b0709140d0701035000034000084407410b0918142c00b00034002220022108a0380140d0b00b02121001000001d4100820081c18040f08202c1c440040e510b110100000c3c600c103a00b858018200b10803031a00b1541e204007844100da0082000310800e60710f6804603001452880804107000100d1314040742001c0303210400d500300038180315220351071404803c05113040e15515000c04006035203011001581c422039000144c0560 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 352032167 1250 352030917 352030933
    0x40b0603100b071401111306050c0a08090301020d0906050402040b030708060c0315030d030c0e0303210403020c030d0504060e0a260313030c1a0301080712150504060b150c 75
    0x1001180241c040b0700c0c003c41c4c0d1800f4204034407488a0035620f0301014034482150002c0c0800d074010181500300080c0041c3e103001801e10b01040420b17a81d0700303050b40004d850800085030340c6c0c0559600b50102c0d1031303445070f0741d205001101c024504071000d00003c0e2400c032711541c10492006501e050000d450000c950a0707400400c6035450390708062049034406401e07485402086101000c40c0c0e2002c0009984200c45640c1c000b0b2500610b80c4001c00410681081922980040207c206041100c04040008500d400b5101619485629040e460216007414241c2c05010702200c10040c160028044c0c0203d13030781502c921411404007810405500c503903000b1203803100c180304483c0298141c80605a4030030300c51901180e151110b1942c6100c407031485d90b4002c85800d90900c2c070600040608c40400c143c80704880816508550600322550340310380c5540202e40000c000407104405010f903405c80b0241a440c2040100b05a0505007011000782100d20055405400250428010340c801442200c1e41c403245240901903007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 352033417 1250 352032167 352032179
    0x150c011e1512062319111b0703050105101401230711310506030c091003020621062209080723060901060e010b0d0e0a03020c040b060310 60
    0x42c601e981015281c1d00c1da25030140e0b150100109041c0d2010700e59024480140ca02818004402c1d401218544c983e02c0c107040c0c100744010b0f443c000b618180700550a07441101100c08451a241900960000d0304540c00c10051100758100d65040c40150368645c40c0c10800141e00000548a40070305800c051403a42c1130785400c00e07c1030903507405008030b24031400d0301e190a25032400008410089c0d07003400349003584070811503e130441508800380a10301c900e07a20078856803038480b0000c1e444265040200b80150410000541100f241c85c080002a650041540ba00d48201d600da0140300a288264002000359410115861b0b203440741c41411400c030540c20a80c0d01011440407140034003250082115080820700c400c0b00054203407041d101602c01c608102010740c40da4100c0040c074001d40541681c1507a458000240103240c1c648c40c010307040d6000044803e45c2d410340d003004036004019401c0180d50703d0082d007100e4000c0640c0030400701c0700d140c6c0446040c004404030204104003440b09071500540c241e2001010040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 352034667 1250 352033417 352033439
    0x1704080403060209240c010c0309050c1002070f0902090a1e0b09010e0312070c0e0106020a11010504050d050105010924050d030e0604150219080d0506150c011e15 71
    0x184000180072209048206035040b2690701c82170485030300011000c00c069141d850b091044007601020b0b850240000d0f241d58480c07076129210300282c00c3c0034100020b012094035008020080060114200305450b240d59541c5150003500804038040c81440c40b58000100d50f040b16280c0c0f904d04103001c031020119850074260301020303480441242d041c02071016046044d80d905024003804001320034900c41c1e0303882951415415240c005c0d0403007000745c2c034128014084950300048070090705034001280c00c0c2980f44000180ca07103006076403040340d03c1a62400c0d407004104064002c28102c0d0042c04080c04164000300c0309128820304a2904055426210010811864018140c2561500a09040c00c0d40d848050110300c40c0d41c0039030001d007544207600760440362031681000304c03000d07070404103410100e01001961070703052510610119180450b1a003010482d281d0b207221203c1030948840d00b800340d960001d00305090103003500d00c1200c00d520022039422007107100380e40070300e42200105034458140c0d9818101c030004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 352035917 1250 352034667 352034677
    0x70203031614070b0f010b0c060711013801020c010e011d041805060702061005090421020c03010f0c0f0804030302091005070209161b03170a0c17040804030602 70
    0x81040101d04a6a0884590b030008004039800f03488074003030300c3c544984446090790041c5c0c08910b804004022a441d07000001c107659800c1a42841c3c0072150103403000b4124090031101ea54003041c01c00207184009a00040d29030aa0000400b10320b01c1000c20bc1c10005a85410256007828040341880da118a02c542c8030b05803840445041c0c030141010311600002040440303030210562413107002c40d4903181042c8401003010680c000c040b0310040a203403400004000d0764072214418980204100780c003280411211610400092080203100c010328400704400a50792464880c60b103000354030b480410001c104283c0103240710303070481d03844030b10344040b81031004c0380c42142c010425001c050f402e00c103990880d510a60410129151035a4046e2514107500422280032000b80a80d184070402d2005102041c1d005080d803603147c00d100314000c07580e1b140750401399450010404280c8000c201e07002004640100c0d030340111403041c490303552402d00008103175110480314020341300a4007442e41840208001811500101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 352037167 1250 352035917 352035961
    0x602061b1608070c0e04080405040e0f010908041502210a02120403080405040b09040b07051605070807081c020601050f04110c010501170109150b0406030f080903060a020307020303 79
    0x107403400351441c1c040302003030707614660031503a03500700042410a02c0413003006500a800410740907003071414190340380281031269200b00303409039440f1a101401d1a0341440001c0300d00ba03141d4006e008036001c525050809038002e004210300e65103041c05400c260340c030006d8040700a071000c3ca00300c1210040c1082c8030085820404203141140701d1001140504808000980f00035071240c40e00039100c40c200707000c000c01d41d105500041d004100c80c804210101e802049880c2d003262013800d00d80d5503000362028007800c1509101b009006072055206c000340381ca00028283d0b04441003c1c09450003480007050b607420b221480c01c64807005a0262006103d40d142801810980c0140180700082c0210144840880754000c10141c90541e50b45200400c055121003404421000c0540c000b0000c0740d50310755400c074a1032729174511a0616540c8031400110380e12250b01c000090754103d0b84e0880c0491301840c100b080e640c84021554002e010b8070001c110300c405e09000ba6405820382c1d030040c60555031140300310311010f0860300e481 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 352038417 1250 352037167 352037221
    0xa0f020a0f030b0106120c020d0c050313030b010e070e1e130504140616050706090606050a030510150302010e0f150a022d070320130507080a0501060206 67
    0x16080d01248054002140f003000b40c0d51140d03152180141201204903000c00101d400c1150340040c10780d0110701460110207030304001108a03441d0420078507502480e04948800c080802e404420f02c07031800344150480c0c05003216500182d9034031004840950320300c01034640201c00100350f1b4481918a40e0020100c0c40003401c64040b03003030810401000c0d07500c1610305a0b4020800741c240820500180401035010341d030b104410400740c148040c000c0540c8900369018240d070341d0301c46800d410803010350495401444001c05440d102d907200d00b071031a103440b000304956049900e131140107180401c5a24103002200c0c2c05071502c200402d1903006109020b41c400384016070060090aa0141c82411000600f4440c6030300e60041c03010040010020b0700c240022800713010b180280e005003030a004000250201a280d00c803414851042070420824040c55074007940e59840b000c074024850300c2d1191944002d104800784c1c1d81b84c3c80030307407a151240c4e001c40d4820300995005030004c0c1c001810303002c1e09041c849100b000b0010a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 352039667 1250 352038417 352038419
    0x3232e050f030c06121306290306161b02030d0e0127060804080d090309050118030c0501140d050103050a41030903161716150c05011404060516020a0f020a 68
    0x288078115140e40d90010111a801c0c400f40012380151a004c0c101d400d030540003030170f85062008007030400340c85074101c01080001c0b0031050b00034040c0d05414030401e107602404a81c10607441d13030000303800141c0c45030049001480c03040d0707500d6894900340c2c1d0b0100805003c0c07c6007401e041c20a6002c41e000e02000300705031130b810020010305040c3c1503d031003582c0f540c600a80d02c0782003d50038140010300701c41d02000d00c40d00d07859a0050a201090700140c0d0841120000d0805240c1d00d14803203144000343c024642105a62440d0a00001c01e1103808110030014520540c200b550001031000007071442041d81948140700240c01450b1a07606102c0e01e000510450f815049038100a0464002450f1228100c034034580d60800e04020040c00360140c0190a004589002801c0e00c2e084c448144c0b11889550300c281c180040009405594003401030061044094200c0001c0c8041001d800c211504160300350b8080316910700e044005405055200980040103045a0141c6410f00050300d40c1210120500070903030f071020350a00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 352040917 1250 352039667 352039673
    0x10121b0b120f01080a020f040921080610090312030c09080304061706030303251202030108011508010e030409110c0d11010c03232e050f030c061213 65
    0x5070008042525000c0309526245001081240040e8015107580d07200d9400b200044c0c0c0d8031401d030444048240e80018186895040501304e841c0502e00b000b50030505040b0b46400e0a0384410607500c120f5051b03620860700311004d0000c643c080e0300303880b01070000d01c1002d40b10881c440c86504502200342c840d28089444588802401c5d00755401a40880b01207490a9030561120407900c120036030008040340030794254039000d41d884c00c029007020801c0d02001d43c10f0b20b02000c1140101e00000142c924403100310345a41e10783d4111402840c1811034a208040303280b000149034541401050181e84090001c1c40c1014a40351440011300b201711034141c4105810b1121081640081111490399a00c80c5d4851144480980f01e2500b110f80244411082500340052040c80c420503142e14032030345140e104092038641e121031000300c3c1449540803090340e006d141c58207191411140040481030f14001c46040001245c103404040d91801c01a40b11600002d0070f100030190040400c08850748542210b2085551071016a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 352042167 1250 352040917 352040939
    0xf041202120f0903060612032a01050106080708060405010f121a0f01030308010f0e04020909190516061b060b030f01020706020d0f02090d0b0a110408070e10121b 71
    0xc4900b4961540496030500d0303840c007081080c0d0010000e98502081150304500e194a031320425038684403643c80d0001b500f0700940d402a12810800c01c1400800c690b5850345002081c89001fa245400010303080e01c0400c4261070a0320900c3c1c102e522510004003ca4a05007608175401942c0005441081c582003a080941c094074600b24860148180511025811441c0c064603200042e000700217a06600e0f84180550302001c50701d0f0743c00c00e0301102e2120442daa6179000c18a07144001184100c003c45031050712082183c0000d154944880b0150001d40c1075071501d000729900095034200288590442c03141c1d5000c611243d000034001c030b1000c0d0a03200816030300004c041c01c0e41c0c0030140485115500084001000340d00d485000314a01c0810400d40c9000303010000a41041c082c01000381a00e98a00085881004680c4c0518112000040d0ad00c1e00c5561700c1c903600380c941c1e109108822a405104001070380144040010200f500e1204001006da1300b000d84600c1e154805840da07403481c440c4415030220351742c0381c01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 352043417 1250 352042167 352042177
    0xe0c0403050a2a0308030a110405122b1e020109120f091703030a0f020915031e061011010b0418030f0801120f020409020d03050318060f04120212 64
    0x84461450105280c00b44554078442e910140f00d543c10504001d2002485400803650060407113140421240d1000170100071a108a9000a0f484081808007407030760071010800038840340310070302d01c0300e4005003540703001701c2401000000307a0001340d1041030744e03103081c0b10b2110030350f12070050313100001c0c242d2a10b40c0c41c1d001840350944190003007440d00d103008500b280d119140350003411840b401000d10180780c03e4500c2c1c1d280805030024042036100c400380280d80882e5410303100c030000300034100414419500c03103c010f90350090764008400382100f14a815203c144030b00c803a010b9180500100c0c204401001c1c125a000700100100c505952074043c0680309079114000c1320180350030501c82c1c00e0710203000c0c60003034440388446a40030203124203c40100108044e400f614414250031024a00469201c0d100040c0201030b100c10082d40182043c440405040d0300c00c01030741c03280c400340d941811701081d503140b45507650101310707803490400308803038005170002e00b0320110500d04400500480307440702200d80b02100a5001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 352044667 1250 352043417 352043423
    0x50d080c0a140f24040f0203190201031b2712080d0e01050613150f0e04050f060f0a0903030b150307030b120d03020702010c1712011d010e0c0403050a 66
    0x84442da12558241449510412040f0304010031600c440740c00c41c001c03c0c6001521000001508000050500c54030718502d100c2c050b07008007a9001d032041050440c8160000e0081607002038070f000510b9040d83c507d6202c1540003030141e152024054100d4036042d5011000303422203910100b03292000502000300484014083d440b5980c15138590a040314084d044400c51202441c09a041c0001c0c458191200030600359001c00c205004605111149070507110741d400380c3d0010441d0041108c0020f0540840c2260ba40203510400903030740208032030200780e0740d5441c058501c03076500c5000b48042246c81d5100d9000c104601d1290401082014110300003609850040710f4080041c880081000310080d41481180c2d00030104980030310ad00540700805598810b003004005042c236500003080c0d815a07004000d99076805078441c0e400141c40342c0310032107421070740c00072905c84460b0141c07200049515820f211000101d26140c3c0104181a07203070003200101604003810003a5107000410010011030f03414808581c5540c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 352045917 1250 352044667 352044683
    0x60b060f1603080606090a0b030603160e01060e010c050c06070f21021c0e060c190f0c1202011d041b1e09030206030c0a02010209060d0b0a0f0f050d080c0a 68
    0x1d85424082d05030540240340070712810b0100200710302a0b982c1011503054442e082c81454480c0d0310f60780400e25028003600e8036400d0070a5040001000c0c0c1000244606850807507444120020b00b840c010342d04101403103c01011030300080311401c2d4604006014207030b0103014081080040850303448404245004c1c41c40410000381c1486990b42c40e5030104902400d10b40c852030804810a69818000c0903000c074420b845200d00350004622620a10400519400c1c0e60301c1c803005c11250403649081004051455421103105684401c009200401c00c2d0008482c3d64060319201a6201d4404c424004501c8102400390b20a0b40e6020f10407241e00c1070740403045820384545504000304842c0c0d4081c5103117800b00c0010003c000018005100585401042c3d94000001c003800300d484146a50090b4060b000300107240d0703040a80070903000b01540064211600360001550b20410b210348502c40c00c0040c13481d9014500100f50350303c6d410005400d1030402403100741d010b4021242040308040d010750078501c602c201034a49407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 352047167 1250 352045917 352045957
    0x110a0305060303090d0609020d1407030b01060e0a0b07051203010b1e031b0a0e0925020606011b02040207020d06060620070e06060d050403030f06120f060b060f 70
    0x582500c591600048110029420304007548000b503201640e400008002036110a5010119280c4440c2d406c0d14a030311500c6144032200c0c410009540d86607500c001c2d1350040d0240f0000034104d0240e140c0100f09000640500900390524840c0040c6078803846044031a4840d0030200080c04450001546c064070f4406000340c0c2c0e039251015803500044030034041d518034440410501072030020600005082d800701c401c5240d00d82d0701403902550180412555160010711341d40810011100c0381d40007a80d0414181c0c03c001f032885030007000f00d076151011204d444c082400d07010143d034854107032071914442e18070080c03016141c0780c40e6902003a44501803800841d6801e807185002c7c8002a048240100503041c41e11103441010258240c013980c0f081244a000c0c20324210101050650f00c0301021244a000a080184020f003003628000740141b00c182840199030707283c10004034104281603002c240154003c91145034190164031810024080b900d4143d610040801505d0b03441c10b06c0360007400c49612112524035540b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 352048417 1250 352047167 352047187
    0x90118080f010b060c030d150801050705190e01021213080a080705060108060f06090a090818030c010507080d05180f0c01020d03051e040201050f040801091101080903040918020411 79
    0x16032490041248545000c1c0b080c3c2402c82000010380e04403281210021448c0b8990f40c0d5414007442190704800b0391075007400104021990004000c01c030342808221490fa80800380d040880d002e0100b00d461600503001482c1116910f080301c0c02034407031941200181c1d0307038440c1e49410861500300c01c1c00044401c0c54020840e04140030050203024010200d1034013902c81442c0004607203000e440010101c0784103082c6030b008a00c00c0c201130786c018090164801e019aa4900130880c40403102c0044840d001d00c2449580c0d2004225441642904c0f0a07503406100203091501100f9480041c20004141032039140348000d02c200e24100820803401110b05002c09080c042030190002418000400c1551703051505044c24041c00001414103030900070408400302d0b08940b180d00c0101c501d80314102c10a01010408a004141c41070194848980d031841801c288800c0c0e420400150341d0704104560081568200b444200031034642504000584003980080303658103101a40010b0865a440c21103c85496010443d8115 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 352049667 1250 352048417 352048421
    0x50d03080108070e01080a0303180f061d0304060509040216050d080405060f010f090209010c170a0e090f0123060406030b040e15071206090219200a0305090118080f01 73
    0x135080803042030080d9810f015059030740d1140004014100740d61030385e51a15455400f040407069543c800700c8090000007505082c030140c44200c00c041d045172440d1a03480845800001120103c401c0c2c1d440c1c017410010343c102001300030340000001c00090345a2001d20b8001034018890089a50120b44640e0f5181c20a400c10600c0d020000308007050400328007005000140e0900241710481e00700020250381c40424100407501000d080900034500d480d08ac11102070902454003400030b03e2801e0383c608030800c0d910002c104402c90281c98040c0b00000c804010310242d501620342c0300304201a40a030b8081a9001004643c10754095441000081d6031488a40881d20342401501403103002c010042400002528240b000b04034040c2c0440e0034090703242019907240341242c00ca080200f240300c50031034950080c3c01e14104c0c1364120420a90000d00000c000500450025078180850b0049600030600c1214950b23081c0c0d16503000840c5c40d8180710602e0010b9401d281c20001c00f802903c0000003402000c024441d40c00d003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 352050917 1250 352049667 352049669
    0xc01020d050f0714031311102307080403021009030b07020105070e09040b0c0c07030206180a0519030b1b070f150c1713050303010303320a0806030106050d0308010807 73
    0x1040b400580344c04600051000796034201e0051003920f02d4080d0a071410480300aa40d4003800c1e045205543d420407060f4100d10589056524680c405032642e196941030540342c81840c10060451409100520241c240381c2000038000d10941070040c0016140d45a255564104851120050b0345542c10410311035070007420b401c089401608c220401d424190b1b10302e011004010908005c201c800704040d040a0350800c40c0d0b000841d00603161079500c100100c06010808054818a07001e9514240c0c002224241514850744a11654140a003131504583c0d80c0c00c08400f014022524540c1c0d4841e007940603030400c000410700c1d50302c2500b0822040c030251406c180503082c8644484895450314a80c4e1003010b0304090092425203025050010b0341e80e03000303903641b2010383c880e00107412071102100100030160040c40340d00c42541c01a0b030380c2c01040c440c42c28003041c0464008c80514038542c10304c031a4107214003c00c50309404c82e00040c0082103158864000c0f42d40081024070a500140846004014260341404050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 352052167 1250 352050917 352050931
    0x5120421030c020a021014040b0c06010b09100807020a020a0b0a020706030c0e090402031c020303071803020a0b0d0b04180215091503091216050d170a0905030c01020d050f 75
    0x100c070350a408440a51100007050001e1b0040c3c44181c02054054490842150b003956603800329500c0c1d5031101400160341d0402d04210313945203c1c08001040b2808441d06448403484002c2501c0000fa902404c201d400b08005021481507100e016000f90040e0b44181031140138180ca840074540f140d034031a0b4001c0ca0031a40ea8400b0040c50b181c5161350f40358543c2f040a6142c1c2540903a0408240c1c0c030303507201081c42c10001c030071001d41141508002440380c0e40c2c0440114040d440c0d17076941c6514540e50304160f444c580290700c00294450182c45040003a280914050030200441007000038050040b00c000c10183c1c1d1403014401300c12682a0300c2d5400b103240c100c01c0c10310050303004202c030350600c140c440101d0010307504010000446032000c80000d4010008200c0c0d80c0c240d280c20b1100c50b0b1184094005981e80803640c14080f50580984541848038a210301e64040d40035140400b40065034603013000030f80042c0601074041c4c40c140000c00c240c07500c1e080240018544004088400038240c03504c2110010a2040a040703a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 352053417 1250 352052167 352052171
    0x70c05011b030b1f0504090e12070501090201090e010e0a0c030e1c0212090d0602092d09010501020313050405090309090f04031808073c1701020903070306020a0512042103 75
    0x880135065101c0300381c405540050400094070303801200d04602c1c0c41d0b0003070b501904540c000203200b0b0030888107400122105200381c0351a002c560300d4030b0141a92120900814030034080c008000ba000503165002005511844c1c140081c03070300e416a08150810940d4a02d2840d004850b40300c19808581c100424814801c005100a040609110016103103050f1030718041c000c141c020624401c16079444c04c001001e4505202010f600d01034a07034103810140440c1040920403818500000f41550010040750f0005080e44000500f66080c03074100302c0109000f90022030239201c10300a44d40c86842d10b020700c9024001d0b040110710780303140070314006022001080202035451051041002200e500007102c0007900e034880f0380044d82103480d203156413105003224001000b1403200e480d11405469100c140c0402c1d100c441441c100313652546030442c3e00b81d106841c00340340c0503407100c0000c00c04180940e01502208142d17180542c6040502d0042100031641a1011340c0c8402c1401000e1905003804680c01151000074101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 352054667 1250 352053417 352053469
    0xd031e0509030307020603060301270b0f07020a0222060b04090b03280609060203190506010306050d021302040b040f081c0804030302090f0303190201180b070c05011b030b 75
    0x4607841c1c0c084c0c4034000b40501e02c040013107035095500790480e032860f07003900f1002503020103001401d02c801441380c601070326070641040100d1180c0d020089030510031011900289010070300f543c00d0001039107407400c420142400d50b00800840124601803072000704034a0001544031070400c99140c08840ba2402d02074404e520044030b4022070003076891280d0030310303441c07011b444c0e000c90071424103001900015200402d43c620000c1080114203031007204000f131000540d0108002c0e0343d51001582141c1c03540c06002e5001c030001c1804801450140b90020300e005002001600b4940d80381410388841c0c006400101160081460a00c42520100300b078001301c40205500d40c1001100c40c1c405001e0180c040c1c0058101500016150625150b1030594080038602400b120b903140d800f02d0841642e0380c10f01413058015400c1140c401da45105c000c600100040c5c000c0d02410180c2c4445070183c2d00500d514004880c59500c034a1078611646120a002c0e5031141c00ea2000b04070410190100603c080b00c00c0e129840180d0281c038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 352055917 1250 352054667 352054669
    0x702010c02010e0c030718060801180b0a060b04050f0418030305061c03090902160b09010501180b0901050105070f171905030708061302091306170a030f031a0d031e0509 74
    0x441e00201d40000c0b80707148080202c1303034247d406054160408007541d801d1000801a12111a580104880c05a801e101407900c0300030409040c0c610f00d2040111800040c003040c00645041082c00090110017080004c680b2500c800d01c1c81c040e0501e07002074005c0390f61070f404c2003454204403914040e40103002442d01000c1d0625500501a00540e0242d01402c580c0800c520b01c2e61000c0f03001010040e6040007440080785030207083c05018090900869085500e4504040340307050640c0501c0e81c4145006060b03108507030174680110340355040950280c1c1c5040044002030040307510b0341081d42d9801c0041b850150381d40c4104002c05124900075002c1400c01004008000019a00c44661074101001700d81950b500e129049022001e40a20654141d0101050800300841660380d40310004854070200303610114442210704940f41c0d6002080540400d42a40005440764400d502420704e4502d0058045503107000c02c00400c0048040d898218007092888107800f00c41110fa00d0202d50304103192500600e4442d03400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 352057167 1250 352055917 352055923
    0xf1210230403030504080705011e0f02040f1203051b0606190303021c020f030a0306170303040c06030e071a030604060503060720030c010e07092906031005090702010c02010e0c03 78
    0xc0010b01010b60750b00c0401c1c1042030010441d162240c100740240300b0079009001e203480318940824491303e5071340790140144021101d402540c08440c0b84103840407499203420301d40708450509403c03c0b020000100141d111b900303c140801e110b0710110300000e040c1482e0100a0148218130408090b0606401500030000242c2c001260740074860f0414503c4609103850405230320301481c42802144078000401c4121405515134480300807207050851720401d01c0c1c0729142c1035440c1d200917280503150f0600d80c081403002c94040d8003e031107a035078001d044520282e541d61003540c02c0c0d17035916500c4d0b0b03a20200109000031380c80d00c0d01a41015010403005004c02c0e05210070003804030640c120302da07d40719480d001c4600c9580424400c0e10200b95030320009001290300d48200d2600d6513524042c500d4247d15204d6070010124846049209d100400c0311b00c0083e20541004011007034200428084800c1d100c03001c04143c6440b54401c82d40500350540000c43c1d00a000600039096904003120781107242e00c0010004115a800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 352058417 1250 352057167 352057171
    0x1050f04020a0309120f18060e09041106070f02040e01060f1401030212071e03060608010501030b03010b04090803090c0306040506060405181f1b17060f121023 70
    0x440e00141c0e103498400060307000d031140b510043d100192980c01460016040304001ca00108565100360600d803901100c00716540c0b26000d0040003900740118441c0605080702d40503000390083c0c00501e0b840c2070308800a41036074000c1d2000c1f00c484024030015021030405018030940060158001d0001d5402e100304094003030010311403440c0d0902c80c4240294240d029904071002814009403426291910110181500d9880c2c025103610300624242040420b00c64851442030301d1050b03844250f641d103024011409440102c1d000303a415540c03004401c443e59070b5480f900c10064440c00b80240c99140c145d82890602490518003802500038100700400900e01081165120504990000c1e06480f8188000721441c0c0c3c0041204603403284d90750070310103000c0208450b001c11503142c0f0240701da07444041c1d40c0c2407800346c48843c4002241024054100811818040b10fa1101c40038120180c0b180b40480040e80e103080d0180c100a0a070000b50401c62038008a0041d10491908103820310200e064400c02c00840d8030700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 352059667 1250 352058417 352058419
    0x61b020915180a050601080c12011e090e0109110d02030309060d0e0a050109021c021c050c030111040504050c0f12100b0309010b0f0f0a09021b010213060e010801050f 73
    0x248038200541c1d0703580024440a40e0b0107240c0c90900b4030b00100e4120040c641a42e0300b81c041000800003030b800d05028000c4403080d6411152184030341e480d011014440c0000c80e800038050324040080810520300354840c418811207240e002040e8a03c8a062400c1070010000c8003038002c0c60b4448000303015840010403200c0070721007130350f05558900748001c0d0400200206424403426004070303c4450306000054000744490350003100d122115035105000080807403200c20f002034000311042025201940045030b0382c065640660144c0c0c0c0030b145408002400c5660f82c151006094401040500c1181010301c1001e0f401101d048034585000c454140841c0d241c0100380700302040c001c40e4800260203262480281e0010409588055201d080c1610001c0c044d010106030f80d800f4848040740001d692034204e02c510170408014040b8a0740504000340880030f540701104a5200003010016000b40d5442440203113014014003001c07031892820103a00414850410420504100b01034006120b20b5482e4840c81c60780d010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 352060917 1250 352059667 352059691
    0x150a050306091522051605040902090a0203090a05190b09030307231c020711090106080c2104141009080405040911181801090f031b06060807061b0209 66
    0x2881200301009225840103c0380c80c0c404d10b0078418204800054a00d8407090601e46803640d054507082404210307011070070040c0d40203039030001168117469158000c542100500082e102130007416101e540c9070900d04900012403c02248411007880703003403da042c3d0012a0340003e03500d0342c103007404010301c001c0890f00004214401d40d0081fa101d070035072100700d41480c3d034160b0286000080c4a820b078002034200b2203040c0c884449001d420712083c580340f807005041e5101c82d11a0720383da8488807815840d03504817040352040100e0301e00745680e640401b0380d031940c4200e100e00c0a646502d4103124106040101c04441007101d542042d84002c00641c030b441c2585c0c25503d080c1c07000560310f545c505018a00441c2c1e480c0050300b058005403600d000b2100c2c048918802c1d940d180b030404440101d010400e08807107148501034a8047d089941100091003041104850802c44080510041c295200c40e01101da41e03a1050013590f00a03041013080c550010401048555010f2496031804c55540110f01580801090301000d49 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 352062167 1250 352060917 352060921
    0x1d030708070b03060109031e120c170309010603050109050a05370611070f03180b07020d0203030c030f04090b010f08070e0a08010e06040501050f0919020315150a0503060915 76
    0x11b4803401c00076000b160040c10840300d00080000842c040d00140100b525600d045a003074146050007a84103403502a0b00ca40c264403c4200b0300d1980c5c0150300042c088a0f0305548071440007011036070074000ea4160358002c10150813500d185180c1140b03030008415032580440f203031560940d02c1a00f12a80704100e1014041906e85c0306910340362010007801e540c080e0401601003c81c48005100ea0311290300411031190b10396818810b06624504c40c410418030591045240c1040b40f04010300340044420b032054800b40c200d07420000c003544241e041d40c1000c41072a546030004030707042005031414000d030325908900382000c10281c001d8000c01001800b00070085400d112500030b20b043c1e591544040e1100a00d40c00c00200140a880036045031554020b0b28141c4056007041e01083c0710260b10510140a140e2503001014150791400e00440ca400b4143e0050f42d03d4003440000010768404034440300e11032580c200d54040c400304510200300e1240b0454002e103004c2d6015204014690600044003c1c0c801198904c0c51103030707 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 352063417 1250 352062167 352062169
    0x5090102070e010b0a080a05090a03110703060c110105060105040506030a0509160b1201150e010c0302010603080304060209180603100b0d1b062a1e0b04031d030708070b0306 76
    0x40700540d44640c2c504000440000340301c80812001e82800161aa102000d40e03c89941c90800c0d07544c140c4010000d034004960081c0041d02502c1b000407a1007032041502c0005a49031100c07411610510300711004900d00741d40d040c496800a1140660204090130072a081a081034040348145c0401402108440d030b445000c204845020818000b6084044481c0e4070003d80312042c860041e00200c05021000d1941c40011503842d0740c100b140b006010740c0c2e42e6a01d09401c2e141004640502400b881501507560760403001c030201d01b2102c000c40c82070740107a82c007680d5041d040f0305112180c0c3d408441d903007050791341c1d405010041c0e030003050036002031900e00c80108051001e05e000498800c1000e800a00c8200c1d441e80c03016030050101802c4044520326160204058044080c0004025142d004518a041076060000000f948400012a102000d613449101c940e002e0703950541003c0213540c15808200007202c0702d40550344004680f804400103a01514603a8906800c0f1607403231010f4011054140e00101c00a095 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 352064667 1250 352063417 352063423
    0x312020c0d110d09080a0807030504080a061a03010902092a1204050f030c07060302130803070c08060c0903060f0402180a0e0c06041428090f150f030305090102 70
    0x32540c0c0d0015908194010800a40040302141c03040d201402800b9565034031a0103491036404a840d502c02a101e801e41c07a0382c134001c01e43d21480701101804814000842c1c0748404011a4500600c9242c000406025a1303c4d40b0015040081c40c0354801e030704181100d00103031a0b0700c1c1510b40201c14003d50b001c00400c20301800098038684004200760020203c0d0b1a1840844150441c0c00ba90207001982e20741340c0300b150001d031248152070020009034414070007007010030b100b90300030311605d00070301c00c2071200301c0d190107560741036a014038000d582000b01011306000c4a81e003407000ca604001c01c0c1242511301403403200480d494800050540402e0150200010190748416808480c103c411003d00d100314a884217040b0020402c04810355420702c20b0000700c03038150401208440551380c00d00c0051440011400800000b81c0c50500329008c0001c4000c2080c04400344c0c0c5078040058034a0720004a002c00656019008840d0320100c0c801c1240c0d030a2034200840b81421540d0801e40707801d031801c25a90b46000005034a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 352065917 1250 352064667 352064677
    0x706081f14130608011812030605030604120306211a090d030207060204092a1b2402030c12100b04051c081605010c0206072a05030d0b1003090f031202 66
    0x4079175401c2c565003a034a15030800140700c0c0240f00c2c00d1031801a01490b2002c0b011502940242070301075000c400843c1c0443c0c3c10000e00310111103185808200c03140c6494007101070802c01840421109007007200346040107500803003510580d034900150100380c41e01c0041c0f90798405280041105140c2d0001d005001d1101c3c680484024280300607041c800b01c50303242c4800405e0f06080c121090384103031703032120003422500c940807200c1c082040d0500090200080d0b1652042501c4500b4000f010340c090b0b1024801d503c2c1c0d03500181d0f2062080910303845d12a00448294141d40b000100050f100760040c0c0c0062102801d10420740301520002d90300d0b00d000c45800311000196100b0000041c002080108003038200c0030100a89131025842403009104c0984804016039540d09c0c00e84a60011418a441c60054401031408082c038074068920741000c1000e107074890500b560300071b0032b50400b00c94486d64070303205a00701142800c814410701d1400b0804112a5100c1d0040840b001c1070040800c286a41c41114400803030301566 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 352067167 1250 352065917 352065929
    0xf01050a05130b190f090f03120c050a20090f0106181a03041707020a1404090b090606030c01020d05090609040209090a0b090610020601030b13050706081f141306 71
    0x65584519503508854079200004c1e050016103d0a10550003d01c10b0116004503a10540c0c01da20302d40c215179401002c001015550340420851038003040c00300d0010000300051500807410420a54440101240b07030591801c107890090340c0040c1401030b54140d095070581110303440e24042c07541440c50344001a2a4200e42c0c06206a00c61a0488000021802e8020360091b03118084c0c00110303a0441d6091030700c0340035002c000b03948242c181404002c4002d028202044201e40100b00044541300e598600c07051030015540c80b4144d510183c1080041d00f02045440b0a0030f02c01d000511341020302d40c0c030003400340c440e03210341c10f000741c070040750002c5d0684a90301620a5410002c002d008180391100d4500c006100a0000c6071080050002141482c2005500d04c080c40807940c1c0600308503800d584820400d4503020b001103900075180d01c2e8007404610103104002c040c10346603a0744050390510180d600d0400c280101c10700c03039284012a081000d032a00001d025500102541e6004403207200c0c034040c0c3c0081c40340b41d01c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 352068417 1250 352067167 352067189
    0x20412140a17040602160803070201110c0d060603020f090903040306091a040b101a0901050f0705061006080c2b0f061e0b0406080c030c0c01180209060f01050a0513 72
    0xc2c0d028803041001800548031160b003100d0300c81c80c40e103c0304400d0705c0240c401d14410f504108508805540300d5146c400f00380c16003904039070340011603501007903010460002c1692030f0303903552809000b185489500c00541c02ea0895001106041810040d03883e442030340b100422199488200404200141c48180b4860b036405100b0718041c0380500f00060794042c00c48141e010b140b00301c1c0002c200c9c440050740000819a10b1050b06041458500054910750b0025041141c010000e2003000c0000300200a9035119204106105115602e0103c0c050300300c08002e426250034240500c148100c044400c1c00a42c0c03a07540e03444c50300d03450b40c1140c0d600780014a1184c0d9194170b06801c010340071038640c09001132181130455600030b0208807551240009201c0c080c0d0300550300020724000100f03807407601a60140d50064005101079141100311302c4800c0c00c6810042c0401c0d6840c0d425800307482580790071559654003400584004035032500181c0002d1045c0309200c0200c045c08008511144d05448295038607015107420228 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 352069667 1250 352068417 352068443
    0x709020a0816020706080127060602010c121e020a120504050c010906050c0309150c01140a050c0c0a060519090503032d0610122409020412140a 63
    0x20041101d90100d402d441c0c1c041c0301840409400348005084421616555510080c1da402c3c091007040700c021400c54002c0c6007900d405481c0c81e2264078800c0b0310041c030964000250008080c1c40c040c0610b10f18a804212043c904104645642000ca054460341245074030700503503074071740a00306845403080814901103042c9400d0401c010000d00145030308180340c00b603d80201c1d0658600003187c0900c2148640d10880d0010310014034142040366401c1c0c0540c41500c1e01c07508040d529440d5074211034003c03103203400900c030f41000d11070061120b220345a0481c150300c0ca59460031a000e9280e907030b01c000314680140700c1d03036030303400014402404034184a140a00200d0300340410055410f205a898000341d40c0c861010a0741c100c20841b80456010709110003550940d1720300c0683d80c01d82082844514110014140003d4262a50a00816200e10480d4a0321220350b14000383d4038035038041201c0b9954000041d41441000203100849243c0b0741c40d55030316884204480030402810b581800c0640d2810001d080c450f00a031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 352070917 1250 352069667 352069687
    0x90909022205060a05061305101b080a030b010c0822150c12020604200d0b0118060803040f18020705070303080f0907050609040527010e01150302010503011205070902 73
    0x2c56070060000302c03888100d003a1580108401c5d0b214103054104404a02c000410141c02c2c020008071004206003441504001160980386604040388400c40d042c100000315001003907014454403030307c89004e00e0040001083c0d9920b004a6201e0741e003101003011040d8091034800304608003000080c00c0c14544040550000d084081d0107180000c01c21102480801c540d1200184002505841550000144400e01100b803149080707200c1d000326081c2e04281e042c401c1d07501141101c1030340b074002c0c440821013101890b16520960b08807042500009410f030000c200c200322080d02d01c0c00d04000d8484140c04052110b0481003035a00034030550500424a00400d0400010325800082580c820000c140018140d81d80c0d52520761749410030380c003449a01120a000e031341d109080a51101c0d82c8501098040c07050030440540803940b5200710074806072160745035031010754407040070f000307400c1d03412880044003000a0071035001a14500050154644240c8400712030340c1031182c200302810040000c500c0840d5207458001e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 352072167 1250 352070917 352070921
    0x804150605030f071a12011a0d022b14010512030c0f070e01091407120b030a050c03010c140d090f0804060e0a0501080402030a060203091203090312090d0909090222 72
    0x40b065800620300710641025142c402c0d000c54010510769004030744180e0a142445203191295100c1c1c3c09980001e101c10044800b161006001c817070481d40c1b801c1e801600034100030bc940c1450704c0080584030300b03003a5441800b05045003070324190340b022140400085a202005072660040c0c50341d01401e031062910f000c280700c00108044050b504413010054140ea2290102d1007601c1030944015091881400001ca00034030868010b8049c0c0403401c4045810396902000928114403000191541d030004c050443d040d00d000d109103c10850981072444141c0301e01c10802e43c071405185080743c82e09890f00080007c00440c1c0708203211955101c1041da0f2555155035004044e41c581d0344070f4600440b1500c6020070103600030001e8038459a401001495006000e980d480040e420280c0140981e2083c01d001410054810010b075104681c0d41c1c000b1a103030408181c8140b0000c4003e040940c0d6a0042c2c481141965401825541601ea503500040ba150040d88045212a10030702c1003072034240d104140d1181141e00503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 352073417 1250 352072167 352072169
    0x231002030d240b0f040306090204060509040b060301181a060d08040b070302070b032a0c121801031515140a0c0606080613170409020c0303010e011202010804150605030f07 75
    0xc0c114900b003610792400c05010f100d01407001080352820300c41000062140d1300602c08261000d88041949951140409c034801c2054600b100e4000e5800300304059420240305030740d40c9400e0b89040c504010040c2d2540d16040580900c15080005400001600d9031107201c0441113442d844070b6069075a80d070303c1d10001c615410560f022030040c010340b500000c20400540c107890150f008a41159120f0600d042d1402c40e03502001030b410034001c81881401c0d80c1150600c0361302542280f031800c0715504d20300000c5180e0400c00781082241414508081010100500b582e8202a14806c00103c4604045044c0039181c04200d030b030740d140c2c09190005031343d0031055101b10b80004241c4201802e000785a100d075509901c03200204c5010082019018041300410600c2c440d10b000f2030018103400e0310305601c4400c14016640090405813155000000401c4041c11510820780103098039054110700034825400240b640b8000b8001802c42c402402c2500c4003503100b640040020640202103903408500765a03480c0c0c1310465 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 352074667 1250 352073417 352073471
    0x20f04030f050f03130f050303270102010e030d020a03050a06120b090304120309180c0509060702011107030c03051603050c01052505010c11010207110108090304030606080115231002030d 82
    0x1b0b1100000305030a0000965a40302e4100d0310140d01400d00da01551205c4000004040c11592a481c00d809140340c02e0005204a80c6a1040541e4072000e0520240a940024004002052415804210b90740c50540308080302035001d600341d010781d11111406071039802180c01200e420030010100004042e00041524111894500b034519400c0b40d0861440448010002c9080421001c000d05203a0b413905c0c3c0e00801d40a03105042c00807010080e40b80032440c04121760821540c529540405000740103040001c0da4200e01d40c0740c28507040300d01790350f030302d544031a0b041c61240c0c18408080355843c4007808103401d0075982484e03500d82c0f00c02e201541c01e0503806844480322001c04524088440d0759400d0042c001c1314102c07504103400310805200f030801103507043c40086c5000304c680814000400020a14007454008114050000c2741700040c0d00242c2d259640710b548030b40303c1c4040c0780c40c0340c5001c600c850415a051280444030403000d1031a09500360300f544118515a04500d1900b4000e00c0840703011038001d000300c56 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 352075917 1250 352074667 352074689
    0xa0b030901061d060d081b01061511070b09090a0906051e010911070f210512010b040e0f09012c07080307082706040e0a0f020f04030f050f0313 63
    0x2001040d040107083c10365000c0d400481d031045040200c0c58903401400001c0b40624903003240b010328002c16007151400d41003030000078003014005d03000315403081c0c020f8910324a5801410303000340380c42c481210702d00c070303140c001c6000d007603840300141c0d81d1103440e03026a4032250440401c0c0702d01e14003141142445000d51665090205410f000450118418401c4c80c0d5212482c600c400d00d442c50f540c40708400110340020440321000a9030060400031101d0740100185a080d4407203d07112105400c22110002c0c058000c1401ea880a000402844c0c50005603141c00c41d41c410242405512003880e15800b40c294500380f942105078500e00c0d05000b4800c40c3c1c40e0b40c0c081d03800000b501c10f480e4482403510f8803807242c2c1c10044e00340201441401640350f00f458400c0c2c0841c3c03418444000300f40c51340f4003243d600d8010703500c801083c002440270030006e40d900380156803042d40f10f810218174006041101700114041c40c000605103030a1124000100032080100d4032090320301c041100d803100c031007039848251a1030754062540350071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 352077167 1250 352075917 352075949
    0xf0506040b010f1401030e01022223060405040902131e050937020306010b12090105010303090b090a090608011e020309030a0c110a030803010f080a11010503060a0b03090106 76
    0x3003120f100c1007035811050b1040c60600c9440d00440c042c000001d030500b03855500700801c00b01c83d043c40000f11031000c440a4420169482e040394851000850500007081070300c06a40a0340a650703803002c84094075022a00004d10400070300204200c041d0a801032540340e031414100b80c10b0100e11058125101d16891400c3c403065444812060710354024030081000303101540200384250040c0300d00a13405c1d15035040c10390707142402078000a16158007a80038400c40000014840c886110840d04203034008102030090202e5495640d009101d5400da00c106c0c03030944404200c650f281c0d540c1c000a41c0090402440c148007160701c41020300e00034400184009610540062114906610f80c02941d1150340030802a41c1030210000c816214015141c00458549600c2c1c484141595140c0d0402c4001c1e50142c0702f920f441c0c0d03040c01450160b010080c0c00491003540000c041e0800a21960780070a103003907081c6011381d180d89580000c180030301351541045e0500c090100820003400d20550102085854490002e4684 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 352078417 1250 352077167 352077179
    0x30b100905060d0e030d0603030509010f081006080c1308010608160326090d0f06180b0c090a08070b031b09030d1d04020d060f050a0b120604090f0506040b01 69
    0x200c40500ca02a0400700c107116085101901d54000424100d86400742c1e0314140b00710103180e00312030890f0800c0b03020450201c1c291841d940e1100a045440c5214201940c03a03041007443c2e400400828452041044a104d0019400703007170141c29103042008521141d003005480d0000c49000e85928000c01c2002d100301400c000c841512001810304903034000c802c14420011340d00343c18642d091a100c980101510402c010800341c1c607409942c107207141c069240b042c182000744c501f440540e90007102c030300007640200703c0441c0801c882040c041c2d04813904003d01c9a492000c0e8003c16240d00c1640c0c00100e05003d03d000010303003c48003070010340c07050001c88204601180c11140082e803e002d1420b02c15010f52200e4001006e43d8010b005009c0101e00a01c05030511005c00c40c002000e990042980c0303207156407506002c004180000c90103001070907007203655403003480c00c142d2802094010300310039141006a16000c98441c0c4c07990360201813141e8000b03082009169041c10155924041030310106c401020a50000481c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 352079667 1250 352078417 352078427
    0x2040e1c0e01022404060b040209100e0409020a0806070905030304030f0308090c1504030209220b0705120705270303030c0d23010611150402062206030b10 68
    0x40305100e40c80400c1524080608841c01d6118a1515040d0720500381c40c0b20341c44141e0090b01600851400c03902c00c036494146050010b41d44004860707805540180650740507a03aa2040700c6101d000c191030402c0e4035125540c00140a03044620b4040c0d08010000000f113800000460000e2243e5019201c10700d015a403082030659a00c2a40320180c00f5000301068500000c0c40f402d10300b42c1100b811f50441e104030080200040c442d02c12010580060280080d0400842c108100c0f040d078880e407010700d52425481c00c074001c0200782c020004028604520403001404160048080d41c208440e014100d60b15880c00c4c0c1e0340601030b9801120304400950110101c0721064000c000719124600c40540070b141945c07113a020b030000d603070084440c840c00d0b9130b26007034003568084000d80c002c0c88900d00d001c510480c82d4580072001d45481c0044001540d01e0b0004000c4a009031081610039804c0b5a0641e1900d41d182904c0b070940e40387c001d12141483c1d045080150001c0d074141c0c0341d000342440c1c000484850760580c0c01040d081d41c3c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 352080917 1250 352079667 352079683
    0x180b06030f2103090f0714030c0103140c030c0c030307030207020a14011403180f0102040603050c0705030427050f0609011502060c070f2a0b070206031306061a030402040e 75
    0x401011202d1100000c45420409540c02081c0300080710085800346600c1ca082004a8003d400c03540d01c82e550318070052600304151110a4020f0804203c252100085207910f4900201204164140040400c012001c12001c54220b280e001c001e030790300c90610707000007006503120040981c80784042c0780e80840e07a50540ca0013a515014140c40704c1090800d10048003c030340d00300030800d0910300d8040201d220802c105002c007607102034182c40016542c501340700000d4200c4402810310015100c041c000100021400400c0341e00fa240c2000860242e44428504081019400542c0511050038182480b500030420450180a240100c0e50001a41e0300d8545000070340039404040c03030040c1d1028020914800c95100100401406040c12806248154582c0108001c102108207000d044c1d07840c0650100c501150010041d00380c82502d00d10b42130380f50300040e4180c080900709200d10504440d0301000c22400f42d202800500350361058040c220034424990001c1d8200316400d83c000d9040c4050b1a03400d03c004581e40c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 352082167 1250 352080917 352080943
    0x8010f050103020a0c03121806060f090e030d0203060a0b120a0b0306060f0f030a0c08031b0a080a030f0e0d02010c1701061b050708060c031909020a1404180b06030f 72
    0xd040321a03182142c540907100903440c102c2d0f9a50007504ca235100207101c040021801600c01180803840c100803075900710099032010070b8592130036442000703c540220031035083d000c0702d500258407070701c03001d00051041c0b04035440040070072400100c0d500c0100d184c2100d503104199240c000c002114070704041c107072140710440348164020740c21114044c581c50030130541254800090300703c1d08000c1d0195185c00e0007201c03a80040c0c689900c0410042c45110b005000603e00c551244041d006141941d03450780c003c4c0c0a80480902450380703942c03a590102d126540600a0442148200e40d22505a4134003e40240508a08440000c1040c1100080041c4c07900c1c0e4241204d1859070b50407201b40b4403281d000302c8010100e104031024000c02d000014521000c11801d4000d68405604a41c0c03800c0c0181000ca40c0580502200096420001d204000da552685254202c900302520b0b0b031119144100001c00901d1010140e410b10a204060f40c42400b4180884901c078601c26400c031070042d50f14406107545c806c1166504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 352083417 1250 352082167 352082177
    0x9030b010b0c0312040c210506070e030a05100b0a0501050f0a0c02030a060c03060f08010c020d12060e0907030b06060f09060f07120c200603040602220608010f050103020a 75
    0x4100440541e0000e00c4185500c01c00c0e20304152460401070640842031300c1c142c461400520041c401118240d0f49001c0410802520002e000d4041c3e44541c0c650600406000c00d01038050034034034480e14107200b101c082d83c3e070000950b1182c3d074001034200c1c0189070140d800750051400c0c00000c2003a5008904880b01000000c004500b840e03005a0308940900610400300c0c1c042c0075a0315001c00040c8180030702d01360000162404aa55810842044007a00305540240050380c101401c840b0440e801195806400700f451400c88581d1100d50406805442c2503413143c201c1c2015030081010095001c141c4000b81e921071000c1c1007058403507100b00055801840303d0610200000c0082010b0342c03808034000c00d01031030701402c91410300c0c00b0758540300c00c001100d8031020017003255800f070748081092100307290180355480395800552480b80804600c4030300004200410007079002401030302d405001d8940081000c002020403c4c16034503440010500e070800e1041c41240c400380c2c2030200c0e1a60290094030701e90b10325076441d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 352084667 1250 352083417 352083419
    0x10209030a0b09012304150c08150604080a030207050901300c0b071a0c0a020705090a1b050c07081c080a0608031b06100b0316090905190c09030b01 65
    0x601440301101903d4041c0c0e0359a20240450054948150910103800e1502840d4041c50182842e40035062860075204005240444501005403c8603810342c114034000f20404241d00b90300040f030021720640d04241e01500c40e20b0181c104156000660905407175054520b01c076940da81d05517000300700440d0540c8900c0381491441c180d03810f098561000e0103240c0500d101c1178202c1d59441005440e54050318041d03810003d4035540072004002d1351807403500520302100c00307890402007250094907650107004a038440c14a0b64080750008003250400074404803490480781e900c0100680250595003c0640a01540a04440014614000309004880c900d80014803048810b200d1001c0f554454000c11210019964640218030148204090005c0c40b03803c150340c107003010000080303d18102000f07001c270034900c5400340180901c041c0c7c00b094a070003000c40c5020403100780700040140c0d1f08240741d4110070b083c00d01d00030822070840704001c0c008030040c40081041003001200e03201120307918800d010281420910f600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 352085917 1250 352084667 352084673
    0xa0608090a150b030606120c04020d141807060f05190512070807110309030d030b1201050702060402010914090402060d11041205060c0a14030709050d05010c0e03010209030a 76
    0x40295880302210069a200000e19660403045100030903004058950764403140070a41401c01006411680484503062a03080010301d55913141248818580580e40110380003450742ca56030030148401400c8035100411340340005820302400d81a045440d0144141c150000d0b0f018003e0b000d00c010075015a81d01031070190001d001c075503034031080708080081200410154080c1070074044d2941c0520855502d0303149905004c20010301e060303070341c1c4203954417078008010180c560b070b80011b05a0007220150501041102c4500e0000300340d460020a01180d42d401e00f000c02008aa000c80c41034840ca100f601c90110407a2240c0111442d103002c031205980004011f4003180c09490180007402c4000f0752100041030341007800203183c039660001e40c403100c2da119000c00b295040020920040784c0c0700801880c4241001600c1c14010f01d40051540400304141d400808680d0f04c0d07200d10004005064050190b500d8940203252150091540301d02c00300010340c43d0b40d2241032524040c0203e68030b0b0480100103101c10f040e151 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 352087167 1250 352085917 352085927
    0xf050a0503040f0807021e01030c0504140d030c08030103030c02090a0c0c020d0503040b120402040f11040314100c020a05010b1e01210507110706090b070b06030c36060a06 75
    0x200f0984020109100b00d0340107035252541030130324154040700c4840d00c82922002600762100401c0714020f02030140401c1c418050038011424080004485120120b803070303070400ba203202d0310000c3c000c1c00c0110000004424560400ca100410920030388030f802c900d50b54180703204c040302d0311514107100040150140e80b025207400745171150780900400503a454540ea440091003181c0c0b004607a070a0f00031a0404100640c80c00b4454480341d0040f01c0310511452503042c0c00c040341d0b0301c29400001c100c140040141d03d6041802c01086400a0315050100801f1a43d1a8007941d81c83c2041402c036060f40c20003500c01403034180102820511300c0c1c615100b0754500d07a004015a1803213400301084108914414a01490b041d6a000c0c190141c2925210030500d80b0220010701c0c00c002c5150000030a00105040800024054030210758013140c012508a440361202070010381005240510103600c40c01782482440045807840042c100300790064140c940c5010944201d80703107004100e6441da40b1083e4000204100c42c020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 352088417 1250 352087167 352087193
    0x7061b17011a0928170307030905270705040513110406050a1107030b0702070e07020d0e041e0b030d0c0b0609180706050a0f0c0f1103070f0b07030f050a050304 70
    0x800744030b010440201140134150b01c100d1103103010380d009401040051000202d00a8010644003c0c5103000c04a8402804d881203030b102d203d01038408020003040844920408814034040404040204d040c070381c00003003094206000c0c5610510080c08655400c201c00d1145081c3c0c2c1000c018130504152810205480f00e070444100c2c10305001c0a61990041764400340007440c06503100300c11022641c02c00c0c90f0001e01e4045550410b2051740c8400062021075034002840282c40d00701440d0076004015030502040140501d02607a120031042c1d02c1c182444442c02d50001d211082044e07080f150845154039044030018122840a0048018100401d010b41030010456600030004a908512520242d591619000480e03001c64000356011481d540c55030b0b031256151100000034548202540c40c2c0d902c662400213031424001746a81042026051320b510305200e0b10000f041a510300100095071180c10840079804404110002084018107031b0646000c1e009a07060f08442d581c0349070031a50f41e0340d2415000810b03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 352089667 1250 352088417 352088419
    0x5060103060b0d0e0c01091a090d120e040b04020a080f06030a050d11010b0109030201052a12040302090702150f04020102100c18051f030b0607061b17011a09 69
    0x1d948002c2042c071503500042004041c840740010f10100d0301c00415040415011500303040084c15041041034119841548400381c1c1e000ca0035a0740c03050f01e80c0005030100802d076001080080505968111140c00c80758541d0360759000d4805000301242c0008000403032003a051024041174514000c01c641d00400d080581d40818041c0c00c40d02185070f141c88440c0f901c26008178082c00640c000c00c00c94131184081c0651501d040f002c0c02e0030184e050660303002810038000c1220100c2a000840c3d40a0ba00c001550b007502c03042c400000039280a0402c0d00c208401e030382e00c98002a8000c403000004191801e1001828590342c7c00400520320aa40381c00800200e0743e0000b92080e03045202c0c075840a0902d103010f21030303422440695183c286880d8150407401e000704046911280c403450b01e00016401e29407025a082985560900d800280003040400141246c040e48201400903445c1c0603a9040a4040200c3c2d02c1e00710400313488210031400200f54203191081d090041c400142d0a40200c41c0750b01c0e81c404042d040840c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 352090917 1250 352089667 352089671
    0x60f0f0e031608031b030306010c0219030c060e0a1703040515040f2403060605030a0c02121603080a05100b0f121f050603060a1707090f0501150215040605060103 71
    0x12501ca680c06072020b01e40018600d5000051018251030410b0a900b0b64000035001460852501d8000a040183c14101c040e009945580d10700781a0068042802e01a50740000e440b888192998002031440c1220745415004480c00c0201040880324241c071010343c0c101c4c000003145854201014000008482140c41603110414840441c41450348110300020300980e4480300409081c00ea002d05805512400c900203051410740300748030f240d0703000045a07440300c41d80c1800700d000015020300300c1c542201c800250003040d01c04610101001200c400d4054540d00940d42d0301e04644500c407000045070420348840704800030b910800c10402040f40054503842d41811803840c04c100d0840141902c0140445003001e8520450810403100e0032412407580140c541580c480d8194038264002c25980603147c007503442e1040c83c081181c06284401c001c01405012154028400e2000070848440941028010101d6000701e554981e6100c40c0700249214101c0820b107000c92141c0c80d551510350081c0341c05482141095 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 352092167 1250 352090917 352090933
    0xb0910030201110f1506010f1106280504120f0f05040612111305010801060527030304033f1e09080f031306080103050d030203090a06050a0c0801060f0f0e03 69
    0x18505202864505d14041110403140c0b908034001007504442c1c91405c0180510003260066801c5c0000702c0907448282c100c8a0fa03442c2e00110f214018001c0f8641a1401c0365060070304200810410310102208950f4944a034070340f0b0f201200b42a94254400701c001c0000600600c81048101e00c284d42820001c2d5141c08000b800740301103240c2d0039040e8420340d01d92000383c500a00070422564030001c414013714040c507180f4200ba29002034201d50300300c2160030890018002c0354070140c655081c000c03a0010740c0d0000844d040042840c414000b41c801d00d0100d0440c0c00c3e444515000401d101c0c40070303a0046c1e40250b03900b08481c0310322050704101c5107a40e44014100440e9403c003080d41c0904111104520040000850300c802035a000c0b40c81c5803140d500260104420b4500400000e03078000ba80404900d41400c0260700c13907407a0b040d5140b8003111114060700c0d5608101c00d01500d200154081c034104026640e030004142c0c1c03210001e440303070000c010009001540c01c503075104043c2c1c4140d0300b8206c00180101070342c6003c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 352093417 1250 352092167 352092193
    0x40302040c0f110f0705010302070c0801020310080615011b0507031b090501090207050703020913081308010b040c1b03050f040f05011b15180605090606040b091003020111 75
    0x4400d020200300c0422001006500c0054000b0764544260720103d0040c00354650300364001c1e850300b1452140c42d06058000c50501c0400119590001c007030705d4030320002c40d124075154a01122084052051a42c1c6000c3c03080840c08210004012070300c5980183c40d8070070041c046080307940c5600c0101c24141e81c0c03170280d580c011000030051440080d00d208202c0e045084c00c0d0510103100121001a030102c000d481c81007100d00001100071a4510482e601240d004140e82c2c3c502d600340c0003002d50845c0040502c00700058100341d4522440150040e281888000c010a4002800348411500e01c41c0202c3e0116200d010704010a049030300308501d60300d1191606505110080030800c01c0c40c0c0098020b221040c641c40c5040c462540d200c2c5803d009090440c00302c82c0c80281940355440c041000380e5044000d0f503100c4c480d9034840080e2050704040590321410800c130780c1c0707040700505442d0130041d0f030402d12035810152168150301d000d0781d0880c02003500d844024149451580159902507100f07640e64228000c000c0c0300f51003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 352094667 1250 352093417 352093421
    0x50706140708061903021005070507080105091c0305151e040509060702010c02070b030106050a030204052106060607082d041d0606071220010204080318030c090a0506010504030204 79
    0xa980c41d40c64940881c1012410028074004400740b140c240d10320090304001580e10b048036a500070340c071814100d0365864035007070103820f000907904503200c80c0d8280400e0007041c0304002003540706141c046a034640b140780001e0080303080e604180e40701d4030301c03842c0130100102c00d00d0310790b00b106070317991f904202140050158400306064a004a940381a1a0021010803002135020302a600000c05c080c80500100360804000d80164003060150600308040031413000c813118003a90446002e0f200007429480c40b068407007540350b200508600460114018180031500340d01304003041c2d03410540e00c541210308251f4004004030f03120051005050b509034101507802d90340c94124000f00054601c0070444000d83c0884a0328005d0004003610a03409020104011030200d03401e07000c1c07402604898078202c0101d9003041e00240580e8904140142c3c1544002400030381c20b43c2c000020460f2209a003045913029425508054507003401c0050b282e08540d1030400242d8204d1180d010683c0050141070417030078181c8030380220701 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 352095917 1250 352094667 352094671
    0x9100f030b0a0609051921020a030c03080a020d050f0a030b1804081206010216030605190c0905030709020901050717070501050106110f011a010e061c05040c150203040605070614 78
    0x10103c4c00700602880241030814034181c54207003a143e00e419061522000506010210a0a02c00c041101680e0021566a605020700840d080b101d4a0300755600c0307042c00c1d40039501100c0c4d5000580302e400d802c01483e600400c19180441c000760707003003800d00440b081e080d000740c40c02901c02035000b0401a8403595510007410b13107a01940c00340c40000e440d0440ca5014018100024198505540c4590300001c4000503040090042c0c2c2c5c4d2240300490603486851140c6040030079641c1c15132825007480e020801d0a075001442e04110740084007104c1c20156a601030303008901c0f450042e80d002032420030005000ca0903040c00c0030b942c0100744102c0c038035183c40c0c1d40350715084880c01c0c0c1220000030386c05020381003031560422030070205007404802003182d0107040e0203c0d41c00e6051307040c225041c4900384d0080c00302c654401044c0c6040044c1084050481c038046801d120041c6000c81c2c0407584000c601b032011030080b51294552880f050310350000c524050a00c0c00581d01034000b690300302c0f034182e200c100d50b914150483c0d21840c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 352097167 1250 352095917 352095929
    0xf1b030918140109021222140f070501050f0d200a0302130e090d1d190e011d0c130320010908030c03040510020c0a0b030609010b09100f030b0a 63
    0x24480b9803012040003095030603031042040c1c40c01840150f4520381900070b540c0d080007591020380100394105420b0f0700c0b030b10860707100680300420344200160300190200e020144a0042000da4140c1a250340040d0750034051782111500d080000c4c00721070300d443e403140d1000d40f180b04c2c850b2410041c210a801001380c103a0201d803840c00000d8000c038a40120080b40d00c182009800c1c254240300c03283c544555095035501d00c10100d5401c00034501013200c25400070420401146002402c0070303c0c0052400100d03400742070075120b0301c0f40c44044240001116186580894551800d495445402e0380f14000d5505035a0481100b042c00601c00c00740000c005000c000000c900328840c8000e003080640000d001400400443e40000c025030010884a5100500801101c0a5030070440300701e0090200e0b010202d14081d0076803250f5420040b400408110301142d200070314411031088907801e40c80c3e80c07910703203101640c050510440c0d00710920f4903a00c0b00742c50050214940400d4507144c00940002c0071b03c0040d158810b158480 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 352098417 1250 352097167 352097171
    0x80f0702030c1512010e070507060c0302040b0c1e0307030f0e0a050a090b120102130e0a241404020909281b1106130215070b0103080a0e010f1b030918 66
    0x4820702c3e903040f0013681c010061784200400a2402d007002501d98840d104d0010328050361260078103821400307581510068502c50451648a1842c0c2c00b11542c0c646500c001d1f0343e02d40081042040b1a00400000c0b40c1c0c91a5165460544a100307098090f21a4491480030651003840075601285603114000c0f400000c1011b10b1020801d0781c42207041c010320714404200d100007640100b05044124910280c25070840e2042d500c4d048869480c1c003006802810b020000b40f88800c41c401200c0403d0840072044001e9400450010000013030510410003203205000d03003030f81c00a02803800500c844030356440200000903520b80303a04014005081c0542119102d228140c58840800c2450784000d5200e000d0406442440005056504203880c0d00e481030744502d84d000344980e14034200041143d040205441202c1e03401941800907585a1404410759040740040600007504104142d80d00d6100cbc07400088131141540320407408941d90740ca14149001610f2040d014014980e40029810381c840e944102120203503040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 352099667 1250 352098417 352098427
    0x18040c1e0e0c041403070312050901021905060f01090213050d060b0d03020d1403010806060d050709050c0a12090f060e011410031202150a0f1404060b031009080f0702030c15 76
    0xc082040c4d0781500c03019010780c0c04400d0034400100d5a217000c800d24103890420649075584070703004030316200b01400064070803082101c5803c10003000188090156400704c000c2e41a0741e0300d82c1030403c12401289200d81c0b410300d000354101b255080c44044007800602410011407440c0b90000410074000000350120010792103607080c60307582540306002c0117051503001025491949012051580c60f070380540070911a082c0042c0c01d1042020801002c2c004011016041c4420300e0480e034409155000ba9000703a000c90720f0007402c00d02044491055000b0254003403028a982001c9480704001045d0f030326080102913681d49102e03805140100030f850b100ba0b00c540e4580d0203890461624180e9261a0340701c14044d588040008204900d4592440c0d80c0840101d5000542041c4800408064410b1078029440f04844400340400e02040e0342007200100c106400b1a101c03040190303403082c00c42c4c881c41e03000303480031800344042030903600703040001c00c2542d00040494a0450f40c40000882d181081103000c8c0030001c0000b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 352100917 1250 352099667 352099679
    0x161b0303030c020a050c040b010e100306060e0d21110111030604110313031803080a020109061b020a030e0f060a1101060504090b060d0c0e0a090218040c1e0e0c04 71
    0x2401904980c1440509a41c419980d0317400d0385c81707074105443c0e07204d6901c40c03100b9400382c0d100c6d03e0051940b000040880c114869a1580600101803038004d010002d42201098106814400c040f2140070354003800021820340d108020100e03002c150701d500820810200f0281c00440d00034003c04603902031901c070311552410518201300444400e102100c0071541d05204012048201424410329280c05051030310204503820114040204540c20041c001d40000c99100f0009905500102c0c0a42c0308220821900c0a0300420104415503d00d5590059002070200c00010344680c40d401e51420f4040d0000c000a102d20740002c3d00368100c0200d83c80000e03c1030403103080d40d840901500b0001c007000d40b401c100c0050a81c44117241c1d8000201014001c5060340540d1080090f02420000100700107080c030f024909166214402401803200709034400d02c02207040c41000b02c001c1c800700c0d0049078445d42c0101d80510307010710024040f85040d90320107440703280d030170000350303042402c800c0c500c158a02c0b90781ca555241840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 352102167 1250 352100917 352100921
    0x210102130f0b0301050108220c0302091305030d15080a0605071b03051b0a06050117010c080907030609080c0105010609051828110c0a03020c090405030a05161b030303 73
    0x15022000710041080100b140304030110480341912000c0c40e007185295109682054907601f141540e400f0b00c038400f0034250501c021060b91a0960344200c50b020840c1c2c407400303e2003140303042000d8064101c2c1c200f004a4550026a64030980741440a500c1c2105040d542e21007250a0001041040d28519280c0e0100020240d02c09000a62400c81026040c030900407518014094040d104162521855212110114a0040200100b1594081d41c03e020359a1034804c800610101100aa24a503007058a007034003150191500030310030382c030b0b46004000092464803030038041c2005120a44e03000b141002802d03114042070284e2406400d43e0745880e10001e00d000280308a01c0103540c0b04005070f503032a105007c02e40850180c0d04455840000030780c10041c005200c40401800c00521500c0b42c2c0d4400600f49031020300c0852180d0019000e03400740c5108000b64028410806000c44000b4104d4000b0404000c2e1140140c015011004410388010304c2d0305156521a6141f46000c03c0040080c1080c41c0c040003019494 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 352103417 1250 352102167 352102169
    0x15051006050406030515090a06080d050403050606130e06070c021815012703030e040f06060f030c090f060507050d030213030609020427050d0207051e21010213 70
    0x54100058062034214010002d01403406040c04150b180d1300440c4042480408044038414001e2000c0038030304000640c1e030700a01c1d00303101d10003880c02240f10b9194828007410960341103a8014028080c0365483c40100064070081d40c203680000c91751031070300e0721169400304800c1d4481d60386602d03000e50000050040000482c14034540a805085843c10000035403900018411b003410282080d0700c505000d03408144082411b55909000e100307000d6400014960302000342c0900070020f072002c10403107101c1c0486409807141030140b00301040080a0004036540701e580b00d80135401240c909104060b454121211658405a001c0341c001000442c41c0c00900c90300703001d035191130138550504514154905000c4140458244805000c0e03954401c025010742d180d40c0c0203188520488a041c15441d402038800710070901060303101781c82c5846841c1c020301c0e5050000072204207039540200403c4881c0303000710f80781c074036808010f440d581c0250031030b030f680b0f248280314040f00d0440500d51000540c49042c000d0802041e0001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 352104667 1250 352103417 352103431
    0x180f020c1e100c0e040e070b1c05090a030c080a0c021009180c020606040e07090207060e06010602010b090f280f0e06221a090c0909030a0905090916031505 68
    0x1c2c000b0f42d10151504034002c03400c00c4506881c04103000802d0001c1d10700340f482e10b910180041c800051114008100c03d1098000f00d04807c80800054855488899403600c04405c020045000e074281c1002260340c44014041d10704052924103c0540180d0201e40035030440c200705800701d0040002400403a4084007080d42c10050b1038010006c164140000a40d614000307860180600c0c0c1e62501c1000c115424004a0081c2042c800b09550f51051454254010306244500b0001c60103003400104687e0700c10f000707688510000402e401c0c001c3c0c0350080109215030f00600b14903051013805100360701c0301a001460408064602100040f401310b031014150a0f6140c0c01100f4603150006002c01c0410002110740c0c00c40d03081d4500b85920b54200d076151228061907280401a0314034030305030401c0307100b4030300103003d6040580a441c04401a100e601c0f9003a901d002e10421800482c03d41c1c181405641000402e80f03500c10300c408111212102c2070a01d10460074a03903042560010340500a00300c00655500070741d03801c141 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 352105917 1250 352104667 352104671
    0x30d050a020c0703150905070e0402030f06100e15040905011a010e030304120302010b060301080723010806090601140a08220201080a05060d120203090f040204180f020c1e10 76
    0x14250728450f0322550702e40001000105802e80c00004000682e01c00410154024111030b41961590042242c6d500111012846442085e0078900c02580105407640603401a903c0f40541d85d050002c400e070560401000c510180c480348000c0c1e45155207034010981c0d001c0c045c00000401c2c010300503003a801c41a8082c4c0240c140035851200f1005903c00008071400c554501e100071004a100346001c034007509401240a922000c044008121800007041940c111030140c80c0d00620070b0507012058504c0b4521141042c0800c0b081c0300002d80c5810588561544590140750002e481840d03401c0748030240d003001003031400081d45501042003203030400340c04541c08821a520301c40c2c114100c0d40020200c0400820501c40551500041800d40e19030064801082da0700c01c041002c84150090000c0d44d070b41107050210722a200e0a8140c1c411403c1520898041e20b1412070340010841440310340d1405072250016a01c500e40d4200101c480b0b101d800d2005160210f5580243c0c044a541241d940c0d04d010f100e4040080388034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 352107167 1250 352105917 352105927
    0x20c100c03080603120a030908042403050f0c16060b03100b0405060901120305070f0c1701050f011410020703060e0d020708010507080610052a0d030608061b0d0608030d050a02 77
    0x91681006c0e180c070803c084c81d000c0386090051415441b030303001c0c0b5480322440c040b0036044081102402007111041700690781d800c0000343d445ca0502c0c080d203082a1400f24070071000b000140c94100310f00b419290301c00d000b40d801141400314030300403d00e04441114800702581c1e541281403c1840c00303000303060b08480c0848492690354102000300035498a10b40000b820721100007014010849c62007800d00c4619084a00b0303d124580d1180054104912818420f0040d468000064111012a6402d9050b50641070703043e080c80b4000014040d108480440c00820f51190b92000030000d09a0b000d000387c0d41800700050907100c03204c01d401078600180354200e403501d0b0341018100501d50741d010416550202c8102c0d044640c0010071541078416100b41c0608941e180d4105041512035a89101401460040c4108a40411910410490488446000e190840d400802c0401d115968480360800400c00d000701e0507245c011302d006070004941a0b079000c0700043e00045404c2591070b01d10300c141d5038010890f0400303601c1c00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 352108417 1250 352107167 352107193
    0x130b04050a120210110f010618140411061c02040305010902040629180301050f0405070f0605180411070609020f0109030506070305040302100626011e0903020c100c03080603 76
    0x104000902150412400400c030040418040040140c01d06c2c0c454002c004450b03d4a2600040390400c1d0a6444210301f025010704018020388e20040c0f00303d4015a80c41d81004c000002c005240c1e008902c08200450402c0f0030383c1d00c5840030b200810082d44201e0000540c0000c038410300c8207a805c15804412003020a00c030981d0442c0202000c030100100190b425903540d054110008d5440e070001287c02c3e050762921003000780803604825041d011710300038070443c1c084507990700b00a2400079650182200052003070051005030b8144d5102559601c10060010440d80c130054000c00e015001070703030141c0c1d0083c0c546500340c0650070044400700025500b841c0203115035080d07031105a6222406480001019a01d0b40020305141c03080c4940a45202104424086c0503560316080c541180c0880c89420844d5000c000c01c0c115120510460807110644505405000d50080440d002000c40035401d44c01c2d405958100314040d911640032580140664460360190b0401c0d0600401640d8024051402684580d90000c1d00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 352109667 1250 352108417 352108429
    0x120a060c030b0a18090f0b150609030307030806180c030115020105060604050f030c040e030706060b09090402010f0c0602040e2203020718090203030c150903130b0304020105130b04050a1202 83
    0x941d640d419081451324100b5510320018000900d0241014414506050030080c0c405a0130b40540310700d224035002d400200301008070610a1400701c07981036004010700c00009014920312580620b000305140c4001d84203441c030a8200d001190704e10304d820800001482a0500c001e80600d202006100030400d500d0485c003c00e010740700f60300030030303118101416800b005036604009910b80c141c40500207001142100c4003ca07529000310301c0442e100c42c1400f0000c43c0202529098601e9808002c0018945850302d0700151501101e031107690f02000362801d121008142c0c0c60000b0801004d0f0030042c0318a601c1d00607036040120b4145885040340300185451900842c4d030018660050740d5008514624420f0b0f000070310700041440f60302c02905808041810303494020003040d03081c54040400601c0e039060b9030301203500c1c3e16882036506c000e01110403213005228940211000e980e000344181450383ca000341181c00585501042e0340010508480090309129a08145141c80010102550b5a8801c1e0310a9400582 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 352110917 1250 352109667 352109669
    0x8010b0324071409221103100306020c07120f020109080606030d0e04021b0a032a0602030406021b060910020a142203050c04050f090d0e0a05120a060c030b0a 69
    0x2001012079480c20203990344822100d02c0a0b00a00c51a051000b03174009503690380301104000c04040c901960f016100d4060002c5070320860322100703001400f81c255a03801000b1b41000420b00f90910500b9004219030b0f142e10038141d02940103c0390001904d21034030004200c14040e8200030351070b40010080c042162400a604090a101410035482a65851011500030b009440380c1c1c066001c074504900c162807a0106801100900a54440c40d00e502c80110407031300a049082d0401c48074613406a001c0105900340e01035a04248640c90141c03802e2070300c148800c4030b00d20410f45000560041818800f05542c2080700004c1c070841400c095041c1310060802924007405d903440c189182c070300003410307084180c08425074a1a031116003490090107507c038140b441d918105e05900c503004502c2d00340401d10b801d02201c60107104198034401844803520401e001c83e0ba1401c0b5184007074100c01c0103c404166030303417014a00c1a05040c0d01004003a1100700b03080840584140300300007400e261800c806042182c42e400c011b04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 352112167 1250 352110917 352110931
    0x30c120c151e140d05090106050925030f05010806070306060305070c020405090312041b0f0509010b160506071d09040201200708010c0f0e040b03100b0409060608010b0324 75
    0x2e0400140000a0f10300c1d001ca4450000d010000003903180842d152548028000c0c0158002081055190010f1200300300301526041c100c0050761150b404008004035201031601c02910380820090030101201c0d0a486081c1c200910540118003003041c020360620401005122a180074400d9040c80030024108000520340039004070f44403800a044080100704a48814004c68810421072500f03080844c82450440b03002128907489a00000364050003181b80c9040e200c00504407001a480c100d0079240700d41c00007003e041c90950521229011a0007031041030710420a0362100810021501900c00c480c0f40000442c5100b94050014000580d0f4044031513051180d040480011905064284514210b216882022070750700306055010110303402100c0010019182e26080e80c05150b0208000c15244804016138155100c001408260a401e4005a40c5048081d0001580040540320103040c1d802d280c022040680d15548402d2181c2020400c981004000d100480c56074810314011519144c1e000d8510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 352113417 1250 352112167 352112207
    0x60206160543030221030c0c0a14010f0c0302040f090b0607050303040c0501080f040b240402070506010f0b030702060a050403111501080106060320070309030c120c15 73
    0xb445041c1050b2042c2081c06148081049540c5982d00c080c890301080d003141200140039001c0144e036003c03a640000303a480c00f11404e006065603101408000300b501b054032615013611401014602182c621380d00b120250030a4800818104400d80c60b40040e40c0d101c8840d4410180304000070001c600701034251000340e900c2c080b0045003904545000401900500350080c1150000101b8070007081a0074000b0400c5176000c1c3c891013400d588807500302082c00c00849018061103a10b40001d007004030341109000340d40c10400824940c00e1043c40c0400c00701d0304800821030b0076600c50707001403000307820402c00c0c2c0c4020485050351a240d0702d03041c0b0000752030b0302000c0c01c088074045e00d0b480402c00301801101e143e0f42042c045411918809001c13009a0f20410080c444e21000d540382030070120320184280076a400c100b036804600d00d000b00d01c50320444d4140c3d01ca494190100b213481036010000460a81442e0001c200d00c4180c43c00b5922142840d0848090544c00f0380300c040e988265161000d07800c003e4500c0c400d100c0c1c1e000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 352114667 1250 352113417 352113457
    0x105090f0607050a0206031026150c040b0a030621030f0807030906020723190209040c0e091b030d090504021e0a2604080301030f080c03040603060602061605 69
    0x441e20f0130312000b50080d0322243c0442049608160300760303400200c80e80424003a10a4030018000f582d4054101c2036104150001040c940051412041d80c640041500b0340440c9410358a005150054200440d01400a9103d500c00c0244a18081349024010b022840c44c0000d0341c11075402411241149480030280f104600015120380d0095001141e0070307030040c10a540e100c10130714062a111005d039240c104d400e08641c1c20502420710000b40317418092480b00e0105c000e0b40c03a030340070000d09800c010012112001c030443e0200e500300b0314506d011302070391800c03000301a01003514100d00b140081401c00140240d0050120400c410b43c0702c8031000483d10147da0041c0c0d00d1030a00044050503445c6e4181403400c080c0080c5108940c1c1e44010f00701c400c8401a40d0008140344007030125044a02d0036100501101c5003440148049500b91a018100c030b48280d0605191800e00c005103402c40c0c0190380001d000c0b07665020204015501485010b44c005021140034500080c0b182d00a8800d000d054480c00a0740000d042d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 352115917 1250 352114667 352114673
    0xf070801231e01020d09030c09020d09080c0610090e03030604050403050c0d08150301060513020f1608030403081513020f04050a091505151c0902060a031a0105090f0607 74
    0x824281140d0180200c0070224007000000b410030307880d00701c49005100c1d103d4005c2140e4400c00140068a5010488130030203440d220800f40a034000e240149106076450000300e0000e1011802005851295070250001c2d142c101d410780144501c0383d000380c2100e4240140950040c201104480d40150304641c0068180c60300e040445040c041c510001049201d03a40d407443c1c0c95500700001d9482080b0382c458401718144090f00b41403c4e28864070489400540c4030310190380006c256006010444030700d20212b400c00098403403c501180ba0540c041c2c5010500005100c24141d201c80001d502201e15040854518030402c04254100804244424010342c00710b803009050054004a07001410010010410b40b80c682042200810b0003164a402c803031003201c0001464100002d40c08907003043c03645100d0070140b1483c0701850005810390f00c3c504040d80e4010100041e0340382d00203080c00c0e241d42ea0380001c504d00c1c0045013140f404421800710341070040512150703080740d881c0f005500c0794020594050740c80301e0b01d0b8a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 352117167 1250 352115917 352115969
    0x17011403120f122d100b0a0e1c120e040b0406120f05031306020f0115030b0a05280c0e01091a0c030909240901030b06192c0f070801 58
    0x41c4141400c1c1321102d842d4071644401d0782c490300400383c4141503a200b50740c40301c140c0510302c1088804000308810340200d600b186800030b044004c0908000035034251a038541e407012a5515803003030580110341211054102400d2910a00384036000641f01040a46d0070110040d0710050502d90090038079031203440c0d00341041000e1094a400c4558402645da010351225400703912918045c00d43d10040d03181c40c03582c54003001014010400c030381e00000584059150248040042c090062a2003900741c003c0d08582c4c44150988145070111049031400620180c0000b00108902c110402040c1005180402030200c140701c03400c000c803c0001680700c4e658400c032241406003940502d500440d840840f001c200500b45ea00b15035640049102c403540a8029203102c010003074900820b020141c0428510000074400e42040038240c40c04407130400c01012607543d111217030a6598248030f40d06900e5049070745030601029025040c40d401c07008107805040d4a10f0541001496498148100b034419030000060340c00e001520 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 352118417 1250 352117167 352117201
    0xf010c0b090a05160e0f070c08030106030903110f06130f0f03080f0f07050f09011206090b040c02070b0706021b100c08060d020f010302090117011403120f12 69
    0x1031039003052441d0442510751100c401980c00c0d0748034000c1e8400005981c0e040e2030700300b064400310740740c2410a0700c44405555007414020080818000c25000102c04101c21002950080c01e0030303500400c2c80e10040c900103101c0402a22480711913440307002440d50b2040c012666652101d10300c105201032800d00e0402840110450101801c10307258080700e40c0c2455030210446204a00500102070207071a840540340c5554000c44a42002031070a004558110729400020038415070f05241c003e02c40d90800c0c40c2c82e02107500b0f5038801d84805030f440086546c2420540a0a0008549130016124240c07038401d003403056211f80180101150340c0000c4001e402006400c0102c2e03484103400440e0740103104100c058008052200124001c15013100004032985407403440d1000b4542d01410a401d440040c00041d006900f0640445051042c1078401d0362441440c1c03807202d4000c01d00c0c6000040524810f00516003089481840d008503ca020826500da142550040b2030888030010600700d0f082d41c03030300004031020100d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 352119667 1250 352118417 352118423
    0x100929040213170d05070b01060c020d0b090d020c030c0d020d1a0115120516080c2b0e150f0a20030a14060120030f0f071104060308090f010c 62
    0x6032100210340c00502010880f511000c80003120380480f094401aa80c5000304003009101c0071800005001c01446070031900c000f80c0c400b0f803200104e0340742940c500d00000e13030490f40440d541e8801c070b120360710682e030401a401480701c0075005000683e20b2300010030842944200040e0042016441010030041110440b0b21450008601c1d559156140c5601560030181000c444000940600390f62400e1201c2d0700ca000d000304800407805410b452001000d07604c001c0014074106503100103128954103140504040e9a079500d482e115114400417600ca00011104d04105c0040e09a21130340c0400900550301c8203064202d620051030302d04aa550242c0303400601100501c458045c01c2200641d2000b48094000d50300480300c40200780915540c801040200d1802241c0c200d00180351032040706402c5408a10119045540805a0385847c0d03013a10344000070b900426034030408900010f01b0106010b0000c075038042481c011181400703002d1640d1101e02c414003034640ba551090b0529903590015030701680301c600150368 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 352120917 1250 352119667 352119697
    0x50405091203010e010608010902030c0301050d02030c151e0a020601121103010f0603110d120c0203281403040501140a02150906091e19020d06141009290402 69
    0x2031280300407000c01303100f882018003144051300041202102030003601e03ca802a044414116032a1400300700c3c80b411041402c3c0d03098060041030300c1a80e100c10710440703d0080c0641f10160703100c0c0100982c500c521082000702c10410814400002c00303542c00308074241140c0d403e120900880b90039042c890550842e05210980c958039114000c2d909201c140c000404403805080340c074410392940340510040e08106500100042c4108180109680c00ba80e940d00c0510b0014040707d800c100c2d16046004400e82002c4190460040140c85404107c3d0700428890b01e100100c5c0910300309403400002030f01c2020003054a0f4140c0802042c0d07a01021320030006c24203c000406005546402c03d4a51141c8a00d01502c050045018250002541848901410b004a005000240f0b0600c1815028001384e4030b01250499014140d002c00300b010a00d9030203001c055006048012000d03040907020340b031005005600080b941c07030801107418007001c401d4114804458500851405d10340b8082d0014000303108550071540b4090b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 352122167 1250 352120917 352120919
    0x50705070906080115050103020310030201112112010807080d03051b0703110c01050423031c0305010602010b010e090f060105041a030130030e010212030f0405071e05040509120301 79
    0x800f054000700301c010044250049000c0d20b07540110180d220840d0300080761502e40404000652082c103c64108494100c140c4035a10030307800c8980445255010003000e40304012584440d05c4070000e4082d801040204024812185010041ea41355140700c0050010715540b00002200300f00d407554040800320104c0301300c55a038042880e02514500c03200c00d41007014400d18500000650145045409840391540c0264000c2486030200ca0822220700c04d0b40d406024042054030b40c0790513090320060401031600c0115480d81404002030840744035100150421604d42d006074144d40303490341c401c1d81009003980d032954599602070040c3c0d500c0c8a1030380103880c0900001e00140561036500041d6042e500d8440822a01d20b0040708160308002c00301c070603440f034140c01c928950b000900980072105040da060064905814944080032441c2c0c0049401070741c0402e03000100400c00c40203104140203405180e4a0528403c9a05401c1d142032002e801900d004580d5200840d00c030803400c1110017420310500d0302d5556a9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 352123417 1250 352122167 352122179
    0x206040302270f15120f0703211d01110c060c030a02010b032404060917190c0507121703040c150207050306280e0d200d050705070906 59
    0x203440d80642c0c4440c1c8441c0b90000c9a4414218822203026188850000b0706508100c820491000c01194000d4030900c901000c644080800344940300065015104c0044c01c91482e00c140c01c50740345082110300810183c0000ca100c0002c240c644869400420710305030040d82d10100c104c4c0c3ca4520791103c01944401c0100d40300d4100f03200003005048103801c95000b0300204000c003040c1691400303240c42d100061240548074000307001b4203d0b1080d0b0311601030b060101d00d03000d1580362007806c2007041260640300f040c0000c44200034500c0d1702c0202c607161240d151140004209445040e16503019002c2c054859841d04140018041c400380344a2420500300c40c007960328141460444001c140910600321002c0e05d200048100c58008903117041154005400b80c140766513070884143c4c3c51010048002d40f1a0721a2100c214800302900c074034160440c51400030860340d60401006880c06115140d01004114004000306103448081010100c1100c40c0c1401d5480d4506480d006007084410b81291624a00e814400551 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 352124667 1250 352123417 352123459
    0x80903100f0b01020d170412180914060303072d150c03060f0b1e0c0109030e090c09031b06091206060109060906020309100201020d060b07150c0206010b070206040302 73
    0x5185801d8017200c00c4001d0200040d103440c1600945645000da50328005004101d40c6000c0400f0100c151401d0803603600c1132060b001003000030f07801441d94955075078404042012451040340c1c0003041100118104030843e940c203501c000080c040408409201071600b6000c284003005c0340170080d40a0105d0b0a03100b883d00740500248020320711000041d007015000a00c0010200d0071b0415184402c49240c901065000c0d503801e00e0315010054207110b142005252403062081c49503810b098401d030780d03078044244c1d11400c00c102d2400181100b5104441040050565600010300383e60b60400c680c08024440c220034001381c0c1e00c1c0240ba045a40007a010402d44442c1100071402c9172043e5030981b40d402da20340d101c0c1e07400c60302c4504030b000307120150b4405c0048034010320700f03020b0144d0f90000d036100151605410740c200609442003a80600c210010215802d400c200310354008070302100e4901d030104a001d0045000954521040c800e80c10050720001c1e000d010754841600301d9000d15009444910100140c40044032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 352125917 1250 352124667 352124681
    0xd03110c030702220603150c080c0d020a0e09010603051f05061b0316140d0c020603010e040c030c0b1b0f0a0b070c0b1302010314091e150c0307091a07080903100f 71
    0x2001920346080c52230454010a016070207140e441c00c000b41407413488401c920003903001c00c4210080c00a47c50540b1340d140d880805c1c06003c1c02e20b0713036008100d0b428000691541c46044122005d2100c0920205200946407503003501c01003c1103444400000302c0c04131445003588103001702d80314040004002841448000d18020906072403200441c0e003031640d8100100e510b000e0000380207500420402c010451190403e031390b99000303401341000040c229640c3e07944800d11546548824101103001c544603250b074465908085891400001400d01d82c40881d4800791a000e440ca001014801c08101007031886105102624020340d000710300c0215400c26040744109601c507035000b00e00285c200101c0e51038a00b44607800310302806812780101a10000c0d030955400c03044885002918602c00c013900380b41c0c7d0402110b0308a00030740150b9102d41d07503070800f694001c103030220740d800c10307001000701d00c1401d10840040c208903420250003211107505c0720b22a200003424448840e01d800d841da400e0108401d205126648108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 352127167 1250 352125917 352125953
    0x1030302011512020901030f05010b130b03070e04020a0312270f0603180803070212070b0405070501090305030301050d1515091802010203030610021507020d03110c030702220603 78
    0x20848030383c2c40540700344646003001c00a40012541004000140d080d8000510303441c0b094002103808480100807a03001050285c203140c100e40c0b2008a1102801c0030b0182c14041d041442d0004030380d00e010303000304511084521008014803403580300d000c0503c0c0700c0d07101641c0300c11130074003040504444070100b10400e150f03500504182150011000a410740030f40704116086034940d5444250540d0342c0c4410001d034000500031000c1d0b000b08400000301400f00c6000380072082c41514200f48500b401c0c10107500d003c03503e40156050211001c02807000c9103001050b207044490407546115a400f85151410008000d80d41d04a00c05080540061106600400038816074201c19000c20900e82e13080316103801001c41c0403029016030800c20101da01d5040040404040d44010b00486804450b80400c040d12406c08950710001170300080079241c80d61b80d01d1302414182c22141c6851905294001717144075100c2c070034140002c0c400c5141036017488900c2e149110302200440701200c20000c0c03681d40d05100e404140901001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 352128417 1250 352127167 352127201
    0x1b03050303011502100204150c11120106090b03030306011b05120f0c01320604090c0e01150f1706010908010e070303031d0309010513121a100b0a05130e0103030201 72
    0x518031781060307482680d045401203a090100c0c091f00e00360035100e9181420040d00c000554408070042a1511082c0c0411102e580000250051078034140300e0466600f6160103102c1e070020024081d5a80e48403101c446446204582c00100d0b40044c0303090b42c44e102e42100300001c0b141c004100f049840c600700000d420940d482500a01060740b0fa460900b0200459245a08080b140311108220440f61510481c0c1d02c0003000e08001003540c6161200854802c5507400f003943c4041140c01840071b210405184160003009040451034600b80201c06441d0302072039903480e902c080700000010714589c030641340d82c0018198000200003151307021490a454205900013600071a08201c140311001803400200d02c05051208059401c006820b00111115403007401c2ca0301200d9801070340880d01094015025028a00c5030483c00b00c1080c0300c05c19160702c1280144414001191900c0810040c140c2604403070100e030321460520b603201040b00459080c035055400000c00c80c0d4410740003208040d0150712045401d030840040d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 352129667 1250 352128417 352128433
    0x14060a021c0f080702070e150a081002030403091a030c07030c1a1b0309060109051312030515240a02070f03080c010e0706091e121104060503010c0c1b03050303011502 73
    0x100ba65143c100340f1909800700f81920001c1c64900e0002c0d108e4514400c000c003101c00300307a6101102e62510104502041409a000040c00101504504040c1c000c0142e802c542601101100402e00140001031100d40101c10006402040500c40c07040341c2e4802e5440103034101000300701000341c0715041045034444840350195100b400000041c5c13040d1391280c0c40340b0b00100765603800c1c036a810001e048080d1410300543c0c2c01030100e800054524100104102c12031780e0004540c0b406031403942c80c804006840e41d000303070040303818503141d244138505030049200240302c0140c2d91340c2402d07403c80c0303041d0842c4e2020101090000000c001c004280b4010404104007000a0140c0b640351007402c0d0b2100b01e40c0c400c001c0407510006080084901c0c107004610442c0540042c0d86880d9641e1002e026061f40480b4125658003c82205d010b2500d0180714850240500340c008000035019010050004070502c10090000c803c021850700b603c030301202c4840080d43e07010058079102d5035664000c4403880040b0300f6100240c007071400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 352130917 1250 352129667 352129681
    0x20f0d0f0b030f0c042003040321140a110906040303020c090a020909010312140309010506010f020106050d140106030807050a060c0305070e091807121b14060a021c0f08 74
    0x50752440b5075183c031010f007107081c4880040000800140d403520304241400c1040300441c0251102851040b4000e840d8041c1e841d07070540e001d1105c000c607805407100441c0380020281c001c0e1000480c41d9072003041d2020008000030001d2841105006000886611080c001404820154041419000040e05440e0000592200183c9001b40d0148441c0b45400c41d4400004002056000b00f00800548040c00c00b80c3d51184c00c1070001d4841e0788101c40c3e690181c1c0d1614107210080d41d02111007804801e803440204040390805000840c0c001a00a000d0592400441c0d60000b0200030f600610046a1189816544124030314199840f018040b074250750b145c0c60400401c0b11a4024000d00344200072a40d150b0451241180402c100110050a5800c80306607032400001c18560400c440c1c00070b40389950b03045109075070301c0c07820300210112003c1c8480840070b00d040400c01c01031352810007a00074500322036803500c480c0941001c070320703040b40351015002949500e060002d135076400c23103020500002c2564035002c02d907035255 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 352132167 1250 352130917 352130923
    0x703060b0915010c080c0303040f0b060d0c09020a030e030406081e040308011205030c011d071a04172812170703052d0f0f19020706020f0d0f0b03 64
    0x1030342c080481c921100724021a43c0300306070404906115024141c100050000c24a240d50801c4508407810504035000d5814040e0400340994800d000b140c410750300083c84c1e0742e0002584064443c0894081e004202810700c18001e8001d1030103d031400d030490707849954031100104403030b0703040d40c1d01984100401c9200040420742c619040c82a0340540724004140d103000300540160340f0805094039503010500459010703950a010b49817003000d0545800c0d545585141d100d034100001d03603100c00b07815102c1c05819403010111200b902c045810038140e01c4881910204180d0825402d030012401d0b9001c40841220507101041080100d40d00070480a42038803041282903800f044807000c680302001038000066103091081e00b0441d401b00d512440c0d008a20000b031106080c1c11250880072442103551400c000147d220002e05c10350081c2050380c08026810500032205d00b0b50682803030326103030319000a0a68240425901154461103241e0102603481488020003002420079080c2030348001d06003400c1600d103103000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 352133417 1250 352132167 352132171
    0x30a0506010f051f12020c06090a020102101a0904051509031806030c03360a050105100605040e0403030b1e0a050f150309070302031f200301170f030406020703060b09 73
    0x6104020704c1c01480a0301640da000c0ca800e8001c8420341c0070001507030864418004603009100d100000c003446016071001900307000307048400911803441c0200f40c0c8151800c945940140071802d0390a040d00762a503007006410245400e08040001c08110b0901003400c20000c014001c035450301540a140c64090020071100344011f803082c001106007072020034844078404030413084001e0a51400801401240f100918501510f401042c95820004402061043c28060380c0c2c0e1111414880d030201034101480500140124082e40ca80c1601c110006410180a0b5001c0460484014045c20340400b06e445900615502035011600950820000258504103141034501d1814000d00410100307202c0c0d1101c41040c0c000420114032032103243d0b80080582c07001c0c013100c5140720040300b5845603100c47c45200d905648142d40c80c0d0440e04a0301c0d080b04501c000760401e69040d14101800f41c10b204803504d0190345010070b12101035106000000700090095000030b43c24080b41e110780c0d014450380303103c401080000c00007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 352134667 1250 352133417 352133449
    0xa05070608041b2607050901060507020a12080a08090f01060b0910020c01080a0c0905041107020a0f120f0614011707090204080a02060306010909021603300b0a05030a0506010f05 78
    0x8500c1d01c3c000900d01c10310150703401c2d113010b070440302c5c0c00b03503100e0000e680542c081c0d1002021039000034080c0203608200413000c01514160b201c1080c00c40c8103994120320741c440c505440d1f0401501d4800301c4e100860078480c8007090b2851800030302001d82c48072480030701548614600380c0325104030080c0c110b0890010070941e0782c2d444142c4903000d81d6900c0c4440030010f040c4516110342003040001010915503030742e20075031542462040304c007034032216503105000d402103283d04220602d2a00c07250800691450913942c000d42603001c40489640811450010050a400008400c0c0d40140c0000881e0018101e812000b00b100c4110444500d1665a05500c04038400d6014201d0281c00c122280401360421030300650308414185060318a030360b078555420049070404511701c100703002d103010403000341a8400a810034001a003504803100d04025a1003403004100a0207800000e51200c24000550b540d11800000814000e0140d6602d410680350503a10381109000e400c00c004d21801e40821581407000410003008a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 352135917 1250 352134667 352134689
    0x80303160f0f020d0e12030409060602240a021308011e0c0906050d020c1c0309020901060e130e01020d0908120c0304080f0306030307060606020c0112110d05090a05070608041b 77
    0x20382c40780119680f85c2d00d104016008048000e03074507004501007000304002d01c8003040002d092824070307000038240003007000d60b01c9039114103400c244100280c4403c042d8000070240c0c80103a807418801001c11440e01c0301c1d031007030b031a6518040c480400c141d8841010300400544500801490100c1541900da100c01801849c000070418840c0d44180c0f0151785c000d00008a62130110361070801c070003281d41140380a5400100019880b0310b400c50850800d26202c5000d000282080c81c0706a442e94086907107a444040000c48558546d40300c0e18030720714294100c540c80c038030b03940c01440f000d8554140f0031556800a000340d070300350030390074009000440d000090364001e590200c4021714140e6414040e44254101a29040d45404100010000a18180300e00002002140c020313041c24000400050030340c00c0040c410203085414541c10300e0000c0032410895103280040d00300050251906101c040c503050109200410070f100d4440040744480d0400a540c0c1304074402c1c910048580b1203040c40711803203079451103417040b114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 352137167 1250 352135917 352135933
    0x8030a0c080d0605040c020f0d05123918040605031911030a0606170a0201020d12060b040905011703120708151003020a0201060504090c031209080303160f0f02 70
    0x120707410300a0205010640c80850010303154400102201c0d01c081710480907900c60f06c64410f10150034040f12050480034100a0f04000c48921040148180100340d0344070845085001c403070b40212000382d101014020f07a0345100d81c1d43d4441d0319120540c454401c110740c4000c00b00e5800680c0c60640070321001c0d00c1d00500a001d040c081c8083d8100703408607240040380d144601c5001c4c184613403010407071244175600401c008500c181c5041c814402c1305070480f2224406400c158207010261b41c00149045c0e44000701e1800d5409070000c80c800800501c00c68000d00160303c00080e000880c0e68132074000c00c0c183e6010351480e0100b200d50074881d1b40c1d24030402c95109015208000041c4200b801703400f18940c02001e51150030030322909600024203c1c1170302006000882e601281044a42d40d09100f00300203440152000c00906a06484080d5400c0d15480000d0920400c0c1e91140c40071442415540010000e010071661039091a40041041c49031502c01c210000d40b4007407100144030b00c1000740100381403c0d500130704004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 352138417 1250 352137167 352137173
    0x6040b04060804330b0315180118060b0f0109140f06120907030c060e03030d1107080d1b05040b180118061e0f02070b0307140a0305060a08030a0c 64
    0x750010030664105450041320006264142d5a2400700c00d07404054804542c403800d00301c412244880b850a000760700c0f560a0481e03c0d03424865040e001a040c061810100c5008041a0302400c00003044562407298110348038200304031604182c4015000f142d07020500292500119450741c00c6100c7d024988001748100d112a040072001d04030640750141c4540e140000121620480900075102101079034043e032402c1060242c0542203202810084c0380c0a403418240800103035480c001c02c00100306150762040341d0a009200d07101100c00305a4007803001a12030035603440240052203000d81e07402140c01d201c2050001b0030310800c102e8041d43d02c9074105030b0500c0d1070b036504903510102e8038000301d06021090b5403a40240e554003216100400055a0b051000403201c0700300c10310600c200090600384040301200110f80c41d00420120140e482001d8480d450365138100c0100c8803000410b846a1100c00009142440107a258200501c64841031b80c5003110940c1e255203055482c41902100c0b000500407400c02400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 352139667 1250 352138417 352138427
    0x30e070b0c030904020403110306010602010c050a05090d0b04150b01080c04060c0309051905030f010b0d02150d020409020406030c020d081b0c010c020105041703010e01050d031e030501080c06040b0406 88
    0x4050009080b00d050106010102e012070303001340c106950030300d044d64545000c4e1800b040f03110301400b5644000e000c0740104440140090240242c00070510501051a05458031100f52080c4600d4024451861904080c00c0601c0d0079054558031124090801c0c00c00c1078194000c0500e24022004650541d142a00d084d000301d9001105100840130412a44000a410f503548501e50105480449403034000a240200701441c00c01d50007844c0c2c030240d0508560700703160fa40c2c0520f00030800750182c0f120003001006e0004980c0c141314001d14410404d20208000c03076a04020740c0a40300b9110203480401c05000a0b43e8140c0c0da910fa00c400c50320003c0c0d20480042c60401444122140c40c0000000e55814102203011860a6503104000f800042c0e648400700014480d840d0002da1100e01c4c2c040c0801d146504001c014010f805050160600443c102901401010300c034101c20110342c600443e21500404d503030741004025010030f1260320114401c2002e0110303580f07003e50458045600400300c6510f800d14010301520 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 352140917 1250 352139667 352139677
    0x141b030601091b050a031d030d0c0311031f090207112e1103090414070917060c070f0b160905030102042106060b030f04261c0f0c0c0c06030e070b 64
    0x4260b190603c0c2030354107c12118003211503641e1310295131904244000c0800b00c0381c40400d50402c046c00c0c0320105c101e510400d000c890b001440445138000340021050b00d03803944082a88400040340c800505101131007502c00c1e10b00800d08040707401104001c0d46410810044245044074850a50700d000d02282c080c2c043d20f03044001b070b45640180c900f0000d040740001c0440d4074591808a9180b0b403d001c20103d56448900c03180505030660907090110303001103202c1e680d01c0004140c00a4800001000c1042c0404403207020486548400c980710780d40707002401d00d44481810300e00380020403035007c0049094501030003030f00c00f501c85004c020606520042c800d00520100044140d8486580e49404620740d40c50000070b600c101d0582d405240141050b00c0c2c5154411202c0600003514035089510007411056503007100c000362000007580e1411040c0c42c82741e80c0100010008912998501201c1400c4c01e45c00c10a00a4900d010b80100280540e842c04140d0591700c2900c1002c01a8015580900c2480c845402400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 352142167 1250 352140917 352140937
    0x10806060a0e181204091b0f1e120608010e010b010e1318060603030f0e0a1a0901032703020c091003031b0503040b071b061b141b030601091b05 63
    0x6261014001380d00d507050b80c81a00302c5000e894507000f15965481c4000e000000c5403945183c600040110880000c1c00281c03e4138a601e0b170b4482c081764a260080c1300300d554240303c401399182009200e82c0d4161850003030416042820441d42050442501c41d8061320100c00f0100010700244044900f10101000034080c1100d25401e02c06c0c0d03903542c440031801c14413515000d18460703220600c0da02c4070160090088904600403030f108401c00c103000d2003903099481c0c2c418050f07078150600f151200c0c85100107a0161421a01259101c800189052000c90b60800c1900203035019030252080c3c0b5524030140811450100c0c0c24006c03c140d141c0701040000e11407040424a5003102c210710130034107140d40e52941180e21560011102640100d580001d11a18280700d07100300c088024268205031a103400034054410490394092002e03d80c2d41d2000502003d00802c01007046080281c5202c1c00c2000d0a40b000480c00021250003031140c040040381c1013030745100d0100307a081204455420201d2101d0200d0b43c4e507201100d61 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 352143417 1250 352142167 352142173
    0xa0b010306090c0e012307060c050c010e16050f032d03130f05030a0c060f0c0209130b10140603070512070906080c1c090302010b0306010e010806060a0e18 68
    0x42000d0540725105011181c0d82c4c6200f0b001214000040c1030415030124044588500c1101c4002d400244007284da40719070041c0081000c0302a02d00c1031303070701d4010a0316100c415407d20b0a00c845d01207005c10b00480c12401c0d003000345041a214400e001052401c142c4240c1c155028602e461014000301107542d581c40491003400e002040304000060840d0004c19a80c80c80c211903040520901c16203201401c050102a4020044500c46844640b0803440758820203042c0190300d0448070302d10748902e17000712440e80c01034001109424a41c540551041c048802560701540701c1e00030a450090711159a02141d40c05440c100e00e5800d88810480035074000742c54001030050400000108915079050544140d0485e01c076245003500d0f014000d0900300008040506880c0100108910b465010001510402e058030b00064056294a801d07030041c1200c13440c989d41446000000201d45520032641410381c0c0c160015074401c0d4442109101e0000010f008400d4201c609a00040c40704980b9244045102ca0b80380072 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 352144667 1250 352143417 352143419
    0x5160203010b0a151b050a030f0e03150f1503060109020906041205010504060e0f12210c041d0403050306010507020f06030a090317060108060d03050d110403031206030b0a0b010306 79
    0x252520316113501860404807500100340c4440c2c1c00c40720f4259400300100e610074481c403556403450b440f0b48101000409202a0f16071790396810340315071120452408003070200c0c2d500b80954860a000f00e0000c0b1440003105040300001060040c00300d14450050001170003c0075241d00341400c6501079044613034580c3c1c1080060000042d6a1507948101a400703001e4400020282460701f4000c0c1603072141035070030181e0b03404001900014440003c051500d042400840b6845060740c0c540340c2e03420700601c06011002041c50f000e01502c40c40d040014412561076101c04113140405202501c2c0d0140c2c202c401a01040e014000200c50b0350066000b0200716100600c0f542c40c00302c00500180140e00103550201000d555a5030400405400000c4080000400c8200f41040d2500d100000d0000b000105540d01810f00d4203641c40405010b0810382e03e0100319203000b4440201c0040400b00030b034110f44800c0d000603041000c00200000c1e5403084130256a00304c2c07494690390340c2d415601000b40003001d050a040551f1f650b8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 352145917 1250 352144667 352144669
    0x3140c060d06090513020a0510020a05010f050108061003110d081e04091a0303030105190e090d0f03150501030b030f0102070b010e1b070209060a0b03040c08060a060605160203010b 79
    0x34241c0400c030703280001e4068203080b5050220386000f07055401c412016940035015a403028250004c4402c00c40d111160b500c10b14000701d0800740400001855507080081840740311080744c00c1070f8182d448201c12500c1a944030b04400f80802c000b44405060464813040103c01800c10800d0403485038001d158880c40c0400d0340031801c4095003050720311000d10001140a200d403000c14010103202540082404803980510b9001984034030040c840c0500c02c0482c40b50070000840c102030085c004100140d90f0582519200c802d01d41c0790640c03a454000055a08154030480d58007a01c02c01d80301c1c100c01401c1205007030400005600800500c0b59055041c840c050307131a0201403003400108030301c62103800c904030715502d030100803403003410003a14921518403040c60a840c4018070303000743c0d030b40341d42c0440768100107484060118a04e82c005401c5107a00c0b0071f0000400040c480307981c04c074508440c52001112403a585444080c01150494000c2c600003a00411101488250306100303207400500040c000100141c11758 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 352147167 1250 352145917 352145929
    0x901140702060a110606041112100510030c03050c2a01200426030a031808041d071b0303090525090501051e061323030105010f0e0103140c 61
    0x103403c00000030401035101048150510081e40c021506440620010707981c2e82070f0b56018024030f40f05480d070180381000500c00b124044511402054003425842c036040b000714005000d001000e4491003c00d0401020910380b40d060b1048543c03800c20011030680240ca5292280d6000004800c42803e644d210200b031119044920341c110a8180e1a4004560f264601407902c45d03800c0d61000410400a205680d008603d0008011620300941764a00021825141e11030003504c40180c0300f0103040403c0c00f04000c5040410504140e082482c110070b2810140c1d81c2c0c120884100b00404a54820800c00000c01000a4066040702000320312400984407280e0042a110340441c02009140e0810038514400704030a902c9841074601407d8291505800c0320000c2d41c81c50480c0d6965200c880c00351800041c140d54409070400507a01034035421001510000f088040d0703207658514501c50600c81e518040c000511001248042c008441101c907501c50702d68a1520740d40c0080d40c0350105c0350494012102d600d5490340d030b44 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 352148417 1250 352147167 352147177
    0x309010f06060e0f10140304050307050312061f200c090c07031115041707020a06110106141807020a050601030503030f070f140315040509030d0e12090114070206 71
    0x40d60310804880c040d8400c00131600e00711100b6501600220070300c00e0415600091044650f0300d0200c6069aa850320f03c0c14501d18416543d001d0710034000840c6080818101034042c60060000f114501c0041540c0c004c91004807941c01b4805001c0f032495402078056028088680081041040a44101c01184d0303010680b0510105c6e00e01404000010340301c0209038101d80401d2050600000803d0b2028110020048000025201500f03601844140b060085901411181801c1c2e0190860303040e40d035140005403a90b041054000d0b515401c001c000b00c3c0b0000110540444d03910002c0c001c5641003031030b90403101116805010401180507a03d84500400e4007005200c0c000d51080005507a0792400328042031601c0e070041c04801c10402c10f0392500580c00c1c1e04c08680303114250f12000d155620744607010030507061050200c4443e0480d04040401034a540044007918140104600034400b515680b400340303485002650244101d81c0051020040b1340d441001214a003285648006142c803c581d000148031b5004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 352149667 1250 352148417 352148429
    0xa0204051e13050d02071a0313080a022803080a0207020d0f03050307030b0406060c02040507020f0f0a060b0904150e0106030812090c01050408030711040f090326061003020309010f06 80
    0x1d04415036081000c00c001300e44207001a40b0252003294207120000403298001c2101e80400c06002c00400c07109154121444041030340141400ea540c0705184000e512000c00e00d0100100c9145900f203103c0c00310300400400705007076042c1e840307651315070712455414004e4214543c140c3e004040a4010350000d4000409040458000e403a03451700c9140170740c2c0060550300303911503c40c05282450400c00c08a60007031142d919545e0b0440b030204440d80d40f641c08030700d0480c0e96440443c681c4a0342c1c081000010010a8541e203490050b0b20078807215011105220103004240c0f03004083d0900c540e158062400d0b00c0d0b2000c6c03402a100b00010030056581d0f02c554025801c00060f141c2100703068014400c841c8420071070f03801c03145400c2c05c2c018102440e02110315245e0040c0200a411700c50710100c22461656640e00412440c1e04c1c0c8c0074204540e41140c2402040c00c0304089608a40d10540803c5c07c2c0c0c1b1344042e120591003a4401840784280a44120048010f5007000d0300155180d034954950940e42c2d10140912006018 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 352150917 1250 352149667 352149691
    0x9010b04060f140301090309090b03010e07120317090322050303120a0507020606090c0c12040f03120201050108030714010209120c010f0c320d0e0405010504020c0a0204051e 76
    0x814818100221406883c81c18807aa1410700803500190300b0201c42c44c201d030b02400002802d504e008000c2400f4040b00f16110401c0d01a40c403000c03032044040c00c400000e0b80d02a903140c40800c1d030803428203066580c0a0360b18210942c41481a036004919400580c0c481000410340401c0d25582c0f0350100c2e1840e00070100c0e1200c1c183d602d8080003849004d520650f544034140d0b00c000d00827400c0c02004280c001002401500d01040c002070100c1004004200d000500d4003180c20460369160b54450585600e103940c0002c54400c03001e02c50107c010fa00c14043c05042c0e0300207130301035450807216585d05410201c1d030058540309075400b4408008180c1d15808009074007198103001d410010307040d00004042c1141002240d050221013207240d00411a110000d00d270914010900c10003c0080207111800c19a002c0914052803040c040d1030206070740e103c1c4015101c2d03002610b0900c00c0d46d0b203800c104000c0c0d0242c585e1144156004540000261402d0341049420540c1c010340341d04100c0914242d181440b501b2200314142c58 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 352152167 1250 352150917 352150919
    0x1050f0402010e0405062107270b1509101202030406060510020d05030c0901020f0a0501090b010b0c060a050c04120b0907050402030c0415021009051606050f09040509010b04060f 78
    0x3580002e0800b002000032a0100820318018001032101e01c017214800d40505482c4403500f0140300200101c6025051240640f00340c0203803080c206609000d271210030015039040c42200c10a50405003680c130f80040700d42e607590b410482e0140c00d202503401d1559100741003020301e0501d40c8100380f680c401180958016a8040350141c117001c1403140101040702034404640c45005a403113040d0703100b829290440044407480b940d41068400403032501c3e101c0b502044140c043c01c032480040200550043c52641d1003010010070303aa03a03d0306141e085015160050010b41c010b000041d2022086501180d0302c120580c203402c1c20140c4405420810132030b0800708882ca46040320600c040860104042402030200300d40c2036155251440728a10b0500170343c1300d4141400c248a4911134240e009002e0254182e14890040091945500700703150380e65040c40821080c50a018000300d9170134415030454031880280c0440904c3c00e4000c3d018000200801451140709542e01c5110700c450b9690303401124010f0044104090010b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 352153417 1250 352152167 352152169
    0xf08030906090c0d02011d0603010b132102010c030c0b0907090b09010605090105070f06091a07020a0b130201022401060f02010c140d0f0606030203150d021503090a0501050f0402 78
    0x20015020100a50240b000e410076540d41d81c1a0b0804d0300d038286807101c2c20290600301100c407049402c0fa2181c0c09007000c030001c00c2c4144060041d12211810002814000e965981081003201d0f0941d2812510804403055030099400350458030a682d04c249090320111469403602442c1c10400d4030820387c550400c020400850303810303004054011408580d045102c0d4902540502144510741c011418014003090711000d0000307001c400d59205400c0380050103a40541c2c40c01904070061007030000990102040850030030b5100103a00da01c52036003d1603450060702ea54410318443d00d40d1000480c11849072181c00d10301e8146031080b1510152101010412650411070050710540130b4031038002c1168502680c00501560000715585881c2c5034185180e61100c865082001400c003d4a60700c108030f0a2050020b00313241d1650045118910b070110710700b5145100c070104003002c6501c0030043d50202408019450b000303035484c01180c01182000448012810503030718503080d23032070449003001da004000c000c10044d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 352154667 1250 352153417 352153423
    0x3070e040503090d0809040b0423101806091103190e010204030611070308060d0b04030305191b0201050601090308090603070203090904030309020f01080c1206030322141203030c0a05070f080309 85
    0xd4040841c1c0620031004071b80da582503040cad90b01a04113280707040f580c04501c0e50410f40a00c3c03006014601422011445600c03201009008144900703007000b450300c03811300c0702095034200703a074001c64080600341130721484260081d01030245049182501d542c20800000007075540e100b11118a0030130009a502c0d1440341c10051b0001e10010500c0c0c1c0500d110000c403100044245070b849a0082d072504001070aa1260080c2c100842c1081d8014882e603458001d0020402101c0320140200c2c80190b4020b0000f6a600001140d024107148801410f40d00c041c4018112450980003555102401c0c0c4122820000f040c40040d807449801e0300d040e4040390351038032a04250304040304514031000d420b00344103400b400e04c1c4a01c41018840c4002e2041141c03440000f0504603030701442181c100c0005859a92440e5038032034420700e04030b041486060346000b5188a4400d82c0c1c2480317001c000c1a000c4d514040c6083d961400403510459001c0c440c80020000c00304403950000d0300111812510900502241c5c3d00c0c3e2920b40301c0d15103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 352155917 1250 352154667 352154681
    0x503060a02070236010b0c0615060a0e040906050c0c1002270a03060e010c02190b22080a03021b0703020901140a08011b14040503070e040503090d080904 67
    0x400349004005400143e202d11402041c5861410128402900a521601c0c40c2107a40b03051180011140380000820300d50f2007002d8251034a01d030095980c59102c3c6c83d913640d6480c018800c1e032a0030100903c01c004295001d851552030400c00603001007080c0c409550703a0005c03644212121100c0c28000704003030901940404c185124889244411031600c0c175140c01c011810034400c18031424906000114200365121035503e00011503025a00380210a91044282d010300359030441000103100310100503004030007402140c8071071a00316180c43da07152180010703400c00c0c60004441c054002c4101c1e0f08100090012402041e84072660780e001600c510f01c5101d4001c1d0b404a24950000766800600c0074000740e520507401a04603044110714140c0b241c81c040214000880c0756115181551a11082005440080303d000d81511015613900e0740c1d40703e151400c400d2a002d1402010b03007581c08607500340706d044040c42c1520341280c00b81040342c6c100001d10b00011044c1c01151800c64280304081125251030800b401a00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 352157167 1250 352155917 352155931
    0x7080f0102030c04050409060b03010903030506040b0d02060a030b01090f080a020a1202090105060306040f0f05060108060d200109181d01060305060c03071106010b04061404060806040b03190c050306 87
    0x5031843c1003d00c41041c0b0b60280e401950700c03030395aa0f51480c040186550020310303441c6003e002445564454200540207150483d01140550300f40741c4c90050910748950158055940140624248840039508500502d540c18405050290034100070505c00f403908080d80081005000a11820015205024600d02558040d244062416403000e006986000d146415203034282c8401e0384035640d250001d40a04030307403a40c81740c805140c168500e054030715030b8000c2c40c4101001e0701c42c41c0341a280c413020710214008484001d400004409060b0700c801d0000311444101e058145020900e680e100c855040350720020120b0310741e0007551500300c03102001001c07038404900c2940d8002003040c1440c54036115190301c001801942c540a0000000324420b0140c2005c0642813103400c1262031940c0c4804003503900d07510502440002c50020041c140604501c2c1c0c0840341520115030384d0207002d450b04401e00000d420086d60a940c18003c100d208011084010002e03010b1a0051104d405203e161600b81420801c02031f00714 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 352158273 1106 352157167 352157171
    0x1d04060b04080105010e0420220f0b01050a02120d0914031c0209011d01020a0602031314060c0702010c050a06020d0e0f0705090106050d020405090907080f01 69
    0x50700036070703a1103002048542d80740c1d00700702c842c02800c5038018036503103074070041c05c2d5028407a08804007000d00c09014407030501400e0101c20b030240c000300800b5810f580d40b41004040b048050091440894081c24058640031008000079203501400964406c4104000381120601101d64010b612460b003101c1030400e40075a10705155103c0d4800800e41c042d002d1645180b41d4000c10718800c4131011101615011000030303e0500f080c0600b02d840203040d055020301c1c0780e80d902040c028001180b14207030181664004000c0c17450a070300d650004005070003050f0b00000803c449010f480c0c0450f000a902428940710009852a0613480d221101000a1402e80042004010824a90030000005442c20142c07000b0b42c1c884401561744400601c02d080d800705800c0e004000c42070060b00105210113498201603d0303da20b500c0403401d02c42c0159141d5070558450b00b4100801314003031181c00c2012104c5002 = true := by decide +kernel

theorem cover : BRFrame.Cov 351978417 352158273 := by
  have h0 := BRFrame.cov_init 351978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 351978417 ≤ n) (h2 : n < 352158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
