-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1313
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:19:20.178658+00:00
-- url     : https://prove2.me/submissions/e9947cf0-dde3-4233-8235-13258f8b1e80

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 235971223 ≤ n < 236151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 235972473 1250 235971223 235971247
    0x70b060109030c0b0a1701060509040c120e0303040b0a020c0a26031e06030712020f0a08030a020d08070203090a0308090d0b0703060f0b2a07030206040b18090417 71
    0x207a8082c540c005910710009444680700c6019401c14540c0c4400202e100207400b00c0303699251044d9044c0e601a80d078607898006a43e0501c4003034084481c019080090045c201031458221388544000344046901440d42c1c5d007043d05084440c007901820540d00da5204020800c06507200103241c1010303582c03100e480400054103000f450608403050341460100d540020820914920086003052200385803002043d8030780b00ca5007410356034103880c0070756401a61641c1655000d854107090b0480201c10040a010802e900c0e480c04d6811500400b1814000d6440028000141c54104008a6201800d4402903051035180070000f070030740300e8521000d0416800046c440c051511f402d0700e40017200e80c00c2a2584824101024000c0007003115124540c030880301b928012903080005800c48000020148a0704480040d01040d01001812042003100d1031003803c5000005880d0308018100901c000c1d04074175240c0003082c0040680d841c440d244280324142d04400c0200040b4010060031041c1c0c18050324646940d118480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 235973723 1250 235972473 235972487
    0x706081b030f180303040b0601020f060c04090b120f0303010e0109090210030203061314010f090203010b040b030907030c0305100621081c0608070303020f0706050306040903050d0c09030b07050c03070b0601 90
    0x241c3e4241e40000400c1200340010004014010f85003a4221034039482c004011a888032400d548a54101800300070070810020704d50030603200c040009041207003043c1e20928680c50030440d0300c500c45032500084010045111200301e071a0040003031071018400a540c980c005200048841091f10a041d804004102d05480c1c030042c00c0035244541008004039005100701d4080b64074240f142081c299041140030500d05403e009480c100c41e081c1c06038505107810710000c0111a040107048000d540b084080c00000b05815586950080d8000d0015269201d0b021480400381c03922070300038100b600c400c14210040031200d540103070402174010b01603903262505e903e2032581500c0d008854070790450410101144600f80824048102d904ca9021035862105011134291030f03410b544184801726030280001001420180c02902c04548a498507a00e4038146104400440340d900900360b0004103003200910412220000726034104466042071828541c81c03032003003541e80c402c0e090000c150145a2000ca003aa03401040313 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 235974973 1250 235973723 235973761
    0x50d081009090b090d050a0905090603030f071220061b09030a06020d0e010c1d0102030409020408060411010815060c03040f03051018020609012f0706081b030f 70
    0x7090101d0580ca051148074680150b94203296405030101541509010310200c88003426161914082c0a242c14100103410700d0007410180c042c042000008d0b40c0604150060080078410020134980380080345008041c2040f84024000c04011581c100505850010796244d100b50400c4c48107035200d0500560039002e010300907200d90544206283c0904100b03107030300601801e680120003088a40c03400c40085090310f01070039540c030100340e055103511064802058400030f210030600490346895550703203040c0101d0b482a4841c0b0081c2d041142800f0401060f03800e00d040700d06003481c0c0700781d0a04102c403e40007130002102400d0f21500000400302410300e400c0c415140207100015201c040166a0300b1310548800100b20103140e0145059182c01d501900e001c042d4030710b90b401031301907070903c0720381070054408603400f0104005404858540880c0c0d0382401808890700030884000c0c110151404202500514000d0859040e10107154040d0582400c05001d0340d6000b28480d0b07000c485901d62000e00710705c6410b001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 235976223 1250 235974973 235974989
    0x20c01051b0f1e0c0a05090415110304121b08031306060302040e0312010902030f06010f031404030905010212030903030408090607050a061505100807030b01030e07170118050d0810 79
    0x9a412210541820520712240e43e4030094480908503c2d0030009036100c0750090661010301180400d010a203d000c028140d04449a0009075408907090f10f01055001200e086a5069800c81d5940c030f0f032544925440303045a080e090340e000300d182e81c0c1e07106140d5001c01040c41c45c0040086840c1c00600c0516000100203680142c8101f01100d008003500c2e460303074088800240c0080c0f00400020f0103e4040c42183d10807001199011001d4a034200110f850640030001101050340395900c5900540341003130b0030381c055171080e100c40b40c60515100001e401c2603c5a0075072244403030305004218000d40003008130303903000e44d2001d0320300d82c1e0744027000c0064001d006050000c0c1507441684442c07030401c00150320000130b145908001d4024a685c0e802000100c58041e8401d00005a169000c603603001c0c00303508030b00341c42c2105060204100e071300102c10528003c82d40d4008003030140d01070400d60f84002c0030300c40d0441082420002149454031500d48a940748401141402009000c0000031480382e41c64402d000a84a51 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 235977473 1250 235976223 235976233
    0xf0f0d0b090c1503061906020a020121020a030b010824060d0e03220e0105010c03031104080a061b080c04060c0c05041b03050906060d080f07022e020c01051b0f 70
    0x8a40d1000070313a0412644d081c09604c0200503903440704090001d503412686164002c01c2250708507801100d00b92003c10102c0c030b03040a8407400138008007080c0007414070200b00c0d80d07000a42c00807413000144942400b9080908901e00022410300a61500c141071240c80c400780c031420f0303441c20401c60050003004282c4140c9441e000118250312040700c0140446807105060580016054443d44143d0a10b1420311a0b00c1c089400344981c0340003c1d000350001f103540888045443d0405a441145a007000540301c0e04941d401d5413582c2004041d461420758aa808180d45460006031911901100d4140301c1c0b40560000c0c0310038445070004000c4000b0116019000c040c100b44900e015900c5007180f040c01c0480104042410880090501400000c072745d441008002c003412003004454030b0780c01107075003c0c80014044500400141c0e003d600c4019000084d03c4401401c1900e403422a003c1101806a04181e441103401c00030595000d41c1c0c0c0601601d40003094204038100750391503804d62618048030b01d007074a9a18000c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 235978723 1250 235977473 235977499
    0x31603021b0613030908120301060e0103200a080c07020a06050d2004051f080c09030c19050901090506180601031b02070f0f030c090903090e0a0b0f0f0d0b090c 70
    0x1284105025042c03282d100c90181750748920403e5225019408083c0c1504014001008039512032110019007000c1810000399090700341060041204400b000116405d80000300c03504042c0d40a440b0300d5004018104180c1400c1484d030000d01800b9051103800b0401c6808294841d003141d2960114101421582d0303000c1d0b142c489500c5581c5c1c00c0d082840f4492284c81c98084004002003a04040039109a1a035140d14140c1d5a9601840e032070f1304185245509403084607076030100d58841911060b002036035200340305112403400c4208a11800140c001d110400d04080a105142c0c030707800e4110074032000c0511003003110760391000120000c015132004202d9030141141d200c490713a030300402c03610107070750052000c00311954a4009100c81052184001131000044090402070f10003154000d4000601c207107020020744e03039180d0301d1507010f65080d2080032516640382c090050500d45100180116031095582c40d06140d40980040c1c199000341034080d0040311b502e800181c500a060200c840810317001041803c940789 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 235979973 1250 235978723 235978741
    0xf0703020c010e0316180608010e03042103021009080705011406211c020c030d020f06010e04110d060605100503090d1407060f02070f1101090b031603021b06 69
    0x1d00710191902090080c0030110303040c200401c0c80744130040104150b54460740740000003405000c100491810b119959540452200c0c403c3c09450710785a8000021900d940c02c00780d41416204008444000000d5440010300000f5000300e00c0c425020609a00010352201070306140000d442510030007480d5500c0c200c0d9181640c804210b42500680c01914400e09001b1150070500c180704044429140b0b60b405030401072403c0c052400c40b80c807440c8840c8161152030104030003007440c020740000d103840941c104000d100c071a00000c00040b40184518491aa001d040c1900c0d5080300000142c0d080e070181c1080c48c1c100f42445007542080d80100350290040c0d101d407554901c0100503800503160b541e018000c000103000203501c50255000054402d10540e0720b0113000d80d50b6400202454901100b026800f840340901240004040f449818001c844c02c06104080b44001040e05a01c0d80101ca5500b50a209200414a00454081d4080858280141d441050700722440c1712480f0b42081075007074441e43d0b00304141c1d04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 235981223 1250 235979973 235979983
    0x9210905100c060e1911061303030504030506072c0d0c06090302030f0c0102060c0a031806050a05071107060e0a03211112030f180d050a140c12030402060f070302 71
    0x43c0030b02010000a00c04000544e240d8541d40b0f810341c100034540c0c440c40f0108031091600401404010b110a01d001456107582504846aa2061b8040b0380c0109040080c08018024954401803914101880341209015000c82e000100c208003100b4003c85007646864503841c5203c1c0030701d6040b14000000e140d03101e000801c40030950004900038081e00d010342c4030f0048002064542c0480503000341c08507940700684004980c02903802c1604143e103441c140b0708404c490101000199008040210301032800d8111102501c9024080b40c040246280c0d1456034904003040307074001e4922130702d0308800c1600020002211002590000340002d45150031a104964402d01316002a15031900ca950349100c944a0640d21108810400d140b0a581000041c1409085101c01c551194100c03203c07010900b50b0038480340c50800d8042401e400b0480000324628190703000b50b840404560784048051910454418181d00e0791126961000c0c0c3c00c0012011a08641d00c03442034500c3e810250700d0140c4c841c00f1b6414001c2d035078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 235982473 1250 235981223 235981247
    0x201022517100e100b06130b031003080a02010b0109051e0405092a030c0a211e050109020108150d0b07020f030c010b0118030b0415020c030d140601030921090510 71
    0x980340109441a44c00c29006440247c00120700101003149014400c10f001c1c1d2008100c12070b5004a4074012000644020160441001c19800000c15920301000504041c3c600e07003002d845820003941c00c1450069038481e003a81004c017070701e000c81c0ea51991401c0710302d09540c6640c04201582484900200c0806c0040e040b100c02070210100c9510107041c40601107081c40034042d4030b08004904d0807241c0c2240703024030f00300c542c58891002c0003020241781005204890400b4070494903039440d80c6105056691001840e50010450441c41e00c581c410030000a00540044200604640d281c50020310410300900222540c010ba500950b136a840e41100c449008042001350140440c100e183c01803a00d042016200007541d0303100e80441c030107440d0303500c651640000400d520303e0840d400300170b0038214040a10151a4440c201075010409440c1160b80391151240200f01d20704152402800d600400c41500d0800e82240340e24a0b4050740780c0d0803400448216810340c00094102e4451344040c40c0213540244003642e5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 235983723 1250 235982473 235982503
    0x121e0507050c100b0604151d040c050d1503120203040303080a05041707110a09020702011b030905100c0215041e030503030a110903060f040201022517100e 68
    0x185558010342a203941c082c000b50821194030607104100301d40c1c010340c40410080c000900b000d060650310382d10000010010a00c107130005003403054800940c40c4090260381c5188040b90305000c031303001510000f0258051483e540c1d00140c1c4601d0041031020188045102440c0c01040b03034401092040c078041d6480c0c3c820311045001a0b000070000c1c01d40c050a100f424001c5074804900c80031020104d0421a154002d0003054038010f150740d2468840c1c0d51680752460082086420141c0c80d025203000142c4011704036005034042d0078809400400082e4002004810341d501112144400c071030070601118860900340d00250800c0076200200c4288682c600078000300c951407604c4602140e258840302c0c001403080d1100401a5000b400414481c54603900018251568800c141d07041c490140002480d003041a50f49100000c1080d0030700040d543c0c14848001c05000400f038601c0c041081d49510080b0041911038001c000303005248008160700c0038040f4003078003845804240030f4072015200c816255a1000c4514407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 235984973 1250 235983723 235983731
    0x30501050405060708011214030909090705040c0c0b04020909071d010312020a0b01090b060c0a0f03020d170601050d0f02030f0906100602030f0c0f07150314220201121e 74
    0xb1403442103c02d035060b50305044041054074078590b90580235080b034003024041d0740410b010911450311406d0a561003409000024482d0a1601061000712a00c170300d2210204081031540002042c40050030b142c009034142d070011916913071031498908249181c1c021400c801540c4440011260160240505885c050181e01070504205c040690342c41d501014010422400c02d801040010241c0c1c1c0021212030000c0c000e5490620780640503070404100d044100c42103183c000c2c0b5039060607410040014071a583d814805000382d000d80c000a1924802070580381017040024a003440c82d40c0903000b001d00c03060313003d40542d241c0c01c150b041c0b804007503400c9031001c00510850001038841b50041d4501c1301141c003550051440e1000003446480c0030b60060b0302175540ca20a07254030b1840c80204102c071400034880201c1100c140f00c2058401000e998089203c400d52042d144244040150040300e0400c54014000140440400a1006039095070110040d11f2070146840800310242206080019509000781c1d0700304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 235986223 1250 235984973 235984981
    0xa050f0a0204140f04180f0c05040b0307090f020f120403030c02010b0f15041a0408010b010507020a090c0e030303010b12131106070501090c090207030e0301060e0601050f070c03050105040506 84
    0x201d0040f849440002d0954070711040c03407810800c40b8071501c108050030210b4010b215140e214110560650121748429011405100380100008000c001e0b2800700d60a00004004c1000250790b0f0520307002d000c20b6242e41d41142c0107105441d42c103d8444002e4582515280c408410144030114002c64003036003c0b07420b104400d04c540e0300c18400c110680000174101c0350196942000d0010030510507600d0507019000b0440490f0f49010700c180b180d030901010b000a81d43c1c3d800e000c2c0c01825144030162003030502005000400042c1ea0f0f110380b03038042d20501e620009100c0c110200482e01c00b205110380304c0d010f000020010070f00782c003068020890004560000307040b68413003041074900316848000182c08060140b1111000340750a0000380140c81c040c030000f08902080e03403107290b07101c035256000c5c101665001031080100b5412803510307851004200c000300400d1307140131aa00d002200092801c2d0402c0b900040207074601a80d4820b42e40034540086e00381c07041645901e00300340204416141501c961043d00002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 235987473 1250 235986223 235986241
    0xe0d050a02030d0507321b0f0102030a05040317010609090b011e051801110c0402032502060f0c03090606040e0102040e0f0711030a0f0c03030e2e060b070213090503030a050f 76
    0x20607070601ba00c01c2410718004694008031640e8400b42028a518090703044011078100c02400698050318138400300041c542043d1801504018502a19020704000d4034010444240c2104117581101d02d0341d0804a01880c1d004012160003c451101c0c04045803070b11900b41d41d60b9400b4000d072845c00c113006600907018a1440041d91240c6a00c00d0b201c15542c0618603201040c01c15030051034002a40304600c498005000c01030b440c03c5412040042b005074441030401001004441a82d0f4110300c4501c5203038034600f8014101034861000030503441c021611400c0c051105030095049038010101c1c0c2d0880c0e803040c00c20540d681d101d088203980c140c001034400513100f01103080110485540c4d100f10348803883d6810a110703099500402003031041e4203141c1e8070014030342558400e000c40311308510800300e4408149000800c811044c91440301c442d4010b03103003c00130700c40b140000f011241000e8045580c203c0407102d248200303001d00510500203103540004418401c0c000d003250806401420700c1220241c10b80d03130706034407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 235988723 1250 235987473 235987547
    0x403020a03080c070f0902030703060b0a08040f151406040c050a0503010909060b06160201021e0d080604060f0608090d031a0603040615081b040e0d050a02030d0507 72
    0x1a5000c05000380800018003408024400d03044820262100680da800c00484401c486510400030150000200b00803603034184200c501604682a2190034a05c030b1100090020b03000800007000606085810010301c00d041c21800a1001158000e1222041562400302a40c0040c0c503003a00407814200a031044900500684100311035541e102c7e4116841c204800018114049094030750594445d410003260300d807000101100d10f180007518a07400040d200082c07900c1c40030700104d0000e680c0754400202c02280407800950703034074151a221030592500350018004042642c00382540c01c00207a800208150082c0e4281d101d0010001a0f42d200300c171440040d029246010200b001d00c0b01848903031406803800d0b030095a0480c2c01103000080b074503800310840b03051020a411600d015442000b10030314844100d56a1144200700365400e2000b40c0249031040c0c4d0701c0d950703049083e040c000c0101d1283c403014400c000361105680a544140308a0500700d8000d454801e0807020082c180358500ca448a002c051000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 235989973 1250 235988723 235988729
    0x20a030213020a090f12201005090f01090509060d1406010311090f0910090318061d03010b09040803073e0609120a020c030703080d0b030a1a070c0f0b01060e0604 71
    0x6180313241005141d55698808201f11a181c052504d0118081c003030f0f0711365500b40440526203450b256618a248000c02910501c0511241e0400003c0e103410302c40c80d101c441303001e40c0000b81981d032034030004075901e04005401d80581602400d849201b0001050091244100807206070981e5400116140c1c4aa890b00f8040120348440f101d074440503039041070091030780c441c6d055240649002500c62500a41e02122000c16130b001100140c4078000c44140d8002c400b21518104804030000c20000c1844000b044024038022f1002d13000d0640031000440450090251050800102c0310b10f03014055601c403112140c8000004804003000d0001500300000c01c001440b5010703c5800300200301e03c030300555050b20b080d0b00c45036a010840c01001c0300e50203561000c00200f00510b114001003500c505c051440c07203080f1528002135502c02d6003d20380000c041200100d0799940f42981c40e403d841d60703903101641543c11445094004184480f800c280d8024848041140c0341600c42958459030900c0301c03c0108125405240 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 235991223 1250 235989973 235989989
    0xc040314301806041205010c030524062203470403121517031c09060204030c080609060f010506310b0a110109030516020a030213020a090f 61
    0x856414070541c0e02040c24007240003043c00303141540302c0720507801c01d8034160002c5a0980d10303040011842c6405002d003d80c0704240602c17200f02c604802d5240070071420001081d074003d00c400103400d60085d4907002006e40d8082191903c00d02d465880c50800c0c161110040c503041d028148038281081074210301140280c1903d40000030025890561031401e007410068001c50a0281c62271340707030401a00394040d16a4040d0b01c11203d0000524000c0d1403000f003d680c0482039100c2d00208070b1195a00d003242001416141c1f09007000030781c0411890210b0080c480e0750005442840c80c400c0004e241d40000500034407401480c025100c40d51aa2413490710050000c0c003d49070700c5081401070f5050002c4110031041200b0004203802080482d81080c2c00040581d90002c5600001c00076507207442c0d40d0041c1000200201210003000258020f03100103110340038220844444081381d10031002035503581c030140005950000d0841542c4011600700100a601104111010804c0a00c00080706401903500504031040c0c0c0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 235992473 1250 235991223 235991227
    0x21915020405120303102903070309021201060f05061e0714011a21060c09010903170a020d050c03030604020c01020d140114061206061312030f080609100e0c04031430 73
    0x3150102c0711f5030002407600040550394481980036035038840030340d002024140000a903a90901041c9040c1220700c0d000710703010340303c2004070800000b20340071811005110140701d07584444051030706000c000d4006e01421065803c04100b06100d00c0c500e000183c52540844038402480c0000d240d8a1001c040001c80120035002480083e40100480e0000d000007441458116006074580e501c2261141c01e0b481f20104148010aa80f20b4242e01082a040d111813503007025801c10204442c000e541c0d00c8010b24030350246402140003940380009405580110480d0101482004404507400300041c3d402d12900313810070030b000409003079070030100b04492080d0207a1070f009415a49803401d0182d01e0340b10305000f0891a0312400300103020910031070305174116807080c0c0d54903d424803070001c002c101d094040c01c2a40305095130010310000d08c624140000c112480340155031515070300c6044d814158092940080d1070dc03006804143c0209401003074102c03e86030481541603140c00410345256a00120310611840c3c002d003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 235993723 1250 235992473 235992539
    0x100309020a06050a0309080c0604060e0f0a170c0d021f090209060d110904080a020106090c050717130801150b1309050c07081803060702191502040512030310 69
    0x105400904000c126405d021511181558505465603c80764581141d43c01250034401049014010743c2450807454000309070044059004030784619054100030600c0840e29888410324546500f558005100711040d100c2504884401075194840c14680c14025290f0580d0281c0c1c40b426440b90512054018140388032640d2020140710561803002c0007960351229a0880698a03510208514410391107040c405403550b52400020f400d580300303074100081d11410f1160300d65a0340d41c04020744a0240c0c00002014405e01404c141c45540e104103100b44568100c00d21000c5403c0d01c1c150400c1c4080e50490b440c6001555803008082e2603401400492031026a00200800101c45107030045c80d04407150034101d91070078000e41e44000c411742c0001c2c1408030600500c0c10340380ca00e01e42030001d13075032107662800940b001c2075920b901403060204010008280d1b1400d0342080d080f43d641030741a01c003c0c00000c1c2c041d4803a4400360115941c0c0750002c849181c0d130341c1b461090200d510000e0703520509100c60a10b09602074865 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 235994973 1250 235993723 235993727
    0xc030d0906050d09060915050c0306090705030711010e0304060206013c0e0f0a0f0b010e1c05070801090c080109050d0c060b040510060306050d050a020108070c0803010305010b100309020a06 83
    0xb102c03c0603814460344580c0400e0119459101d003002c1036200303003400c01840e080aa50482990f00050a8102020b03052080001d0b1b6280c0041c501e910081620300151b42e540c5800302a901840d10300072411140d0300c1c00c0740341a03480034004020010f54145808580d25030b80c0e2500040381140c0203801c04501c4000c05001d83d108548020805a912090041d06042c01a2100b000402e40c070710440c0c030a4072801c1c07041c06100281140d40710f01407800800e008188042e144000018151200500030039000c1c1084e142c60300313886613026103070310203055010f070945102c17aa03200540d50291104500943d0280c0000d000010444030520450350480e600401500701000b0702e01003076480104503201540d489488030184800ca07502c40c410203204440c89204640c40e5802d00a000782120ba25400c506c0c000c2906506c13000220b000002c18400c025424070700b24482d9529000d0031103d94a85c040001e096002c007000100401074190040203100c0401c2d0340095a0509070b21040381a42c00c1c07414082d401c4aa4280301344411b82c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 235996223 1250 235994973 235994977
    0x9040f05220222090c140121091a04021f121a061b0d030216020409080c060703050402040b0f010807031125050c040207081803011404140c030d090605 66
    0x1c0c00286488440070202003030f9400e0b4400780c49544401956100b0500070800005440e00150800d2038500d0f4404000b040080d000e001120040d0145c2c0c8900f25410203da1503980143c0c0000b42e003c4100f40c42040e1000c08401ca0140c2a941244038102c4a2401480024004402c4110850340e03590300c00c16818032107180d00202500f0316520312640a4030070009040e06c4550040c42603620150400900c00c01c49080c09041c000400c1e40c05003014010441c284440366121101e401240c0c048800107011019807030300344843d1050014045040c0610b00030000940c0e01030b40103900c200d00036502444043c440000b04920322920390b030164041441c490129209920a50092900d0403400130f440340740801d8035014001540c021500d80820700b01e01c1030b9400030004248008080d03c00180c1d4158102901d5507205801d134020001303020300d468840e0319540da5580c0d00350023200c05001e0755a4034140d14181800d1038541c0c0d041440340a19940b150003503c0c0b8040c00e0002c1c1441d0700000710f5990710003a0342400401c845036 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 235997473 1250 235996223 235996291
    0x914190c05070c0b120709050f0f03010209041e0b011b11010309140304030501060b070206040614090915030f1f0e0309030304080d08010b09030304060c1b06030209040f05 75
    0x14060000c40c0004501c2500c0c3c001614a0002641d15a01140c41c0c0c40750a042c01040901003111a6034204025180c0c030200b401c41000884007035011040c00d4012900a0203071078803856003d820101443c050b5501400c0c4051017240030b0000b03016a001e0070300199804a40c051046101100c0002c603107001c555904042c6050041c1417401082442c4641c03200741d913414040b80c902000340c200140c100704210b000d200d003a00a081134200f441c10071040344c0008107540500c2c070a02082c040c1001c24044002b1000040302d101d804c00409143d240d0078880100c09461801d603401034000d01c41d03e40c0307803026507030006038014100c0c01481c8528339480750000c00201900051440402d144414046007a095400b80098005040e03083c006040d000340c8444010801d0074180c0c06880240d8040080342d1560300c002c02140e058804500702449000c05614110b5661600600b0b400142094580b003c00e480342e26400600c007003002142c2c1880001803110020048840581c0e42c071400c07a103a0724002260300c0f040d042c4542c0f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 235998723 1250 235997473 235997477
    0x503090a0f080315030109170c0f0a030203090411090f040e0a050609011401060f020303010e060f030d030c0f1b0f02010e0306010806010612020406021e0c0303070c0914190c 76
    0x20648680e03807005460301c0c110500b111420004420041642c0740701d45a07150524040b4000c0c00101c95540310b40031002c1c14803041c10342c04800000c0c0f011101c28204a1501200072100441d1500d15082c10020740ba5042883d1181c0f0503810700d16940d500201030010760350982e03801050705840707070001c00403c00142006403030380c6110300134604880c1c04680709000300b80c406c082c80030003c1200c0ca13800c00e11060542058200b007080c010f8560701a005030f0790004c2039905550419580f0407407901d5600000e02d6a00703140950552511816807402d20b1140c0c160050700310501e084c0c5034500b0880c6048800c0e038800030854512403210320100b14240100c2e1548001416040c01030600250340c50791840440e0801c10260042e8200780d11031b0780104001d55100503403c00a8030b00c42011401e040c20003800a490b00c59907411400703980518050851044404d000c042d10ba000003c007104c0d507444180c41c2000002801b40300318200f8602d400c05803450101784024644c070591901c4600311000f4912000c9400401c43c02c030307030042 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 235999973 1250 235998723 235998733
    0x31b0f03060b070b01090b012f1e010c02010515030a030302030a0906050f0411030102030412030b120106150201050c0a02030304081b06010605030f1819021909050610020106050a0303050309 83
    0x4003040442c00528101c0c0c0620f0030526107604240008096644454245c0d04001101c07038400d014240168444519404100f0b034a01c1c1d00303405141c0342c2e2a003020f41c2c2c40f140d20302c0e50f4a0114024444150300005408205030000d202c5551400300041a0078801d0000d643c054200099181c00a4440d40c0110790100c00540300144080d210b403211421500300321030b521070003650030050005000c000132110040d070780210000c0d451403600c1e40d10b0000304440c0040c150145074451192030171036079903901d001001c01c0340400200721150340e400f59105d07411541e451303002c00b41d440d0070045000701030b01c0c00443d041d801c4940c00031440c60f00c59950301041ca901c40400d101d179002c0034129608001c5014400b80380200785554604d5142d0500c0c0007042c4442501811400d545142c60070962400100031544e0a6144081a80c169881e440f034004120104211007800810201c0f65401040f081c84070390040c1c1c024802583c00300420045031100364202d079110301130140d00c540905810400a44900e008560250440c0143c4e5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 236001223 1250 235999973 235999979
    0xd0302030f0f0d0c020307030801150e0f04021b0106140648150a051014010507230c030f0606040209130507020c012303010b030901090f0b040b07031b0f0306 69
    0x104549010707030b860340140c10011f02d8006050780154104e01410704401c00f14840c802d10b00000d010108028404c134050034101d00000b607241e95a50540350990031694221402d070f00003415550003401d0350302941124514120f5800110b00300b00c810781d440c000c0c030b0258051898018801c5c030a4580c4d0183c0784021132540e4003c041c2545005611001003251078000180300c440440380e800050340800909106a9a240908100d0718040409000080700c010303110400c82c40b4628801224503100d99940901441c1202003a510b00c2c2e2050b940c0e0012180042c41981c1c0401e60030410075854a41515010040c0d80c060700200340c003032078030354001c00f08150000d21000c10112540104000e6580072101040543c00070020300d805541c04c1030b880360401000c07005411030102e41e903800003150301041c040d108a4510110005400d42000d41c05001400d0b0004001c000c50901071a0101e011707501100c0407580d6100003008201c0c5c050107405045408130b409600c1103a120744000007141c0d0000e082880208142c1c46807000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 236002473 1250 236001223 236001247
    0xd0e010b120a03090605070f26071a070806030607030e070e010303030b030105010506040b0a03090204021b1c0201021608070c0b0c010f0b0d020f06160204020a0302180d0302030f0f 79
    0x2818507420032002406050103a810050f088541652152043c071100b00503100c0080c503020100c03402c19034010035030100500541a805032281c0000e0500f19001000584101480b122a6409070546100034445075184da403032104441144080d41c00c60341562140b0007280341d0b0f9001c0d8210b42d141c09a00b60803038402c0f42d503071100115031400030f9009401103a695080070307416041c00c0c090a4003600060310118036207440c1c034000842e24800d0b2103817101059919210b0004560700ca8049441d800b120644403200c90b182100b07510303110b5100b400354441a1000f40f0402c02c1b420300600070b686030320010030488a410680c6071210711065000c0c0d101100d450380207200119110808a0181030702d428250000280007482004403c21240c2c00b00400b403280382d004c40100b0060361465034941c90300c00240d5809032074500203a034845d004218188000d52090000c241440d6142d03041e40600780f40704500048084941c201c0e010300c100400d0f0281d02070010380040007103541c108140700003007051004002c401845c25001d6000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 236003723 1250 236002473 236002489
    0x1150e1305030c1c1d031e0307021801210218061201050403030507020c0d0b070309032105060906040b011707050c070f0509010e0c0405040c0905041805011a03030d0e010b 75
    0x120304c000d403940030540c44020741d2005062200c0b40d4403d406070401140c01c000a07581e01c3c0e080444e0303290410700e14035541c080c2200340309032080c60f5401340c4400751403251035002c8580361209002d00e5030201304600a902001284c05400903032140c000c5e0120071071012510101d000090000c007615080441040e94925404003442818402d501a5400041c1030800741402820138040a56113441600c1311090030002c10b0700c400c541e40c0c01c03030818140018140070a18041c1c4d001d48201031031050488142010340d103090b40075040b60b0310800b000c030b800d030200b0b90b1040c0c10002154201560700c0d001803034803440d03000841c2102510b950050a10b090640c10840c005c48413a281c031840341c01c0365403503da07411020451800c115000c40d014040b030042c44030b214a0066000e00c000e0086110325403180c0e44503a00301c080c0c00d0261410001800010304180040ba507181120000002c420000700d0f400e62034450942c002c0320341c041c600b11005a000780a90724200c0d462000d08040c040480d1010440d540e244804c1004d507883c020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 236004973 1250 236003723 236003743
    0x30803060109030b0906271015030813090b040e030904050714070c140d1e150203010b03070e0a050105040e1b0a0c051b0907030c0201060e0903070501150e1305030c 72
    0xc01021030b40b5054006200f04520b1f40180180a844244041e0180002240014041d40e07844000603c007140b0400350041d0f280a40c2c4054003881001a1000340002c1e0b810301c510542c0e0340da807400e2008401034014402114000341e02c8080b540c00074070007000645010382041d608010b0074503000380602d4a90386404a154442c0c407040f5440718815204101e200e116280388400320804581180180741d0586900b024084402d07540004041080589410441c4000410310221040e10b0210b46968480c00c1864072940143c4018011682c0703040103404500d800c12440c010740d81c069440e14141803900300140c50141d000b401c4504842c80542d40003022a030720308003a111003a61681c52003021009814420304280c1d6204165002e40c1d004101200c840c0c82d00591a03800c181c03107103030000d40300301003420490050089402c42c2e19892040810320140441c0000a46007490140c402000701c62804000300c401069144613000702d0740c01000004540300403000503880c1c814014000d0700e24000c0444202410008168 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 236006223 1250 236004973 236004991
    0x1809061502100204080a081c0603030306030b061009090b01031404030c021e0913050a02100509040c080609040219030b070816080402090f070306030f080d05100b04030803060109030b 80
    0x3503540d03000c03607040080c1c103101c56081c030046280c142804052626000d244401500d900c0380000c40d11100051074400080720400c240703003041003035103a20f00180a040e243c401070351052120f102140316850442911015103016840e25901c2e240b421907000094060110340c64145035441c0342c040110074002030020b201e1403007640d805100c4612403040101140001c0300030920b13046240030700c81050b2030300c0041c2074002400c0d10380c002c5c4890031482d00e80c3c6440c108180080d0044c0141e40065500d50b0040042d105405044406200a230300c1694200c42c1c0e01000c4070745660180c45140440e025003841f5400c00c501c203d03045188a04161240c6a0076a4500182d60503000104000c040000b2101c5850310700100d030b4100e00d00106141841e80002d8510100a050318001007880382c04101d10394002e51001d0001c40d0f0190100418401c00e01304207910740c00541c1203242003424171002a2000030301236500001d5079081c1c010142008c1c29501c5c0d4fc1102e070802040c450601c42d6644012001c02c5a0110300c41c465500702d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 236007473 1250 236006223 236006249
    0x3020f03030f1c061d01060810080d0e030c03010216021003150b04080c0d0203030d0b120703030215070206070801030b0c1c090516050f06030a0906091406130308010303180906 77
    0x186044103c1d0003035403000081c03c003010007003441020040205ca0454219103410400741c4c85418001c150b2886e5a80018114410107450110a603005014500d20340c408505541c0302182c03800a01d400e07071050405500000f01c040d1034030001032a0180e58041040c40d40c0c60000b940ba41c11000c42d005003034490304510b00400e0045400c10603800c00700b00fa54505c40c030a0724204d05014880d400b0030364038000c00c90540c99031911101200002d4407000383d031858425116046840544c0e403410040e40b01c400c40d0169030038000720400061000d5000003401802130704940d0f182203441c3e10715101c0d49421a0f002d00108444081002441840c10740e850310550024503507031740001c180b20b02e49440c0d1300e030622801410b000d2756a54003040040d903450210380002000f0544501740c2e40d54400142d80c00810308514010240340c5020010306c1801524021402d1415800b4112130090300d030100a821205500300b0010009900000184000f0b03100320611100c121b5402040348000d80c4603030300070065602a80010750798102e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 236008723 1250 236007473 236007517
    0x5100815030304240306231306060306090e0a0b01150306090c050306031005061c0312020d0203100b04030203030d0e0a05150901060504090503090f060d1109040c081003020f03030f 79
    0x50a80360785402c07585003420031a940c64401032004499464102c50a00c60305842c0d40c1c0e00315154884c0c040d540340e4a60340c040160075242d02015004000501582c250f441c40e02c42c1140c10ee080c0010105038450700007000c5a8207038689120412058900340e803000406031103101c001800007480c0070b0b4000c1c40c890b41d11103688916210040c146400002502c0e501403d042001b4081c0b07688401c030b2002e203060b4440c41201c0d5018500d05003640e54074a9410b08001542c400190360302c940031140d02442c02455024a82410603039103040c040c1c0c0d180558040654942c104000748004400103500c52103502094205a41704c02c0d01c6911100d05080c0c0340b101c0e09000c2015082040b1851200b8800e007030240c802190304003e9040b06032265503032800380c02000c600490082c4016071030f40e80d62506403800042140030038016030b00300704504c04503074004944441c000c0d401d09001d000f8440c06070301224411158038504100c83c9245400700400d451a585109800d4002081801d90502018004000540c0c0042d100403150f00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 236009973 1250 236008723 236008769
    0xe06121b040312091d07090311030f19030e010513061206180504030e1c120314090304060e100e0f01050910030e0705010807020307030e040204050604031b0f05100815030304 76
    0xc0d005072005e54000041004880d003000c8201700352034204111400040909010a25110409408035018030415400c02008920f41803510b80e030728130940c5d50348084d42000307006460a00401c450001041c0e102041032251520a2300c0c0340070990807a100104419550350400c0000ca003e1200320301802d030710364040205242c0c0058401505480985c2d10050441002c1f0518415601e00c450041c0b071054070070807607194103119030488001c4e0f24401000381840d0401b07840762aa00da01c01d205603070124a50101d210034a00d4850410720414181d500d40c001505055002c01111110700120141800000d00a084860711444200511104e8640703001880406140e0b18030724000c9280c1c0400c0c1001542c40030410071036400f1003910b1006030b03d4200091884c05640014000e03003d035402c4150008400304e000014400030b00704074000c091600018049003501c03032080501003101d90103840e4022035142061050304d4800d203015540201c2c216264000a04501c0019086600550060318805000c4160400300e403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 236011223 1250 236009973 236009999
    0x300905060406051b0702210f1525050d060312031508010e030702010c030306080303041505060d020a050f03010b1c1e0c0608040503070203070b0a0e06121b04031209 72
    0x201013461142c0b08581c0201e1101c0300c0c1720f000c1c402402040b2004030003110a054004026a1562000c161003c800700d280e403d80d5995240d101658504003001d01040407032107180310b003102c050100001c42581c7c440080c0191040c3d400300801c7d0780b605070f550310000003056a40015203880c00c40c85d50701141200500c00107044100050b00081c00310b0345842d480043c040310003c1103511103139081c01c2c11032103c0082d08080e001491540d10407000ea000000400007007080c418200c0a400004e18420845603d81c1d100b41321030b40c0c1814000941140c01c1a40500072440d02440aa4030804020004503100000318041410244034052101c0700d06501c0c0c0c0520204001905421903c2110903a62148070003142c903a00415070446c0300390400e0040300000b240900200f030080b942100c1d0060101c1d41b1440c0d0310010208203500680c6004001940c105048000346800000c82d0180041b601408110380c4070100c1c0d080720446001194a40000200000800500c0002464001883e00d460b405041c42ca0003010300c002c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 236012473 1250 236011223 236011231
    0x60f0e01080304050f0a0b0307050337050a0e0316060c23031905090c09090307020102030f030601020a140c010305060105070b07030b190e1005010203030730090506040605 75
    0x882100005111242000040c0d4044907403c80d4003030450100c00c0302055900f0b2694000e403480c03102c000200682150030030000c500070002c000b02030040c80c982d00d101e11501d002d24503c0c010410751010b82070b02c1040291b0845500500d041d840043c4000400340c040e4516440121201e40d03000c015403165050000500c40c44002860310305042008010222a82d103403052682e4410400039408000b040c039000841400240203a401035003005a0304250700420768940c0d00f034000c140b14400103800a2100c002c0071051302c0c601d030b41c183c00840c10a540c1c156240e40c5600000c060a0451007060403400c04254043c00031180f1003030312000340500402c0ba000040a5420040240381031150810403000043d8014060325070242103440c0005403481514000f4103160b03407600d00314404160080c0b02068503d0081042c5011300418607003103030007503960b000598076400300719081004251200561580d610100480040004500241300003001685a40604642d02c0c1c02043e94291300503802c000800076039220701900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 236013723 1250 236012473 236012489
    0x406060903020405011e060c050a020d080702240f03090a120804060e070b090906040914070f0909032a050102120f0901060b0a0f030e010507081e0103050703081b10060f 74
    0x1b00c0003160380301e2111138528441d0008008601001c001800004c0c40515505580142064140000c908005d201c0ba00002c074181c3c0301c3d0710500451010351440c20603990b0b9101c0c404040508140174811300c01c1c0503400c0200018801d00660b288440014400000740306024100d032181c4986082600b07006040b29403980503002e1581c00300b217040c00920345450543c0c403503002c100e400007500d946460200b03000d01a40a4024820201c11460542c07034040820482d054600c08075805103540e544900703000503103d007100003401103441185951040c1c3c10002180300d03011441d5180400341016940da4508a901c1407201115800300c0105200b10328885c082415080004d540c02170101f103043c0a80d0340740f1131141011003801e101c4148007818980d40a40c100050100600b4003c0244d4505004050280e04080b542c0546102004030f18a44550520025a040c0d030307005401820b0140c00d595031081e030744d400084407041c00c1001d2601c070728075180304001409a0300603015010a216141046121a02c401034100302a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 236014973 1250 236013723 236013749
    0x601080604150c0e090a0204180902060909060123040303081509010b0d09141b06070c030204020702040f0f090201200c040f060f080304050a051e01110c040606090302040501 76
    0x100d114403006442c2d242d5500d000007580102c880065480e64003071400b10382c010203184100803001c0101e40c050003c0f50150070606001ca20002c80c050201d61820900a41c0320100b48039a038107034148034400326480541811319001507100418001842002c40c0c0b000466600000307401c1c410036601c21489e50b041220b414241114503907400000d2100c9105021b20f0000000114a2400c0c0390f40b650091a03030150048008103820100c6000e0588580e540604901940b151441019060400a04071602c00d90001d03130814030142180e0030040654048481079a02907200e40c501600348500c0d100e14161109070000010b0300c5009880054042c100c0b075054005685050020a804150040340c02d04940c1d0088500160206c0d040307100724000c1071150010389014584d0b160106112070004003c1040d120100c90100206540b0380030400d455000c0041e40b44200070700580040310b0350088a00c2c0c000c03408450180c3d54580000c1010404a4034640d0020300010300719041081541410322449005d800340c0e0324916 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 236016223 1250 236014973 236014981
    0x150902120406090303110d05010801150614070201022e11034506012d21060c0e040b06030601020604140f0102040b031e07090909061b020303070206010806 68
    0xc4400310010005050710303454001c0c400800d03101c1d6001c0c542421403001d80710f0b2503104208a170780c0146800d0140c0400ca61801c1a01c041c121020400c034811111980e4841030004c1001d100084581c210550407070640c0724040051110819102078500b81c90b040f000c0c901604100b540402082d242c5528400700c12460030818041c0c20f19054003110a41e050707040d0b0044102000b07801012000001f0b1444112a203a0a0104080381c4c00103c1c099040351700c08840b0030b900280c1d1000c1d1300501c41e02141c0d0b11103503441d11342c001c000c1a1004a41e203d4001299240f11080d8101500ca59050f130b080c100b2854000b034a028241002480d05101d489102c013007d44043e41907281c005c001079501c0b040904041e2442041884c0d1501e125820858421290b0b0034070001c1d900c95944202d000440d030010b03202288500040300d110700849020b0703008a03104000a80d0f810708624a0300000000502d10310f44103031a03040c0c80c3c010807080ca08a01082d440050f026030b0046603249400e80000781414010780022603260092400c0c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 236017473 1250 236016223 236016247
    0x63002090102250504021c330b0315061c0501080d030204031a060d05150114090405250506041203031d070902030a020c0d020601080d090501080c070c030206040306150902 75
    0x50f400741d42003030720016130341c0b451061105a804458104800b2080c244011001c20851191250025042d8401c50f01c100c1480040f4000c4a0106409040d15110061000903084804040102d035459405820207103040c86000d640072661018000c00c00b060780c1c40d00010030241d20304001a01c1d100605113400c43c201411a40c0303846980320401d082a4001c02010041003542d03942c45d0110408651060854a50040da56049500302a09101b400c40051a002440440e030401d0314015201d81d600c8000342030140210654171600722070111210206441c08078001c50a40c03160070090016103028003c506c0822541d2034000d091b6416000c00744201c40d024401d1000000000400c1401c3c0d43c2c0728031025071a81c1e2040e442100030302690298070707251b00c200710490318060303004115a4142c609a0b020360700c001012180980d48000360703104050008044400048629103850080c00d8528812403541d65643e50300c0c0c000400640041e00103551142d80d07446043e4480010707908ac10000c010010065003400192a00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 236018723 1250 236017473 236017543
    0x41b080d050409020a0203040506030f0f0a140f0907091d060a06050603010306180f030c03020d02010216031209051f0b030a020604030b090f1207030801140307063002090102 76
    0x1c151003107030040345d105407660081c01540d0191101a180c5a102d1520a00c2d1004041c1c0c01d4440c1d0444100c143e001c6200e884040c000d5043c0541480d540c40031540b074003052132904030710042016980c0d0003240300c08640304100f40200c0c4050124002e0f0104185d550b419001c0c20b03c0005000d0300690b503c0c0090402440c2c6441c82a241103e070007010004518a860008250001c51564000c10182200c040c40e41090f40000b2903c101e58065800c68120040303018059080b480740040c2060200d422000100c000b81c862014460486034203072010800500d50b0f610b040c5481d0155115569203140c041c03510355514043d206103540003c04400a03c80e01e102900801d100384030307600000e00310b0780e5140c0000b10700307030f40801589540090b80000c03105842290203410580d504003c1c0124000340300c40c80009100b40140352580000c101c0180600086440c000003034800780c1c000c141f00c01d180c480705c480b0059000700d2001d0350031005401c4c42016903a032840c0d5000a0806a005411130003503400108421140404849 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 236019973 1250 236018723 236018729
    0x114131205030a02070602040609140a050a050d080c01020a02010e0607050a093008131d0a091a070903031707140c0f06010b041502150403180b03041b080d0504 70
    0x740766940b510b42c100c10002034440c2d08030140205000281c00250130b0740c0900807a0071a100b0221044161070544c00b0081216024440e05074010442001401145000094101c4580c45800c00a240100b41c003401400d81e00700c00760440150355201000b80500f1014041640d211985261084c501000481d0140840c2070500482a646d01d4074401c41200c1e407410591416600901c0c510750f1050091840c0c0400c942d801000708840d052190307480003640c5040032010030145910210101f00b641d80f20b5045900900c100c0701d0544200c940c84450b07220510701d50742803078000c1310540e0300c10340880d0940c01c000e0038191450a20b140d5100a0008100d0001d51195884090044144e840ca42c2d40caa000d180c24603044d140195102039014100001404064410040c401c0b12035001c4018210949554181d0322035130284000c0c54512071440014001a10429500c088104450310f69850340d03031070700342e11141504102c0b0210742a60446e942d0b2913007002070003407690040020400500041b1a4600020304a001c0c600c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 236021223 1250 236019973 236019977
    0x608071a0a030b18040b07090501050a0c022710030219030f1101120f0912030e030f0c0a120f030b0901080706110705060a0c12020c1807020f010e01141312 68
    0x5002d072030716594003980c04d009266a84000c8425017450708048410f1007042e5005000305059200005a5500510641d280941c1503140e00b00d02c07901c680c09200d02c000310300b101f5089207024002c2c0440040000e0070300b58005c2d0440f400c03242e1928114810b03c403400804140c3e414210204040c2000041e2019000c1000558044404107000c075504c401030b1924403243e4084190542008282c403140340341984000003c501841c036460900c50041c106508580f1520b581c815184c10803c11006c80c04442402855801c00e03f8003200c10000154131115160300000744007000142d003c48c10000e140768140510540701408407005145c5500d010005580d464031445800140718a07101451031201040c06550300804001d444e8035550005c40138000d03c9032030541c000b282d11140894450300120700c0000d207240348070400b0304505211003444a00088892004019070308511174080c104217020002e0040340790b16016000041901b004c07480b0003074803604008018103880360070404d21001003100b07820303803200b004128 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 236022473 1250 236021223 236021231
    0x2040b030a02070f050105090a02011e0e0607030c060f050f090d09050d060603050111090a0b090d020f040902031f06080f031b070305030a09091103060f0909010b040f0608071a0a03 79
    0xe841c4c038a00c00a403083c0040c0c800c0d440e0900704044402c2c04942310310120300c00d030707100c18440d0082d96480c8070725110880e07240300095000e0420122814070354005c0442601034108400e0310365440c1d5072003007903400040c0241c0c40c0d66211414042145e0102c1c1d00a030b08040003c01030181e0201a49004040031010301c80e1510840031070815100f44851a0310000c051500a0001c2c0440c0c040025000700d0350707210100030f0b80a00446a0005101070408003650000711004180300c044010720307000c000e0700354449407845074031a98441d913110060360100208045400d841100341100c2550048910445402d07901001c4031390800071300101034a40110032184045481321060038841400b1b0342c0e05180c90740e540c00c018a00d1000145519070f0a4000c45c005080b035079480c605004110310891040e000c0c3c0020350f22a074010703e182e0701c0a5a680303005410958004070310700c00003039040e4a010000381514440c4402440e550741c6ea860034050010244403d10203000412a8415404048110043d542c810500494101541c3d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 236023723 1250 236022473 236022487
    0x5010305010909050c061e190807090608130c18150501030b0603010b0c0309030303041104150602030702010f110a060b0a051008010306090303020715020918060a0605130b0c030a021002040b030a02 86
    0x1001d16a40344040c03011f03402e280ca801401010034803902c11607404001240c000800a0030301c0780b0804030710098a90580e1400016221001806407070544044102c506100e00c038408104565021085440b91056140c013190200c011b0038076440c0b550640c0c1100b81050b08200d03030784140751105e100f224111054821a2a41ca60001e0010b90a5020300f2040c07580c140400400c2c072003442404540801407600c1183c08010082c240844038028400c10303c98440540c009004907000740d805a08541804c0d5102c1c00c0050f0700318281c1f00c2450820180d42c4040310016500e075900602800c081d6181c01c094401914030040e111100c01000d41000d50502c002000c071038a91260718205442501942c00d00c59002190394a006080185c40d4082d4200b000718a02800c443c4030880ca50103d0140402c0c01400c003c0c1c2408001030900a00311072541c00300502c190303c00588140001c140021a00501880074a40702031925010f01120080c1803418003421221314500620043c050283c960f4200da8201d03801a80059440c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 236024973 1250 236023723 236023747
    0x2160b03060a092f1315030b0a06090602010510080718020d0507050c061b0a0f0c05070321020102040602031605150c0a02010f020c0705041e1505010305010909050c06 73
    0x1a107403c1010303c10300700b10b41d400d0302c2c43c2c2c07040d101e03200d12080148065446550020213000c40c05125000017205052410410056048041c4015071980342c1c540840d40c1c1c092400820480203650344140001900e000e010041c003542845501e421803100040c10041c03d00e005d050030b9035030f1028000c00351044600aa0364213242915030455031602c5811005024034641002c1c05010364100d904641d006004a0001418070001568035a0085002c4c400e406c1c10b0050610048071206420722084013800441c407102c03008103c04200b000020361080110402540c1e00b040710000030201c40c1280380c00d680c0140001d105498010042d1815071a03210f0211411b41d0300f90410034501643c1c010050f01e2011480140700c0701071590b90003009260700540090204541a0182104030b21071400503820720340142030140540d24064008a0013081214041d01185104d5400c5c0400c841c0d0000240d8200306040c2d204010958040c040c05004002d202000c221002071510740f180c0341e810a10700107100c0c00300020b018420203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 236026223 1250 236024973 236024989
    0x261008070e010315020313060506240a030b031203060d2a0306060602030a09120302011b030609050105010516060f0e070b1201090b1e060f2802160b0306 67
    0x461501120349003507540200400921003030100362100c8580014880881040d802281c0c000e0300c00d4201540ca64a1540700e0400a2001802859102c500c50221070030005600b100003100300c0703103066180d50b101802440174044070122002980a80c03c0201d202c3c0007080d996041c0c2c0e611800c2600d000c00e03054828601004c0c8580300784200c500302007005105081040c44919450b007540d00c907110802400e1f80f0340c48160780d01c0c0524045d5400113a20410b003400b01c0c404c86140d00ca0901d01c00e00020401c482c001c41d80301c07000c182d42700c43c842c0083e6841c1c9080081c0c01241c02038900502003802d042c0e00d000942804444107058240c0c000d4045074031050f501101a441d50302034140005a0010f4542194070b9600342c54655201c0c04001d141c04d500701c400840d211950b0300c101e2540d0040100300170200303070328204500d100b40049410103600000c01d006c0e5412082a5a008040d01020098020b48003608998911407413010103d8903002c651010b00590703000c50340c04c0040802c0e10001c980307160301e90340d40400041410b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 236027473 1250 236026223 236026229
    0x3021804091103010e0115090e10090b040b0f01030f061a09011e09110901080c040b07211403070c110406150807030c0e041a03060103030509040c2610 66
    0x51410880506022180781c851000000450083c0500ca24216011b801d8a0102a00d16003644124004002d07004540d4880c0c28007075510421703104885220a0444101d404482041d1400d211400410040044a00440d07501c00f03201c0380070f05201e50450301da0345440383c0300d00d2005214980d545560f840c0b001501c00e80303c40700140104070b14010342e140e00040c0a203200c07146c2119100041401c002c188440d44d4090308030b21410303074035020741800581d02c01182c8001c006025400600c00c10800400c00d0580940140807883c01907004007215019100040f90301445c0c00c0c050317420007481100d0b101c6d04040900449400025914100503104038a0410305c2c06c0310840220158494504140003c0d6004d1030840841042481d8840038403e584690054003a508a40125070000e8500402c0c8a4036207025031100f400c00c0100b61441d04949049800309241c14004e1304141c0c0465000310303101e031440c50140200c840301e403003078170344a410005402041300ba211084a8485040c618590000300303080c02e103409180007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 236028723 1250 236027473 236027479
    0xa14070c0303030e010b03010e030f07390608061f03180507140a0e04080d0908180432041e1a0106080403120b12070303030b040f06060f030218 63
    0x100c41d52854068010002d000c0d08034030384d500700807054100307243c184907203001c406240001e103143c028280b814418a50010008072580c240008448400c003d101044180c2c2248802000c0b602c141d10383c012540d6114544c2c808810040010100003180d207442c09400084800040804001105282c3c25409414011500d5241c1165000220140400002c2840407104c01c04102040e4203071820a004400440340141c02020300c9540210380014603100003800036408141c000a552806035a07690f40d00d6000b8010030040d00f007007010801c0c141c603041c407a101c22652041081410712040340769040780b2a0b140144008105000c10003e0700f44840c00e00107010b1003440340303010500c605852810b20004545551030301d103401c20b21400031800900030380d0320b9400385405884034030303020b4000700491028107204407025030081c52420480201040c10000354010b10300c2500d010070b4900901c2d00384401c071508100d0340720f0f04a086c004101322194000d06c001c0b5928096107409a035856180b40c5201c4450b440703c034640c0d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 236029973 1250 236028723 236028743
    0x1c0e0409060621060f050405280206070308070809060603150c041d040b0108060c040311011e1101050901060b120c0f0a030204080607030522030903080d150b0f0a1407 73
    0x1020100c0c80f46044150703100351001c01103401e082c1d244908403503007110001c10a030b001c201c0c120691812218017415130700103074220070300d05056940850115000f40c94100c000c01c2030b244c284540b060f00701d0b0340d01d94400c0c02600140760902e45500020f684246403e420588556481c003c10150380c0c1e20400c903009403d00540300c141c8000095a410290302e412103043da00114004004900c041001c100d290041c3d103031511003400d00d821070700c070810b180e0f20101002d81800340038091500e0403007100c55500c02060181e1201041c020907040c0315070940c0c40051040314030345d04d807200c14003590074445c013641d01060200c940018542e96000302d081d041d11904810b0b10240c10042000d00803ea45a00100242e810030819205070361901c00c2c0c207034203465080d101c070740c00800e00142c0240c200d00c504070141c0d45d0302d0103403030f214882d10b82e03d444131255503000035269080c182d12913880a501c0300001c12403800404650348481c0c42d141c002c3c0178020f400c1c09401c200108100b400208110540c0d43c080960b03420070f4021521203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 236031223 1250 236029973 236030009
    0x40f03080405090c0405241614010b01050702030319090807090501150c05070302010f0c020a0f1505040e0106030203071e0239060a1106040506091c0e04090606 70
    0x80180d0000d200b2079206952050001d283c07500302ca81981d00f02c50001d4000307140408601c2e002c20b480f00b0340e0140051000801d000540c03072043c01300b4281c0001c5004521000d074040100e800282500c0783c40060380d0521804000c0580161000002c840da20a4040814080703003100e0030341100c0450060384130010501c181c40001c1141d507030782d0f40018100c451019041d4904e111034401034a22002c00303280540141c214850800c095400360030300815442040c54809070a4503d5800908807a1480c1c000451088044609000c07000b03600d00184c43d492400d0400a041c5031401404442050050154104164010010405003405005400c0030286215480c01d00e140c0e034100700a580721510040d8a07485c000f07c85d90603582b10310030400080402240e48940d001c00b0f61a209001c0507074408003003442001007501044260140502420780500d208902401d110b08110b080b1038540000c91341307650503092400081402180d003000019040c2d07807041d1404154100b888c00d10200600c2c0b140d0044000d01a2a4041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 236032473 1250 236031223 236031233
    0x71406010312030b01080601021b0f06070606050a0504271104020a03140601140a05030c0c0610030b0c03011d0a0e010e100608010615080408040801020409140603120a050f040f03 78
    0x460015882e5a03403c10410341c20300c0044030301d52002d448540c0540c12445900c1a60000003103c014059809080703c9002e044c0d0801251269021407010740d0030594415060056242c2902100001c00040303030180f101011008180300e14a070782c403080f042080c031600200310400c8000798605100d40001003085445031901800a4042c0004407a04540c0c2d82e070030400125070b50701503a1004040d80d55948294100031644030260380d10b9101400303000610e041071008000f800001c100051094406900c030300d800c0b624500c1d108800700707809016000c1c541070510041c460414041ca90781140400b0440e040e103140c0b581c8120b40010040590498629402c1c40d400c41d404810014100d00381e4400400c080141580e5160305900300e8070315014081c8495558140c01c040307107103d5101070350014019003146152640d03400340d42d070032a8003950201d08650745818451811300744400246900c90700a801800348000c9084480f00355204222074402071200110b42010b0004041c01039a0280110b18119000c41d0303240c0c200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 236033723 1250 236032473 236032493
    0x14010e010513290103180503032a0409020403020307240c0f0209150a0911090909031303050a03080c0313021002070e130b07180312030f0c08010503061e0a020714060103 74
    0x7035113000c207082480c1520002d800100890310960070401031400c54685142c10700c155402a0301d4101030b02610094020a211014002e1008011000c40141d850b450340c8140350501c0da040d803012054140480408544098440a0089001d19071500c0e40383c1c0c400318540422240e610940294001d2282c4081280c40002c401055034804000c035103c031441c13961405840c080e01c07054075081c44103200500410109007010f0042c3c0c3d03005890b0b141540e0600d040780015030030300403440e070003a80e080d40010b0080b000d16030410341980e007000700016100d14501d05488181061219004000d01490f0100d103105e00c818800e10500000c2e00d1140304059140c240007140f800d042000100035150000014049a40c460085001c0d258804201019080e403d15544030301c200c2801034404681410740f22000030800307401174890105101440e4450180c1c41d4104010305142c0301c03008000300d054881c0c9440303041800e0700092070a40d21103103444000d80c0e52f0000d0725212490b0040d04a042c0514409c482c0040204209008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 236034973 1250 236033723 236033801
    0x4120606050111120d0902060702180115030608061906051804110315010b1c052805011208030907090603030203030f0604180602071403030c0a0314010e010513 70
    0xa0303119800f000c80c141140d10f4924000c0740381c420b4802041040c01c84203642d00201003203030005221608298840c0c020402d0070002400310442205160014040951001e6032a45e00c0341851070300b040810b09001903d0340d640d4024003540220002d00001d020701c505aa004880035100180803080341000b08642001601820790342102e050042d0304041010381400038985540c00c03c1403948090591a08403922450740c0040f0f140001000482410401150385001c0c441c040d405038442640900d414070080e000e0115403050500c103107814000100000e000d05217040c010035401c00043c40c2da907101d89111500d0410103038000c141036818010000140350f0048040c61042c0c00b4403500300e04540c3c680c1d00708000c603050300340c1015130030400240590208071307150b015060061045000d40e00917240d81040601d141c204441c024111070002980001d1b169060080da00c076001120190106541803031605249810140519030217403100c0740042407114669040f000322101c3d00c01081c00b5490350304131195000703a0480 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 236036223 1250 236034973 236034977
    0x2d05040218011d030a0b0901092118060503011505070f03081009020309060a02030403020f1606021006051021050403080f160c08090d0506010f030302010e0a0f0602090105041206060501 81
    0x10303d031460000c2041c0301041c95020080240009464a503200c01c2c40c480094100c4419641e10003c07200090b40107881d120545151403415103541092010081451a800a10640c1d0ba0030104003007101c00c0e003000a490640d000000107001d24a00d1850480700b40c0100316010307205a003001e01c04030604d904085528011800000c0b2001059103810f4041d0a900c000d0302c004a0543c03000d40020144411640519000f0f4443c0c41610780c516842c519551510100c00140300c0f04040c2d040b020802c40380c0401c10040444900e49003441071034507100c00501c1d400e4026510ba0240160006001a4124907d400700844001a0800c00c0f050800f0704004201520880b0702c50700c178001c407501040200b803a004030b40c041c0143ca956490f40c424255034800c22650031409642e03800031000c0007490000759080c00018040c1203501d9081c14228910700b002401d403454066a80504d4203e1010355000c01c0b18002100c00aa4000c0c101582d02e0040e00e00403a40c82c4520b41c0045907540c10460988108a070304d410a604440c0c0903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 236037473 1250 236036223 236036237
    0xe031b01080903070507060c110306090c120714131b0e0102070f081e03040801020a020609010b0103060b0a180e0a090605091f0e0106030204020a020709060f2d0504021801 75
    0x1e9000c29690740320b809130107040755015a0040000c039205600410382e5a1245d03000c0641c014070040131070306d480c5050315403502e290480f0104900c0c81c18607812840040d51400700400b0703204e213040003160300398440091040c050022040d902080b03030f007107800000b4403920800c00e0100800000308018000700ca816074a07401400b403140c3c001201035118207410140c500d0440601032495940005103566003004002285602041c130000400e080c0030f00c09010110500d4014201c1498000049802c4905104001d4145807610005210205051003039039032109007400c185890841c034002a64010b4641c2c0d0020488a040307a0400800d50031a40104601510400c000d000b0350321100b40c0d0945035000301c000e1740080015180c07400261003c0b07800404680c0c00301400080d01d29200d8004c2426a48010508405680091030030021420a07110340401040503041c1d5910060030089a500350403100040f500f08500301c0d241d5200c000038513141040c02454000c0046640c1c840c142101e0b0541411504150702164403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 236038723 1250 236037473 236037481
    0x31a100c021c051f0917090d05010f14090a03020d08090a050111070212150a0216080a051c0c0c060e1606030c0e011404090504031803050601050906040e06160e031b0108 74
    0x13250090100003a0321201c3c046282d0504000d0116a030440101c10303034480c240100c0703500800c0e000c3c0314081100781c1420b40843d0460050712000d046950241c40c0220703e9011781792100100340e02140398049100b0600e0072146036101d8054240c036000c0300440140c02546800702d4602d414444c44020aa114400d50b029900b0242a105254480d008103080901e080720320000900e400c0d07090707802801030485c600c402100c0c20015403070303211043d0000b48180c400314034001144501e02d104c0390311800009490079028020221104c030014603034071b40305400030941c81d02c402605c00d100314240060108601c0954201811541d00c1000030047c1040d081001c01044020b00038400c0c651140d102d88100c5401c4a078a1440c051a041000000307082c010030a9080041c14001c20307100c016100d8881d0002c500500040c4455414078081044080c1d0107401d0520581c500410381b00701140100e001503101510850120414580f40e10a03078400a110109135498056603003030300300407154016110090303502aa6080041d5607 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 236039973 1250 236038723 236038783
    0x304061a010207031401020c0f07030303060503071d040609060c02011b0f080f0403020c06030403030e0607030209011e11121b060615090a0b0c030703031a100c021c05 73
    0x280880001e0058000c1a42400031030b056a40001102e82d654000501d800c000110150904130180d4020f81c0ca07801224040062641c58003400c006000e00b140a416140e140c808040b105540c1d03210a0203c0c0c1c5041e000003014890b00358441c807803194011400344501c04042c28020700034080100203003200c44500298032000c0d0f01c01d2440f9942c1100b991100d007020344416234841e4901600034021400c520032803210308983d40b5810055400386220b1f481c042000c03c0043d022030306140c8000d02c40004c140c4140101182680c0c0000b02c0705502428011507455200300242c2141c101750001c080140b5413140c4801d6020300c2e1034800040440940c0d449404040101c0821a143c8a02041c2c80d100d80c1700c0b2101460001c58501e100082802510040c1103031044c03691041104110340000c0048002c0f5000854080241501402003420b00480307440700b0150304e4885000152610203141d420780c00c03c40d413080d140045441c1c00000400c5965102d0315140d001c0e00703525000780e8800c000700d481030f20b00e02c5809401504070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 236041223 1250 236039973 236040011
    0x3101403030901120b0a0308120108060c0708070c030206180f09010b12100302090f04110405040305040b0a0201022203030f0c03080726090303070e012a0c030512030406 74
    0x8009019600d84150240112420060060034007a0103a03030b400215000e60303e495200c0011842020085d80364032802005e1150501d050b405100c8d10341080040010041d080811581116440545151a4420703810415030f283c5a503000290407800002d000001024290a8980850000c41e14001c1040089040c05142c400c20b200348040f04030300f40f007e43c5140c05e07407035405a0300280c0aa65000078640d00d400041c840081034a0385150341c08642e0911081c480c6054103006a903070306503028800b07818140d400816a00c514440c20000c41008038003440d6452003901200d1514980c4a0340342d03a082c6100200c1060518984000c43c0410070060750a407003503005100e0030303a08035003540b00c40d500e40d9103041040d11149440309034401000c0e4002404e19640c035002562500454030200156200c0ca8203e00142441040030b0380503040c0018207000f010800d020300e80d90310349100d02c21581036a001d51458105415426500700410327034043c01803210304450f24074002c3c0d0b1082d4003655003488a80c000706a848015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 236042473 1250 236041223 236041259
    0x21806090306010608180d05032508010b030a0608010218090f0403050d0504240e0f0a0c171603060207030e010e090703270b011701290102030d020f0310 67
    0x190019001007040c14085d000080e0b2285400300f4107905a1601c954440c10b110800501070007149010003030040f56017008070059095900302d11111035a5840071009041c44105204908030004000300240b0340d0314258200c2c400a00282d4000d40d200e0208000110800c41c484a005002e110014002188114000c14180c0070f00e4050300d40c2c614126100c8021406001d0080064501c012841d4941d414149a08240704094a03078900008240403d070ba9620300304841102451301075441150407101007001c3c5d0700c00000301e804400d0030000303645030516120b0030310b5000940000350290303403000003060000c150003c0028a01c25501d20f00b24461074401500c0c0480b40c10745041d0460030000018000d280680d00c100701c0d05d2001041d00110450310481c44080c04c01e201d400b150080503400040220755070340100314850076141030090000860a000400c5190a925056650003a9048540100d64004d0040700d407482c5c0303101e00c20742d90745034862000481684103484106040741079032800108010715496402c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 236043723 1250 236042473 236042479
    0x91b050d0522083a020d020f1c050105040608100504050a0807031112041206020307140c0703050708300f071a06030c090c0d02040b03071e0804021c030216080102180609 74
    0x1c0c10701c140120300029000400c42c0c120541c0c1c04c106a08800108c2e0015007143e16003204003401000c404d070800000d9600691240f406107092010522144801103602d0350b010b41a060001001e544500300340e4904005003802401d00107000448205041d84022030364004050a41268a10007403400c0e4500c2d1407280b41700d0b610381c03200e03c00c600e0350024000d0b4008540042052414034021080314044045d2944480c145c1d41140c6c2c040501001004010710868000781043d90150070411051560a0f010030415420035221009801880e80c02c0c185003019203184c5d41e40040c0e800e07101c1e001032812045000021090300703e84141c207800070381b180c500050b44002c441809040c061442c1c9400b2032485158102c030065100c465020322012610b51345900c013440c0b04005035550260844820340300d500c5a11b03c0450004100100c403010000075072206851603c3d0f205a01c2107140002d596030804905288401c2d88640300c88040103c0028040415006000404a52456810010b003040c01b0400180304040750260 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 236044973 1250 236043723 236043817
    0x9050708060103051e1c0306050a060806181305060f0106030e0604021509030c0324010608131203020904021305030c03010e0c0907110604030504091b050d052208 71
    0x202d0450400c6040032903451500841c2d0100b200d50b864040c4004200c071b43c082c00640d580404000700d16001701010028407150900d5100c03800c2c940b0104107006081141200340c0c1e00d1550200707204176905401048903540000c1a20450300744188046402402031007400c001030304000042c05120b4002c680340d40220350080c503000c04100c2d03500e500710310380c4c00005040782d00d4003481c100308480d83c50510000003000f038880400c4da00341020050304c040f01501a000301c0204040c507410000c10120305183c42024580050594034040ba4201c0c044003c5c2c806c03a800c19802900101c0e1868003019004100b1042d42c0049054400101081c0b052508844400d0a04000c45c0c0c0004505400b80c2171601c0166000700300c40c54034140d05110800524608002650120001000002c1c20040c2160351b205a4600c01016184140102d6025800a0103030203038820825805a0310404074282c0d17007500c4034407a817001200d44810b080c9101c46c101220395070801110058140740e0040103600405044610b400c44203140c45241c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 236046223 1250 236044973 236044993
    0xc05041508090f240108160b0d0f0207050f06060306070f110f030f031803040e04060c180803090310020304020907120f0f0c021b01140c1f0905070806010305 69
    0x494541014114881038001d8800480c500702e0141301c01c40c0c003440e0794400203c10b1208071858000b0360205034403011b0340d80c21a01c20100a04041b801050898491414440e02e40000c04156070003000c0d400c0529805070310004040c42004008103210307015a19402c00d443d10307990b131401496140d00c4201e0700c100c00240d1601c0282c40c094000c64a2840f080034000c11682243c0c15001c802e031a40d0f10010f45da140600000c02000041c00303060340e0b070315200c0c8116000b55040c9813400e803000c841c400015100500d543e40320414800340350f00c50400c801038000e91518003034665a03550f070142d403258028885680640a09135000c16901c180f070080b04d0180e5030191150100760740d4060100c8880213a2101c1440301ca464840106903c262401000005120454006060300306508080c2c074080fa140d00e101c0c100c0044c0443c0112a80c2c000400d0324043c010030301020381c0e03010462605402c04610030780a01094002c200c0759024050706070301c100c040f91310560440d0707082920348150300d5880c44244401082030707020b0704e404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 236047473 1250 236046223 236046227
    0x20c10120218090c12090f0703200a0e070306050603010f03030c0218070e01090611070b0a05120408070b011e03030309020604030b1f1d1302010c0c03080702040c050415 74
    0x401c80a08161010045064242c001030343d0803c040d503841d00b42500110388020780c0010040e00a800115140003400d020b029120140d231145a10310000d4402e08194544a00c0c01c03241d110102c0146c90014503800005465012491142030107613074080029140c80404030340f03030503c801288d050362002c6000050b0145165411200d0041000e012a0003169985000031800250102d560081c43c540d190810141009000180080c8084c0e0051081244002e544205100042040c405440c0701e40c4969580c5d20000c80142e420b407054074242c01e2a20304800c200401e01c8000c8004c1e010a031b12503030588400e80d980b1403880040c41c45194100c00b2034404a1010000240203500c03003080141701501181c02c00350b5988a440d00103200321140035410210045090380d15801030030182c007801e10725040350241e40f946072441d080d49400810700340900c44c5669518055a02035044421711a522a043d054040c0e140c1c03800b0320341900003a40c101e000c1d074104011000340c40c0c00342003500d003075a90001d45190625015103007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 236048723 1250 236047473 236047477
    0x30b0903040f1d060d1e02030705030703061b0e090f0712020307050306010f031a010509030703081603030b06030615030a06090c0c0201120608030910091e06020c101202 74
    0x4041062004120005050070596540801031200c5043c030444004401c0320001103540c0100141d01c10072498211a0003e2984c4c0040c000145a40d0010000703401d082c070200c1e1500c2d0207038108960610540c04000108007858024100040382d0700c000c6110000041401d07148420f07040203165211701c0a900040a141d001b6003540d81c800c7c10380c98214411050500702d4022a4030030b6031000c0c00642c1c00000c00c03c180d604001c0e61505d0342003c0c0341c00c03c0002c00d40c0080b08480390440050504204000840c01c19039942008507101171508001102d9803031601455034000718050707507030440201c2d00f4244003502505d011001c1e00d00c940e4000c0d00b59120070510902c0b9118691000b041e623940315994401c0442c0740b05a0f442602540461030b2146642b18a0a000150004c00808144e00c3c00c0d0303007400d1050140348030100943d1101c0328181d50202444105000650308542542c128401040c0007040b40c00d51100d9115000c070484030140c080c0c078000c99058090002030715a6440b4000842c07540011a80d02541540c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 236049973 1250 236048723 236048731
    0x1914030307231e0a08061e0d060b03010606020105012105070b03041e12030e0105040206040501050f0442020a030e0307050405040b04050111030112020108041a04060510060c020a030b 80
    0x145503850180c8903d40f091840c41c540d644001031410200d030700c40000e03811400040d00880c084803500c1c141c0e01e4105049200c00011003109000d18011282c84042294640110454480050007031002c1912a10024000c0600b481a944411890a030b5020758903540001750305026000405400c1142c10003a02d4180c80c1e20203041210380700b0348030f00380e40e02d126000704003249181d02c1000c030300c00c010100b800f004040e59680440700c28241d14000030721006a803a64102c500f218020709103103845080503451000301d0701413544a08890021a1081000b140e12000c1c43d8400c0c803581c1c180b001c3c244402660110fa170103820301c5c800000d688512081c8020030701620031103005010040840d14201e0721000420301b03803041600c0c2180c0d072a4012080c401004803e016150f4016200781d4010305640c5000640f54500c1000c1e41d010b414400c040300490140107199030b400741070740c1c03128244491900b0186042d900400e0200c031003071107101d04880042100340c410702d608129a41c0040040e030007c0c0c00c2d07844065010202030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 236051223 1250 236049973 236050037
    0x3100e07050427090b10050604052202090613051e0d0f15020408011b170403030902040b1e030f011a01180e1602010f05060a0b070f051914030307 64
    0x1440d2000e0203202c501501356600d105401003440342c1400d00040c0c080b655550000c030f100740780c1031000b0b1183d0740310f0a40800d040b090001032001240c0440200100134404d01c1034080d0420130010388d0000f00c0f000384241a0464205881d15041100c80c1d440c080401c80e0348503c03441e484001649058003045042d07844170341c10350040012074070894040d401d00040764856804910f440e51207604a088030850120312004a00b09403c00c3c1c01e00f000c900c8100064050002c000800303065980b240707441952156440300c120074401810120f85030b500f2a0190000c8030040d09420300c24850317424440c21262040c003801d020441a0141d21031550b03425801501d044402403019442040412000101e0281902c2a24058402e240c10100c0c10030f10b042c030003800d59514102e0400c4450034002805400e49492080d107040340c64452007035881d0784803850680a81184220b020308503108540403a80c800302c4400c1900c0c0c00c02c1c810130aa004200300404010786030b0008076a01c0d0003050818a460440307403c3e025a24080001030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 236052473 1250 236051223 236051279
    0x6040207150e070816030503031605040f090222180c0c0501050c04050a0f0503060402040b0105120c0306030d03060305031206190305060f0105030a0c03022701030803100e070504 78
    0x180c18044201d074010182202c0030343c4001c004000c5083c0500c10300c5100040340744918141d0741540c0702c1c1c59480c40007030403030014200d582c0c902803030041c8070f482a207000e04201c2d0041c1010350390304ca0030354000e5000300701141001809400840407969a44154500319000d41610300380001b114900170006200d86007040c420b0201036070000b00001c00a03c1788078860f008084c0303025101c40c1030000307000c0d101c1540e8000803d640c1401320305204507903000400551150381102c01041700c0c00f101e1700403106030080c241204071210300300b001d100680070960040d5105a80980031034a58104414085068640a22001d80300f43c0081000f074074400c01550225511680c00b8107072030b514035404080910b00e0000d9500607100b03030b0000c070180440250450390040c0104000c4009081c4081c1c5034644000030355251000921510520b0040b6480d05a1b04001c5122080410994255580d40b4100f039241544100d55002e1a01d01c4000045010100203d165000b0b078419038841e8100780c00c1c00c807040ca0b10351321403099100801c08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 236053723 1250 236052473 236052503
    0xa090b150409050a0b01080709051003022106190b040b03090c0a15080709030b0703200708041e0303090e07090b07050a05010501080316111f0c03020c010503060906040207 75
    0x1940148002c1c20380c440006074030f1800c03810741d00c115107410f404141005500001d1090b481e070302c0a000000d9850465002180d410001e41c190000d00c91402031b00e0b0080841581d02681c00c000059140c803500b01601d0000b1340c2901c4100c1e50000d0f2105c0d003c0c2000743c0384180020300501b0300100103168003040e1503044542c50762031140050041c54541e8081c0d001483d1194606251661181800341c020105082545410f410b65030381158a100041c0100c0401d5500c203c5142140580c1c8954682c0c1401015820f550300c0060500180c5903005000b111a103070110602c1c400c0f0780401c0d085803001c5a8165856000107070130143d4545110034003038582410480e401e0310100342c060b285001041d545110304001c11035441c0c00e280a60a44505901404c265001440781d0080c000d82e00c03800b00e41c03039903100d046800390181c4000014501c00440c84901c2c100881e44440004460f04078074072024143c080d07022a003081c04048011580c0740301c102c0e10950890742c000041620703404e01c0e8015003411403140b001d803022181 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 236054973 1250 236053723 236053759
    0x706020d02030108071a03040b01060323090a03031b0519021203011202041d03030a09060615030504140705010c0f1104090602030712180b040f08040603021803010b0a090b 75
    0x20f801444c0d007074009040800181e00e03c0105105200c0303805000c2411444c290300c40c2e0080c00c0c1b05218020034140c5441c0099500d02401c02c001246012a80c13001149042c074400080e51622242d10440100340b4111030244850582c001e803103800c2c0380c0d50f40c5492422002c1401254182402011481588140c0c0c1d846d0780390034856005075020b81103003060701510506070700420098030020110f60400c0101103d013000c8800000c000c60341c1c02501c02d04007013a007192528001e00288025409003824513200100810510391503003000d4020303401650810b402c00c1e00b0007071460f1104164881c050200c0d528942100006007400385105210b401b6008102c00301d440c0304049402d40b104501c00311071641d800000c0040b507540200070a03040d5900c0d0358007080060b000108841c41640e01841c05001c101200c0009001c01041d11040300515500c134031882d8469681e0349000c1e0207508070080c0e01502403801160001582030503c82e02c41080002000140c500e451b22341082d008105124506030805a26a00d20704011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 236056223 1250 236054973 236054977
    0x41a1201060e03100c030219030515013c0305071809110c0d09030c150813050c030f060a050610021005060102190b090d0302072f0a1e09020a02070b0706020d02 70
    0x705c2c60b80c07030141c4d4918242d1248c1e00ea02d4040240b038028145850140035a10711000f082454165003030070142b00b040000f4000b609038190504910800c1d1880b003a04100300314921442d50200111500c4c180a603031203c40c0280e13010004c0c0400e400b0010036107a0100071600194014440e080c010303a4444d80341031001a181814030700c1100340100845c034406d504204202100101c50018001c5030f006200c110481c040007030010b1f00c00391004400d03103d40d140c07010500c60140400354501c1e000404403490100103071000e0b82c031690102c4074543c0341490b140025005040020b070b850071402841d8081d0042804600904008240c00f0301454114070075550030881c450001149214443d0040f00b03070b58142e2411461803880d01600c85081c1040600500020000071450412106803007c00f40950741c03482845014440600d0300440b03e035a0142c6192000124451540c4810030391980102856134010f46070384098040e84500c901340c01c01640041000c00210500c01d024201c1c482c400d40780540344c901542000c105031f07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 236057473 1250 236056223 236056241
    0x917070f020a0311030601090e071403032a0c0102150c0a03240905010801020403050309010c060f020d06030b0906061f0203070506010306050f0a15090b01110111041a1201060e0310 79
    0x2000d4031404c1ca000c82d01c0c0400181e4010b00300041c080c08001082c0c01311945403206441201c41c0050035200109407941c0034000d489024113900308140660b00c40c6120800090721010600d8042e000b110700e0300215500c0403441007031054110058880e20b48482519031590743c04245c050341019525070716103242688191144d244200c418082d04a8141440742c0703d000c883d010381c0700c030020346e204001c01c000180300402643c000c0f50003420800000344c0b15081810103400000c41400d003a500c0020890300200e030544c04441603900070a100400d9a43c0d401160b40d80c0d2800351010f43c2c1c030049540000014103c2003482d0000d22016105a90401d030705c5558262030400c003a041241c590ba00e03003041200c03460103e6041d035808000d00c841402561219036026440003001d000b1104032b55121010718050340d008490a90703864200344004c200400c0e00c00102074590304107014245503460399014803280303485000251140052040c400381c95a0b460321100391401e0440f8460180c2600031902448044030440c4201d11074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 236058723 1250 236057473 236057483
    0x4081c0501030b06100306050310051803041806140a090e07170307030201150b071104091505070e01030623030a0b011502070b0408030d0b06250c090917070f020a03 72
    0x202c4d00b80f100820204c24203400d0860101460003604026035500011240380380e0b088008001007549511000d1241c00f54510280c081601c030000d000110084d003604544450508020f0400906460340c6c040c404280440c04001d40c0820100b80034000c0500c503902502c3d58410800071520758950b51a0b01480440300107490144a40011512600340b5030280a1001c0c4080d4034804500740d01e040030340207203c90094400150202d003141d83d03030f80a561035590100114642025100d039040c005006d440000c0c00701114000700041c024000303d00554003a0048406940620005c102100f19840d501c0500c50365103124254584240580c64020500704480a406000740001c0741d03918024440e00070340341608075031040344041b0307041000300f014081c040b0079220b00050115010506802d1030380081c665001d4100c0907100074400f9504441580381d007444440c0201d01c00c2d076644403200d5031501000112101200c01030048070441d00044214003a09009005061140500b1142c42515801040c0303010340940007210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 236059973 1250 236058723 236058743
    0x2403100c051903050910050702150108030a0212131e05060c030307030c170103030e12060709050a0807030305032205071202091f150909020a0203030115030c0804081c050103 76
    0x821150b0040220012402604090083e81000d903130321551400c12000c3c1001141e03540c004192107910a000c80d42c15603910000c1c107585541c58848054803030380086c840b80050310420400a1070742d0004825900c103164500006900380e40341c402403207451104000c000244407250300020035240d6400000e8080041d90308025601da141018000e4121456074407080144403e01a200300c41c0c20405410764107481d49417800c2d10b4602061400301d0500d0b501d4085d400c3d664020241080710b0654441c40c0c03101240d0084516980c1155520f441c3d41e1203601500014001500030800164a0000009a000d840441080107010312503242c4902f0b0410080e5004588007000001291041d4a004200d0581156901050318510a000c801501000141d4800d0058604801f800d0401141c061440f0900a014002c000e55584e0740841c4002d4495003340036480c44124910b1100f00740703e20034402c10080510325100c0c12541c1c0c4079034491030510340040c0218409000c840b00790800d192041e00075075000310b104901041e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 236061223 1250 236059973 236059987
    0x3010e070e010f120807020402120a0218090112080a020708031309050606161103190f0201080c070c09050406020f0a0801060e030d0210050612060103030503010603060e2403100c05 79
    0xc1c004001a880a001582501d10922106444031307408410103511812040d602d81c201d201050190040350784161041c0c0c0c01000f0044040c034150014402c0551a400e15040c42007082c04000d0f03011000e000300c203c1c00903405070380400540c580005001000d00ca0045505075580d50b0f01381c41c51980720f90382800b243c800c600750400206415006054000320304441203414106110f803101804180c8000c05880c1d040740f280c0d0100c0e0743e1010301201e20b00704400c0d021440215500d0a010342ca111645104900165000d0001010201c000091f01e009503413140c0c01940543c90101c0c881c0c0640f10162082da0069030030050110b8040180c002019030007200d07107480560790715150b07001d409545c200c00054040e0300b00004d808085136002c40d80601340c141003a0f00240d01d48039031001c190345043c102d401c000c0707a200f00d00c000300034182c00001842c101c50466a0034045c40380c803801e10b8035640c041a22500400d25042c40d502c000f40890790311010280c50058100c13400c0034280a201c1d0156810191960081600043d0003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 236062473 1250 236061223 236061239
    0xb12010c021e03120a181109090606090a090809090a0506130e0d12020403020402030112060f0c08070f0c08040f050f04050903030705131a1b0a0c050d03090503010e07 73
    0x100407074a0400a0008005601004541d02d1340324061364081c0c0c0e80440d40000325022110751020510000c8524507000110492a2002121020045880c0729200e1400041c000d00d074000f030303a544190130290906a40b1f46a40700b0f054050040044d0440c1c1800c81402a070065803a42000342d81706085001000c030340c0e0709000c8141f144422556101e0300300642130541c0c1c8100c151001500048844552a04041c25421409000020f004130b80000f0340c018000400042c841400b0f0b00b04440300790084104000d15422003410b030044a10200980002c60704000001e800280509458400c0c07081c0f606101c1c0080d2a03503540d0b20b10981c045c0d0001520403075042e0050042d07080c0a100f40c00340c110305940802150070b1040365982e0b0790000820300000c004001030104001040e45040c2030091440100070400741c1030550844180790000d90041c03c41408100d202c66040700c00150811045800000c03001001d42800240072240c03000c408141c0c24003110200005d4591024400c0f0300c0d52402c5c1c000642040d40c140801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 236063723 1250 236062473 236062483
    0x20f070803070e09010608010b0c12130503060a060f0302060711041401180608030f09060f0d050402040b0414060103151d090601060f020303160905060d0509010c0c150509010b12010c02 81
    0x183c280603403540c00040c080c00b50814000e03810b50346541c03415034031189103801c1180340c24102d00003c0000140400d06174680c5000c00c52100030b58100701c0a880032a5a800889000c0303608034806d50080d43d501510801c0981441e100a1001071b010f1040c04054503220800306d4181c80e6203600e2094903505030001008200d4840e4540304800d5003040061200c1c40c41c121a85969000c1ca02c2d24144501001460511940d10401140e00d070080c40c078206500c4a007486c1c41003004040445040e8029800c241041000f0703d0b00d40300308412021b10503010506a1a200011002440325002040d0005840b101c04165401c2c0113110481495429529649601d0f10082903810719406a110a082c000710b070003040f95054001c02035940c04600300701200704110002c0412104410141e00480e007007640001d0156294200750003041c801c4607080300904c402c00150104a41e070f00c0c82c0d103c0142611552601207880d400e00c1c0d41003d0b4100316400d0003c10080300341c80009000325126612400d1a0703550340c0c1101003168040c46 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 236064973 1250 236063723 236063747
    0x409020a0902031918031d0a05030a0302011406010306050d060c030e03071103010b1f080c070c1502070e070207030b09030702101d04110a0c0c08030a0f03050f041e06020f07080307 79
    0x11101d140280c00c4e80e4081c00d0707001c00c00003007509084040c7d8010341c20746a28510f03a00802000b000c0382d00e00c4581d410061300800e140c2c611984c0c0701c042100001d500d03500174016001140c01c00b0382401c07007049460f240c200041c400000c20390100b5803120002005e0300002c01c080c0402e00c3c01140b5060010b15168101402c480c103400e5028092000485041079000381d8100313040c25240241090800c680e96600e8202403440358072001440005100b0010440300d0340e2003200c0741a601aa001ca544503602c591085803071790011504580140d204e5007050000a40314189242c00c1548501201c0c1406181d600040c00400100e030058009001400e8850324854110070300d0140060607601006080702c001400c1d0780a2158094000c00d100c40010445e080152018000f8000c015034800d50751a6411060000c000801d081c0e07100340041e08150100b40d910110610481c065035000d03c105114030740c103900346800702d80c0080c0140d170b005900384607101d40303140c08000030028603100307000d869580c0c98040c03009015480015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 236066223 1250 236064973 236065001
    0x3120a030e0c1021060b071416030b060102060f15010c0c0506040801090b15030c0d0201050705061f08010b06031609030b040813120f08130b0409090c05031b0409020a09020319 77
    0x50020400c1e039017024122079090781c0108c2013200d01c0d80c80032245841e003144c0c10400d80101c0e2042a00109010b200c01e846800744009909894650f19110030005014609032080d090003c00d4401441d01c56000f2070310b00c40305038418070600c040b8690310300c00500103030001d070b101c25400e9440700394000030032500c00c6030998080c2d0f85150144c1030041c2400800d82e601000c0b00278078002c81c2c040304003509580c05902134502440d44242110118503150800107001d1512103076943c0f641080b603401268000e0180109400310314054035183c1140d9a032404103400001507805041404204140800481c01d402c41c410701c1075001d004190303035a10714605049580f80c96903102c4010302d04000809400074000c10030300d130130f03454000000644a40000c509142185101e0388100c00c103100000d40050700c0150342d009400914010045005034640c6c46050540361810f808810120001303071000340301e10746002d0f03010315041d50015103451041c0d078942086104a0380300340d41e1503482e07564501000c070210a090140240c401511 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 236067473 1250 236066223 236066231
    0x304061e05091011010f0204210804030812150a08030306190f09052a07061a0603280605150c0f0111030f0603120a030e0c1021 56
    0x2440090040000a4514040c1000c603108065400d1180e8181d070344002c0c0081c03c84101c00c42e91071000d4080c4a040500c0358803942441e0002d51a45040c1c8255006c035048060205040b0310380b03410b000f00034105100c01701d03480f071414400407000c145510041d00760160034400028940c00c3c044284d007e203001c903d410300d1040e24200e505121900001c01a00d4001c0d4090310029128211208110042c40c500d8020648146441c0d900280320251074009500485031240d0b80320580b41d494485c1c4118244c0350a816480c12070420001c0e0018480d0743c0004d01e01103142840c3c21b841203905000810b20b500503a080b1a0704141048a48120410b1544181092508090800039145024041005494645003a13007148901046180c8500310920144542080c020020003451051384085d840c07540042c1c0d2003d05d101a6040012081d080015921003903000e030f40d5426041c0b03200220201c020701100642c4040500440c0c0b207035401511a031980c62203e130b9603900c4902c038009a4a51200204d554078103044581c0d414 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 236068723 1250 236067473 236067479
    0xf1409010f06031d1c17040f0308093a0206010806010510030902040f0e0d02060915060d05061602010b0f101103040f030c05010906030b010e040509100e03030105030f0304 75
    0x500390032001102c001d4240401c040c060307030394181001007040d00741020301d02518400d08500d900d888183c10707802c0b49548844e401c00441d2042e82d0440d81c0c0843c2c00405403409101030602190007510b010754032120201c210743d1080c40c0c0c030040c0711009800d200750309034054990207100c07007010403000c0102917001c503440100360035032500e410302c0e54581c0107220b01402111002c8500303086030300c650052842540c0260090150060365841c4000400181e921001c0350300444040240c8a4400700340c3c83c2c001c2c8002401040f60201d01000b001a4540242c480b952140c021510280010000c2c01100e02c80c03c50340250400504511902034291042c4403110b5100324002c4010711042d40e1401e5803203c502c405442c0511809411890b4940385116a41041900316811040002049804284802900c00a0780c811200b99507810040c0c041d6001c1008450101d008000b0030764803400c283e4000ca90181009003211401188280e41000b2541903c24204c0725410010041c805400d0070050341d12520076280065240c02c1c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 236069973 1250 236068723 236068739
    0x20010807090e101a0702030712030e010e0f0909010518010c09151b0f050d0e0d060b220f06080703030f030c0e10020a050606091605030915010f140901 66
    0x1a00d4011121001c01010200f41c00c003c0075444800a040e05800200541610380204c1c604c6070003006080f8440e00c1356400101f614652a4900d22607030342d06844180e4000280401516400c9243c00030a41100540c0800e0b4a1a501d02002c1e03401070146200014950030024159041d408a00450034000d030304003110782e006154060f16101c00c0b03036021203c02d0b2041000e10750888008044c0c604444650f090444014140014403c01040d442d20a20450798000ca06101c1a5005101d01c4c485540c809240320241c07010901c80d40220030054130040400750f1042c4000400724100d035040c11500803aa640c0c020005c0110654032806024191450080501600d507581c0103014040d5200c82c4010181c0f03d042d50b002c03c9004800c44424070200600b00316120441c040c0003555201030640c160340302d101d184041511030601c10780c003600071270112041c481d0780c0c6034440083e1069031026160024500c42e83c5c8440c6e21610500700c5079406010580908808545052030300c1b94405200040b1600c2000b905004100084c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 236071223 1250 236069973 236069987
    0x90b03060315040203101e061d0414010e01050703091403090d020607060e030f0a230405010f020c0d0b0906090f07050f0f0a060806120c0d030e0604080a20010807 71
    0x4a6408002e41581d0b141e1000c82d0070001d503800021417442c00c11101c102100c2003d41c8400e1441d400e00710404c000c50b507407a0310007400103441b012a55502c00400c042030100b8030001002050f0030542002051203c4017400243c00c450b811034407100025500c80700441001074403000811400c2c5031030021801c0942070b00001e20b08103540138009100f588002400700c1000219006410458004000d4a07201c1004022030b8030710b0340c010010f04d00050442614580d072083c1118152000c028034513081c609050404006459150940c1c140c0405c6d03102d140d040f50580d540d844401881c1c3c2e880b03070402d8021400c1020083e0b10300803002d480c4c064160009030703100440c83c0c00001d01400f02e83c400c07284003100d110b000300803545c0e6030100d025541e0072200d412401b04405404c0034245014090130f4a40d00008031030300b0f40264941c5000601564001560140100413074420a4152581d0100030031181c0b40a40c0c4180b07d9240070700d075400403100c00780d000ca21041d411905500c1912105800c1c2000c0e04c80d8640030000802103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 236072473 1250 236071223 236071243
    0x117010e060d021203030a020d0506120c2710080106081506040c09080105090703020312040b040e0c1918090b06030f0c0c07060206010e0108032a010902060a0f090b030603 75
    0x801110b00800e081d99140d0358041c0e8100601c20659a42e410040f44400c080d620090240b5410b60922001c51030f50b0510301403505a643c1c01d00c0182801c44450002c0068140344008020706014404210340090700c0704640543c0101ca150090440d801d1810390711a003521210303440b003041c0b500a80708402c4410100409039034803c00882d400110501928002d58090b9003540250a4030761904007040010b071702c0012401c055a008030100c550591541d0019249446940160060501e0500080224454148041303400c03a803003c0c5400d007040c030088540025800701c00140400900c9a181e032004124040c640400501207141c2d062241300146c0c0d0125400d4807000d04201c802292200000b24690340344000c0e9a0f2440c03001055030366951f940c071350084d40e8650a0040100a20b0028000143c90000104840c69100401071031105160703140c1050190540000c1d02c010103540f50206800103a80702c00051440b0011a02d401c0050404040c00070005500b6410010565004000b400340582c1e00240e10324207 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 236073723 1250 236072473 236072479
    0x50403061107060c0c020f030c010c020913080307080114010903110607030c0b011403010e0a050a0318090c08180d05040b0d18061e09030f05031f0806060117010e06 72
    0x40030050002010082c07003042006000c075440c2108125001d98401080d6540354000c48000d880342021104240d1180e90b00c181d9140803800b41e131150300c0141030042c042a4040800c2031101e031850555159240107500803140c0e07000240310740b001408108070404800558500a1811015176815651030030039810203810050700c00c5402040150805224280ca008060350005041c07042d565114003200200c00d80d96200c901c02d5007051407001718068009030703881c1c000c1c0d002030080c0120314440d10150385c4118260401680b0744600c0300301145134009401103001d1440d081d541d128041c902034040d031140200d074040424654100d83c0c0001441548901600c3c00d450b201c80b0310740e0703443c895602690010800101c42d10521091420394409128069004100c5614054442c048a00c403543c90201100c00c4814006d0215492080c010503983c41ba5000d140d00000240754800390860b0160b03140c1c0829140c0d40071081c20350000081207a5940d0181104512405020303045040394108051820f41e18001800180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 236074973 1250 236073723 236073731
    0x91908040303050c01020910051903090c1a310608040209040314070611130b040b030121020d0f030f02011109040209010e0a0b03010618080a031202090a0f1a0a05040306 74
    0x4c0b40c501e083d4120340300c028006014401e150b2003014043e00b1a08550340d050000101c4190b079810050007030081403100355106000026060801622810f600046088040001d10a200f0603801c98850314244214500c03015002290840740c00303210b6441441078000b14200600d203000d0000507114514101d400030f515007051040803212015046040c018400c0c050070a904140d60628041c148d100208502c00c8950020b4a00c561500d4903e0000d11803071003149400602080104240004008002107030040d1505109405035940c00181c461050100140c4103c10040a44420990000741011509032140000e0001c8249414441c40e64081d69401034040c2d038000130655841e0784551002c4140032002040c01d880c254a900507801d45400901444001c288960345050042d00940090002c66540700000c2034440c041f0f80d41107940320083c807140e403440d6800344654469990380d1602040030700040c40b41e43d20350600e800e1b061280034060500c11486804104008100c1c1c039884001c0b5400d80303401a40c082 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 236076223 1250 236074973 236074987
    0x108011112060909121c0c032304050705130b010e100e011809060b0c01050c091e040b030d03020a18030203061303020f01060609050102010b01080c0d09050c0d0b09190804030305 78
    0x600b8514a0200d142c145600000d501c507010070205640d0504041c00202001840e80c0d000c070603821274030300f21a101444a0350211160341000101c071181d50092080d0150b40849603900045104440e0b4035400003003083d121030710900709591089407414902c0c4202e0b2642c450180501000d030a40d0f21608140f81000324024840c8019010030510f0801846111410066541c2c0c4008410f2a5040045001801c0d42450f020460b0042d14100341c0c1d01d200702c01010042c1c00503030303c0e505040d102540314840f90084e03140c4e2015112554148600c0c01000401e0320007607510030f5405001000e10040c20180c03092040c2445041c00980c6000803c1a80705248031440105403e076401e059260080d03070791558000c1c1d03082c80c1d00410180c0d48402c108040b11400e800a00c40300c1d180303900541c0c422904a400c0000c5060500965001c0406a00601c95030b5000f10281c404880e031040109610b1040c0131020740350607520005000c4101c90412105a0381d0189440400d669107081d0366140301c0c0d11030742c40081e0400c50082081 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 236077473 1250 236076223 236076241
    0x2a12040309140a14061303080d05010303020d020f070e090109050f070501300207051204081506010528050c162603040b2104051f0b060301090c0908030403080301080111120609 77
    0x1b02c000d5500840c1c43e503100c0c2203042031a8041e06003400114010f0050202640c009400014200c89080384e0710098003003581000080c0c41d40c80c1c4d004018003010340d02d034001000800d0052080710101c00c1c0b190083d00ca1242010f0025114000810100302c1d00c00c00d488034170900c94080320650440210b58a000b507540c800c5c0341000da141803035424106207446800640042c0c4040e001035101056083c422031420b00d40e41ea000191001d000d56183c500c6d9224440c0950a0f002c01121038160741c107206400c1050030568600a1507290080700c0080c1c01c00081e120405100d0100d0030300c0c2c20b80c515142c140303840d203c500d2543380c0e260f168040c5104900c00e00e5030100784501401d2111700104404665070380f80e00c02c1440c09013401d541d101c2180c90342c3c180304003141180503e121114007508000d184040c1035a45542d00e4070b4031170030080c1000b41d1214200240200e01090146040c40180000d5026881c255125410002024210385d01501d84007909403081124050038410000d00d607521820440f02c07e03075590381e10f10031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 236078723 1250 236077473 236077507
    0x1c0f05040902030c1309090c061e14130b0306040605061c02030402130f050402090702030301122307120314030601090303030923010911092a12040309140a1406 70
    0xc031800c5c113a17804004603000d0400d0380700d0000a80100c816083c056541d0505554120117081c104c0c5002040c0d40500d044140101000c61046030040c0e0f9480c0307060040300c090006012203070042c0040120000600080d460503001d140094802100c0080c03800c0044210b1107088042130030740219140d0040005415507454503851001c401c050748003440b40301628242500240801c91381240714003d40c0c40450111880041a40e05898070808843c450d84581c1c0c9801040800c400301d03c250b14581a40c0c08078a800040c4021002040314542c0c22007070344d499180182244180c020114000001801044607580c1d002c2034006c1125003504001419005608100212000ca0301e140340d00391503406207508a01c0015172140034a24018220028100f500d2000c101300c070b20098404000c0d503613552000342c0321018400031480b00c2860810201d8030b04074031222000d0012904460580c0803549400c4200701c064015501040d08400c1120b144450f2428840c000044540c165201409200f020603d01e82c44130310009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 236079973 1250 236078723 236078737
    0x10c0b070903150507021005061507391d0c0a0c02030f100b0603040b011502280303060801150611070302030109060504061103041e021807021c0f05040902030c 70
    0xc403181848140f403c96015140a5a56400520501900c0c0d20268001d10540e0b00409000f4903d0052038001d10884140381c018503025241a090700d0407174080c2454040015134003800160b150256400502c10817100401154013028045142240800055100b00e003025406000946560f444201400f000c0701d00c114680b10081d0548241d407503130840c01c40000398855800d05000d2060141181c10014080d46d80010b0350001d01d801c2140c0c00500212012424005000d1400c0c41102c000d001128031006c002091000f040c01854503c000b00800d0503414007840c00a45540d000070b025613401000c44460000c2d1511546080041070801182169420b11008004540040080c000303440b46080040c014030081d0742c111035081c501020040042c1e060740980748a25042001c131603100340e86c840c4000c601c07103824004981c1b00c520550310170600000c0b6000d01d40103a4240d8014800259401a40c0d07010030754030202c8805200082c0401003c9a0740141124103882d0b00701005030316501e882c581e00382d01e401562 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 236081223 1250 236079973 236079983
    0xd1508010507020c040b0d021302031e1305060a180b18030c011506020a020105072a08010b190b1605160b0d060605041d070e0909100b060306010c0b070903 68
    0x10500c10582c3e40000c41d001c100004441c100803455031801003218411072540025040342c0e400e28003034015000c0f0ba01959104262000c2c040486a81c640132145442003140c00c0d28002134040704030400d21404100340c0390300400e105002c105403541c107140650301c0c0d0101c402c0208041c26100000d40d5860000001c14428181c40084944503900d144100c3c1c0a8000300c000e2220340d62810a0015925200207001c075587e940603121075141035160340310302c1b00c0240f034440c106282d125421428840103828a0784003004001030000051104410820000300f403e0400c030207410030310f5442d804d0081481ca4401c84074451000c2e542c1e401e48000394a011030410348a42d40d0074600c040c031381c4000203c0c2c0031000010103440d82d184a003046103a4540f0019900e074020360140c1c44040441c003030200c002c500140340032904000c140c02c1100d107142842000420070201216481c0c41500071404800d8074000f640140d4148010441c3d030b0030f0075498010b000030303c204007040c00500040c0b03000380440c11041c000c40001c0c01541d005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 236082473 1250 236081223 236081231
    0x50f03010b0303130303020c100503130809090f0604140705030109230705030f0906010b040b0715090606050a0609050d0303050618070201060e01051c060f15120203010606050c030d150801 82
    0x5884c0902e00180520040d00540610601d054040c40c2418030501c0c40c4c9142d1704d5460958503070b41403d0004c12072850b422a0076150802a070150380d92481d807003c2c424500426007441d10319184043c00283c0d0f1103950740c50f00d91034096003030016183d00a02500d06440c014103002070703a45200c02d1411604d14a010540419040560a0040c2c1591200055103e511001000d401ea6120041d1107a030342c0100b48110040d6035028402880345061800040c04194002d00a0040301641d954600044400c100c008079038065846008006c20b08007200850014480ca040c0890340520740b0001c0389071844520745c001c04041d0b80d4000501d1030340ea04680d01208001d0064454110315024030f010f4024441d1f0301032941d40c41e25035000065640303008511443c0d004110003050040c1681c980e201c0000e402d0707042820700c0c01c0b5202c1405c0c84000700000070000042550180300704461547d8014182100c1f910740000342001800c10184144410001c1200d014414820000850f03001d03540506102c040c054000304c115500b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 236083723 1250 236082473 236082487
    0x1d070b03071815030506010206010e010311060c0f01050619270246020a06090c050301110405190609030f0305040512160b2d040b0703021014040c050f03010b0303 71
    0x6114140d440d401c0c25601c0c05c00ca00d031504001641d9414091064240001c20b5031300510019450303441840881001130800d40c00c241c5144849810a140e145d042c44da00ea64a10400640d4541a2007168403540151070000503181803850301900e4066a9210a142d06100500f201844100342c0c1143e006004103404115076004e000c01c241100034a18030381c07015000e820007250081c10045903221510000c02d40003071610001903a64400681070524042ea0390010400c0001401d80702070042c2c7c918043c40c0d112141e540e500300700c200240603100101149036862486800d10003039030008014400c0c2c1c0c1e04810194420030651604135990f00c00e5801148d0481c50b000c407483c100360300000f80080805d607502c03061002d454031030f50703284564019842044020061403040f00e544c85480e20300566001c54200340e55150070b444002c04620b42d4404141100164007204907110a030580780b00b06603040054948000301c42c103050b180d000300351000380240c900ca000c00380c112084c9590309602c40e54080c100941900d4803030072 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 236084973 1250 236083723 236083739
    0xd0b032b14250b090706050301060807090305060106270b09191d061003110306040c02070e070804031707141615051e10090b030a0b04080405041d070b030718 69
    0x42c909000c860050702c0e4804100c18100100c2c80b4001da41450390b51a0542e0701c1d02074102e4803100080c18003014040c00e544040041032040c400c0c10301915407038650401d440311280c403081c0d10f081400808880c0904031142403018500a03400c940304418121019803505014dc1c8105803030344655807042209034481c1c1243c0c502c42801030740c2075205a0003252107080c14000c0e03a805030142c52103151640480c42041000070f0880c64185d2004481484510481d10f00320b03201c800340d080448058900501185661080104160340450100220351100040c00c3c03903814040c002920f42c0d0341d4402e000c0c403e1800441d192071050300d4542d5540b82c061b0044100071900c0108280745d0000e03e41030f02c0c0392180d48110700544982149804403503015206040569003c1072401411800800b00c4d55009a8580180d00414020840030f0105a02850140c200e003035a9034603240400c000c4402068017220b002c0040031182c102800e002c203d100807214000301180e500ea64100c02195040003d940414680081003001701c2d1000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 236086223 1250 236084973 236085037
    0x110a110d150e0c0f0303070b220b09160f1503050c0f0a1112130504090203010e0d03061e03020105120a02091002011a060702030601091802060d0b032b14 67
    0x400c20f0301e400130312608400925403244240b80000d0416084400407800009081c0c01d900b40e5840002c5e81e02c003940015a079886018081038505d40f4039503011041982e1a008012080401461322411780b01200c0e19000018101480480020b070601d0340c0c07a40001d0b980d200c22000c480501604600f020b5a61810000140c42c90403006117030600351141c00380680700a40c2650451b0f10f0b908103184034040d054504002c010143c13506050490f055501c80403244465802040314a400380155100890030b203041c409150000c5220410340803800807444810009030342c00034121382186811030076a580781d6480ea180074000c1c1c443d040d03442d03400041c0420200c20040d0b06600684010700120303012140740d0391403010405240180280130b545900030100401004000368040c03801068002398080481e12140c00082e1240c120300d07a55001790b40c4600c080036843c541480452a58840000448852030300f088408078500a400000c0c02405950700041c030a1041800588107494101103c82d048504a52410800e40c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 236087473 1250 236086223 236086243
    0x12060204030f120f0905210a08030c0711010822020109030503030106020f150103170a02070504110901080601030c08150d05010603050c190510030f02091302030106110a110d150e 78
    0x302d2140094513040d1040504104850340104440d11700e2048286c4a4042c80150b46052258401c40c801d0304009101e40001e14480d4016200030781d158000b0b0b04103010108815501103041000c20300c100440c481c3c0c4c3c290001ca2032080d0b1800d00c1d00008a5100584030f540d0305800242040c400440001101940011081003110b40c24003030b90340c032143d10000b180400ca070a000041800e919000203044925218000c2c2c001904184120340d0b20559a4010400b06c0d1540321003411040000141080b207541c2002c1c2203074014101303190403c0b150542030740041c100e54001c0c10183c4802e446251480f055598483c00035403558204000708101c81e40d918040c0da41d4040d41ca00300c7e008592005804480700c5e211800c0741c04503940541010042c140741c02046005042c07036612903010540c28410b1002c02c1c4c403010061011080065001a643e5042c004d004d070070f41c0400c40f5500e0080c1d0082e10190002440c00b24a100c14207410780e540380590b1403d1070444003002c00720f0700c030312006490044984100c502c0001d0003000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 236088723 1250 236087473 236087477
    0x308030901060e010b0a03050c0415120506090f0408030709091b0201151206050c070f1209050f060d020a02011103090105101a09090a0f061d0f0f0112060204030f12 72
    0x110b2036844081c681181003d110303025005009002c1c002003a070082d00241d0740b00d0b061190192030b00c1d032602a01511100c0003c07960001402e01c1000400e44030344e504c1126000f5104440c1d080c807e150082108c410b0302d200510003081410007001244030326020309444009003804020a03c410007042c0819900000008600e600643c00d00014060b1010184200c0c0183c2c0c8250085c071074500040d450340300182c400542400c42c0a0350400914020070a407041c07800d03000d441403a118045803440c40c801000b0061070741001d4850f211032a2000c026503241d000b141c1d59001c58503c05a112884900c040c1d00400011100c10000c050000c03c1245900f01988070a20500604403003c050a4844142c0c0b14011403c480c07242001d80d04009008003842c044204a42c00414481c020401c20400c2011809503240d582c0300702d454000c50301440049403640c841c1507a11261807002e80e1810300d091800790001407018403030702a40040e2080b542040c4246501103c02450700f00100400459043c60f100040580107104140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 236089973 1250 236088723 236088731
    0x3031c0504050c040b010c03030b031c0c030f02030f160213060b13060201020a080f090f0304141e090105190b040b0301030b090a030f450609080a030e0402130308030901 74
    0xf058a81881160003491040c2e440003040800c1d0382d42a001410390401556262261900c1c580c041e40d2a541c05d003d44820958032811100a58030300034040c0c41c10b01c00c09c01e00b590002d001c80c4c01c0581c00304007a20940810f0745403003000c006035030000c10495810300961141803400d00e040402c003440c41900030414010f204051104495941904030300302d006a4041e08000f07104900421080d151a442841d0030000d800c0a50300d81000b4820940e1a6134001e030300c106014501003484c3d00c5549422180c40b130100500c03d4414203039400400004000b88014010070b4400c040c502110840d50110806020190070b0003020260b885468040d0a11142c2091208503100f0b030368800000d01290002c2000080958951902120810580700035500d100d4914010034210300644041481980c6c83d404548640da03800c446040c884129010030b00c04079001c0c0d00940240501e03800100282080003070390500d0190586050b80451440d038000401034440e000c401e5640c01001c1d10080207004d10340c401107001d151101c000300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 236091223 1250 236089973 236089993
    0x20c160e0103120e03150703150803220f030503190c050a02040b0114030406050405070e04110907090b1903050109060b12090109020904050a02131b0e03031c050405 72
    0x4801012030050380c1a0118090040000901c0c01c82c2c0c858044420307003440c0c04201821408240f034210041010030581d8015000c0c0810b998061007091116006d0004100c81c90b824829010358a10078000001c404034028810080440040708001703000c0c0485418040c180b0383d40b82441c96407038201d061081d1900c003030b5000740d04a0074003840000341c4403981f0a0107024508405d400700802840b0b0011818180401600d840031040168002548500c0c0308080c009642e06150030014074044003908040d14030302000050001041c64400c0a4411001c01c8071808020350350480200c4001cac03561f074010340d803a03c00428080011001c24a0f401c0450705182d030200516a81d0300d007441c082e44c042d446600c0d0b9184041014814192281030302981c070049800000c0742c82089640450400072003120140c0c1c03950080700e030900461401c040c520300e001e03000310030900a00c400c40c00032215582030200311030f0034402c20461f841c1580e10180f040d00d006044014085d1403100c07030003103008003400c8111002c0301d00e1f0142400782 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 236092473 1250 236091223 236091253
    0x30609060f1003020d020f19080a0c08190f02060702040903020f0c04020412020105070c0323010f1406010806150307020c0f06070c180204260d0e03210408010609020c 73
    0x20000703d070b40081a5820066454007840000c203000420a070300644039420030b0400c8004038441000810f0200018012207219081a034251416a0006801d40e041175031044914044000706100c41508070001380c0c02c040c894400a01d039031003000c030b000b90000e041000030810725801003110301c0328402d2507013650540d2502c141000f0032442640900c00300201c40d003140d040554031a5010b071a41c28030503066900c03200d849881e01c252094141e800e18401012180c44818420030a000b00c1c00d50384401c100a200b007144007148004503000042285042107401000641d455941d1841c001c145031602238802d81e40d0501101c0207480d440e04440b0b03d4002e44021000380314a0910000311401e803604601d120440c0d40c10241107400c45c1100c8902c0c0400e00f502804045406018200c3c0c2595041c89242d02c50301c507070101c0c05800d0400982d40820020321900e17800b034850342c1d100424080034141c0d040c03031442107001349180106e038280920b801c030360850740c42e0420224480d102d0f030b4020008441c0c075100b02c46240c804c000d08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 236093723 1250 236092473 236092501
    0x406110604020307061101150b0301060f0507020609010f020c100806010e090f0a09020604030b0c07021f08042a0e040b091b0607060e01020304110a06030b01020c120705030609060f 79
    0xf0340507880410100040ca204640381c60691a142002149248a00c0200400c456041d00201c00c0c40400100411541743c00600401c0800c0e15070404074102003094001070f1050054070741080c140540c4048bc0402d4034802d001c10540410300400c2403a400c5255000213208a1044808601003070800031821040e1503c00c1c101407141580d500d81c16082c0d40c0b02c40d25880900700e103a80c00c9801100900020000607481010688a2355098080d19201c00e03141c01004803411400b900107800c0c80401c5a118646a80b00000650140d000240d400c0c400c0041d0000031600190211142155940d2400110f90010005509030065008035000800d94540101c5203481d0070002042e03130304201d031003d418501b0342003c00190840c98019200040d000c3d40e1000c183d42640c3c01181d0445105010340042c0401c0c0c9452040c08000e04810300d800c0111000000020b1741d1044030349001c500c00c0460618801c00b10b40208030500140c14080d0a44045040c400b800b0b030383d21641600c44c00d80c40395501000420165000308 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 236094973 1250 236093723 236093731
    0x15070507060e060f15060d0b010e060417120703050a0f110a0b0a1407082d0c030a0f270609020406060c0c060e0108010b0304111e090f133504061106 65
    0x110492800d040c07c4c0c00ca07401400e00d1180c0c1414051000c581d5145683d070400035100601c00c24802d15001c0b00141000b1381003c07070851921130b0420041c00b0941c04280c2c0b041c155400d902c0759003015044010b400c1415202d58a441082800034855a10309001b0441d26101540c000c00240034144854060069240425002140c583d07000503034443c0014031503050f019651012242c2020455210b4840d09041c0a64100449808400090000a000c0b00449500c911800c41c5a078100402c10f0b088140c000b040030012180d200b80101407100c2c103103c180103441d48200d5040e0750080003000748039503615010700861410107060710a2030320000b001640c280030344020880400140e5640c2c5061303007000c207005404c0c0c101401c265003000c40385400202c107840e1922074000144200c490209541c03445020031817070303900061111400950f110107101908013000f10314030000d58804004640303141d5500c440a050840b1600c1188a003444c0d100502000c502800100305841c00d0f0741d00d001c10f040c032800045070394100c151 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 236096223 1250 236094973 236094979
    0x70f1d0405032a06240a150518030a05150a02040501050d0203041b0303090f06020f10090312090804050907030b130e0c0a0f062015070507060e060f15 66
    0x20288244050700b00d901180648602c040304440d9800e100f0305490308804a5081541c0c00d140c1c495051800000c166880b12000101c413225900d80c00c04e2800845400481c00c40030034040081505030306844c140445420008026003120400010350814907070b907a07840e103000075564881401092a00401d4002ca030280c0c1c2040c1c5070f40e4980200c00c00080029407000700141e0304e0005007100c0e9030070001c0c00a5443c2c019030207a42c030812008e081611021002c5a540c1c061030540d444494000c407010000f080c601180340460320300240c45281400d0030345485089884210704149070410395001c00080801420981d1015192440b650362445015402c446a540807143c0c000e1101044003400c840c1c1303070001524038440c4000d9070342540000000c5411090300d40c01c48020102815014040543e101052260307108595140101403c80ba0085075203451003008a07441c05d054100000b61280d0052045441081c0d1043c0e042000300c01c02c8030722684810301a40d01200f804180c00101d4984c1868410300c01510a000b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 236097473 1250 236096223 236096227
    0xb011403190209280504120207050319030c0506070f091203020c220c05090306071404120317070c020a09060506120a1d060a0e03030f0f090f070f1d040503 68
    0xd0b8080004410008190f40a01a50004000d0311301c2d1300001124410109120f010400b802d10b41b820403e01c1e0039225010b021580500803c100580e40000c02007002480d00b484081803900c28141210886030350440a082840744800380807800358048000101401035540c2d0481e43d03038941c1c1c0201c6031041807880c0640182e02400e1940064549180761111940c2081910305c4004040d403002010350704890401d801141c8041101c0100b400c05100c5244d100d81c0620f0000300005d1042c0081d1400e02950161143d00480c520350b0350b041600070002581c00140074140c4c0c000c185802c0e1030051003016801d0040340a6408a040002d00880e14002c040c00d0b211700903e020f0801d15039015050200b0f07001440e00c4d80f4152039104410584400d070b0140c03042000d000029011500d030025058094500141c0111001e034000c000700309443c9480140d8980010313400344154400d8440f00482c6103007101034001020705004140300003410811482c025000c44a001e00010000418014003500d40700003120068003540007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 236098723 1250 236097473 236097523
    0xf050108070e0a1419140108010204031b06020a0821010308071b0e010b0a050d09061407170f070e091f060201060503150408070b0114040b040213061b0f0b011403 71
    0xa161280d985e0b010368544009015181e45414102000082e80000e41c0ca9600040902c00e000401c0040b00d110070741c1045030504640b404900039038035a00084081c22050003c10400400d012405858000001c95202d00100396164108120b099205203400c550082034454203506a65428220008891180c030381c0703080742da103084241082ca911840d000e40c10480100172015504d01d0900c5141001070055400080398020560141184c034070140c401c0c4144000c0f40c00c002c1204405ca80ca20380e01070444001c04901d80c490000582d10400d4694034603034089040400c01030341044070000c80c1c0311007500461840c1c00303947e10f4100780d0890b40d4034083c458150b04110105040c2c800b0400900e60054414141c052811b05103448403000c0c40000c1e0032090010310301203145011450940035111040200711411403070b0440c0311145003905100d501c990400d004181c850548654843c840403640981c105417038080c000d0003450300c8182c915090007100b4003c01690a6052541000100c0500c140f45c01d101c6011803800c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 236099973 1250 236098723 236098741
    0x10f0e0d03050901090b130302043e040918030207050a030f02040203070e06071109010506030112060b0a0b0a080105040c02060708010b090307090c0201050a0f050c18040f050108070e0a14 82
    0xc44202404d050085240f4006403c3c2040d0009241220085648500484c114410801a00c5c006803006661005415101000d02100105d0340f102821000d038030703402c0c654222a0101d50b8013469121800191030000f2805011406c81420034840e0b100e9400d80f0030300d41c1c5074810001a2032080c00060300461003041030300d0050400354015600940f0381d00381310040e1080a00000c00d2070b0700011040340e078411a403502c101d42c6c0c05d104001c01c1c09040c0440d00b0904560429071001e0072100c2000002d001c8a4554558035401d440d582d0464001d8128518502c2c0d072020380b0080640040c0003885054000c510701800c03111414404615540944a40d940b0071405074a821441c042da40c00c6520324990500600780c1c002003900c000e2103046c0700d003041c40c0c0000c103c0345054140c1d00222244469888546410002081f520820b03000c00c0710540f1a03e0400400c12002c40408580202405400e1016007440c050000c5101140018000300f180c42c1041b0107505940c0e8020110181e880b0580d810800e480e1760004200c002c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 236101223 1250 236099973 236099977
    0x50603010f12081909030501060e13020d0f0204050a1d060403020309060a0201060503070f1401030903230d0e010516031503030f020f060115020f120a0311160c05010f0e0d0305 77
    0x9014940d0b0500b002400900240040303040c4080e0004605c00840800c1002420700443c001410485003862003441e003c0d480071850010f031680280715600f0f042003c0c08004d00c0754620004203401034810042d514050440388018900c20205914142d2a44207411008600165141c031582d031681c041c504151400e028443d46400000090341555207c800c04281501c0807c217000090040703011880c0d00c1c0e0301c0e1081840034002c83c2d903800e5040608001030280842c0c2c002003c020303030061401c0c02586e4950303100400b1885000301c64844d1981810050301085d82481500311702d0050101000c000c507003a1101d40300394220f49442840c1d0058080c0d224040000c00d004002442504015005442c8050300350700340203041c187d09801100b105111248030246681d070400c080c11112002d2402480c038401c075061590352900405006208042d201e05058080c0c680f80307010307074031200100000c16440368501e00d400f40d400303011401034900003009203106c8a40706206090b080701c000e80160001c0d000781a107440446841e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 236102473 1250 236101223 236101259
    0x212571305091905040503090111010c090b0d0225020901120309090504030903020d0501060e071404090e010603020604062106030b070c02041805061803122a160606050603010f 77
    0xa0407103248400f03261080f900a15204510500145d6950510a0001340034540d010310b01040ba030b8505000e807481c442d04940041c00346c80c07c1103202500e90b903008a003280030340f1951103201d1030003d100468144098034850310a446510848a1089a0b030300e030121b58843c4240c4820141c00505900407c10000302164001c941190003840c01d00c084030f442e900030422070342c203400c41150541e6486504003c8040c407615100c7c2c0104540c5081013112401140400c07480c09940100b0000c03995903880321031007010951000004541c040c0c4480e85035680c03402e000d4580d4080d1001c0040821502c13050788018207840c49503400760b9034420200c247c0c0b61a601402c0350341112030785040303800a685003c11070b610108070b030b19201c985100704010300b1149059166404001351204807541240e2082c0000e9908242d103542040d40041425078032046003410b4584030340e0b40c1d25001000403400d80000750400b00d031229460340030810780c082e803420301c507840d034810910070b141c80248103104060348040428880c150010b0065144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 236103723 1250 236102473 236102491
    0x1a0d03050a03090b040b060a05010e060d020c010603050a030f0f020610030602130504020f071e020a15020a0209040606170a0b0105040218061201030b0a021257130509 73
    0x10b0803400d84d14130310140c509580a82d0714480c2441008010701e0f00b5442000944000e2030009055980d5101156882c010804054112070700490351101d500400d501080045030014110780c095041801d01403da46400024040020120b00910707148030f000083c124042c012113201c4000c10351854465100940050509442c1001c010b0400140c9941d81c0c0040c20040c02c004400c1c69840c5401c0c07602d1500d00740b890b01d0141c605104601004003680d00e0284c0e080848100041e00401102d0381c41080341030420440c0c00a501001c00c2080c002840a56403080040c0e5031300443e202d00075a00100300c2c5540740c5482000030006a90980144610701f42500506001c0e402d19001010b00d454000002d101a0402c0c20020220181c5074010828440c281d4050340d004003400404503d049510024001c403880c00510000450f840a0516410744207141d5646210800c20107144021820240400c1e4000c005e0b034101420f18903800ca589805a4010310442ea001c5a4426079840b10510f09400d01504140003048031358 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 236104973 1250 236103723 236103731
    0x60605210124180b13050a0311090408040305060702150f0402030a06020a0c0204021c050c0309030409021b010c080f07090e060f010c02030d02060103021302031e060301061e0302041a0d03050a03 85
    0x80e00c1c03040c0464034000d81200d07814030b1748070340080202d08030103541e43e400a4411840088100b0124683c09140803041c4400e0b500c8202e10342d80e44c14514a01d1255038002000b5100f03050030444582e6011941c04020380c07041840c0d480350b032520015060401825140a589074111a07040800116640d004001202e614107000c3c40d42203c40e00041c00300e0b00010302003003000292102040d401061807080c50f5119103880c802d0b45c118100806080da4031b01481c0030b07684019500151644250104120105000d820180203025103440000d005080e5802540d80340d80a1010002044c0c540c0c2c090b03a0303a2401e0341c1c01c19015641c42d0351100100a507140c0c03110501d40c14080ca00c0141000351b2002c0c01510503694503500205070651640c41804140d10742c0e00400c5120030301c1031090009010b281000264468030700118400c0e0742d110280060f004000c654404129050100308a20407504540c0d1950126402182c0800c0240c3d01903800201e018a00464690710082c100d02c00c40002e07004002600c026442031074001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 236106223 1250 236104973 236104997
    0x1605040e062b05060f0c070305072402040b270f1c060c090608090703021c031e23090d022718010c0c110d02040e01060605210124 57
    0x8090520701e02c064a0f01e8209504110b04810440804e82d08415143e0030940b0f0145e207a200103126018918000f442403a6980311510319070a01100c4042c07201c850f640c11580c86070b4408040410f58032084079510950000c80300c420381924003001a034800c61010f403401c0b02450a030700c00c00400d10049840e14405ca40900d601d200446c40d04e101d40d0341c142142e510303062074041c10f01342c0103010000e006203081455440040288016101d8150030100c48060900320b03104504245001e0302c0c000488000c0c000d03160300350601d500040f036003d04224030b80d401c90400c841070641c0f8451960402e06c211140d80b9009040704034244010b04101540050390152082c220314840ca80712214203c04006450041c0900d024804680ea5030000380300742c060b2903041e41400c021010440e0b45d12032220300d030b01000c1445441682c1c0c3c26415904d0b203420580440392168000c1013129140c010152081d0480c01c20304030300d0f200364109c8210318814140c4040c180c5403c00705403095405002001c408251081035400b0400024031007103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 236107473 1250 236106223 236106289
    0x5250819050c0a060b0312090d080f071b05040c08090303071103361f030c02070506030a15170604120c0b04230c09041401020408070902031605040e06 66
    0x140464416000811803a03015420585005c010f90004c8401171f40400c4601c0260b520701c00c81d102d000d0b5104c03030501c0e102c000e224031102042c0502030020b408944410020030445206a03e010140c4800702c40411100000140c01c544000080354071243c2c9601c00c01c00b040180380210028610002e80070122172030060410b4003d05075101c1090940e0440405141c24020b01c203850302c420805c4d4005072500c0211268640e02c106162440a8540e01410360b24481200f0f018428810303940a404041d00c4140d0741c0c240209020000c1c8214424130302d01080c2440301044155440c411840201c400314000c03c1c1d2074a42e40c90b05424260203003195410304c98a0880c20001030702c01e010540c031640c02411b2441c900e0100d0f800011501c44c0018400c1c0c0290490300724088e1079594640a80e82040c0c000c0031102d82510760554540c020310036500a020144a601000105038079030390010b51090400d80355500c41d4009180e4161402e010340d0103882108640d010002e0303480e041c4a00000642480c05015142074000d0700300c0303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 236108723 1250 236107473 236107483
    0x3070314030d05010b09030c0f01110106080f010b030d021f0207020406080a06050708011508060315010b0d06080304150c211d1002150415050705250819050c 69
    0x1110003203400104504410070030522400d070061064600320b42c81c00c014480000d407150040503140748a501060030100060b481039140650b0704211100030041e03103842d40c101603501c81c8181c040c1c000640c2000d40d4040d0904000c190007007003646580040641c80c001e114280c00d203802a8007042840b980c00d001a50160b0f440b4090300c40100303950700161140c9900d504019040d240700800500a00c5681001003140e5528040341540704034191400700100c0d195803000a0822031071008801c1592009030001c01c1c071300b5141d40100036910503807070300308201a6140c800a490b802248203041a9080404000e411a1f010b54042d128031449626a0610400c2c0d10701e80d440c10001100400b800240003040341c0c0b20b04020300f0702d6100070100480d000030075020b444100035940d02600030504001c48280c408030341040b00100301400314030b1031800c05100074500310310018003a80000500d15142d50140c0c101c3c1e0004201002020143d1340c00c511810f2070062080141401850004021800c01404200f1641c4802003400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 236109973 1250 236108723 236108753
    0x3010612020904140402130905031819060e1c050601051c06150620030a1107170a0b18071e090204090e1515190b0d05010618080703020d02030703 64
    0xc4003246404e00d4014411f1580d0f84440314a191480c0020343d00c0031827170000603200f0001c0610b244171280300d42000031504881400d4101c010220301d066010940a801800403001458140c0d81040114101280c07082e400743d4180c005840c94111000502035400c01101c1075450f206411621000c21815586490072100140c00c0440c035203140b204180413540e07010066001155051b00d01101d160a45000907484e44124234000303040c0116848900c3c98400248001401018150f00144032425a800d00755101c5580c2c20088034148600000070390000442854500b200a28000516800782031520108240c9500500100100c011a0f4002112200780c0020300250a03452408511074804290507403174095440740c10000c2010607802c00020844080c501181c0300c10481d104507d002007145040e81003000c03a0000f650882c000120880d60440c0c603008079048071a982c0d618005200300155000c02c404550090101540180d07904001602e040f5150620780d40c0000d00b9940010350f03070303941d082504000c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 236111223 1250 236109973 236110001
    0x40c120809061809070203070c0b03060d020a06030e0c0402121801020c0706030609061703070f020a0504050c030708010f050109090f11031006031a0a0509151315080705010503010612020904 83
    0x40c800380e1130030407684240c0c00c481c9600003541400c4061f901e4024070f81490040ca400400c000c400101e080d41c2c0c2d0141c01c2580398003c0c00702d0b0100381c2c070366900401910b1408042c80591052504002603410544200c0e428100c50b07002103a40d81d1076a50003a40402032410170002039640a000640c80c40300180b2601e80145801d4500040e10707450100003400b600e86582c010310703c42d1404010181c9202020044448040d841241d030f120704002880040c501041c0358005d079820a141000b0014400d00c00070056004228a84850007241c1e40d0300b90514139603403030f80100c1d400a020100b041000700d040b50000c0e5a0828100804644e8410f00c805c4400d0a0b00b0450ba5510b2082d021746003000855018480c80080000001030b0a0420b8901c2000c64100031103889814002c0503154009801c000401c2d0350814500d10042685080002414884000d00b104a900c03241040e803001c400109050001446001c8a01c180c690504607882c0c81e0003520520740051b00008001d40030004040c0c16a103600c1620807000a20b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 236112473 1250 236111223 236111257
    0xf100e1306051504060503010b03090a0b040f061d03040b090103020d05042102060c1c0e150a0b04201303050f0a03140703020a02060a030b180a050f040c12080906 71
    0x104041041880310503c100c000e143c2d08001c2405010350101c01c50b415211034098880e80c0e621001c0c2c005250103a01200900344040c100280720801c801501907403202801490306020a040d08040b00c0061031900b0300d0003c2c02d92003080100210094000640000c0005040c01070405400130340c1074007900d2080b00c080f50140040080300c070404800d200d076107041640501c005d1001d443e0150440781140b180356800c01d002150301e240d1312100101a006045c540c43d0700380c1a55101c04001030a4410518152425210b0341d04102e651512424903106649010ac10400701c2142074500c800d5501090344603000c0c405144003201000b0002c218100131141004204000030900c05995050081034100c14404000b94614100104004a50b0004481c409150111011a56492624816401032440340d5106800055a50b00d614000e9013021101c1e1180c4e00c4200300703104668654000c16000c0d0b804590080c116107056109002c00c442440044114621400700c9a00c3d0258110004540390401c0350110034160f19 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 236113723 1250 236112473 236112479
    0x60f0c010e15130320030c0c0f0415030204021b07080a05060a091a0a0f0e0106080115180b060708030a090201110f0a0308090a020a030308010f0b090f100e1306 70
    0x3040000c2d180400c81c0103030903101030416145590140b08003041c05810480c1d050418104098903070401c0c00b01101e6070044a588500c1c1504140c0c8030090f00c1d4090344200b80c010107080c403e01b454012001c200e901c54108039a864110360806c030094001c41411800320041100e41ca40308042044a80c02804010000b400c0c40061840e00318a804c40c01000c10740400d040c100310b0310000f07078a82c85d039000c00e406030358414117a039a07502660030003400640500c0043c1c030b003804103800c0168019400b24060b119001c0082c0181e614091400100211500c1152408800303000341e401c018940f0340c0030303a01c651401881c40b49000c20075114001650415118000303203503600c0c8002011076801175049206048044003810702ea1519410f40e546440d0300007005024400d00c9000190076000901100188940c018005000c40340c0f2801d0040020400f4050b180407030440b601d001c1403600503c4192000c00300010001d03e5280e08007000d001c0c0300c0d08440403180900408031240082980c403040c00030009803a04000094a81c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 236114973 1250 236113723 236113751
    0x2100213090c2a030905040b04140712050114100c0303060b0301030c0905070e060d0e0a0c0e0103031b12050a0219060b01030c0c0c050f031207030f080115020d030506060f0c01 77
    0x440c00d2140c04940303c1d0203851100090704592071000b110400c0710001080c031780f4040483c0280c41c81407200580b4080e858100164140c10200d60300d0f6400c54680708201581c2c031052680301c4106401e0440d507105540803600520140301e00001800d642c840c0c40c01081c0d4a90301c5000000036002a042160b020f00e03020401d02513100b1901c29035502c1140c600e0319504019500010440501c541d20085c04001d07103902107014050020008804000e0f80007100c2401107598202960883c0003c0c08218009a40c9038200071321100c0b0000361503250340c0c01c00c54080c051101484180c80b070b035101103103d00c2035009d0b04059904202142c07602550041c021080825a0103180000404584241c6d11130f1007440101c60180c004211080d14030310540308151403000e410f159810000e85030401c40360010148110005034a000c065004400082400c0c01e41c949007010f9898080006443c81406690801613000b82e0803244450f109030001c0ba0007500c068007040c91300d20004094031099015030b1100340c0700d80d103c19200302010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 236116223 1250 236114973 236115017
    0x5060a0203011508040201090303080a1d01230106080105010f0e1e03010c0309080d0c05221a0702031507030f02270a0e0c070204020f0d05101502100213090c 69
    0x3d00e0a10b841c03525450700d980041c2c102820380c000501003100800006454132055072062501c900c0d0b00180200c804081d950380c5000c0c0c40c0303c50f11025100c00141c08240c448000a6005040c0c03081f076154011719a00b00401101c2100d4486c0b458020000542e494190984500e99912402d40050502ca183c40c0ca11800b40340c25035400004032010586401c000d040440c13010700a682655850000226222445142c2102c1500900d0203402c120080b90300380e10801c4090605240c00c0350300035030481c80b1000c04445008079034050300c44083e405400c03000f00803540f103c5030890158018842c0c200064024034005c0b9000032a04002c109131045a1000340c6001d5240c040e1408004000e001c450840b14141800c602440f044805009228820070110f84030381155582d8040e80c00c1d11344c03004980303901c51a031040104090041640d403103003442c00014011900c002c103a4212321507021030390010480c161091100b80002d501c61010b41c4808941d040c1c0100da2817035680107120140300d076a03451603015852420300b00104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 236117473 1250 236116223 236116259
    0x420030a06061d0103020c01020705030a091701050115030c1e050a080105090403021e070e0a1b080709050d1106030403020606210a0605060d05012a09120f0206040305060a020301 78
    0x4803180492000410050f07020300303c4551420303c0d0140c0c442e1201c04003240640100d0800801901001c01c0a031000d6038001da455045461050104041c008103500301800c80380c0038060b0801700e51011250480d03485c000c1c0c001d44c070640c4451422400311005c580040b00706415900444001a20008034091829403220300706024040881d40040700e410f15507006541c0340c08050200302c0c080405c015490032a2401e001398002880115142441c0b8178101042000500001b0744c00c1c440454000075443c2007a200b414040d1044103244c441c1c5000c2c908000c100300070311075811002c0b9110207100e641c0100649410010358040c61094000344441e085c0202042030903410310000001c1c0180040001c001c0840c00100a00040d422520000b03680d00c5003c0401d0211130b060101a000390300b040d140f00103aa0a01c00d05510040811814958580000b041280e05168510820722014807503000ea41c04606081d81805020784002c240c945020b07540d81c0c0c0c1c5801c0c80e504079002c09000d50301000420004910b66115852 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 236118723 1250 236117473 236117477
    0xf0307141318020103110c0303070201061a1201030b0901110712020105090a0c060806060d0c0c06200f0a1808010b01020d0c0b0f0907051302180f100305060420030a0606 74
    0x441000e094007440310300b101c2d0740282c101a164405a1402d01481085590306a90181503d07500d103001c48001e4043c114500c1507035454a071003108602e10701044015952540000300650a940e46151141482040f01030001112550303500f00341c0170a1040040103280152055000c2c29000c0c4203030b140682100c600800c82402a00188514000503411004410076554103091040b21503c0340c0c0c01040a5000d03403c2101c004518240c960180319030400789080701144941000c0c410010b40200400c4052442c094400c1d1643c020301c184c2660642800251018003a645442200f400b4100d415815410041c0e1020905942d513400da0203135035a05204081e1142c2031420481d00850301c0d560b40742c1d0560002840c00764030b000580702203000e054082c8845001080000c001030b40c190311085445000394080504126001e1214480a10714105120200d098a8004140c000380b003116050035009050010409640960b44800c40c40c05400d940172801ca000318041602516494007406000441c0c0054000c0e0302 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 236119973 1250 236118723 236118731
    0x3040f050f010e06030a0207030905130510060311070312022109010e01090b1602070b0a120615140703090302040507050301031b030b010b0f1e0c12190c020f03071413 73
    0x20141c131000c0c100e80d0001c0800e040165108002d09084031400c5250300320683c00305020030709006650305600300c54085c001c6e111074030041a540c1c09069089a400100200440c81e06120010110340125003022480003982c9015203441c0a41001c02c520b82032130017004004103a90010311840d041d0900c550b1031150522700081160201da40c4401c401d15000802c1c101c0b0100700c90020300e180314401e01151009180c00301d1050340307404908001500e80d4408180440b00540b5250300006c40d591a034007d100329407030303d031996011b042d1900d11002d050750002c0310640500c80d10030000001601c642c072606105410950300c40da2694150b10b026046109500c1042c2c1d082c5100440c14801b00304000e8500341100c80310392a42c2e50ba54000000302c28036014031100520100c4050804407031070582034000f0005140d5100654100c03940d030b00300c4203205005206d01d02c0c180002410180070001d001d8041d800110340010107100c0c580e01407100080c5000071036000b442009035541031141030707803c10880d150f03444690510148 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 236121223 1250 236119973 236119997
    0xa030318060507172b06140102060103020d080901050717030106030b09151309020406030c170a050304091802040c0c060e0d0507060f021209060115050c06180f03040f050f01 76
    0x7201c100d03e0314900791000c000c005a894081c03080312400803100c10b5075141e0359258851402184000344880d1043c00e209503038607c1419000c2d8404585507041c0ca0f4000c0601000c130490341c544040541240e01582c5c148003080002c03d0110f042d0016022600e429403051a64a40c100302005080c6c699044a080c01164008180010340b454001c941500c131400b980e17a10b008816269180340581035042029400a140082c003205001c0c00105410a5580340c080d484000e050141819507100091100500355800900050000f500e00c2d42102c0103038502c8031040358410060fa00020125a0042200408a01c0758190311041200c02d010740e181d524003040181c41c0000d1105000781840c420101f00400780c5907194051031801160364160f80c0904000c142240c22450b028000720f80d100c00c28000c6205085000e00594403a910a80031544400d0b502009010140c541021a544940181030f840f01c207805078412030300b5241020000340c8000c101d4218100d048a2a2406009280035500308190400a400003c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 236122473 1250 236121223 236121233
    0x100b09030d03050a060b070506010302150f0d11120a05070305101202130207065009010e06070203070204232a070303050411040b03060705180a030318060507 69
    0x18042140d04011500d030380c461413024000c1c4640d420500c140340d0701180540c188040025228180e900c00d5901e4440307600c074500c03c840381e03004416103414038003070030006400c40d0701e41d42e082081c044040248240c1440124003031121028400c50345020f0541d130740c40422051a40c5030103419000b01440400002ca0780c10311482c1240c0c4032189a020740940d801c0300107852924100ea04031010302d608810b04005008948004004000165220b03140d001d030a00c03038040e03500074441d17000d01c46003004c69416490b400c02c11501e0980e03510300804110b2a55654a55201848801d200540c440c4e00309a000d90364800c40c03881000102c46844411b0800404c4a00caa42400c0c40c0400101d0f03003011900b0b542014103800c1829414243c151031340ba4640f51180400c000302056050f401450081d81725100c0c40340c481600b6024041100d0440000703a0741607200001041442d4019001402d00300158111107000034a43d50101e6103000081d0b00880006010f440500303488035500301c00e20080c00c070b24075200e4945030321500c070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 236123723 1250 236122473 236122483
    0x203030406030c0c0818090106090b040302040b061902061f031505040f060c0302040e160c031803050f06040204060b120c09060409090b0109061403120a09031406100b0903 75
    0x309000d050f40ea01020003010700aa0901480c0760b40b1441090385d503401c41c032600a001c0b10351007001c0c0c06541500e00104095024886140a5071610a0481d05103032458007004060007038003484c1c5411400070005089000c190340300000c0100410b8000341300c6400c0c140104901075564211482d82e90360820018000a02c9480b494000b030b024400010601791128200214207541001000745200e241030088100207801da00900104c4580b4400c0030b002d170382e406541000100b1400341d0000043c680c2004c00c00001e0050031b04060041c4d1803d501072295441e59919071500b203c000c8034050542c0003204000c21850107004240280c00c404540e103013800c15042c6610701148004d00302c848003041c0451014003586075507003a00c0041001003c2480309140c43d00708001440c0083c00380a844500f40840818404850a415402c0050181c0202600500600c00c004590010030307a0300b00b04213031048008041503241130b5002480a07408064096420000501c0e201d1312103960101400c034a0510880e07403150b902240b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 236124973 1250 236123723 236123729
    0x2010e0a11011b0b070206060a0303020d080a020f0a0905090c0a0f050d23071d010507020103020d110a050a030506090f04140705220b19030f050118030507020301051302030304 77
    0xd1542807599249005843c00d0b00c0800703681120410003110070060044012095014a010b0740907a10305440e400103200c2d459419000140140c0d01420200d8002841030403065030000341c18500508010910741c01481641c00192040300164a14505000c01c0c43d04501c0c2d25040070000905601c0c00809040242c0005080f00d03100d4140600071a1003ca0100107401400f50122940070340300d810344220f0221410103000f03a03681030001c1d8076500400c084c03160300c00c4802c0b02500141c41d0a41456200c0d8011401307075122500c4e59105a40f10711a0038031000c40040a02428040d0b0780b01c4545414048030020200c41005000074840c44402040c0078594041100183e0415000020108003007000c80c08203141c1481544103075088a0a4100441c08100f070764600108040f1400c01440351703141c154204054924021804032507080345c508100006021070a48000c00d512440020074030745191b0400111b000707491131042d4042100021031004501c2c080c41415030220386000e406c4540842500172942d6400b07540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 236126223 1250 236124973 236124983
    0x10c09050a082d0118050c0114030c0a020f010608010504290627010f170105270a0b070512060d050a0201050a030905070306150503030c030a050904020912070303080702010e0a 77
    0x1071088184040c030306641c41403c10600a000740c1c2c903082980440058881030030b941c07500411140790003642c8035403007800060b04003401403802c644488607040c1c0070358420407100c07082d0300c034801b400340c1888070a0280400030504500000b903d89000c0c04c0203040d92004944d0031714040c80354080c1404812188180c40d82144003942c195800d41800401100d401f40301c10070742c01d2034030b05080002541c00c040d03614030b4003030320517114210240e01010407005080e03600a0303030091080b1054014003c030212120340c80440803005901150380120f469103a10f042d01100b41e0382d45002810000d404000c60844030720241c1c200005440e0522946070584076151180b50000009040201c0080c207014800d21942252400f140c00006803806a5620f281c104014452075140d00c0480c12548800a0a80380101c1500c04042018020311b10300400d40204551662107180ca4550080d4284618041500d0304a41115240382d484000d0404038154103026160317010041080003103a05200d00503801c1000403512400003907107c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 236127473 1250 236126223 236126263
    0x110d0509030f03190f1d011b0c0209060303040e01230d0503030a09020a0906080c040605040b01080705072301020a23070b0a0605030d080708010608060603040b060111030408010c09050a08 82
    0x1800104040c2284281c5094040e0501101c0004084680381340e41c180c941b000d00130080e1003407000701c410074450a685000003180c0c1c1100010050705125081c541d000c000141568039258642181f0702c0901d000f81c010703c01c0320807000d044115040410780910070109007140c00d801d040340725549503981c134480241010300c3c4944904401085480c2c91142001070403210106102c807a484201e040d60320610740e11071510980c10300c00001144e0400c3c2c8101000c20358117079200304603541e4624003900c890388586011282401038440e52070340c01005595a400f4228810700150780c0d0702082c04014440e20901c0e0b48081c0d40032810034440365290907001142c6110b03601c110f5080c101c1c0c3e1003e01d8140100099030144d6094000e22011381c00d500d51000d8072500c10149500e0f044213607603c0340c6040300c02d22412154a41c1021007000858081040d00102c294019014544510f103100d10403186030942d04964820380e080da4481270648101e507041191a0050030b02658142411442c1501c0140e507030b40c0c100420101000d007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 236128723 1250 236127473 236127511
    0x30206250e181515030402010e01050309030919090f3b06040b0103120203030103120c020f0a0e100b09150309190b040303050c070309140109030501110d0509030f03 72
    0x3a0a2844129400000c02c0d0000391901c03242004030341946400301c0d442101016224041c0d40d00120940c0e00454040e540d10f40801108001900d5981c001350401c1000d00c820300c2a0201984d800749407450000c1904e0820700418a010340d4070003610182500301b04900d04250700381c440c0c16402c208914031468004c521040801640d0400104000c05414150302402020308010500088140041c101d80c8145005410040310100482e1280000e000007040b424070000306541041c840c0c10f000c00c1040c0010040c140300a100000500e280c02540d1008521008100420904101148116009021b6000868506040000000c000740307241c08006000b00f002001244c9070110800c07818912900301036035150b840e500e6040141000d5404c441c101c1c002030070700300000c18280700a000e440425502d5290b103182242000c0b40760107002c408000060401401540c0000800c80074000d6020301742122300c503166034862103800d8038141d9000801d41c1e021580300f0001c0000c000c640c0b2084030303400708031a210001d031800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 236129973 1250 236128723 236128729
    0x70f0c1506080601090203070f050304030e010818061512151b0f03090c0411040b030a0f0b061c060602070e07030c020123060306060406140405150616030206250e 71
    0x1240e4011044511543c800414030301c00c280d000354010036a98aa40410404417070302120144000c0f10000d001840350a81c3c3c00b201e5005030005500a04120804120905200700781490030700102c5003110003070384042c3e452045040000328900404ac411015001c46079071194580e8000b00042c061511500040001350342d40c6c1c1d03a0702c090328070411940080d82e0b96810100c0c03201e41d032101c0c0f001200c3d101d50300c0d01c402c505564618404440c210f4100405260440d6a178016601c010300d00364401180da035440e404d01c21442c1e9a01c030010400e8920703502900c2000001c5003a50001c45006820450a5621140092280380d003e03640d0035a0103d141e10740800d09520f40c8600720f02412022400850a01c4841100180d49004950a601c11001502143c200d55102c2c010081030380c0c4c01e445040c4141141c8900680682015046150b02000098900c501a00f0b048085a81981b22010315400c409002d010601010342c1809502d8110b00002c0b41d1820840f40850701c000c00000349941030050014403c2c00c000d140e1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 236131223 1250 236129973 236129981
    0x11508150306070c0b0703020313030c1505010b04080c0609010c12140409020403030e0d0c060c0c0e0108010501030b0f0c0a03050601021e0f0706051207050703090305010603110405070f0c15 83
    0x141020741a91020300700320001610b26014004100e4030105150005190355100b882a00c1c410766201c040102e14421f81d46040d00e0580916000392008140e07001c103040790081c2070013000d0090903503a03412a5201d01c1d01420a041ca8821801c185c440c110400c058501c581e030002086100300d800104510990603c070743c0a84043e00382032640351001d1004100080e070b910040e07018000f164029160384540c090b200081101c0450b0f610306c018009195428103003d1213105a41c7d4506480c420f1f0303c0030740160b40318540069044002d90202250369118401071040100b05898190000500f0151041c83d09040b80c1d0f02c01d0500810380400c04043c2e03980c001070402d078800c204024601c0c564102038640000c0c1501c0301c1d40c4482c8a50300c032070071901c502803000464a108800320f4056440d142c07003450141d21112011503640d4800781d800c0e001c00800d40ea0100c08240d082c41008011441245640c01c803050510074441a0f4a00a201406004008185040391a0003035805240d50307502480c40c02190b184d800c0703054024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 236132473 1250 236131223 236131261
    0x30d050c0f0a0f12020120030903090a080f0c030a0308011208070f0b010f05060903121b1006150c0f02040e12070506040215070c0b090a052701050603011508 69
    0x107841148519800c0c0495240d50254607400b0706010240304c6031519069081c1e4040d807021400c1d50301c154041031100c1d404035010703580000040007a130b442e101482000540b1800c158000c6452908412103506003d00e003001601058007080d0701400c03d40c01c180d00e020b8090f030014070881d2900c00c030041e080010020303810b00301e407089a80320190708850940c0741021031084d2024003902c04c0140421202045c41d24250b01991000740c4010018200d0004d0402400032540214100802c10803150360003002e800741c10f10422150741c14280001a0a81c0f030725400c0612114401c00c1403041c01100d10000000c6034404038503201c0f0540654010400b0240f00500c2850054a00844404260042072a0b030812030013207441c5001c0d500890381d1150305042d8205000891050040c001c29815003e00300f0440c800d2a000909103100c0014096595140d07500701240c076007402c000c4500ca84030b01d210310400041c0107195586001d400d00f550001c1c11903060280320509a2400c1e444130040c84000c0d00010a0f00e0b0800c1081c81c8a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 236133723 1250 236132473 236132503
    0x20d0516060f02130f18090212070806070e09010605040b0309070b03100906050411190903050102040b22050907050708070804080607020d08070e090a1b080108010b040b030d050c 78
    0x450b0101110302000350420458841821200c0000140c0c0440c04070003401a183e000440b11401da12000c5d1030001840c40c05801ca80040c00c039109030a4000c001d001c1000207060000c00381840d0b14040d03200600315444406020f100d11014030042c4034042d404010381c2d05586034a12000c0d62034541184107441c05030f080d8004070640000000b048184007103507203c5001ca03001c4280c1881229210130070041a04e90640c07170715520000900045070700690301c1141160400550510401058490325602e007039a00036041009583d10015030503600d421691044403801300a0250030a03214101400039828407409030100302009408a420005e000c0020100c90f20103502c014001ea032541c0c3c1d41c484545900040f2115000b5015484860005138000d10075144105890790b920104818140100240994081c001031001a0345680300120325600c1c0c600c00ca000a0345490b414019854004a2030a440c0c10798400c0307010324102050740b045a2400616405650754900745680c40300c9007100380d0351812a80c5911030003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 236134973 1250 236133723 236133731
    0xf0c0703050304150f0b0a32011e0503071106060a031104020d0912031514040203191401030203060a0e030306090402030a0c09020d060e130f0501020c0d090f060f020d051606 76
    0x50107115030b010040b1b9000030740359401207613507944110540307038000364003040e079025020920101d4906040d24503401d40c00504106494003800800544060080d489550101f00d0020a1015154102030110200c00c40c920060038549004000b06004200c00d2000400c034000040090031f560b0b4481d01521205081074004101c000c0c1d090800d498880e1041c214140813078a011810b80e80d08510003650800d0380c3c2c07901c0000a80796424014000290f000602c03094103400c0e0321221280f102d0450041c0740c0000d03c0c0290426895045004042c28400b004c0c160817801072900a44078007640b00441920b61160341241d201c4240c1e03032103001107420b0101c4008014a141200000072844060300c0e8050003202d503056a0800026480d0040c040300410b066542c1c4810899002c0c003580044d501060700b40549110350b00240c202602d04200500d0021008113900120743c0181c410b2040c003140518010003042e0600c0c0455420045182c0607468140104e110000c100c0c0000d1241104009009904502541325000308 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 236136223 1250 236134973 236134991
    0x108210730080103110105030108030a18120f330509121c0b10080105041805010501060c1406042111030406050a110a031b020d060903050c060f0c070305030415 70
    0x2071400109000c01c03101780c2004900f2820319407245003624141c0c1d0105c0c00552404030000020f486140010b01140a07800882c140494030144000203405494890220000d05a0052a0100201441041a40c810202c0c1d840e07400f81700ea40310034140b20240004600050f03035114907200038100002454001102000011124001342d12051100c80700300c259081041001c030200c0422451602c00101d150000c0c0c81107006000031710b010742c84108018140c40140c295414a55542400d41d2805d0703101d40c0c00f10b84140120f500303000c08400d0395100c0c82850b1025050502e0303d1f66440780c2c2d01041c000440303da030004003e600b005502171010490103640440481ea00e80340d49500041007540403104c03460002c0d5400f40d46582c4244000b40901400e90326844e0308042c0402000f001d50030007880941643d00440c0a01e80501040c6648103040d5014082d03036a1503652948451001d10746200130304040d4003121101c003000080300300803081d1426140d25150183d541c0e12030b030420001007401c4109010606146c450342e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 236137473 1250 236136223 236136227
    0x20030a050f03030106090602030f040308030a0b0a060f09061103030f0402012105041101020105091e030d09051605032103040809120601151d0f03030c030409050108210730 75
    0x60344c12a60305954210880b0748840c02240c0303074001c0d101d40c5c0c2c1840c00144414400140c1000146501c4804481c0001d541c00c502030000e81b140c1001c0c1d1144012420031040500001c0e13100045001600c56410040a4500040b25180e502c1c80010440c01403641c4100204085a03c1440c1351140c0c001028804980c010903184003900400c03003a04e041f07460040f01d03d030303036152540107010f41032041d14003801805c0012584102c15604001c050b86000d4540401c000c0361117020704900c51001d105002e1b070024002c20a0001e60030a41854035080244207030700c40006c80802c81c40307000e00303032052000d40440d0302d07181d84a6181001f4903008035030004e54400b08900c10104141030001e103840c101c61504469010461f420f20342580e104555074221aa42043e2580220440c24115081c560301c440280480e0301d41000d40480350b0541c1c002d90491041d00352108010420901d013006550007040d104441900c00e92110f044040141c4290340d801486840e030440300c44207101451001101111a840041184e20007078080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 236138723 1250 236137473 236137477
    0x6030a05060102100c0503040b0709180b0a1a0331080a081005030d0507051005070f030c0509060922061d100f17010e0a0804051c20030a050f03 63
    0x10742e0062203a01c1c08207212001d0350041c443c00c82c005d611864170b1611603849866420b1001000d10041c4943d1500c0058800b01840108114411901d40054003943c54000c0203c103c0c031070352040c8002200c80c0801f0300182c0c0307508216030b000760501000542d821410112010f000c100300c550780b032251005051038024010004014010a4840d50700c1000c3c59842030f40b00900501c0d1402820b030142d05c8180c8090150740220001c14040d40104200d07810580c10003683e80a641c01190010005019001044a0749030035010750b042404007410280d084c0030000e00031601c10702410414070b00c07607914491142e0380000c0e50030318001c005000b00000e200060b243c2071300d1804000800c5110303643c10550300004810180422601003074030140c0031060320852400040c46e178240c1000d18140100c0d5a9464071039003140c0d0410151400d2845641c0a41d140c031f20304004c0219a00380110b55210b1613000081d0100062140c00d040c00c004100c0c240031108401d08000400d06d06544140010458071602d2903a800403140040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 236139973 1250 236138723 236138731
    0x1602150c010b041e0e12030a090c0f03170901031d0c0f03070b0f07380106030e072106060f0807050a080d0c020f0d0309080618071202040b06030a05 65
    0x2480b10046002c240310840d03070303403405003880124a403503400b203d41c00d103070407181d0807244007000c85801030251800b0f05603d40c400d5400c80c013520307524201c2004205140d5900c1004146010031120160701d56100c0003590308003821030602c06540000c0d00038991f806603001101282c1e911000703540c2d20402c010420740e10050070807881d20990714840b400c04580740004007002a0780f4a0180c00e400c208507641d03101601d402015080b03d006601c0304400c1105c240e081455a440b00c80703141c104205918a500f0f00b401850180c0043c0205400c064425040b0440017503502d04a80034800e40c0c2c41149503000b503006c0c1146417804010140340c141000002c103000d441500304280c40103a0705480d11b2503650b0f002c10801a149208110885d000100ca018070039009402d14414180050544055007038400001a40001d6044048000c505031a00510060300c0400203d0380c00404148000b18035186041130954401e0240310302081182c2a40d800002c649544d04403000c0d070613000d44200c2d00c2c1c2c2000001741c0c0180c50121 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 236141223 1250 236139973 236139997
    0x2706060503070909020a0b0a0309050f0723100c0204060b0d0e0c0a060813060204030204050a050a0f11090909010b09070f020c0307030201140703090e091e070e010605160215 76
    0x42c0c0818816060b1280d001c1d070b15401000c619800e86000a81703d49034000a02020034161f580c069007001c140140035075005207001d038010f130500c0b50030170720301541e0940c5094640f086c4c09060040b2180c0750b16520782e15070b82482c0908050721151028400280035024a8019121251001c5501001003405030403420021080070180c440c45141901031190b00100b502c1050005014240482d0407400c00f19245913240d4044c0c2c0015107869141d401007001d581c02503e005041c0d40d500d800f00100d001c100c0c8a0010b40c5184413805004009188003038180c58099006414452600340000ca000108250701c0703d010320030080c104680781d00d00080080c240c4401110b414000d8040c1d4460f012052501140e801d00303503a030584a010300204481412101034001c51412000d102180c80c0c0490020582d01c006407090308500002c1200d030035200012454001c00800c00b00b03165202c220144960548200360a056840368a805038454072030440d01141507900d040040e400c44040d1052500b1071088400034000c2d0302200b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 236142473 1250 236141223 236141233
    0x206092e08090d020601050904030c06090b0105120d0504090b010c050715020d020d0f141c02180d0b040b0603120c1c0e010e0405070314090106050a060c050706032706060503 76
    0xd00c2c0020344982d068010000140c03c1940140314610341100714036045402850410500b041d503903100011513082440503524440403400402c07851500782c828008200e2100c010b00121031011101600f9030207140514602d10f9110b0041d08030903407042c840b0400c000d801000700c50105070703076112003080d180d0415100300042c05462803503907002d400012462014010341d910a001880c0e40303c011030f500301013150250105178041002c00704201c9544800d01d14100403200c01641c80c003080811143c40c03140aa545805042401141030201b0340080100340e01c56003104000c00d880d40c904000a0910700482c17041103042c4400b05048000c4c4e4000220000340c0424400103612140c0154019540e18564540140c0010503400d900300450415400c9541c200c0e0306801c02040b006419509a1010702d412201d401143c0c1d9649810095803500d40b03201c0c0000c1c181800c6c6204040910380b54180c03165081e000380010b058840c26010b41080e8407407443d64020500c141020465125444c160000e400760f842240d00c03902c12 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 236143723 1250 236142473 236142481
    0x4050c12070512060f0a08011e0e0705090604050a0219020313060c051009080c120702030601090525020703020913020f03030a0c170c01020403080d05070302160206092e08 75
    0x207581128a075080c1001c01d140c666641c60b04001003840294517072600407075140c50010361401c003400b9050000185d4500c0545030003825174050200d071800d03000046240c2c04803c08100949074041d07269000fa5066802003a20341d191030121020f48200c00d9081d000e070400091403c860b9901102801d804000c400550300f80d03d560741e00c01c8451103181c14000c0d050360468800c20700350400c43e034810340e0f01e140f0503500c80c2e0804800c801c8043c2042c4044014400c01c11300012032100714641480b00d1070250480580411040c01c0c000ca03107000c2c0d081d0450854a54098885040007c18000c00000e0700465009113200b42601d041d08600b104000c044a0481c02105405030001562901000741e40807503105940394250001d054171025107031007075241028124a010050b50310b40794001e00040004e140a40d031380c1036460f00e8004006086a100030481c42c01c2510600c54844048002e4901400141c1c0454916840342e080c0d600107850400d10861200c07405900580043c0c01f0700030300b007100d80d0b4900c8d1510b955805a075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 236144973 1250 236143723 236143727
    0x20717070b0f0c1801020705040606170a0612150204030803040819020601080d1d03070e0f070903030509040915050f070f0e060417070306060605032d15040b04050c1207 74
    0x100a0700c0f2400e80500070b02c9012880d800c041c00c00c039224103052040712441503603940413a00f2071b8080d0b003201000411811b0740c40d5400d9865000e003a00aa1480401c000d520b10b032540003040703070140301c8004085401c0b81c902a2100c1c00550151800f850b00310103079035034904041c40c16260543c400c3c07440030303071410f402000310107100d001142d070034121a400c50103403500712103180080750001648060441c12001666401c1102c0c0c50800c19034014042800500001d810010b10040071410010612f008004000700c00303000180d0300c0802d40d910500c0c1a100401c82460302e180441c8036103c1da034001c041e442d240008101c14407003042001d03401050103842c0c41228641041c0111a103104814400c1d07040346081008108080b80c45409982011513501514040d40c3c0f03a9503048241c800560240c000500e0200a001c11100640144101c480b840c44000e0845100c20003442542c200003400280d06180100c000c1415454581011880750300c028010001881c19082860701c0780c010807000c603030b5031141d1400100b80364 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 236146223 1250 236144973 236145001
    0x40608010b101202040906180501120f03080403110109030309030e100e060702060c0d0c0606050108010320060d1503060b0105040b0f210106030b0111030414060c01020717070b 77
    0x30501402e02001c40280460036180c146140f240046401d81c20000040c000c02c00344a402c000c2e00064400e4040c04260703c0c900310a039071040c1c2102c0b02011410a6400000303403803460f4800303913070791509003140d050b0b03124181512031403940302c100003c0c1e50820020b4403c00d0b500d94800c400c2680b00c1c0c0c032003404848404c01404600701c2c101a044c1c2c04500102c00400d41d84c078100c006050318a00c001c2c04c0d1441d00c071090906a0404203c0529030022462071141300341004254025000030384400c6c43c3c0f04e559503265480d8485480305c41d140400e8401c5081e8064026a180c0c0c0b02160b070245d8080c28140600b0508802e0801810894030003607456500e000852009984914210f070100c0c3c2d002c01c01c80d03041a2440c1c0418031035620050a0707031600c9080c038040e08503444034032080c14020301841c0c40c00100381d07031100c0024201040301c06904010341c00030070042c03101608002604032007031400c0d1a4203803070325068070752180288204440501000003800c203c4550b146640d0050264601c140680c1910b901d41e142a04001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 236147473 1250 236146223 236146241
    0x20706090809130c23040504140a0608011b05071a07050a030f050108070618030f1505090c0303040611030909100609060201020f0403030305072d2c10050f0d0b04060801 74
    0x441001e090f017080d281011100d41c0b0f002d05107a9051419543c0d400041c2101c01c00f05180000b811a2820008011801d1040c400200582c0c0c0080c07003c01c00d405101c1c950281030100007000d010001c80c08506102d461032510202500f10301002e001401c0400c00a40160480f007800c400003030803d00690585541401424100ea10901c001d204a5080540c240d400c0410801c1840c1d88443c00d02001003c64a80800140790501a41c0004652490344c48a0803c0e10750041c094111a48100090013898a002044608440d1a4170f441000f50b1041c400c03031819403188d40b61803a4030005142c2800306601503014500d0407030f0401e0300d8040e48144c0d035100c1a0f00340d00480103c040c4c08103060100f0000303c3d00a800142d440402031070940d50700c1920308040d050080c018060f001301c090340303006108400f64000382c040882c4440c03030a100114038074020000410684d80f902a900030203800c080d52141c6402803050343d01500181070103a8541c1070213107028006140714941603201da811320100003501d103010b00c01c0c0240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 236148723 1250 236147473 236147477
    0x501180c0c0b0403050c15040c050901080a031706151803010b0d0804090b0f0414071404030b0103121704050f0c0423061212040f0b09030d030f020706090809130c 71
    0x20581d0f0b0b03600d00340ca940d040607207811900c1c054224400d13010000c5500c02486030b07100e01800500e06042c0b40038022009016044092103034880350000c07006c65007140da1420300500304a00078466655100c04107c03882d10b2200c07a0744000300082103400c0c10080704500444100e90a900800c0303035001d031004110100000031006098128104000c0c4402e800e20381086504040103001c200c1c140380420b01280403550980c9007100520b4484091002003a0b200007034002c402c8400c0b00032410706080d92100410350f45c0c1840700400e00c140131240541c2c490f0181c0c06104a80102d400c1044192034103003806511904040100e0085008502e4045c89516152280c00c0c0507201203200c42c4040051043c0814240c0300180926500c80f400b40c82d184000c1d070701045000c402403003410300e071900c3d1807030030692607010407468004032295034040c040c0031840d0302d0014030903c9120f0303149008240381248669000c000d00c034566000e0300f11410300c0020381c01e0003450000ae11701088140c454a69400f03800c400541201e04010500d40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 236149973 1250 236148723 236148743
    0x30c09040b070c0204090b040b040c05060c0c04020904142716051c02060301061812020607080f07080406050309060708010f14011806020106081b0108041707060501180c0c 75
    0x2a5107840360000d88003c503c00340c00050b00031741c651500c0000c00802c8804072602801d0804100c00c210020496800916050b100d042c1417035a0740310071384e07112881c50a24901451340032038014419551a049951901141c41d07000e2045d0405159505013600035030031001080040040d003052440c400116101c07405c035090080e40300c5038200b204002c103401d034007600d50f5036420440c00403001690320340c0e000394000c3c80242c450050b00c3c003e00103021025452030340644814022a8060b5000d40c5440b030440d000c055020200d9669401000c1da080601e014110014000000205010944c00e4201c801540941d000c1c200b164265030782c0030070859230040240500400b410580b07030308004003400488480034520050400c117210750040104012920903a44c0158010b0707468034420032500000348540010585030f000c003c50b0104c030440c0040d00494000c0d10040038000d00004504580c05041c0039202110f6010f60180401e517942d42402c5032100c1d01e0000d0603101407600300211555070040790041c007c80d50101c8080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 236151079 1106 236149973 236149981
    0x14011b11060405030a2f03031e090d0e03030903031314010503091b06071b0314010204080c06030c040305070f0e0c0901120b0103060f090b030c09040b 66
    0x10420303411501c02d020224102108032188441c190800030301040d0f00d2805041e140120f500c040c000076a10410360050b07042c0100c01107014400c05020b5004d2600c00e1812101c51000c262007040c619480600140d441c180a00c140215402000b0b0030f407414050082c011034295403040d0190001c540c5108424003c5251548071001521420702e0114190326207003001990710040100600c030401000d0704403100320303980c0200301c61100380d11040074a00325110030300c0700303145482c0d07400100e9a42c04140c410544c05d580510a030750498020354014840c0c03a2919043c051983d20140200005660800c00400400d03410400000100034004060003070a02d08142c01c400c3c81805055034040900800001072107a038000720100800c1103040700011440c6500d070060f002840c0d103034402d41e441c1098a0001500b20601e034409580c080068041e9901100c1d845c00b0003840d658115001000610004085 = true := by decide +kernel

theorem cover : BRFrame.Cov 235971223 236151079 := by
  have h0 := BRFrame.cov_init 235971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 235971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 235971223 ≤ n) (h2 : n < 236151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
