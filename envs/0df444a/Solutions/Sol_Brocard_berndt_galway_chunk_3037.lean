-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3037
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:28:31.463097+00:00
-- url     : https://prove2.me/submissions/407dc357-9f74-468d-a0e9-75a0a2271828

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 546043165 ≤ n < 546223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 546044415 1250 546043165 546043177
    0x5060102030d05100906060e0d11030304052d0a0b070f0204111204142b020f1f050a0203011202010c0602043c06080705160804090f0f021608 62
    0x4415a031500d04602d0000302a01e00944502c0c03409800345104100300d540c0f92280324000c01c0d0b1424860740d0600e142000800c521441c02001d400d040e94880e03110781e99035052044a001e000c0c020000c1c80d40c901009030b040001d0041d84850444c4072664103802c01da518003d103551084038050042e1034070345103c0d80d582040d5490f1001e41240c02076100e424070400807030014003800c21171064010f024220b29083c144560b00e1034a207903021002d40c010f400070782503216101c5a010324600512110300320301229003404030310b001d990501c40d082c04d000c0d4941824204803403044000501015139414401512030440e00b5007284400e2054040000d000d078a40001540205900014580100001818130b40d492080001b05407018005410501840b2000300104091f0b280c0d0b9400020780085803d00036062920240c62000054041c00038820301042c0d04021101d042c0d1204000380c0c0c0409040d445641c1da481640251182031080c0080505084400151080a100391030101e03541d1240b1080f01d43e41502c4135010f40c0d00003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 546045665 1250 546044415 546044417
    0xc020102070320030106062a32060c0901090905060a0e0c040302030f0601030b2a300402030c01210501080a030906080106090312021f0e0f030306090a050601 69
    0x80038000000c1640315110142c84041d00743c100e02c1000d02c9204150850792180c2100d003d020130070220400c9a0a4855440d24916540e402d4000d060158181239a03900302440030b0b05206429403095541c64000802c3d038031400160701d0304440b01a12005803100c8580580e0b003801d800103068110400024840381c00c1a0f401034809484802407a482d86800f02d032201c2c0403a0140f4100e1000642081181010071507034a6541803100508055415581c1e104094140034140c4400c4403c500c14071004960466408a42d40c0b458011869680016400700040c0f0840100110805142c0065440b07804070344109840c400c9a0090203000180d111000560b00c040a0f14180da81056600181390013004452003240e01030203880c4028000142d544c03400403c5200103400020402202c0001000b815410040030000e8a40c0b28417041391040c0030003000c0340b03049070f00556204c40c4400040601542c1286900900b8844809400c0d10201142c280315640d503440241d0303c0ea0340101c0d4040010304e00060a40c03204e074001c441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 546046915 1250 546045665 546045673
    0xa120b0418030206011409040c03260a0314011d0a020c1612060e031603030203130b040b01060201050c0c0304050f120307110a060f02030702010c0c0f03030207090f020304050a030c020102 82
    0x30a41c1800c1c0010038106048001da40890300500c15002c030041c1e0302411840c101c4103c0f02910b015651001c009a052100a022041744044041c00a0145140b0803039400d04105d0301d6210901280010058405d5a450341d0200080c00000300b000034001400c06800d24800c42001c101e6142e040715503000750300440800a590017114249a2441c041422040040c464a40420380541860901400f244d449040d00801940100403282200340320b000340406445d01814016140e0b03642030404c030140d1001c060014003420b059400c00c400c01c10306092060580d03901e03600070803d0741d441c000450b00a10880e0704001050788140400c00840c81c0200102200c80000381041c5d6224124140103880c0d80c200102c1100d82c0d0380594011902c07401e0911000300240003628016443e01c60300600a922032003880c40c0a4100000e07465800c09000402140030b00503c0444201c000e41c030760340c1c24000c1d140c510502840050604110704008280824000d80b40290340040103010460b1549d50151002c1d10b0308034049040d07000d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 546048165 1250 546046915 546046931
    0x60801140d1103031903051605070f0b040305040b03040807111e090a0e0105011724070c0f21091a030c0c10021603021020091809071a0a120b04 63
    0x101003401c5d030800f620341c0c0303000c0366601b00400b590301e00d014004c3c929070400030b080c00510082000c2000302c0c0b00043c0c00032040075030758449080481c2c0c103102e03907041050066800070600c41000041c03402000424018214007003a403203a8020400300701010320341141c0f8000c00c5c09400800f80b42090115030841070403280042d42011680c0741c103080d50030990081c00328580d41480d6460380c190038030004c00c101c52030303540d0900c0c032402000c0200c10580000e0862001c110104112a08024155120202854100405d015040d0103404110341030103120203002c00203040d0b804000b45841c1c0c40b8580c2d04540050400e81820340d0f4440071030300e440d40c1001031410303d584106940d40c814807070688009c1410322941750328851412601d0402a182200c8107c824011500d420605c40400f40311b48810040702280746000f43e030301d010440005110400302c01444480c0b41c802030500504c01d00000b8000300b01d40480035051701e40c1d0001c207601c100b2401007411040208056102605d601c400d01e90000e4041d010081000840b52 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 546049415 1250 546048165 546048187
    0x30f0e010608151317030402130501080601180e0d0503040c0e010b130e0609041104020d24080a03080a0f2a0207080f1203100e10060801140d110303 65
    0x20040da0010701a0b80205144005440410f50310503444621103a09046807410382c0e683c00f07007a2040308a107112000000c40842c08541d00c40e87c0746840e03510f010009120558641010b00e0b102c46081c03244018140c00ca0f0700c0407000a20130701402440315610300180c811481614000d58071175200030401c84840301d468601003001a0480d074164081c0c15800a4680c50324032543d190761000c640c5410134405200c1c0601040720710703681c18100941c001d50190400300b241a00710041406070080e40f258050190400e026440380510031050301c2d14440300c00070303001b02c1039507078441c91074586580010140014141400049a00380f441c1c1150a441d942114000b91000800060f40441c00c602281c58400050b102500e40b8001c0d410070045010380085000781502145000070542d44650b04024042a00004000104800128240d1100a100d07611788000b807858883c00d8192036600303078014100031440100000c42c0040c00f01244410580c17026040c61058040c58a420a016602c14002c56040c4000c2203840303103003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 546050665 1250 546049415 546049421
    0x3110114120603062527060809100b01050a0e060f07050c01090801050919050f070b120f0606070f020a21060615020d0807050c1506011803080406030f0e01 68
    0x211505481e078103800c0c240310701010305110005d014405158120703508648800c41d681e0540620039950709000e0b80e103010000030940c0c0e50050043d00049442c048800140c0a0b8100d90003911802e00380c0191903c003440c41c50010121100e240b0340c60700149041c811884aa07014589580342400018081c8e420415030a190503450383c41640c0403100c94000104000b55560449080005041028001d0015192440e02c095554104110703203611212444032640912030140302201012892000750340005854409005090707001807261440800c0310b1000905080004841d1030240c08024041703803070a4800c3d296681031040c2c1901c1603a0160408000103000c400c01c08080d91080d02c0c2001d00044c1e04224100345d82101d20b1903104c1e808900e205500030341c4c400d0f03002c07078000200c05403404e0000c0c2640b5030000455190003044c403070018500c1484051030340005141d100c54400c0c58241c1e030b003031361ba042d240820409140c0c1910008100020510092040500a0300304030303000040c2e44000103c1010708501c050035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 546051915 1250 546050665 546050677
    0x90112020706060902180f01120b01030906140103032606040e100507081f050f01030c020a0b070903060b10020a03080702120d0501080d0c050303010909020d0813050901050102010603020a03110114 86
    0x35400501c2c006ca140a202d590090224200d4802c440010000b0019043c0c0304031080015403d070350351510b55100e0703000c2c4d88607519540c5c10450800c07284540c5113040042220030301003a0301241c80e020305071803518040414018425041402c480b02a21b0340014080507285101c1498464060700c2c2046580350300d10301c94984280007079554400542080c1e691451150241c003224034020b0901c2d081442240c1701e04804031171441c02881d00048004183c4401c85c1001c0d80c03170301b0051010b80000d091180b917550115038001940e020716010400318408070f00b040a00754845002c500503800c240240d00120740101d03841036004440d401924400341c103101c02c03c00594441d4031542400b40d51000180302030101000390081e040102d00b0700420b5410680c607042c0c4c0e40e000520078450341d142c5400707106085490303a0440c0c046080c0e01000081c0c59517540394151180710814041c1e1405007191100005141d0700c1400f507807048a40292500b010142182c8540440b06801c401c1141030180d1709031000d00030401c0748000c142c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 546053165 1250 546051915 546051929
    0x105092b11030d0603150b06040509090c060315041401080a060f020d0e150a05061f02070302150a081b0d020318072c06060a0c150c0e01020606120309011202070606 72
    0x244d02402c40c5441602011910720304030b0318600c1c000e1162100e490700346c1100d05035a0111081c03d902d546441441d490000e101da1580d4000c4004018030152000d0f410344003101c00400c440c00d0013004070700a080c03200388500b4410503109500c0400c104002c41d81c19840644401d168200241c80c0c030744c0d85c001e24801d840c20f01460f0141503000d100048404158040100d4000c00303104014040b50900c00c001a007010540c00c0100b0a540800c4001028280204005801564003400d140221120040040ca160300525058404108040e0016968107500103d0340217174901c2c030043d2810100e4074628030b8004c1d00700601c00708503503048484c1040b4101b070402511005218038018803402100004213921000c1d030025103c420340c03102400744482540c555045d90910340315444d01100c40036060400600c0c0d0001030f9a031075045441c101d0307240040e81c2d004501c50703581482030b0200e0300b0070788500741809080346040011001d40d170028041e000c403541c420346007000c04601c8600c0c09818400d06490301000c44005a120072 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 546054415 1250 546053165 546053171
    0x5040317011d0f0601020319090f0b09030c0d170a020c18041a0705070f020607150f0e1212091509071a07020f0910090504080307020105092b11030d 65
    0x342000b80c02c0030b40355485803100c08400400d0500f40c0020b03549001e250781405121506528404503640700c1c154420051030480c2e00e08034481c0d641d100c1d0011540c01101c1f403038024000c80c3c050305107a0410380d4001ca103860f40120f82448003000103009030081d80100460300114003500d02c0340c5030f480d6164005002d803141080b03900c4280381424602240ea02c203180e9510403410005800300612940c1010075283c009401c62292210003a6038030000b40180316241000708003200b0303644a82c1da103a040340c1c00130b23013200e907251001c20820a48428003035a4071510244003500403000c12a50701005210000690403458000032a151202d000075600c0c5841c07070486000c8002d50000800f001414800a0003075150001d850701e030f510f02141c0f90086406000c440c40320a0280b552000881e40325080081c0c1c44c00200b1000710300b08203604247c0b0b84a80940d00c2030fa4a0001982440c001c80c1c01814080380310b50174009422008a112001c1800c85d46e0f01c4c0310030244c0c8009005402e5025404280148000d180e0420851000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 546055665 1250 546054415 546054449
    0xd20030c1506090114041a0913031d060f0c0307050d02030a02160e070f54030b0a020f0301060e090a05010f1202030309181503060f0a0504031701 64
    0x80019200014580da11540c0307080700410500004508080c085c0070203072804240041d6801095a0780300c0407620250304101c1c000104500c22042d000302002081c466500c071414100c0b4002c000a01340e00314000c2d558080c4041005201000e040402400240340b4101a42c2c10420303103031105410412016106009a040007a022140b00d505100304801103c0f09a02044180d0406031a0a410400201402e040c000c003100540340303c0b401011584602031041c00070340c4480c00318158003250480c00b80800305075a07122004c5100917480c00e800301071204c00246805150140385403034908000d64084c150004181c0c2c00c010413007448003400e00440c003900b010344802d0184490041400400b04000300300d00b54551402005011428805084104448801c00b0502654120b400041e09601c242d010702903001e500380c9100f401c034000b4001d0071481103041d00302e500d86958902e402d05842d820115010103080200c00002141d0702940d030301c0f0740c2d0454000e2070851010324042c40c01043c0c901c003c0c0c0190719003103c01980 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 546056915 1250 546055665 546055693
    0x100810150f26010207030f03050703090b100e15030d180b03010e0411120303150604082b02010b030606130b0a090b030c0a0807031e0804180b0306090d20030c 69
    0x10780b00021414002149048010303200200240c0203803040b00f04041d00c50001c41d0240344250881c4180b20703081004092141040b040d83d9000a205110340040b4081c02c0000030312000700318280c00041280030300039104882130300c50119182140c02c4070b00d500e0f000e014103000c25088115800755000c1c00c1201c5d00c3c16010700301824040001c40041040611030490f0600b1100d81610100c142d81d004070306010f10008549401c03000404030700035600f10224600c5a0403282218034545801c45100f00f0b030042082603000e01d000c400300d00380c40c1a281d607950190710660102d0000c2c20700d0b90044044138500d4000060880b00000011461140c0e80d00c00d0310003035142d0b0320540c0b080c6402d00c1141aa1041200e000309401c0c035100780e980d00c0f82140c0c4005411030240e8844032400d419061300080146600005242da81d5803a08024084000005190a416803038005842114180000c48500851a481c0182200c900550080b5502e0500c086074800800c03042c4500d848803101000a002d00044410141c040400c4c1120 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 546058165 1250 546056915 546056969
    0x1103041509050415090f140c070c051c0b0601030b03011b0207120c05060f070206160512040303081b0c070902180d03170705090a1706100810150f 64
    0x11803249140c0624000054044c04140c1c0890304000004602e03502243c3c114030041044054142c0405240c00400c81c50780c5000005000c0c06100d001410b1107030391601e080c8150514007003c625611840c02c010782004c00c500c2c0c071080c1d500004c1450f000c40c03480a1f0f0300200307080d1034404040d5841070341260002c400381c42d01404040f000d803400c0580e0710624452900c0d8645544010720446000f0388001400340c10024030001116035040c1c01601c1d09984207046640041e1644601005848070300a0320b100e010940d642030221012243c043d078a814003902d510b105503038104c002080110688104015000070b0281c18804080200105100181c44050007003110380c44810000500b481090b001a00100094210520990400d80780907548a50340d5100700c02d03640740c03080110041e0b08c488001c1e00012100c881035401440c8800a00540b100c986540b50b448005492900840455070004442c00c5050b14180e4018001031684803104004c3c6640ca10380c0c81c1100b00c6981101d420090b6091a8848240c2608 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 546059415 1250 546058165 546058169
    0x2030402150d0207061b050f070807080309070303032307080709030b0a0b010e04110a1808010213180e0601170a140106050127180f06090f0b03060c0a050304031103041509 75
    0xd00103200003146c60344018200d1092106100c106000400c0b40c2090060756803c2e542540e51129840356241413103604183c3d581ca080c802200048d040c20180e864800c2803034000c40d0783e406001d0414400e42c071480790030346d06c45600502010401064080000100745c01c49590b0b8061902030000003506941a80010044142e6070142405142000f0341c154001114104444d8650130714038192414400d210a9088910099171004080e50b00108050351200d10b081c16080440c2e1041696840c4040c0350170351802921080440c2541c144c210400400c00d40c0c121030041060380b0618000c2c1c404405d0203554403881c04031001d5448805070354441d0144200c0d40c01450101d450501d05440c454406140708001c40e010000c1d000300355565011072004102da50150304545144268400140111a1600340800080c8644620741140d039081890403019401c0200b507850003051802c411038540001e04c141603905500c042c100310304210313030000b64490b00d0001744003400c080e059200c50014205500c89000b02a61540d07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 546060665 1250 546059415 546059441
    0xb04060b15090904060216200f27060d0804080a140f060c07060f02030f041106120103020613080a080910050c0c0f030705040c03051f0302060d02030402150d020706 72
    0x2c02001d070301a40d824040302d500030b500600150391003501101040c2018031040340107180c1c03d00c00d04000c400c080a200f40143d00d440c00d0b03500c0741c809100801000b4114400e41e801e0b145480f1014040d1603d0000070700301c1d60b4890005400c0b104903e5042e60f03000c0080d84076500550003a00000208420880303013a10f0803d1640491000f0200b040a4034165500c400c0c014041500712080010584208882d60b04000310040034103004540301c0c544400309100c5c0c848100c0d000c9405620ba03099103007443c9421010b80c0d90a1300d4a243d0000668210350074041a42d10119200341048400c0c50300040941081000c00a018800c0c80d8031600c8401680a00803c907242c00d280c0014408140880c10060500095080007698100c800502c003070300d000d021070308005044c2c00c0720390014205840c044101d501034112078040d4500804c03190900300e00c601080d08804440c00005c0d846003040008100c28603450f006140c206000811524000703540c01d032050a05da0080c404027410344c0d0042090b906116441c4103101a403400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 546061915 1250 546060665 546060667
    0x3040b1305090c0a1d010c120e010807050c0703170702030703080d0e010204061b03030608010507050a09080307030912061b0e0108090c090a0e10020d240e060d030c0b04060b15 77
    0x2440c0014000f081c980c544116501c0603c42817038501d82c41034909420b060b4000b40c0a082d00b50403030f03400038143d140c2e82a2a501141e00040814240d078403410440710f0f181d030944041d00c8c4980c2183d8449018030b9044103081e0304508148034890150307a0034002507000318841c0300180d07969a20b60084000750b400103488030750983d20600c010003100e5003001d1a00b003503110078985d00c506030800c1c0c070b4150028443d40d0007085e619803078030081246032604039004040202d59602c402d0301c8660386501855903403095210090019104e0300d010445804810102c0325614030461000c120381000d001c101e0307a00200c6900b88000285140c031102ca4a5070416100c540003070f1160060514040c0010100b1001440540f81d00b81c43c50f40c2e00040300308201300340020310320940c25101c00d650305e184500603070000d8040140c042c0e4040b240340085550100c900c90b00341c000c0f40d42d090f07040041303039640e03108200d810300d25101c040e4140301c0919541400120b01c00980d0b0321070b078491000002c481007014140050101d03841c0c040d04035010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 546063165 1250 546061915 546061927
    0x80105030309100c1a060102190c05010f090b0309030a080c0c210c16051f020606010c02060712080405010501080f1b01090e180610030f031103040b1305090c 69
    0x402004554069400f070b03500c164906151081120242243e2801902c107000582400f001060504003682c0241000da007102c1c1d5400300c4490001d1007480d2420010107056444000b04280c1d4015010602d0071402c1c0d0401041d4242d8803440018254000c880d02d120a030070000c0d0360200780d40c010394031641000b5060700032401d0242540c08160b8501695200e01138a05440c0500c8681d0f0361107501700c2c1d010004401c1600c500015004c40100b00d030005010f00c3d8424403c00c075064150451500c0c0d2a0301c0c1c01c07800d2380100016200c0900540b880308a115003070341c0182040012201285030212564150502d9507076244181c50607042881c2120300680140d4020380102d200500a602c0011f01d0b11a0480006201c1003030f0056440140c0d5600e00d0b40d44410300d000083c00400c0b0704951294003100300e5080500907140e0503a00c01502200801c072602005045841c0f080ca181c0c0482d1180360407080001e160360481e4a4162545400d08440d001301c80703134191030002d1280603c11814521442500800085c0c4114288a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 546064415 1250 546063165 546063169
    0x70b04140a0507061b110d110a08150906090a1704030b0c03040212011a06031806011d06011b080c1005010f03110604030308060907050f1c0e0703210306050307080c030706080105 78
    0x139181c81c00452103802d07d40800c80a210b00c600b4081c07803000c0000d0003007500c5541c2d20082c80c4c4034121828000480e00c504000074207071803000f00c0d034a03100c1c04c40c51018011040b181d9660500c02801c1005912114106000c0440042c40100c1100e009082507410b040d164030b454410003025040d81c8540c0300390340c0d040c55040c200001350100c0002126804460003030b02d80e5118180d648520100c0f0300c05003094882d1100000c1c00008804030000240500d4039926050707915070b070040d5108985072410b6200d486184400c4000304404201038a00e4082200035240c40440c5601d506043c1e810a0300500031074140801c040082050345e4003843c83e481c100362406070a062070f60314043e01d80a0014182401031400c000001d250511403c22140a0702c103400109866201c10310026918440c65801c0d116058a00039004800070b0000800c40226507002d000504609036007400c500810f030800603020300f855243d190100d140d690038440703c00039012000040501540c514101440c100040c1c1c0013000740071424005205903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 546065665 1250 546064415 546064433
    0x1050403092d062303010909031103091807051317010c030515210102030703021b0a0f0204020903120301180b010801030c0608041e0b0118020f070b04140a0507061b 72
    0x80b1941d0410f0303d0495040195509148004c025510200d100080080f4000c010740d03201d0780815000b569610000811005400c4d41ca00c164000a81d0000307032482c4401c18802d0b06d40c01103600040628019043c0003425484035811075240d0041080c981c02e011158040c40c509105420b8042214641400321703082078190152044482c0400070b002c1c140c03098150311811601c8114028608240c0021580c034508504002d000b50000307003c45c40210030045e4100c5041d00005030000349150064440072000302680c0c200002980310409594041c0148115041d110b041003000d94020905d1440c00718540200c0c034012000c0704e580c02e8503941802081030050000c914a0120882582c505080201d007944513410008500d0702074a001034180300c403050b40a003c01c0b02544106040b07a03040c00ca02000c401c0c83d030401c1020b9024110900b20900300922420380801c407481c0c1d0b0359030443c0c00380403910b06051206580c03d081c0402c44030281d480d80c1c410034042100360b500594041401d9004520054030b4004ca590340303900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 546066915 1250 546065665 546065669
    0x305150f0c0405180907030b0708040c0f0302090f0a180308090705030616050315061606050604020f0f07140102030405031b0a0201050409020c070906120501202a01050403092d 77
    0x4c001101300000d0f58080e010040d0741c01650304001c1880c0d06280c503103401090310808980c211803090aa10001a030003424010324020f0b02e0380103226158580d15206410714848000f4220070207641c40d00a03050310a02c0f00070103290107070700a590b08151840d00d6440646080f10750303801306010394000c40c1009075172028890b20001c421580d00d011b9559403540080d6107407081910900c6a4407100004110900d103a6074440d030241d040c46000c0070f100340c1d40c0d00f6003000100d0060500441c5c40500802c0f41c02c818240d854010b0180c0752007540c0395440400300d40d200030b0890308121405c5480340d20004400044604030300c860729460700024020000158a80d00003000c40c0103a208001007180c0102c3c101540442c2803148102800c00c0708010001d441e50792030340741c01c4020115030a0b6940d507e422000002e40c58102a02c800084610041500d4a00030b075800503400d40c100f5a402100214101c2e0b801e42054081c0034045c0114065559410001d0602015100c42d040c07100031600074004080703012000d40045140700007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 546068165 1250 546066915 546066949
    0x2010c0209072c090a0614120304091805100e1002090d150c030f060311060a0c06060803070c05030a0b060f060702060d05091c020a110103060305150f0c0405 69
    0x5182d1240d08003501c06401c0150402c00c1007441164504010000140c1074616420885402c1c038181c80345440e8104442c12405805488004800c0c1c082c65402d02001040c484a400710489181684c0c544085046a07980c40814048095403450002800340c1000502201c3d55942c00c10011042d06242d00b50343e5111410750401c0064011030400706542c0c4035000c0980681d04022034140031301d1440c00c0b12000b4480d098058011030706d80540302103000c3c5244100c0007680d6220110300a05603062080100b5608402d5180c010000c0402010b00099400d01944006054150007551100c6075480d040e82c2c161182d80044d4000d40c000030040c004903580e071418580010083e224600415943c9010a00511680002030741003980098000520445640858801c448100c00d44030000072078040109401807102603140103a11007042000400e4811028688411050500040642d500d588003824103200b00e2482c1d181001c00710410060007030340210241d102803a106500d00e41405c21000a10b0405000c2c8602 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 546069415 1250 546068165 546068179
    0x9060803190c06090b040b040201020105010603090b010911040f12020108011d24030313050a080606010f0e030c1512010905010803040b0f0918070e0102070f050d020d021002030a030b090402010c02 86
    0x202c00c1c070030389600c03140d6001d8000c82c1d140e0080c601401c1c004c0741264182e501724015841c200001840303a200b4421300507181d90095861585074030f010310040182c07504070b43d41c04440c8070030400000c1207041034031004000c15065880c0880c495083c0009071078100e050f8480341200a03001071044900219402081d4001c51340b00f0555076030780d0202c10925840c0742030044640c144c03000086a03041e0700045120002202e0048501040c03081c2c56000140d01d030320742a0b9070180400d880d0041009001e000b80e00c0c1002d42e910240c1101d042c94100d80020b01c3c0008020381c0724022620000b20900e42c000e158060902514480e01c0c2402603501d00100d07079549111354490380e54903413408078880c00d1a400e21000c071040c07401c00a00003411a0018242c510168030280c0784032002c02c42014a604065001180e03003001c456982401c2e108044c500b00900c591304c42030341400c903440341b6400c83d02e10050b076030b9840c0c0c0e0100c04132941c000c54541c2103200e0090112550301c1c0b9100d2043c000f032400c020060380c0c006649d20030650f05903401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 546070665 1250 546069415 546069437
    0x204052b0203031c0501080307031403040f0b07050a0e03300f130f080f0d030c1209030203090f0f090406091b03050d1407030905060c0f0102130906080319 68
    0x1412520030110081d0315020004403501c8241d0624034800412400807000c0209036618102c0e150340b0303c28084000c002c11150016024442039140283d40d0050145002407001c1d1290f565640c01d800044809402254012031003140036984a080b450300b0301c40a070004c2502c2d02075000c880a044003801820a00d142d0005814040c0c5100c410a45071946c2038400030030f403210000060b68030260100e014071500300c28901000612443c000039030100c5900500d02800769424444270480240802101d5171092142003000e02005c16200e1007041f1001e03009034043d40d02d031b03008481080401203910105511829030001c511b01c5a640d110145600250b10400012b034058071441c110010b0701040a1400f400c4540440000900001158900c1c0b90f6081d0307a0354144000300e1609907000c40c083c020f00600000c04424040c411800e145005084450141041300e11101d44001c58500f07a03030000b0000300743c01a4940003000507825901840740038080c11006917007840030007203040000d180228015401c002d911011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 546071915 1250 546070665 546070729
    0x105091801090609020405161403100503030a03090210020f1b03070f080f2b0309021315051203270409080c0109150b01050a05070615030309090f020405 67
    0x244240003621034000d2103860418102400240741108099005a04000018a0089900c10b002001120325101e4100700d444c4074400c040d82e40c03c01040072803004030440c00424203540070000390000e05000d50b0041050341c01841400442000c0d80184070a561200350146014a000305a84504840c6103604000310381c101400285401d5056110840180400c980443c62610200e1996407000109007211441c2c28800302c00300c4001050000b04500000b0300481c001030764032982040304102d00042c07458000c1c5191b04002011601c103c00c0c082c180001d000340800c09802c0c000d041c48062614100514207148000340080911011020a0002006140f040c181c06540b290b020300e40c0c0540040c0316580380c0300c0078502e2500034a0907405c151424a030300c040d2041980c165008005026006031356140c00c05007200c0090707a084d041141d0803299581c4410a00c1440010784c8012002107000e03568082030646030400b1407080700c100da03290b5055140100018082503e620f4400b000051034100a402d190001b148 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 546073165 1250 546071915 546071941
    0x15041808070215040e07020607050415030506130e010902031509030703140c06070905120c01050a26040501092306011205150106030203010f0504051308070203030d060b0d05011d010509 81
    0x1108007040808140805c1c400742c5c40003228420074454080391150345071010262550701452045600d84ea01c00071155038294032030340140d900541701a00700d045035400017450300255200402c420505a40d02c407451801e5280c10040d40d410500d460981080509040911540340d2003005805000e0100d50b5007001c0b440700515003101c201001001c25540d1600b84448c00070b00101c40da00ca07d0341302e80741c4004031006404c004a040500698161142442c0c40d0900b001a02e551040480002d44280d0a440550060110303184003440346101c0d000016a41c0402d207820140030800079400860100320701070f45150b00d5000a01181951121090381900000300c3c500545000c4034100034111303001441c00001101ca030942c000d103040c0d401050032114001d03110350501040b01d50071204983e444100703080c802d01140c040c800038907149002905403440c0a40c0c200c01042034074515444001001e00c00500c900c000038240c0307e91400340a001581c12902d800c035419007844420306006051003222028041140140300d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 546074415 1250 546073165 546073189
    0x40507140a0905041406010903030305060d0f060501091104380c0606010e01020f030f0d021e0405210d0f0e04150306050a02090907030c051e03150418080702 69
    0x60035032607030340c44281c4004280940d14814580560b081c81305080141208240c281d200c2c4106075540200f0302e02d140c400310080d000c06080c5640001c0c00c03258000100c3c0c030056520f0126070082e4030100c0d1551400b001c0008690780100192800c120034072050100d203c02d400c5802d1240004c540c82000c42103200b00c0c140e064030a0b80080e4180010005a1250413400032408134440c0c0e409807150842034441400590302c070428258005843e8200300804001e4400842c040e100b92072440f503005003003502c0715074110780d0150411541814500085410440c1e450481e14162403603080f4483c03066220180c038000e6985103200b045031340c148001c1350420000d5034816042e1300c0308604000e1040c004811200028045450580000c0c3c6045042c100040d060408034001c88a03c0030014210720348560f24241c0490040c2220100501000b01c100103180340005402c2480e480c00e120352030a15603c0c00c0400055660540b81c07184075000d107060441c0e0303a100c5000d41c1841c0700050b4021041d1075444160748002020f0b04009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 546075665 1250 546074415 546074447
    0x20120403050105040308090f1005130f0309080705180f060d06020d0218091510020f1225020307050f040f0903050c0607090b07060c02011803020c01090e01050a0302040507 75
    0x49000001d01405400c207074044c0307020340c40b0403005884000c0c000b0b407903034101d40300c0d45402e61240c07804030501039084d48641da2012a043d841ea124401954454152507103901040d0006081e8450600c01d0308403d0041e5001040d044607849404c211200b4840c0881000800b0001c001e10004002040c9803a1000000c08082d0b01c901c0031235690055402c604001e400c0a6544c6108030852181d406203800c00c03000366401002285c52008018244504208907114000e641c5070444c0121141401c250740200300c680c490814031403901da150481001c0c0c2791048469418041d202000d0031110300f0150f2804603220058640685518403500c46103030226000d8141c04403d0036030a4034100003c000c1c1940710010705010035400e81500c175943c0b0340c2c010071182c800c420b001d6510341c0d02e0100f10140001354240d221624484980c000400c0307505201885501b0001803101c15005a003204504a41542e8090600005851228041c061950405001c40d544c0005400028003c59a501c04968400e005e8800006aa401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 546076915 1250 546075665 546075667
    0x170c0c0a0507060315080705040e0f030c0715050703080601080c1c050105091b16032706030509071206091e11040b04090515100503070308071101020a02012012 70
    0x980c1c5011661807001d80308000003e803802042e4154001d040f001c01c0d04503150b090003080d1450400003000001c050f00c800d00c59452042c000c105000c0402400605a03049801001e044040e00c5c0c82004401c40c091030080c1c07420040100300040000341c000c8100b83d000807003884c0500484da588401d02c40c1d01d1080c541c5041510200c424817214041050308120b040e500305450440b119120342e0044c4a13150200340c0800105a4203020312400d01d64001e02500c601402860040301414106800a41000003202c000c501d000d0b00c3d00303003031005903098011260000090030040240b546010710001c20f180e00e003580180f14540390300441701400301c0707004031114440c0030021501e100740751498616104110325818a01440c103006a4070058601441991480c0e90004080c084900f0444101c90308650010010100c450071400041000d031410404400a144210100c07552400366003040403034205c2e00e000682c1194040440440180d80c441d41e4012140d140506003c2155058648c07a400d00049545c3c032424104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 546078165 1250 546076915 546076933
    0x4210c1d0a05065104141f030212070e0a05090408040801021209010c0903020d020f030106030c0914010807060e0d03120c0f18050f100e060304050303040b090d170c0c 73
    0x846002c0220101c090440d0000b00f4504008003580e80004d506580703e00d10705100c1002022903412600320341400060840700071001011803481e2500c08498000c0000380d0102c0c6601c0c50010001c3d01582042c4c81381004052100320303d0000d04004458043c1c140a1500c500109040007810401e41d030240031240001d540312600d01502c410f8989048845800c613600b01130860b100340303000d002c6110a030398028010449403845078091054405079024540d403d0340d038514001000c02d1168040101400d00b045012402869070b0610201144041e0022400da42200d981001081d400280b0841020802d850401340e0040604080d134102401c1c070303039a148150910040050703c40e4405040480a000c88d11200c480349042254190004994014660010ba501901003012324001c401c5200100241ca4030314a8000c124001c034032a500203440886503940080188000c1240c0050700b16406203032180100440541c0140082c4046078001000750608040706c04140c07401039038811100d0304500f5a048a116807 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 546079415 1250 546078165 546078229
    0xe010828090510150b0403050d050a020f0d030c2607080402210a061407090911070507031b0b0307020316030c141506040207050a1704210c1d0a0506 65
    0x4210700d060044030201d03140105080c8922021b403026280c114000b4a02c24010840c1550164410201e400070361042004800d00c180041041d030301c00c01c0c2c50390f4000c1849403802c0e00141c00b00032000209031101c8010741c400700b820900051032a602a84c3c524001120740c8031400840c4000b0906821070744c000007a101c2c080318500c4001144808075115450403c4a21180b4500b259010020340f035500014013803240402c0701c3c2140340c0040d000004440030180ca0701c51b056886078170303003071042e0300840f92445031804000c3c807910640319003801804801c2c01d0626502d48644001e45900c215090885410188004101818401d00101000d29884a0068080e4509820b02695002d138401c0c5196154407407000200241801e000341c070882c980c0300008003504011355440390003040c56911f1549050b5010300c000518401044442c002400c0c003880b442c0070012040c20101c2901e5510703000b180c400e0740c261400701342302403040034980c1d40b01c80c5034030b80024143c540da00092207049108842d03810010004500070644 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 546080665 1250 546079415 546079421
    0x3150806061305160809120d090c06090b0f07060207060501090e010e011109090411220506010914060c010914011a09070215151806010e010828090510 66
    0x140200300c0c1c2c180740300760441c2d40701070995404440e1130404150321424a4a42401501e4054114507800155880e0700c401641084590300309035a00c450032500d45080e10117020010f085440035101d9442d02004030380c10a03a010384503201b40c10b240443d0450010301d00040c408030740e040e13540d0162302c43c0c014032455a441d55040701070700c1044169445035181058004a0360414850003251044a542d41420001c000b02001150800104161945143c6000d1900241c0d01c0c1850041c9061a0310303401041d03070f106142454110b800081c90300e410b02800000a20207072400360800651500f080303610b103546002d40c11016000d448204801045081c1000040346030b10010f404c00200510041d100c1d00d0009135501c2044641c0f0425540200036030440798500d5140700015803103540c4410f04166500314801c020300401d1204844003813182080c03904405020302507070300001c0c410f442002441c0207003044c18000c000e2302e0f030950b1943c0d41d00c1410840a152940c402581c2d005480c0320b6403c14141c600e503d030001010405 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 546081915 1250 546080665 546080671
    0x50f0405090a060e15011d040e0703140706110a1e0f0804054603050703081c291801120209070c0c030f020a0b03090d020d03141603150806 61
    0x103014a1603000076140700c280301c501780b113012059548090135000c19060040a00108007803c0d0040e4641006403a044401c019450023188180256002080150149400e10f144c54004204100801d0303a10719000f0380005407010071503002a9908100c0720455126010410b0b0104002c11941d44032842c075081c4002403002c0c0040b6034081d1242c00c403540b201110140b80d003d1051290090341c54048401c0c10204401c003030f07030300a80114141d41c0845502c0742c41c2c151038003035168011603c00e000010755840d1900120a0011900c103009001d00035a40c04d10701c558007051004080c100c044117040141030055498052031584415607200140311540c41d0485010303580720b258400d07070180349650003141029100c3c407400d2403404d8010041d03440f030300d0440d680c02c06440008501a40d2140c0980da000c503211092000550003000980d0041c01c101720360301c2d0060b060200c022800801e161801020b070005000c01842c0540c07000000c40e065075545d01100c801d4005141041d0113115003c1c403401d0218030f202002a030640 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 546083165 1250 546081915 546081929
    0x24031d07030204060510020307080309010603080d0f0f05040f03140d09140111030402130509120c01140c0a0903110a0f0b040303090e130b0601020c030105100501120c020d050f0405090a06 82
    0xf0399480d17405006500b80034200c5000182d20800c423880110385008051a04840d16038000328166039241c07034012441c0c021620a44850740e8820701003010740424070501411300b02401d014002e503d00307921003540c2c01a4090000c2e040c40310b20341310007000c2041041100c1920010303610802c0f4403000c9061001c1c008084401942031b80d07180c4500c040340d140030701090b00c0c07040754000c1a0300e10321a090102c4001500303019000d0f41e400c0c0728084540703c05100c0b040281c900e00c0d00080000800380780481541d04031070005407002c94800ac040002c0410035510081000580e0781291043c11044d5051011903c481120750001c024100c1002c1c0100b086c8111000a1049034041da0360401c489480c0e001c2112494000d03900440202e00d019880400142885c5160398042014015a44d50b9041d81c1c01080c00c1d610b0854502080c810713180001c0c07000750b0700710381800410300c41d41d00308202c00401030b270019690352408580c413000e00c100400e0700c1d142201c0340c1080b200905400b62038005a420400b250030b001d40303aa401150 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 546084415 1250 546083165 546083171
    0xe040f1b0810020414060717031311040c1b0f020d0b0115020102030c0406140d0f02270a090b031c08010501031d06040209060f060301030c030b0c0424031d07030204 72
    0x4010302c403030303000307480599042c2e2800d40040c21008040040c2d60b40056001c4a02d400182c40104c0c24020501c09103120b0704540c1c08481c174103400751074601c514031118680b0500c00c0e80380041956407039130b2140ba20420801e004655080054550408000510b0b645034001d41c0308028264010801c000c08200074101e441c4050000140703040080164240e020231a82442401d1040c00204886441440c1e0300c50148462221649040c903000d094005450f200c4498991958001030f8401101c111f003942c05151412041d0301a44003082480043c0d160016031080c801c0c0251a810004680da4060201c1c0d032003030000c02510100b05180b0403002d0403000c000d00c00d0360f002c6407174103519082681006070541c10400140740a45010340d0b46500b000030102020740b003503030004644c4d90414025100d0710000c5000c0c500544100188a16502c1e041c040a0401828081c004c00180420400700390060142e60004482000c0455199942c880490090614024001c09107141d49144150810085042d0040e02d000751014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 546085665 1250 546084415 546084433
    0x7210204050c0712021b0607060605040f09052e05060423480408010c050304050d0306050607030c0206070209011508012309190c05031504050f010e040f1b08 69
    0x20b90711b80d100e4400004203803d1692a803595850640c00411145129807000507445840b500858200e46503407081c1c0306001c2d0346030525010700c0003c000c80c00b01c047c030180b940303042519049a0007901e04403120082400644443c00703e002640d60343c100003900d60520b44805074070f6544890030304040c0c4017a541000142c5800601d4803101041c03015074030b250403500b988504c21040f012003860a80c01c81800d8031009040078403000c1584c400c20b0049000d00c3d100307507480e292642024102241400711144c507000070f25240510802c01c175260b0401351000c0541504200ea0f0542041c008036105200d244402507011704428008901c82c484c441506040d180182d545110a0381c13129030001c0c01c1c0e000c80d0005001c00e030019020403c0b51808828883d440307000d02411f50841c109810000c002c1d2607603178006d04046003001c002c20946c0c4102c03400ca5038926030f04560600c964288911182c0c7c0859060040700c4079049164001020712081141c0307800700950040d22281c2550302c01d0107a0b2044001806205c84c980144120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 546086915 1250 546085665 546085667
    0xf0a0b0a1d010306060507030f0c1e0501061205251a0a0e0910050d0201020309031e06130f030503130b0702010501050f06091c05100f0b010e01020f07210204050c0712 73
    0x800b421784900d92079261410000d0b80b81902c540081d80e1202d81000f03d80341c0c10100040314128140e64240f801204096100303003e00d005820f40d0755980040c0f00c05844c0c2c10045010038000124a80b20102d007508000c0800204842410000400c0e0080c0601024007160f49400070034050040409a0349035590300c2128680004205100c1c9003a42c69168010340d00006104601d000b0130384041d018030500442c1d203459580b4011a04040114402000b00142c003568058403440601000760b006038811044400700c481035403260704210b040341d4050204980800000c0070b0010290640748169040013603c4038621700a40005d02030030090182070f000b40c0c1d600c00a06540d08100d825584068001014012901910b80c0c2e072811003490f000c000d880521034010103d80f151400c0c441c140c0503465032000441d26140260015200b0559404c00340e046500c61555441c8a400114140c81503400501004044118605a1070b140c91540b07003010754082c3c940410b02c0800d0400f24006c1c04114410030310301c0004c03800354030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 546088165 1250 546086915 546086921
    0xd15020408031921050604021c0603030f02030a050316030b19090f02040506120c0f0c011407051207030b060904060e01030b1f06030e190503090102070b04050f0f0a0b0a1d0103 77
    0x16044404103c1413610780c818a0f29800041d84880064401402c0c00810101400301202e81d0110510351070b80d50742d040c0300703040c0c0c40a08a901d4601500046142c20381030600180144030007044130407d0041d0a041444141c401d421500714800000c200d007001ca4030318425207003030f0b10311403003202d4a0601d802d8054403c80326600039981162030040845041c001e0580401178541401003103030580319020840c0e110400084006060f4a054034400003d004440003201d151401010300007106000c000c1c072420002c808a008140c1e070058040c0f0700410f0000c02c03200803071080d004445440e6409420b0035408100b4400a100d454120303809610200625160410307900326006010700811608030488006100b294001d412032103046217110126000d40350a1300166208007042e4200315120340001903c9522036034104151009001448101464146080c1c00210b8441d07038001c0031b60082d000707020400010343d5403040d20402402514941560341464800003032141c003d05082c01c03204903e0101600da1544644 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 546089415 1250 546088165 546088187
    0x6061203040b070503072f0d0c03141f0b0a0906080a1b1503090312140105130e03030702060103021005090303040506070615030602091804110d150204080319 69
    0x220140d03140ca81844000000b580c0114001c0d10a031004001d00c0002507012001070030440c1d0b4509068000302000f5840d5002404220241c51007075201c40214400302c3c603400899000c03030340c1c0800c0c61061516001d51650502c42881d80002c810b450921100709150b9060b045411030350411140d68440d55200c0c0c01c1842200e11034080e02035a0340c03100302c68000250700e1400c6001e170122102c1d44941c4842e9039a481c0c0d4603445031000c0d0000001e46031a040300c2010740080d014444000c0401d024031000f03569a4061900c200305100d442d10500007505801519941584140810b0441c2c0c0140d8ad528600100040d5844000f03102c12030203210070884280307249101f00250f0b62070810090146d4030f000c3c909010480980c01903e4140c4409556401ca0140700010400f150003d602c40c1002503122a11041040f40741c0301c1541905007180030b480c00b00400548402c09000382c0000c11039070003170145001d040c80c06840c141c008403804071500c005400714006c04000080c1036008040d5681d401c0020a8001c100c815a002c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 546090665 1250 546089415 546089449
    0xb01020f1c09030f0804050f060903210c070e0702061308180f030a0c0e090a03020a060c0203040807030b040b071b3c02030106080102122e030501020c0606 68
    0x1d0102a10602090120581801e2606081c000c0e00d0380c803400e51600444c0030031200302c10000b90401c02030401a42c800303140c038030485409e07007451100710200c2c0e1125034074450480546009040c05494040038029a40001d04500440303503231588804440b901d000068641c0c10143c852580082e424540c0c1c0c084500c10117520070302960510304283c50242490301c0d00300c02544d10460b21030f180c4101d520100000411382d400303645e4103034400c0d1500c5020240341d2006040c001c2590081c49104010980014402450319400000044d03401203500c801c80c1180100e4100c1e098a000d440d10010a02c15002c810382d00847c050941d4902c03d03216028140c1d1240000180700c03101c491701000b01008102c00020880684009440451180240c0c0c142c825143d400c03680100d0210886001c5d400a5040c248240c2c1d0150140c1c45c000c41c600b006c14400f21000039001410981c40c00701003454418400303005200c11001c0101940f104424035101d15101c0e000c0c2d0803201803440c1c180314440001d9480d140c0b540b58088040b0b54 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 546091915 1250 546090665 546090673
    0x12230c0a0219020f132414090c040302030703050d02011109010807180e07020706140309030313051504060903030e01050c0901050d060803161703010302012118080a030b01020f 77
    0x625200c00354980942c0426644401401800301054868561141d04000030480c0010010300c0282ca0b01540c844400b80c50360520308100c03086c041c11240c04025010a403089650101c240e031540500030440c821a04025014020000300000300b04000a908452103c42d4000740709488419a00301070500850a0442c0014210030102e60309500982c2a80c284001c0301d92591790304c0e904d071104021411016180200140d0201d81c0400c002c0c2d071f015090070b0320364042c240d025156040c00b8540703656900001e0000185205410384000402c1020090f5800700ca0750b14400e030400b443c003401c1440c002c01c050401500403034100501c1c4003012606100c1d240c80b4010b40c410b0582400c0b05c40c40110b03a02c1d006162017000740c0b40e4810020a2920081026000500c5451705401283d0060301d8a004544d200c070400d643c3c1924140014001030f07030410764424080540d00c0c6800c1c808010764503428050142090300350702080180d000c0a0501c01c1e090004c1041d040207460070700c0041c501c68012603907911026140105600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 546093165 1250 546091915 546091933
    0x210609060603060103020c0f060105030d0503010b030106200a06020a0806030604030c110409020a0e100b04060206060103200a08040209130f02060901090b0a0503090d14070b0712230c0a02 82
    0x241201c051038000d40103140c0182041c5041c2d02c440d103000640781c800d000d1a40454010012490708100c502407070345082c43c10a00715454003518055038007040c024001400f00041d20400c2c8018000ca6101031440300e10210361414031181001c0c03009500c01e0751080006280000054014100081d585000c2d580c9643c595150b00515114141c601e0005041e8952140c0c54010040140c0d0b90120003d02070050407445201d90f05111081c42035022041d03100d010700c804148010407146801040075a4040303004e083c00f2400201c240090340419060f00780307000c4c0948002c154040115072120030148110320070b417406d648985506042841d124400c8000030002c44801c2d800308010706106001d4840840107042110881d615201d501d44250085880c510014170702000300f051008040203107482000c0d8500b400c1464400442072003400f48651000500132502030000300b10070b103101d180e03d4890b00f003513a2420800031034400075105200f44a80030072040c02c0703c1d0f5800301d66550f0300401220500b00c215001009042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 546094415 1250 546093165 546093169
    0x121811010e04061505040819020a0303080702070306050c0703030b090c1803030427050114300d05040303080901151703091e011815110102090406080321060906 70
    0x1007820070041d810689031100003a800150010100801007191511510f403400e0a04032460030b009140701e9809000300c4040300c005a06c5500204003500e4251405068030f07070b0391102c20380c90102c0380da10060556261400300203a1900d28005000c4840c802e0303600784140d50800c2e007045013882003a1400c04d44400300308809070140b0342102d48800440c0700941600e0a1030350b103003414200d0520540104628600c00039a0310411920b5208003400b5003050803048540e01c0181020413201015101000c004904603400c0500c1c042d00350000e1181380903035000319207007a400d0700d100801d00e400c40d1000300c4c00300c3d49081c041110154180100c01d100078100340c14880903854021031040d080d40a45004942d13000802c080081b903291000c14440c183d000c220b4004074142e18800040c001744034044018001303400b4600c14003c0140c45010890808140d00d800100f152842c180b0324020303c0f4825420b54058508400000c05041c0440030b00700507146910100c0059425040350b0b000001d044038007940c4801c0c8040010118 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 546095665 1250 546094415 546094427
    0x3031d1002120c010b0a030537080306010c050a0312060f050d08071a0a0504020a061707030e0f0f0a0b0606032514071b1d0126070612181101 62
    0x3d061000420058060f070b001c40d0890540b50402d41e0560030009490006082c1842070f10000004e003803002503103280c20310b0700340c0303841415503801000c0d2a00040490729580c49103420f103218541100690313003140d0044c1307030283c2420348481401030b0107401d10034005024418000c6420440b040a4a0310300003000383c0e607403c1400d80c0180c00c01c682d0f544d030030000d083e44006904030b203920440701c410002549091500400140c1c14055108804204003000805041e8010186158014440e0300700464070b5408901da042c102131544000c40c8541c4101d07030814032011400070703507000c2c5030f40981e001000544030a0b061140c588811030b010102d01d8654042403200400b40ca200f118403403180d00d40700c0f07030416407980c00c0c032041d40c80954141c0302444220881120304010311800001401050300003610319011140b40a180c0070144651100920f8000744410985600804560a0301616068031443d54a803c4090680c00009480c46c030031038600040f410404407610840000030390428a03910701d40f45880011254 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 546096915 1250 546095665 546095677
    0x207150219080d110309070801060b07020f04110c0d02010f0606030903020303041205090d030c060b01020c0f060304080d020c0d030b010e090a05102606102105030f0403031d100212 79
    0x209983e074044d08404154480a54060181403000e06203080c60a04142d003519070a800ca445100010003403100143e0340d004074003028400c15500402d041c64070001c01251801108486001805440620b00103a6810741c0f1100b00c400320880300300a6030351251801c40882e22103800003405030b4401c00100b03011951010f410002034026160007840d100090340071400040340c100c0100d011030300c503403445070400c0414007034115988400e100909401e001c1c10009020b00061011007402808000b02150520405500721000c030400e0850a56640300070014566aa40c811010320380080e10b001d010082e190310501149607581e02c0101006050340390110042c0c0100005030040d41e45c1820300d140040d0380c9103050444840941241100060040301645040c00c0c420300800380108900ca02c0c0302441500d4440044040f8010710810241c0e0700c00003407400500d184581c040781107072001c020400104040d44802c80013902240c0c000c1c051a25004001407050880d00d89021a01581142d01d0312044640070f5409021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 546098165 1250 546096915 546096937
    0x4030206030121020411070303050a1a0d021804030c02100804050c0418050a0c08010e0102040f030305030c07080c060115050a1e0c062415120902120d020715021908 72
    0x200d0f80f603595000804461801e0310804140102248000500d034151160301d40c000450b2505015000004c3d00300070002d403191602510902c40d4402e036074195206d00068400d080303034042c640e0a20f410141400350400c8829003049124100d040e1092420900c45e100f6240110307800030003030043c00c02143c100400381c082130031100c00303498400100f80c000c241c08101c18044c05014204503c0035a0401031398500b5544001441a5260b0041000708613041103003141c41c0c01c881d05860041c3d204e4880e41b4182c0401e200341503010384900c10108211414080200329a412a0b1440a0b85c00d020070f11401c4c166414050f0150701c101040c01c60402c50000311158150494160303441c5060301003910306d83d80d0f40d0221144240b00701c2c1d1920360403005103681c600f40c5030b03014058180d501d102c40d20104c00b118000c2c0910016040c20344101d49030720040045448140603140c5201541c002d4641048658a0080d40c0e44aa4850780c1400002e044241c1950f500202e1958068442808030b100e103203140345c135103201691146210071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 546099415 1250 546098165 546098219
    0x204080c12070f0320030a061410060e09100f03060608100b0105270d06091a09120913020c0c01020c09010b400f050109140f030a0203060109020406090b040302060301 73
    0x17400030758040c07058200551162000007500725207a10307042c5d0b0044008090140c1c044402c1c0e800e001494204a048924001c22240c42c6081e42d140e214886d0516495031060b14000c1e83c41d940442041940e821840c26110b8180855036100e070700e0407069064490030440c040c04680104040d6955030740503080030141d07007840c1041704a408500b4000c0b44840c40b00304403d41c0d804d036540c4146010409181040d03c4980302810f001001c3c0e0903d00b0100d81c491013050b000d40300300030000410302d902d510350001030790240d030310400c085480b0120906501e4440076441ca0b000c1c014084c0170341c0000355150010340306050304d09040302c060030503852011184540140f001c000c0b02c89a0b404810300707413696244c040b081e004203c500108045a05d8502980781d08402604100d05001c02401c080c8551521616051413000c0110349000c9000441f6001ca824161035040c0650503010790000801d030020b250b0010000c4560a50b2178055076681d03803684101ca4021800000d51160080004226281109051a1010340742420394 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 546100665 1250 546099415 546099473
    0x20103110d020d0b0f1c1106270d0c0611070302040608010212010608190b22020301060210110304031404120609021003020702010e0909030d0204080c12070f03 70
    0x3956107800841401001d19000160030720001d07807130b000f2481c124100303484d12140340650300b00042e090040e080c004801228101415002d0000e5498400808040500190350700c7c80c04450203c030400c0d40b8486c810307200381070446040c90790400c3c18410f00140d07000150013024a040601c111200f044240d070149480c0700b108030110140e40c2c0c0c3d00c21600104284400140d9038005c090070304161400507071060303081c0501c103010040003040680c00304000c1a4038080014450703440400141d101141054034000e030300340c1c1051f4084002c2083d40214142c9159808440c00c80800011000c107503105d6440d00c00d80301c0c009001007400a4010010000401d01c10302c403807400e00c2c3c1c5500d820f0390500180402607034920b480c4d1104500f50700b00720440310000f800d94a001d40c6020800d80000e082d032000d46220764054600100002d01c00d5100340261841d26468400542d0b686684820b1140e9500001c1174440c8500a5140c4118290800081680c1141d0f134000f440f680a51030341d200d9114110410110700c0f440b40c001806 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 546101915 1250 546100665 546100691
    0x290603210f04082116020d06061806170703020d0b0a020c03130603050717060f03010e0a03031b0201021e0717040603090b0603060907090906091b09050a0c0e010c020103 74
    0x2400181c000500103200c039090111391094180500a03110a03408002c001c1d401c0c2c00c00500d0100e1404540607281401007032000d00d800401401c40e94802d1048814034082c14407504510b40008040711004180368000c04240498961255018030000303501801441940340001e15041c28107600050b04000142040c008050312400c40c1c2c030201e800c9083c0d000c0d05000340912605445403640040080c5485a042ca4203c28402990355014040f6481054078500b03044c5c0580d402d402514883e5040003e5401c052494a805000703000352840c0c00e851701040e8840c5034600e0b4414400c0d20046001e01c041255030030860051a126540720a100780e0b00361041c960700f00c0c180c1440170024002170803150b40c0040d040406003000300c254100074119038800d4010703600340401303040005120003e80d00d0400d800a40000180740100080030032010017010101c1c0c1c515020150040c0c40743c0c0da401c48101c580c05100c96076a00e403441e070440d5031504599010441c120340030707002c2394410081c05114910604000440c5058a01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 546103165 1250 546101915 546101917
    0x25080c0c0f062a0726060c0906130302332503020703080301031a0912040b0a0903060c081609030c0b0715050a0e010c0c020303030c03040c0e04290603210f 68
    0x10810005480d08018200817107060001490071030f200182c010b0781080e01c9844461322801d80114800c3d800410001d9001802c00004c10043d0382c014060b194002d00500607254006204a07002859440c40410b0b40411050004661401b00c408114001610003a020005500e420341016400c51084050110024010600940c040c601134519034984a124509160000750018000e4040b5041001080c090a4036042a202610141c10900b902c43c1c0c00040b0072038080303d29905c084c00d0f03a0304001c0864044d40d04058094021588031080c4810449801c0056809513080c0c0310051200040d141c04104040d42c090282c000d0b644102c0c10321242107000e90011082d1001519181001681c504400d50000300134481c52603a5000c600308000c1410759a00001d440780001400f500403c040040090704004030b000b0341c1c801414002502c40c0702030820f0b0034140ca01d4480002044121007030080040340c0780071000b036080d120300301c010003c140c045817141da034840703110a00c074035440321072424070500200181c3d580c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 546104415 1250 546103165 546103169
    0x30b12060f132a05090606090312220f1e080a030c230610090c0e062805030a060902040305030711130c1101050a0209010c0825080c0c0f062a07 63
    0x38114040f80ca00307100410071254005000315118040412000e03140d510080f03103003000803000780000d039180d0001c01d2800c1c2850340101c1102080328510b40d0b0101e6084812050318027551070301c0c01060b540c5203a00341141112000c2d0300841c1c040da4080701403100020702c203c22800d07541d803103130080903030700c8040e1452613031034034901030350603545805c120104501c0d000d81c03911200c0207180d50001482000500c1c600600310b0100d5010141c0585000200310501c16010a41c441c04d980313400145807038800d13040d10024010b810a85211210380e0030541c0010344901c560082d2130136250800e004d10300e001455644c00d0000e603034042c043c0d42c2206ca800d1078400c0340c0a0900c5400110b644c0da1b140c03001900e41c800d42c92400c496000b428030000038410301030900343e070740c0c000c00f0131481d42e43c00712945a440314810001d00c485020100410042148000c1d01c03400c10864201904216035180c045030003100c0c200003003111403401c0050617034011005021069849001c2e0080f0300011043c0ca000d0744010381200e2080d82010059 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 546105665 1250 546104415 546104483
    0x50a0902150306090906060609010809160803030106030f0c0e06090a0e0a1e0501140d05030f0f090f0102070b0a0c110402030405010e0d09080303180c090106030b12060f13 75
    0x102c100441e0b800c00100e6241c4c08205803003d403101c0c2c0317090000a5064000c5001a504200c00440000c56891041040c0400d081c0a288030b06002360ba580843c9a40e41c0c400d00030100000e0608140b2a0241d62a002d404444102d94035600741d42c0144500344603d54019060382a800158140000780e00e22010104a0082d0081c40700424042c1d0f048904030310110303051040000301450500100b1034400010164100000e045079440783c10f4200e400c081c1e00e18020840d01005c0301c8000681a81e540420400811403058113960848600c4094001661602ca981c810030048240402c94401c2c9540301c2ca4015820038440c40a01ea07035030b0b02042c0458200e80084030200c59581d134840301100401c40410a203028101c1c2ca2519004150a00c0346142d00c0380806001241e03180c448959202542c48240a85200140044c003059115a5203000c01405043c3c1503003480d004201a1502c040010000300d0b5440c400da4440c0128000c1d03440e00130f02d4000e0080c0b424030030380e903d0040343e4030b0021014a80409203802010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 546106915 1250 546105665 546105667
    0x50a030b21100b011803061112070806090604140109050c040f0b030f0f0403020c0d14250602070e0c1b0601120c0e07020a0f0c080f01050907120510050a090215 70
    0x401d02c801c0c1e04a0b4400028107061021480c288812070411030204010f0b00d5008101040004202d12102818080c100340341c1c074403085103010003c01f00c1e4440b03001803184c0e0301210748203495120401400110f8981c0c03d038582c617080c3c180e001441250000d4101981204030710114074940740e900d5024910003a0346811100c80000000203121101481800da02d40202c43c1403a0320b4440d0416980195039098404072440c01071740d002c140c00c0b050019044084900800c1202a1411021a41c4500002201c00d60031610f00341c5d4007590128406100281d03840c191000700e00c07002040d480b00c0713840714415005107440f80780100b03054980703130003100c0240202c0e8003d0070b1704800c0003801d5400c5d01d400f040c9004550443c082e0400070a0800425a50018000700303201c2e00401e04a0b84185d0b0342c04c028130140140c0d00040310906c1854282c1c8018101544444d04c1a16044160340040d80c4695001c0b00750704041d60f000d000d65001114943c5078080e1750b8401c03504070305d0b1440006140d00c8154041410640c50405103842d480d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 546108165 1250 546106915 546106933
    0x1205040506042301110303041b031502030f0702011b1124092503060509011104260610030201141903090303050f0f1f0315020a140901050a030b21 64
    0x641d100903040107090808907182c04185c071103543c0c0c0c0d000c02400644044609040071007012203200c2d8a41c007841c1c000e16003010030310b0031140d044040d50080d00e000c04507a05840c001100244103100b4402c002d03c101c2d0196000450a1004945141c040c1000703a8442c0960642526500c03a40004a8180c2840910910351440c010b00903034140088810b4607081601d00e2090581680c22144080055030783c0314100003a15100c1c500c0c1c0700c3c010f00000038a0018135000180110740c60f0214910950343c882e4255400004c1000750616907240c20381035503451602694404148015801401604210b01c101000c40d4100a030030b058840c1407103003a211450200c1e945298000a155240c000ca82e8008460b1011044a08203200d000b5100d41004000035a40028004071162060001c00f401004582180c040310300742210b018844003d51042d003c83c0041403d940d003085ca074030a181e0595009201c1611010308055403210280d000d0300843d101c04da44241c001410311030100c1060b000c1017002c041c00004150b298 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 546109415 1250 546108165 546108209
    0x10050c01020313030f030e0309060c0a020a18060801091109040813030b071403090d050c0102040504050a020c0c0a0b030a0f09080c011a0d0215070609020607051b09060d120504050604 80
    0x3c038179002c1c3c6008042c2800c1c4424201c4100104640c0128800d40d00943d80f50036900b04d10342000390050000b5480701d122440040c40c03013070021300700810100240082120556401c5020b00303d500c0004001d20b003200210406180b8503140c500103a00c2405024614984891548904030039189900101c8900c0c106100740f24006500040030b549215140e02c1d00c502c5c50600481580d0744144101002c820840c001a126900c402c00390151002054042d105001d0340c1449810074010303410400c40070f0301602c10b50034610403e00c1c000e680c100483d2104030101d45952034010822015000d80e400d1149060344401d0701c8800104050000c1001c107620400004400703019204404d011a000c4091a10800740015145d0140e40c812040648580102c500c3c0b035515440b13490044007400c002031001e54001c0000c5900c40902c44045800c0d940c01d005103000101040b5800200183c000c000d07075603550031100c541207031400515100a4020150300c00d080250415959900051003a403240d000b4a041d41c0c2e2109001c000b017 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 546110665 1250 546109415 546109427
    0x506040c080c040c022113063504061113121104110d0e0f0d0c060b041e020a030b0402030c0c1902102102040603020309060a09050c10050c0102031303 66
    0x30000490f0306000d840e0750341100a5842c9848406002041e400d2500303404070401401c202c0350059240804810266500e48020b080246c012080f00c0890411010108080a10070300c0c180700302511600c00601030320b482e1910340007014199840508900e08012540500c002c0741c0c1054010842d1000c145a500c0030740c90a51885040c036010300d80180e0070030000c41136000d0038000342e81c1c0400346120f0000b00010700e41c00d25450080c54011584180c094800303504000e40d848070528410b54041c01d4103001c0b0904c024184070441c0c1b001010100c01d618003150b070240c24400c0e6001000545c2091034081349508207280010100d07030050700d0000205c140010003003032210003842100d002d181540303064044007107a5000719102644035000802046030b0b8480100c502c110b001480a580354806004645403034554001800a5009894020a6209400014418200500413400300642c8840607020307090003d0b05110410a2401d52031083c003c2c1401040c0c00300d0824405140b0980c0c600c44120722602c4036041c09440c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 546111915 1250 546110665 546110683
    0x1801090f30090614090d030206420112060e06100318080705070b0f03010f0b070c030201050c0a0f05030702010e1c0318050301020c070e060d150207020d0506040c08 72
    0xa4032803070101e20180d00c1d030001034082c12510716003448101444032641c00e502510982400d10742c00007800b03244030140340c0d00043c00d40c0300f8000c051032419648201c8071300034005600700120548900140403c40850f07169a074010380000d4040c100725008a0342150203805850850300850310341c00c44a0108426454000010652440241002c0107010f4020b40003805100100e04d020340100c000240207010071004002c400020030940682c0c588070020280c01c2919644203120307854003115000404030f030080da600100d5500d203606c003c041400398a16030042d980c50b0804a01c8501e14080c00b02e00c14085101441c10440c524405e0300515500ca2044c40090240302c030741000d690180b036080c03000400e919138207081c840956415051031071400240350070004d03150000340c01941e01940040342d0003081940018040056034202100d16840b603550400340031070011846400703441861052501d13803a545a6900a1002e280003401100b8400201c0e01c0d254540201564100e48106000f282000440c4060101d546 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 546113165 1250 546111915 546111983
    0x1020d030605010503010e0c091309212012071112030a1205090c0627191707030c0806040302060a110909060120010e070e09061801090f 60
    0x1058500b8400000c01e1808140030b11f01047c0e03400c5000c215000c141c40280c41041e04000c2c003a80c40031245600700405407080c20700841d0a44020b2031452079a601e04038100503c15000e55500c0c2d880340a91419038400c0c0200350340d004460084059240340c41044000074407400303005102201c0070002c400188402001140144115500140a00460f455003c4114001031100b4132010900307480390440c00d400c060700001029484000043d04425202c0111807900e118070b00c07480d03e9440b00303141e04144001240546120040031140700700501494101c4924400c80b41348100448070000e450b96a40c00714030596803c0a1301139800001007008149d4104260342c2d22040164050280b0070100c540c5011501508240c503110784452800501642d01c5042488100d0007a22071003401c880700f10714058001d02104d000002e030b9019109000c28540b02c200c4142e4042c00302000208000d99a01a140c2a100c081503034074089552680104804180314002031840d903406112040070300c0c02c00380398902031040480302c004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 546114415 1250 546113165 546113171
    0x60605030727021305060f0d060e01180b03121612030914030a0c030e03031c020406120b0a09090f050102030118240306020a05040803030c04061116140d0b070e01020d03 74
    0x1562038110013210402c659082d42d010b41c40c2c0280071070034001d0b03010342594031150368504a00011482da258003001e0403240d61709100d03c94540d90f8440c07a419103000d03403a41030301a4849004e898443d02400002c00300c000d203101101c100030311141e0764a40e07460324562141e40065180c02801d0148030005e003000d03044400883c002e5151203a503810141c007540d4580c4d0041d05126029864920a4400380221860711068140000400302c003122140002d4005000b9040010b8078121060f20b0f0340c20f07034480e80c00030800050506401030700d046040400f40c90444c000301e0f0389a9040100000252017400914003820b14400c0110046901c42021400c03201c400602c5100d01c00c660910411489112004100382c03600604007507507035043e080c01030750a0310a941c030141a40c0b00000400ad510b525000207031040e19241d503100c480211400403920382e1051081c00341c6201400e0f03040308004404102480219003071006c2c101001030705913a01c4201890808036080030108900803000780003503a0510581c001c0c1805c6003420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 546115665 1250 546114415 546114427
    0x10e25080f010b09010503070f1806151d03030f03010306020c07050d05242e0b130513051012052803080c03071704050f030a0512090307030e04050406060503072702 72
    0x400042b4440c501c42d040324500200d880c145542c01a00c0503015041d901700c1c6998000310000d20300080d00807441038034004a50404807502c0c01000301c9144840ca43e0040b81541d0031515080025030011201c6000c17886002400200340d03ca11600000c1c2e80d020f07070b010b042145002c0d003048886c03284d85c10195003208040c8041190451401344945c01003021021041c8a0a081030381c0342d005110709030007200c414800480d04003804460400000180c40003900c0c071540d006200d81d00d0006695058134100c1007101d40c80024018044519078402c61139000790101d400804000303414850a028044500f014404500300c401c0a0540120b010350300008130210b0340789946401b10700104403642d10743c4034a1800001c0700101d4140030341000400c0303071549884140d80e40e80c59990740c0a00a98803081d4041d140c04ca142000902010003c42a6002e503a01038444070103000c80b440c200710042c01c00600840d850b640d5200702150940f800c000c900094110b2030100c5203020a0038000110781e48002c801c900c0e0182c010025 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 546116915 1250 546115665 546115679
    0x8030a050a0c0c080601180b0910050d081e04090e0c03030915071b0807060509090a0b060c1501051801030512090109031406010314010e25080f010b0901050307 70
    0x1c580011685140640c1d0001c00307803a046a0100321680000701030311400c0e00114441d66101c8040c0340000031a0020081c10070b8460030700844141c01c450407080103185c0e041c100054101a115084014401c00100d032400519290302a14050001c4419650800225042c8001100352240c54a110106801040e41c8114600080d60b24131a00c1c43c01c0d40105a0071244c0019140003078180d601d03240d030010000c0180c050415010412201501c00d5100300e1081c80c0001550034040d1088904c18480940800080e948240410340600311040c84190400010410317014001c4040c0706d00c3e60386103034040084100c1c1d45010104408a0843c242c22001451a480100b0004100043d181d0141c0784405c50140c8550b0460010380d8900d8590340083c200301c000c41c502c00880d40011a855060b20301c01c5691821500c0700c00c41387e80c2202c002800c446a00e52002520b203d2100644000b03101c001d041142d190b070728a484d50b10440c14000a240304600c2c5170b44440a00d111440c1000c0d8290240c00160b004010741840c0c050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 546118165 1250 546116915 546116917
    0x9060819080903030c120721050732060417120f040f02060d1410151107090204030602040e0109110322020d0f021009060c06020c070e0103140708030a05 67
    0x4001008141c001031000d105031800d0040c0d40c1121045001d0783c80c2c0601c1803502049503405000301f207070341c483d510407003032101607140042202000f1240d130352600f01a402c0e41c030722800b00021041c00400c180d0340c9041080b0b468034002c0e1020007907010b601518043c00d180c600b4000a401082c04140c101c102440f411556a034107621456100848098a80309500c542c180a00800c0c000340c402fa4101c13500103039404424420790401080481212100c4426564144481000c040c060245041c6004d51243e0802058420801648440030a0040e2580c5590f01d1b52504200d03402a48201d0b100ca8010a0401040c207068256900420780c52800344004203031000c004060b440010200b902e140c24140046a82410502e03031400750990207010301001c0e007005d04085030b201c049000f0403442000c010010040003407041c200c0030104c50a54075856201ca2007607641c0c0010790403c030905038031446002c0c00010380902420b0440e008601a0303450204010541c0c84460401138990042281640304000d2250f0b41c69000b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 546119415 1250 546118165 546118213
    0x25150c1e050a0e040605060c1605010c0218040c080105160908010b06042c0a060305011a0f0607021f05130b07020a09020304021c06050702011404050607050f190306090608 75
    0x1281510800c008100040c4c010605078003c00e8205002203030107007029100040103162052400d000205680d41c071001124407149292009410a042c0101c50001c04944640f031038210744a80000044682c50720401800c444040758644000064400b000c468281c1060540000e068800020b008144a200c080381d060300c600c0c81030503010390503c1c00c01c50b41e58000d14403004400100f4100c9817090308000242e40c0c0907042c2400241c509500e80700803416209840201e0001d4060050308000b1003189a000f0428150800041a0f800c03200746981c040c540140c1c0242c2c0d0901c48920384400d516009801101001903005411450340841e04104900150317a649103820b088036541c0c10090303503e60b90361001c20343c8a0541c0f81c00080c000c84641019040250300d4003c40d10400c52a402080f02888580d150041d2040560780035156801c6640401ca14034811001810030300e0005280b1890050070516035030024407201c940c58002a41d54006200d144424020080100b144400400e00c0f031400501851040000c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 546120665 1250 546119415 546119417
    0x130605090a061407051005070f0c0c0302100c0b040f0b060d0b010b1606020d0b0103150b030609130b1503063103030b041404020f01021225150c1e050a 66
    0x10ba610743c10f0415100c0222003900780e204050340c1c0075201816040014140507100d49001c1003000030f030f2400c10380c40b92680f0740e0341c1500503207541c402514540a002451980c1d045040400285408040100d8030304072134103029922480842d04012980e061000401c8409400c1501c180d0141215802050307165060605556440d0301d69643c800f00d1592400d003091921100070100c034008150051040e10540c40800c41c00e8080e01d0922440004c100c09411440050082402c080d4090000c505a818039100031503211116215443d091284c0d9203644d80080070441d0141703528035020f01d9003506400c06001468000c415085c01110204e003510104664408000c0e000b00d602c80080040d10030725200e6000b000140f00c0c041c00810a00d1407207004c1c6102c0c014221026030155000b030707803000c40c0c9501c0003c5906e0171542c40e80342d441c240f2410a052000780d0340b078448010140034241c21800c0210360f100c8583c50400d8842c0d0400940d10304d02c59070107486101002420b0590440c520107540d0001d4220044031000d0303110b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 546121915 1250 546120665 546120677
    0xc03090601171501031101230a030f06080f07080114070e06211302120a0203060606030c07120c12030605060d0f0608060403050c160302060d021b0f03130605090a06 72
    0x14079900b0ba26094030400780b02c40c1810450000400c2c080a00704e15000b2040a0340c491b002c0e422a00740640782d004000f100310403004c00c1000300b00c040f11b200e80e000000c3d02404010100f440d6945200c100c0c42d01c1107016440f4600c0c0c00100d02007210400903c60104901e19a020b25000d525254070041d041c1046400074500030301001890944502240d01403003014102c0d090002030034101607020310414104914124007078a80480e21880242000401c1c000a03640103009200c2903444406000c403603007000c0d10103054180c0034054040014468150120180382c15915500c44415a050903e0b4a0f044040400103251901d00c081c00640c48460403503550b540301c40004512042080904c6001701901e80c01186103019000030f1004040e0710000900c81d94200d070f0102c07441c41404001d980c050300c603d4400258080c404012610f0000210b4000d010b00e101810401010301014501c40b9041c0016149040702a400001f0b10160091f40a4010405040c0c9881c2c100d00f00804c2c0c101241c89040540140418404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 546123165 1250 546121915 546121949
    0xe070e09060d02040902030105010f1409090309040b0d080705150a0e100e031b07090608030a0207031112101508010c12051003020a0f0602100b06191b050309090c03090601 75
    0x1362504201c0c0d101e079026008001540c2c0d40c1103601d0704511035001e45008081e1602049070246070401c4664040d0160030080d600d01421401000014002d40002a800c4100100c1210206244901904160780100b02628040c5c0090041c04030078640140040c05261520111700c400d44000240440308901081d80080c0d003100c0280c9840c594002d103503045100b000f04407100401e0042c04600441110359071401480f90036114084a500c0340220401d41c070040c0e02214007000450082c5003030341000d00c00a4100300b2900390300e90702e140c101001490080e00721604c2c0c076070907040020021400001405008001c00a003100c22200600b03905408490031050b544801c00f040b80442d40c1030f2a04001c1d64024126010140c0d0340f4160a81c01c2c0d0144102c00150007902480303501c1c3c20301c5000300903001100401c2a4030b0031426202003054183e038030000200300007007490745148044000c40300d000c0403800751000303640701c2e41c04034208a0010002400b1071300c601c0040c03061081a510002d5650305490800d003041c03030541 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 546124415 1250 546123165 546123169
    0x1090e04060f0204171b0105091f0c0803070f0f02060c161a04030c031214190b031b03101505100201020c0a1a160503150103090c0308040e070e09060d02 67
    0x8004d6810001011000310303410080d5801c0081d108000095884150ba91603212900540b8213000d1507040c0c1d82c200600c02002002040410040d960f030701501d00700042140d2142e140c01029030070444510010401c0f07004455240c80d001140d09459420520040881d0b15066440746540d0103100010540d0600401c0c5010800140e0861020002400c00c2140e001d4a41824001c00144071014154082542400b004400714140d01492403400400c006960650721103900300300604d0102744081c003c260341c8156100b0640d4040c05144038604c1c400b4008142242d1080405082c600c0a11030028190314001c0241d00c10a1140c3c50340d411517200f01c0d01071560400100c0709a003e4031074080703038000602800000808124800c000d550180c00158440c4c0c0d201d030f54403540e00368045845c20419021075130920007d0700c8030940705105015841c0602d0b002c20032040642d10310060f02102c0c0c0044070a8400810309004c08944c100070301d68000340701c0c5001d4900d030002c034001c01c0003140090204d901411945500d10255 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 546125665 1250 546124415 546124417
    0x42070e0105250b011706240310140105011115070f09092306040207030e060a17040c140625080f070c030b130b0604051f031a010501090e04060f02 64
    0x1d015414010810481d28101d01030f80e0742400f0704401c5410a43c5400041200026094400c10200344841c1c240340144400c1c40070048030071911541072148001d0340001d016107014404050f00800444182541082c0000d030041c0d0fa500c801194a034459200031000c0c1207044441c9820241c141440304803103210140c1181c0c035120b140c0180c4d071054140443d000c03200c81700e0103494500d035802c03505d0f60f0115140c05e400c000503841051009400100c070340c8001e0a451800900510021840341800c2240d100b0b83c6100c07081d4410101c800340c60450108800300410309800602e2421600211417261400080701e040e02000301c2080b15000c034000f2058004e80c00c20420804941d1604944503010340c60f0601807401c2d220007107250008442c1c1445590114080c04081c1c41d204a059038005d141e9113a680e1200140f10003410001e265403001402d2074036841e48206441c0800c0082c6019000e00d05031404520a607608514060303000b68104660100100101000e0801282c0c019a02c101e000c0b03005210f6103180d8000e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 546126915 1250 546125665 546125707
    0x9031b010309050f0a02040c03062702040f0605030f010503010603050304090c02120f090301060501020304180b1503180706020c01050f1b1903030f05090d1142070e0105 74
    0x91007400140f20341c1c0d0200103503505ca0301e031003110103110114074450201c0c02d0340e040f8841c44550000c5900440c455081d4036000c002c5984500d00c006003880d0741c80516030b1802010f81d0000001ca14000306220030003a00780002c0f07000d0704064000388031891071590794903601d10940c41802c041640e2080e082c51101d00c20f200b032001e81001040d1141d114085928040601da00c5500414401c2d80303012000155540080151012540e03009213413031481c2c0403000400060144102501e6000400d101d44207006070070100910701410000340c1600d43e44900c5090145040324a0304034000355840784010400d40da03840821140c443c44022207003601c4048010101c240005014100310480c049c0001c0c007140340c0340030b595604000b0301951b414000c04c561409518112042034a065419802584018443d98042c10400007664071b0a800c441c046c000b003100080d4001c0791142c0c624181c4c0920001403031007407000310f01c2c2801104000c060410500301114040c110440c4030326854180702010a41351012002c0b07100c00e4803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 546128165 1250 546126915 546126923
    0x5120307170c1b0f100902010306050a171027060b10050d11070c0302090603191203050606120105100909061701230a02030c0c010903081b09031b010309 67
    0x1d054108415080d07950740052040e2041c281c04070018681d0050f000603100d8554960707201070320407484010000c0001d000d400b00709038145134881ca00020b03113464050f00b050040508402090381c0d9501c1c510b41c5814041102c0909080300d06180c541038a001d500c0180300e03280140341450031010081c03860000003034150401d182d40d200c0d00b6420f416802a40203401040c1c2d03020342120400c5a41c0c61113400300010b000316407000d046c1258080d030500050508002d6107400ca0300c020f007101c0007041e805910784164040c011040365a200000341c84415107802d402503907000902100d031700b42000c05074212044e0b5110140b141c944030740c14156078015806c0c01601254003400e405c41c000d025258444500507241030188402c00240e600c3c001d400309004600b2030b14000226880d4911801e0340d01c1c2e940002c8065040948603544c3c1039030801c44a8400707403091241524440c40b03030f1207110040c9840c40201a41400203154010642c0d01001101083e51f000704804103188441c10200c5204903460004030000c0281143c010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 546129415 1250 546128165 546128207
    0x3060418111207080705060318060a09021008280209120102090906031504030503091606020a051002040b120c0c0a0f290106051620011202040305120307 67
    0x4028000e2050524000740800c0c1d903031801d01c000c0740c2070050351000740d80700351015500208000d101601c1c1041c001c5822a60404107000295a011840341c10a08150f6035544065501c400980c114188140c01000c4203d050805a0041c5401140841014072070303c1d070440400701c9121043c074014401d0f41a15203240d000761100307803509030000140d07000b540301a18083c440c60102000483c03500d400940d004062120394408552910380340e03019102d9820280c400001401290b8508000c8441000318400038100340d4010100703ea0703a4101542412110b00f0b03a6540280100006c0c04060b2408088a0107201d8a4003408810707a00c290585004e4042d00e901002a400b400b486001840841900307045624012147d50540c00400702c181050400300d42e40c54854404c0000041080600940180c48000c250100e481d000700055948c0c0e03c0b1a66544505c59551140404030720070704d503840503100c00c00c3d079800c400c21890301e411a2901e903a50481165180c20740000080003e4010b4482c05281c0308102d0303c01484 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 546130665 1250 546129415 546129461
    0x1205012117031003051203060612070201090203100c1106061c082808070305060108011203120f1d07140d1502040b070b090d092d0905101a0f030604 65
    0xc3c00032990a2000352214410324212680d41c0140804481c020400106041d00d06440c00e401031080754001007034002035560714140040035803424860091002c070b88200000d00e0a2042801810b5210807a481440359813200041019075100d80c44000e01c90121200e2080c01030140e4a4005e02c18801c80742082564410316005d900011440c0c1980480c040313250f141c0c440c407540d8814040301280d02c212480c034000f50034140100030304558002d20341360a03402480e1040c0c01e8030007078a415094419281c1034a03415a40d03500c454a8081442c84111122164103014101c12882c25502500c05054242c0e00740c0b1031080c0c00602c1040065a03024100015440d250541d1038a68a044144035070304021425551040c0b00c42c0051a14136000c180316500d5007844d1904080e071418400200082024403014200050034581a90088016860b1070001005030313840119240c503024103011a0304802e03500c9510103010022000740040d6a40060320300e030894403030701180c80b65106400140505050500000000041402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 546131915 1250 546130665 546130681
    0x605280b01020123040b102120130b032a0306070c0b190b130617060f010b0c2b03060b0a0c060207020414090d120501211703 55
    0xc1030440382400d80007007243e00c44138011890030420003040d040103001d01344001800600b80307100709500040105a240f8089444508440381e0300d40d42c2c040c95100701c810b99051010091051100c140c050301140a0054030a0700b900860744501002c488103044588802d150172094604100e5a4141c07218410381d081e01d0b404090b41062100301200803140a8020200050581405580f11001180d40180201042e540310b00040d21840e281e4900d645071141c031290030440079568200d010355401c4c01441d0008540786402d4000040004907404610280c0203d002c1200f05024040854112003000240a5885040d65079a900b014502e50380c0680004003c0b980407800d400107011055100042e840400c946a1144030a090b54010320211000040c0308aa2140000c1d00c1e0b44c010785550341c400307032011401c40e203103d11401d14290304840b010b400c2e521805000c2d0350941d000c1c075a44000036a1540400203941402a144406003210060024000500d0030720b40401a52080704201e400390214011346900306801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 546133165 1250 546131915 546131921
    0x131802030d200c010c0803040302010b090a0b1e010504030308181006050108070914011b02090408071a102d0605030702010e1b010c080409110a08070813060528 70
    0x140c80c444070612040d00c03204102c0c0000341043d401005071655035403440169501486a80010005ca04554070358000d080242c0b14030707003994021442982c01150261001051210b0f19404035001c0c3c440c0715a4010748505030740c02600311010340350146400302007079503085280070316001031a000f03150500c1080000341200d82660300140c143d41c001d0b03951507003a403a070305021203103590240220180c0ea044147d540c6d07015030141c00710841411450075240359500841d00007030401d030f000319030680e0354200c00a40c80081201c0b560701c25485000c50800c403103650400c11640c00214229020310220a0403061080740c000c0c003580c1400400c2c00410303010300000c0303440320f034000c16030741058501c680550700744040d10f61030724008640c490300050312002c41c98680c2c489800440c0d510003860030031780b000c034401c02002c2a007003403138011240d4510101610700d96600300048010300340c0c0e00c01805281080002c005129080d001c06a041c06200d070000d00202d030030349a04103480640440c03105485144403490740f0342420456a50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 546134415 1250 546133165 546133187
    0x2c1b180c07150510081507051818090c1c1101110105040c14030307260913060612050f040204050408091008011502060606041710110909060a05131802030d 68
    0x6213140e40b04903940c1074519074079502008907a401440f4500000d40a5204802520b40900c85001e428900607400d8041001c014a402c140c94000c0d00107010411711200400400c400342c0c40a0300e101d0b07030020b01c100006081d000c290600400445000c144244a0380c41131810864130b080a2000301300608051a2199011080b441411016440f039060000760303150110035a400d1540002005062107410440c04a42c2c582800840c51507003024000342520b62103080c14691000d034001c0000a5030780c1005009402115000c3d88500c2d12403c1508200b640b031700b0000303042c4d0020750507078012906031124502a0383c10301500800d641c0004042c6105900d55500c100310354100c541f101f00c00741c001c000e005805c03030f12020119045074200e4001c110070045507045809031004d020518041d684c510081f4445c00c42540c8a0400381e10324687d000c40c00382e01034a4210900e540010701280c4d401100d501d0000402c0c6001404a5100100781d039450344c00c0c000d0030b0740354a004c040b103a000301a1540c9031503100015020040003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 546135665 1250 546134415 546134431
    0x70821040f090e060a0203090709110f0a0206070806060406050a0318080307020a0b150108040f080f04090e16080d180302100206090d0e0105120403032c1b180c071505 73
    0x2100840c44c2c1008a06c00c680c050b8108101515a46080107112350180c166803886804024042141864101c048005000e0b0411254041d209908201c000240781c0d06010340807074400c450401c000c206058215044800030040380c180230941c3c407003421a50480c0c0881c030720041c240403000401c0218003640400c544c1307603841c17040c3c078038000c1e503218440e40044402c103014001e070201e112480881c020440000c0c68011003031050321250720313007407050700c80001c96000707944450794a44d1201c050700a06402407240818141040380e0713801e4010300e071903960f031b5960b104010301b00d0500c003012800945010428401e40d02554000d0300580c0d8072101080001d6888030100d40b031200d5030180ea0301305416144680050070311744105075600341c00c00c04c0248240165001c09401107046c596034030241c40742d10609182c0d07107480c1170301d00803001a241d160402082c20100c40c030003021008010200803000075035603005174070310b14040c241c42c04000b40e907603810f80081407003440d01c00f80c00310302646615141080550801c91044c021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 546136915 1250 546135665 546135673
    0xf0a0c030b0d031e030e030301030b06061b07030c080105040b0f09010e03220807060f0f0504050d03020a02030622151e0204031b0312030b042c06010602070821040f090e 74
    0x20190032411202e581b403640d002c6810400040000c0b55086482c560014001030045160409501d0070340342031401c3c0c00f03480d80240c11003001003003408000e400700d4000700745510003449185015038484001c51070050945080085440116000c40401d40c00120100310880071a0350b2145a07288151aa80a01a150744a1714040c14081b84143e404501141112010b450301190000d60080a48041d034041480c2400c11a0500001660341c4d500d04d00080154080d0b0080e081488a074014142040070081041003400f18605420000030403401d10701d6441c9810041e007410005104160002801c02e171413050110180101c10800c07a87e95650050080724454503403500c6400c80c105908494a446104c0030f889440725821001005010b40c001200de503200400004494800819150002c5c0d400960048100700418441c2103034402003101030f01604540c001861240e207490806652500c241d500114041c0c2e031412080001c5e151082074601909241c1c000c819440c0e19000300000400f4044e03000b00d42482 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 546138165 1250 546136915 546136967
    0xb07060b09060607080d1a0405010603090201020c0307150c062a1119030e150d0903031d03030711070902040b2508180d1203050417030f0a0c030b0d03 66
    0x5414400c44104c2580000c0a50901c91390406c880e000340803410b0403039162a13104804200703a0350b0b00c2c0b260602a001c2c03030f28005000005030000a00d0280b000e0540c40c00ba50018405200c511f0040e03070151143e0281d403400e403800403050f2911801600720b401d0030300d140f0461000580e44000300060b0300e01001d1081e40d80c8401d030400d1001c101c0c2d902c444540665031503010845215010910070000600341c460081e02c80e0b01c4030a03403da0000b045a10024401c141c20f079840401c0c104240c0c1c180036010004840300303c0b1601c0f110741c0c2c49442d0303120710000d03201e8424811074015003015100140005802030450502c1103440301da442c4203000c0940d01c52a06152000840c4000e1440702c0c0e00c0c042c086400641100c0901c1c1001510180c00120795107601c4d056911954140c3e0032070004008001d8a50b800c80036690215042c200f034a4084054000e0855610f04181e00740b0401000385106540c4a9000d040b07040c0c0450610841c1c20150010443d00c0d086076085020408074109054001d600120380210003103102131100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 546139415 1250 546138165 546138169
    0x1506061403010b19170a0507110a0c062106060f260403180b0f041508010b0f09010912030810060509060405060703140c011e05071b05070b07060b0906 66
    0x300c000d000f59944504144048583c11103018504403150390b050030700e603e091041d6080b0040380401291102c1b043c540360000c1144681d070080ca48581101d60744000d0450744081d90301c4a49240f003e00948013000812100071007c1030010141d28000100c440b4204002510fa03013004001d2407555091901080c2520000500480b101640b039041040d54502160151500d40c0c0850340581d041c51030006000882d100410f641d41254014600c078408200d145a80da46080001c0d03c0364101e1041c08024040160b004006000400c4103c501842d10000095500c00e20900142c50000b900e07000640c0c00742c01903540e04201900f0410312406030001002d03034202d0950b9604c0403902da1268100803604244280800c2045003007003c080c1c000e46209041c80088030b13250200c0e4425580141480004580d120b0309c46e800e02c407a001c40381044001002200b80034a01d0007002c00303000c3c04500c08a2842c0425450582c406008042c0315240c06880c0031800c0b565544000d050202c090804001050311960903040414258 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 546140665 1250 546139415 546139417
    0x70b16020d0e030c010e060d0c051803010e03160c030c090903080603010509030a181e060305060f1e0f120102041409040b0711030c030a030f1a1509040915060614 71
    0xc2c400040060030804440300045650030180c400301d6030005028001032007032044174080c1d01507200c101e81c1c038244c2790061703034a4030f04071520004001ca000764500310302208284c0000c01200c150200c0d10810086894003031400b500808580d0384064100005280041201c4202e5081160880d0283e600c00615403503180405003264003e0714270f400c81e940104074139920381e8043d001c00501e031000c0002c4480a243c0c1c2e03c08050401c40701c40383c4052440f030041414031446406204480d00450287c0c1d82d620b150b0001c0001c00d21201c1d0300c8a102c4000b0105000f1600c0d00c0d5280d80d85003215040107092504071210a180c1c1030301030341090043c07403864101e244807240c440c20700c6515540f0030354000d0707116250340c2c1380c1d6170303040c0c84450000f94818054001080711090288080004064103c550399001440b840422100012a0310f0b41c0c0015220b007525a6000d000c41d030360720105c081000d44c4412041e42e1402ca05001a0090202d1030005050300317415040c0000c40340d520f502400440700c40b80c5420007000029170018074a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 546141915 1250 546140665 546140687
    0x4170705040f02040e1605301f06030c0804110d0f030905030d0203030402130c02071208180f030c011d150d060501020a0305180f091018020c0c090606070b16020d 71
    0xc2081c00342314101035082075258102ca101d42e211030300e070f0604000380507002e02048400403904c8400c503564854000008070b0150007020740f40340400281111070001001c148003c0c1c4003810b410720181c404503ca0303440c01d0740510019880300c010350410116280180110440340700e041d11034050000d0102c109800481140d110b944c1c000e0a804589810200c010014000700a0f9081141f02d291000314024070f14840c04c0080500a40721561214518503032054240d802c401048d014081c48601c5004580300020700110903082400c0003a1a0442240315200c500c501441071075203c14070380110b0410a00b090010045481941802c0c0300c0c0c0c0742c54400580e915000450001e0004108000540c001c62107055807800c03000006040521030b02c560800925003035415100c0d00c03440c4440403400c1003001141e00443d1000fa40c020740540c10907018560458981c10300300c1443d401200c5d000001985903451000b01c5036859030041d9203a1807400c180071040701c00e54254944c103015128000307003805000c0c02145810301c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 546143165 1250 546141915 546141917
    0x1005180c0c03040f0e0406060609060807030522030c060f0605211c050d150515030a02070f0516060c0b01061b050d0c0209010e040804170705040f02040e16 68
    0x11003600e44040a04040e4020410110315000034440862051641c95007400240340034075002d4103030b040505146080314540e80c403a0b07092243c00c0104203e0b454200341155801102e82c24005181c1d075070001a0000f2110016480c03200b02c1c1245400420550040c032508041d6000d0301003048004a01411801190700724081e081d0721107052481801c80c5c25200c0c4802140d80004029a5000a440e44130081e0056101c206c43c004900c0100d82085001103610a05170b0141c5d03a242c4d640003051412010030041210b84e0816039005900000240c0882581d80440e602e03141c0c00f40d400c130800091400c1c49600c41311a100808001420400c000888070b2081401c03403c92500f00307040a8441c0d190460584450090109000e88240628100e10200d80180074641c610142510384000701c9142d481004030300300301604840614050b5809120108041d40140d40644242001d0824001c4242e00c8039464100c542d4800b9501c2030401c0c0f08140c5500c8641c024004960404210201030744441c90540398861142c502c401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 546144415 1250 546143165 546143209
    0xb0418060803031b04051504050405070201110a030b150301060c05330901091406060a091a012d120c05070515060117010f080f0303090a15020d0e01051005 68
    0x152569040200103040700c044401135840c0654130710110f00000d0350048003280c414008581003200e410701d03000301540030200b071008210b01c1c044000c0016607400b0b0808040200350f1b45c0c0202c000701d070f00e0740031032184910420060b190701c80d80d50380c800410302520741d00101d0700d42c064080086000000300300f40101c0e42d0304440d080850420200303540e29000c040107001110541d29407401c070300881c02d030441c03c0b0b130f00c030701a840074041c1450400c0038010350f098586d0001c02c155240480080000594824034a00305200b440c00410007041c4148081d1407440c030324400b5940c039241c007960843e40342e04144035501c20006840140700e014216481a261400f42410140023500031180c1101040c03040403225500120504000313015041e401c100b4203008500740c0090070080c088030005c1c0109035042200705150040c0c0b10085143d450300200cac0742e44030b110410006060707200d0045410070b440503d405a901940004500b0821148008915400703800142e9400d0440380b0100400309407800d01a50354804411040125 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 546145665 1250 546144415 546144421
    0x1e030803071e020d0809190210021e0a0c0636120605060f060f1c09120e010905060a020c15040e040f1b05011d031005010b041806080303 60
    0x440103a80010401d104021441c880c405006049400740c201000c034580c01080d0b580c41c90000034000c050b014003a0f038080d92081c11f4060007240e02c5010107141030b6050b107940300a901d52000582c50281c0000c0034044a00b9040001c243d51080025841500c1d80110001c902580d560401a10101c280d2a4618081100c0e01c1e0420380503c2c215040e400580800b038bd56908d801d03900d0414580641d51340d80d00b141d1454982041c81001d241602642003203a070115415403a1070080c110500e024410101c1c22030f42c5000714040444c016120398088801c460700100007010702c251013400208115000188036011500e00c44002c0782c03a08040c41654844280d82d0000c1803428180e4003084001800040b03400c2c00031108101c04242040020702440c0160322034041c550000d0b06034605207000b20182010011035241c603031006c022aa9210000e407404071b07844640c2008019891000c60b041428810f45c45041c5401c24000003406a034030001001142c40800d0381c14040c88542e50b038001624007501c1428500d034418008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 546146915 1250 546145665 546145673
    0xf150925141605120301051f0207030c0e06010201180b27160602060c091e1804030e01030b0607021f11010c200604021e04060503010203010806040c1e03 67
    0x6880800308a0741080c24905441c21071101566022088148080000b51280400c1100421210480c06403691207541190b04010209050400c4440f00c4000c0b5924000855515030003488103c02540d049640306003510f4941c00340201000065460310700541c60024210804d201b86001c800c0b50356800071f03400009841d498007000740f4442d03c0e850a03200040810090400c508204801495000f162000c90807140c6881c4000c3d05080b002410f42100320b0b4100f04440d0b0a0390f40220410903403a1174003120180c86000d0700819040302403c109403290b1454901070005140d002120401440000d907001d002c0001e00c84180140b038001c80100035003020342e0394041a8001080000c020592480b450100b2044000c1c0c01c2c194251030b0300d400c82c0008500f86910a6180170400a0350f80c000f00c00e0040100094201580070030b840c0d498003c0c0d90341c000d4a9000342c10f05181c2e201e4210300b0080400400a42d01c95131980d1056440d031070305403012110010f030400001060911b2004055554140e594416141403550315 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 546148165 1250 546146915 546146971
    0x4060209040209031608011b05030403080c0d02130806130507181e09021f02030a030c020c06040806010e16020604080702030c090f09071a0703030b15030f1509 70
    0x80ca9661058091000b04000e8400f080410643c20040c05413414092034204820b003100c5481803241c207040c075230002d90f031250fa403c0000c0300e40040c3d051426410070740e00c2007130480f503a000d00303601081a18000039580b0080741c2c4000008082d200701a00b034032150788a80c80c11000600300c07140010071541100c0c00800a040c0c040a007050b90030031006020402d5210200404404c100204801d0320503655003d050381036082a000c40112058034401c03801d8802c1e0444c102960b6801030056a104140d160091103500c00e10900c075040e06051701070300f041d0325107440754805503c0d0803003401803109a00040d00003038102c0300492002c202540140d00505a2922282c036100b030725501c016426a0944902d00c4001c5041d00c41e070140500c50041d1604c00d0802d0704219500e01d080070400c1d8130400b0461440084252a0000f140403640041d0303040c20000f8035180340202160598461204a1800301d60100410010071a84145c45100c0e94240880d444401c4003039003005103102045c2c40085521025070100d000c000c02c00c0d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 546149415 1250 546148165 546148177
    0x309100510140a030822140a05040510090632101209051207030e0103050f1f08030a03060f0911030f040f0f111008010506070b04080f280201020909040602 68
    0x10381400c03c12a160b84170040da503840702e201e8040449540030350311a8240942c0d02d640103411350701144012a001c40300040c84010036406a58802e139607a001190854132180040001451300b44401d02001d6901d5044840c40c90816000c4200003d04601500c03203082c1a25652901c070000511030351314030302145401c45d810072880040707600039580c034800440410410050a42071441014145542d0a0b551130001c220b032000d0901281414148414880000481c50340303d580400d00c4801a00c050401d001c600440d0b21280d0b0002000d4040012404240340c0d05400801c2500c1d0411201e503140f95903000088100c0b072003201c010f4140d0310144003266140e000c03001059040f0b0b006140050201415854041c840c0141070700132035290308880302e0803005050117035084400c7c45881c02c0c60440c96140c000445c0442c402d04c1c5005055051490000d010888a4800d641c4407101000c80151903107c0c0302615440f400494000300780344050342125407035540c414000c40760780d0340f8003910501198032680d4503800650051 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 546150665 1250 546149415 546149419
    0x12606130e030d0b1c060b06210f160e0f040e16060e0a1a0a0504030c0303020336041104051e0405070c031403100b0f030910051014 58
    0x14200004000c605030080701c0c01242440041c41c0e40d003a844095604964110904501807401c01c44e038003400a0a00c0e002200d201c5d0441c2010841070215000034440c2c0c81038a5103031484070500c5800c1c84501d008041414030642e41010718078556203803108070110310003c206010000403050184c0145c142016181d0301e000c548050008208076002041e00c0d8105541600c0c1e90500e0070b90090b081101c1a44070500c2105070310296000d6280d5400e2255241503201d01040400f02040c0028000102c10700c10021503000315080790800c0c2490f51a441d0007501c90340000b916001001540d00e1001c0c44803000040c40c00e000300002c0c003001040f40004103000240a94008010a000d001d000006141d11907440030034850b0060001342441c00707080070400c4120703103010740030b8010488002070042c0020703046646000f250072442c0c0029100d5503445015810001d130754014000ca05000300e22102c14003c208040d500600060044c1c5103620754202030b0b40d04552080710b00c0b00c2c03461001c24041010314a40b003640b400c54400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 546151915 1250 546150665 546150679
    0x30f06040233071b0501030c2c06130801051005100f02010603060c0906110303040b01030f0503090429010f021e0f030301120c080c0109230d20012606 66
    0x80c99215102c16004100140c400b4941c4403076449042070703140d04d0400176000c2420304001d820800702c0e004080c440004621228041c0f03096841800c0d03004820341450340b01c001044a503a400b900b07880e840c200e454a1040d81103560034107010401c10042c001c804016907502806034210400c1090085400c0101c0c032001c00c065541e1280088081803850040c2c0038006850303103807080403903d801340c001c0ca08c0c020310b48290010341041c001d00000030703034240050341101d8001090015082081c1000f0b402c5114007140710740d000c0d10300f000041d001c201e001c1040e00401c420698403454180040010740d01e61820046060058000083d07203800c081080d40701d8100d01c1c0b642d0301143d000040240714580745078800c1e04914035210500c09518100303c2c80d0303002800035040401c064143d1401a10018200031858043e4100813650420040c05040f0165800e000c60740000b840e1000d0000b103801c20b840c034000302c422708005039110444070303101650081c04001da03100c03542d06054503500003500e0040c551020217040c6542c8052 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 546153165 1250 546151915 546151999
    0x162c06060d050a0b0a050306190209191202090c1804020309030c0109050c040e0f071202040b040c03090204150e040b0403030b03160801060e0103020f090907090e0c030f060402 77
    0x8402c0c407400d031003800310103000200c49081d1020002d0a20140d80081d1203680181c040042c038019005110000075a850001b6031184117040000fa12407100d03001d11400d503550f03200005032268031000c000b442c40d4000e403030b001c842c1d03280d40c20110000e10450700b1f000c2c10003100b0640c603405404c10342c0c0215030114003142a01c1c2400240134841d0b0070344024640c00d9446070300c280e50b9003885141c14440c4000070407249008200303094450780c1058480d0103902c5212402175050b05060207645a076001510380140050003003190708400d0780f01074001c01d41d068050303015a15100710181044207000045c400d55110144004459980c0d664000701000018003c804040d2030b02e02c11141602d04103e1415224080b504104040341894000c0b0700b1924598001d0740e02c90b92601c01040580c84024184040410030340302484680d9440b55041d00e0021103901c4466602c1c541411042c0c101408264102c60304001c03010b0710013100894981c15902c043c01c0e0303000396106403803100d030840200440c040305201c490200c621002c926 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 546154415 1250 546153165 546153187
    0x2090709090207080414030a12050a022113060203030907090e0c09180606030703020901060f020715030b040e0109171305040513260318071205162c0606 67
    0xf030030072007080f030741e80c04c001c0380a0010000c444c48000303110038260001e1003404003d0300c0d0040c0402054030f4000500c400014031801051091140f400400140b1445480c0500b4801c03407500c2a0340620401410301e6840e42c408a159440070048a0050600d407000b0f004050070803041c040200081c40b00e0300c42c0f82c803c03104c00d840300b0b03210092118880c07204590035a0f500c01c948400360741800c6004101030700c00d030041101400182d440c4031486041d980d46d0f19041c1d082c030352088410381c0780071440d4020a04114408501d40c49070369250304103003024042920127100540000d42e64600b611424000201800001d52901ca540f010a201424a0313014418808589a80d14000309003205c43c103031070500c0320300d40d00c035828000c0c4046059800044e1203800148a80c10582610006890002801b280b41c0c0c1c0e08002d24140b69110200400000389c1002070405001ea000b82c40c007242c2d41c10001c022901005c01c00900000c1011207a04000d00c441c502d80703a1800540c51890355400c000d803000b400c081e8040d1050080000e05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 546155665 1250 546154415 546154417
    0x702030d020303010f0b0a020d0518041419051003080c070f0e040629090a090203060c0403111905060d0f09050a022b0f0302030c0a03020c0108060f010804020907090902 74
    0x11540340e401441d900e5040120200c11500d0581001d4800e503010828824090b40c0000e00720007201007807801980310100001c0d0110b40f04040c00c0e0b01035000e420201c1c8400c3c14a01c0c00300c0103005a04000014803030b0180b101809080d90300450349000c4040b02c4170010004540505c0c000d01c929880304050791141c0c0d403101e0440d801000142c001e00305503003242081008200d10351080d000714402c840c0801d141e849290583c101203402d18910f0b140140800390104814030859006502a41c0c5e00500351a2186459103518110781c2003880300752841c0d4400d1400c0c800c03609041440d44003a0301103221410800d4104018000c42d80d200c40d803550b0500350741d9201c0c5034405500303100701c0303011900c02d03009021104864010031141000b02c0440500e01100c0e850440c0e080603c400c0c194410550050348410480500d040030b90231070003469440d090b43d0161040d0310003015404100380c2c0d01e60800b601c03002004c0c0c90b490180540400403680503804a822000805c0142c079011480301c3d40031029162149040b5180c090070f60503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 546156915 1250 546155665 546155683
    0xf0b010608160e0f13020c07032001090501081305030d05010305101b230f1b010606090e0106050c010e0706030209090a0b0904150207120f0f020105010821070203 71
    0x48000040c4001480015400b80c840c0c6140d00e0f00128401501e40000c1031310703808050b10342c840d8081042d1004010131680540d11103c0b11030065400050752403e110804404c40e014038204414503124804156000d2100c050503980180d443d032003165211002070a120040f41c800307841da84014000300100d40b48a0150a02175031091014005040c0000c8401d000c1e02c503180f180000c510207804140c20100e510082c07010b0601c92440343d06800b1007284111400f5889940c0f0401030001d40041d181600c40510616500b00c100c03000001c0010b556103600450742c00856000d0302c0001c514190041215a20800140546102c440d00001c0c0400c0c1c0d0000e043d140c90070660100d00465008a04906d442c0707844501035034041d054680074000d600002000901c0c0d0500244000c21107100c0104036808000642d0640d4661580700027040d90440151001400300404034000d940010644524419440d1041c00303503034100c4100318014944002100854200d10000482081d0002d000b07000610140c0e500300111f81d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 546158165 1250 546156915 546156917
    0xc050a27180b0c16140d0305091902010c05060103030309020a0b0a0e0105211609050306040c03030f170109060302040e032a0c060d0203070e030f07050d0c080609010c0e0a210f0b0106 80
    0x71170254100707450400f40180c0c00c0340d0615207000c0c100701042c0d00c04583c0c1c9064001c04445440e81d07601178030043e00e494190181c0601a40304450020003011340641c001641c02d4000c44840c2c205a540305000912441080c0704900001d0b6014406000e5500401c0541000200803025840417036030344a0405556400b128444c031000a030114509540b6040940d01000d0a400d5001d02183e142c41c0e00c8034400f2400b103110040c1084020b10716018014031034000707100c014440b80612421540e4a00341c040c00390009010a82c461450580c3c610218800081140ca200355220000c0c0b9042120350f2540c0c0c0380c00c0c50724102101c03038003405282409940d01d85008006c085e4071000c00589908000034020541081900032900076480481c41d911031203000940a42117600468910305840240d2500c45003621342030388070140600c904400e2124481040d00400d00441c187c2d0360b92501700d8800310401a50b02c14500c14043d0819091144e1007200c0c4071101400c45483c0148040d010f24103442c0e0f03802c3d00c8000c1c00d0340070130 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 546159415 1250 546158165 546158183
    0x41a07050d0e0f0406031a070e03031606230406090303021b07140105120a0f0603060c0f0e15120c0f0c0a05070801090b01120c050a27180b0c16 63
    0x1105074a01440c56a65084055904010550031640c807e40c0259007080041c0b0804600000103565512443c00c1c0482003001a0a40751140460031111400c141c0f0aa0229002c500300b510b552030003c410800200103600103c481c411f503403034a13101c400c004c14019005404040d003c1200e640100000b618250b001c0801c10000d151441c501112003565442c03003608141003000c01c011a10000780907800042c0c019a52a0000030b000c0034030405100101a55880100340c01d0a16140e00411900080071481400980d101e03408088403078000c00040c03001f040c960b64414841440424002c1600d1500164811313951906145002d5810482107202d80016081c502c0d180c0c040005201040070510080c0002e000000080c001c0141990300e02c000d9007014006c502c4d14140003081c1c00c083c4840d61140700c0c02031801a02184115441d4500406a2901012824903031002860030004e12020b5200c3c540200a40300b6000081e8a41542c503180f204401511001c1d001d203091101c08021240c1c01c4a040a107440b0702c40d14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 546160665 1250 546159415 546159437
    0x1e070c09110409150506030403081515220302150c0102070b0114010f020c1305060105270a0f05090c0a050f0a02030406030c0314070e01020a0506010e090c1005041a07050d 75
    0x450151001c06813842004190307540200410307180c00094a81040d032605040c001a55020a050141d0380a080c03401e5028412524030580080340100414032100302e40c08044581003c01d2002c40320b2009071200075005001040f2500510800901411124411400140c581441500c41001015081c0c002100d400034200c2c10300415078000c8484010b920700350010341403102c4072170001000060000e0140000c0e0f0340310350000340e0681c4210200c0e04c1c00c8644103804ac3c0c1d4019140b507a5845400e840054034081d0b0407406012541d4681d0114140441380300030030b0381445a840103c8404c40e40c200112520520000f449804402154040039041d0701c100303540110346551804000409407112034480d14189845e05020050030968410780e56480010b41c104802442c2c203002c0100c0c030340300701e18402038424000c0c40004920b800c1074843c50340c06070050500300d42001d2105010002824060842400070070410442000400240d0702c40c0d503590070071351012504000c141d4135000d06181c00c03080610001a018084 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 546161915 1250 546160665 546160679
    0x7050d05150a03140312010b0c150f0c0d020412140d0e061e040b0a03091a0103051009020118030f0203060c040e0a0b06090406121709180c09030d090e010602031e070c091104 76
    0x400c0115084000c0016142d0800085502d2f0a4001404803200301d10700140c0750801e22144d804840091041900641691409003000c0000e86c0303520400002034010400c82c0c1d800d452058041c030003900e0004000c140340581383c44035140700c2403140c2240f41c007084050100140c00007407400030f080d1440150300d01140304802407a007818030b42c1c80540c035a01c62065000040c800b2035400a0403402120006600250114144c00107840c0e10760307410041300d40342401c8400030080040309044401e2a81c800d50031903042c4d441d01010101c2a000d24002d186080d200100000c1304140150001d81d08a039001d01030514004666004c642a50400d03004036041400c050554020002ca07142407140c00ba04184400341080031000000c1c0c1003580101355008811014404507a9410a20b4101c030901c00000f0200c5083e43d100001c041c00c013400c18407a21201c401c40f100000b0301180040101d0f4030202c1c0c4ca105540000f04105088550341e00003c03400c3e50b40f204e02000110304250310b8403607002e0395050501025166031401c20303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 546163165 1250 546161915 546161923
    0x10303110c030604030e0609010c0c23100203030f13080703170a0b0916030222030b07030504021c06090c0b0309071e050f030f0607050d05150a03140312010b0c 70
    0x1d1640c0a94071180070840440d600901c0f684190104403086031340c501480c0012101c18042caa000f41c0203d40200b40040d6040d11290010f002030041b10843d44518014400c0250203a06a14008056001080064030124102c48040e50002d003d1442111503029a1288000341c0c00040d0100c0204804180381001e01080392107032680300c0c0c120501807080840d43c00115a600c440a020f510130659200350030803480b030198040c0c1d0590851414240c0280031410390002d20980b191109031030144925000c07a031244c0c0b181c012107100395000740c410003e00e510003c0d0000c03081441079003613524070741ea040e00c040001d08a0a0750b41c014804c40c0741c05070f20382c1010300d4036a041c0481a409000304502040003002c502c00c44d000407100715002120404140d020120120b410205911200031103800340c00e003089200b5400c14003074050411042c10401441c0c0e0b0348086003100f8820750304103690140b21181c0400014040e0310f8240b00c614918419603081c121200c095031444103007a0460503030210003190100c007140c4100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 546164415 1250 546163165 546163183
    0x3050a0615021011071505010312051206010518060c0a05070909051b0411030405010504030801120b0402150405030a0b040203062a0c010204120b06130e0c01080414030301030311 78
    0x80d41040c0e03201c054007019607205000c0030b0040310203849108144a22101c0015180d2903074004160a029041c01c1d070400000b041d00340012a03016000c466144000c61080080d00e0340c1c454044960380032515150010f5450b134101410818962554280d01d04068036408003510b03110800078001c2400b4503441c64034a080001c9034108203603403860440c9440c0803690000e580d10000c0a6200d1003240d00b9031040c04907002d007200030940d484912000044c8020020154080b900c1580207035901c0c4c03001d980b0f030503c62840c0c0301c0e00b06026000048100c0410094500060208005040c018002c0d103016036580110f420801002d000f0b03281c855003403040000b0b500b020b222443e40401950510141c20905071000d840100e13980080f440a44004264030b0401a401d60494001c0c0044030000341d260b207010710700040025000c46005000b04883c04511003061224028900400304d41c070081c140d55000c1100455450fa001801aa01031600c00c9a40c485440c0034402107006c3c500039a00c1e07800807401810654034241c403003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 546165665 1250 546164415 546164429
    0x350a060506031b010e0a080717010c020d0c060c09030c230607030807081e1302040f0c0509010c02030c09090d0f02150408030a0209151e13140303160303050a06 70
    0x8900c40e0503c066680304524540d50900741602d02c1103040f004190301440300c1d08200103e20841e5804079a03001c480c9110810054a07500901200409c40c0080384c540c900c0000305004030701c0340e03c080d000245030350b04603c1280c40f041c504401c8060396031700d40703102080165000360400070401c266540786a00501d09110554000d83c3c42d285030007803d540060015800401e4401042800d9000c0781014004122982e08411994140d03103071402c1c80000100c807100702407007c034440d500c0c10025207810500d07400307402c10315099a16094181074810b00117581340e40702c2d07000c00c03681405141b800407802c1c1e45a2200c1c80c01101004000c01c60480018005410400c0c0040c1c0c2d2015540201c070b075a40c604500c0d5807503a500640c8002c42c03903140e84400d03810b000613024807040305034018402c46000722454a04800340083c01c0d03205410745090f1061310716042052141414103044c10402d050b00340002e4005941c8030541c4a0064101d0b45081100780b49982c00310304070002200000d032210b00f8001841c259009503009400c075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 546166915 1250 546165665 546165673
    0x7060801051e1507030c060c0e010e040903120c030908040807031a010f0b1b01140a29060729040c050f030d180f09021c02040b04350a06050603 63
    0x80c2d0002444012107252103d202e1000242e18420544100e0107244100d6001406003c08900183c015118203105c41c0e1042c0000d0829080c00b006291900503030211a400d40c9a103c0d141c480c0d00d20b140054800602850b06040e1914148030000e00c0394002407004180e10005001528114035000c5403a04a518003508000c0902d00144010508640780c0000c46603030861043d91800360b210720a1600c03a00c07226182d650751031710f10300ca101c2e0400c448420740300300080181001f0a4030a0300c4001c5070310581b42c0740c0c0d05e40c0c015404603c01b204c0c02c000780188001f60180030218104d0110a51800c4a0032500d0301c8420001281010310080003083e042e68006403804a8620f07050807074540102c1c4d50f4403051484d002c10070050040c04040d02040701c21400180080100c125051031302c030f041c484040d41c0b205c60310038825400e400405014940e41d2003a10280c40803e02001d2806140c101e59109460041c0340f1861011004403014403441400d07200c0340340c500c40c2400604519802c505251044600003480580a500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 546168165 1250 546166915 546166969
    0x1e030307050c12031c15091a13200c0304150f030f090b0c13030618050c040b010c0201050a090801090c05030c0a0302090105040c02030c010221070504062c030706080105 74
    0x2c1c58074103815a0180c07040058586821b03d01e5010380c50096106800c0145400341580402d210180c1c2c0141051042d1511802d80054661120031070b1200c0380c180c2d030080f00b502c441c120980c1c4104010040d000c0003504507800c082d1076460380d40401425100a401060400821440c013031f1701400707910302c90b81c0724520810400d103003910740407503a480081801e04800e100240381c840721447c004c9801c000d180c0080c1c003042100196403510240b11040e8109aa1600c40c418501400d0f160501501e903100310107941d03104d4294016801903a2642000800406000c03200002281d0100d09106424019015021416500c0e150405150400340c807890780a0190102101c1840503865014045045a206a40c006403064000c03800b01d00310301854002840c02d5000107000e041310300d00034400c804a407034030310b10140c3d00ba00c03104e409035004e02ca54402c0a0105d0860f102c00580581480316031100401c0c18051240504508000641400031341d400100204030808014411400e01004100703400c1e500944101c8188 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 546169415 1250 546168165 546168187
    0xb07020d080f04020103020c120a090f050307260604081309051338091c0e0f0406030206031305010e0a0c12032102030103062304021e030307050c1203 66
    0x4031000b80200421100c000c0880c086905c00d50446040201030829954200b0751011154286e03030040c2906270002d2a03070304021404419810284003100c400a0003840a5440d04070360031042c9149684240503c001000c941e8641c15061100324803d601c175504da540c0c1d803414201d809000c4c4556400c1407210500d0724003086402110703c040071702d80f580c001c60b03090400005089a07607181102c0700c0500c941509440c4502c2a00000c644000f80104002401e6810510704002040d00120884421070005003d4100340034041c1050385c00b9200c62030b0060408a0080d0301c80e0049103441e0310685029203118100507054045c08000c0c4150385842c503032140544800b4200e52101482d00c2606c5c05080d600842c40d0644104042c05a050441110454000c1450444840b20600f0007904248015030343d00d0309005440144c0c0600c1c0b04880c252104044010800351241c0c1c0901000d44c002160020141864103010030941c3e408201809503107120708020100502000e05010b110402080d1003d003941c404c0c04111000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 546170665 1250 546169415 546169427
    0x22106030a030e0301061a0d060b0313142409010b0301050112230604030f02010e0304032d02060c1605090f0c0a090b190e0f0f01030207030c080a020a0b07020d 70
    0x542c00d458500440240d4400017401040590321a100c100f2201407203040300505100a00400e06800108008a5a88282040c040d00c000c4030511101c040e107203e840c00040c005c0400b4030080320486c00300e5541c1c1c0041080f104410744002198000f200c44c0300c0030800000b40900924000c01c2e0150024801549850303052800d0f9402c007140140b14040d001d540e2508200c00c02c08804c16008100c084940500301418090f1402084805100c015400c00702039990b880800402c50b0700316940403000039401201c240c55024140146c9a03568803515100000030056500c15019010300c8140202030200314604442d00841510303d640928040c00442c070400100041c1417802aa0108012032004d070354030a410030880f1140056041358013a100b001c82c20160001c0444403001021515407a8400340401d01010800c1c00e0000600a0f0390248440960b08055407080c0c0150501c940702e4208600900025076842103580c0002c905040140e00039000c840c1440410351031150480700d0760001d820b5550038280010b250b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 546171915 1250 546170665 546170683
    0x915031e0201021005010e0601180608040201050a0513060e030d0c050c060306120f061602010504050a02040218060c01090302240f06061216020c041a0d170d02210603 73
    0x194030000084641964001d01c0b45501040c0440c208120f95030f120282c2505020060740c2d01070001e42007000c42402580c041c19014280c45080d1224966959990700441e8145d101c1035401c81000303800d01c804582c0f00b0214110101502141c1c6034040711407020018140352800042c03e40042121036140c84000c030b10003086940b80541e0544156a8170354546000c514906148200e220403442402040381c4407038008074007203001e5074a081c0da1060070611001c040b802c3c0c5000395000b40a6400c0110004010310703050f4003c0607800034a41140381802a145c001400641151860400603510f46e04010109641800314050012202d07503600410b10040f1202d0361400320040c000c40808614001191043e51450161030b2640340174000f610701807800c2100ea4104d28450480300c400762007030000c2080305140c40d0241c100103160303544000401c0c0c00c13a5000c000d074081d202e04050703403910b841c02800d00031442900020156030780c01c0e04000d0b03640c0c4501c0b0351440c1101c510043c0e00f065100e241d4144400d6035004107440325 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 546173165 1250 546171915 546171953
    0x102040b0d0f14012d14041505130e0705010503101206140411030d050f2a2e09170c1f0b090108010e0d050705010e010c0801091503 58
    0x386102d400c6801c8802414407290b400040051030b0000104100c2071070021541e50000301c2526044a20556030170000411130064440000d03141c02d95003440d003800d6010700c00c100f200910701c2045503950030114448103661482407084603220742c2582d402203001c10039000204020320b07040e480c61804100040d0344040c10300990440c150000c1014003807040780d0b00302e14050019003e030910503042c507146ca40002c0041018075402806072801c401c8044c3e02580a8681203a0040c0425240c60010541035003051084007009404c040d07042d41101007148200101030101d010492401007101c905044080100ca03585040d280507801c00030346400084144441c040c4444441187e42e86a10000301210b0515115815500100c510410743e03030f00c44c1d181c5810000304031800f51588011642c070b40244500383c510000e80300d90154400c00200346850300c02c000914503503014600000e504c2c100c1200581c00c1da1208090007000a00f140d006001402507803003005940070324486840441361660380c031086401101d21544c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 546174415 1250 546173165 546173171
    0x3103020d080903100605090a0b03120d06030c030c060809010203010506180f0d060507031109061905040806040803160c0b160c0b010305030d14091207020406180903110102040b0d 78
    0x103020011403509441040c0d0005054a07840c03801c40b143c01c002007a052040c03612501c0c0031004581038181e113114500c2c085030041c01408581c01c4007000081240d101019030b05840b6650364000000c00c110460320405180b046010203031080c13801c0030082c04240b01401c4511142d104000420061b600c18080b0380d9911103884604000118507400101e00807950041c80b03400170200640c00c020410250300a600c60b4081e52020010310900f420202ca940c091000d03c0354019804100240e91000216a002da4001c40b0340b400c6880c207a10381d1000d038100582514100e5a50030040144140081008059541c840702883c102c1d12541082c1c46171441154060a414486544464141e00e0700307100b404500036668020005813442e5a60740381c4903aa1b5423180101a054500e0701c3c00c000101010f120701035000300390400041103030503114920982240d000b00c20482e40250b840d032001031074010f00310031a42c01140807680002d840d540f509005d460180001010b81003070348100000d1140202c036405580448034003036400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 546175665 1250 546174415 546174439
    0x6090612020c0a06092f040b0d050a0317060d0b0714090a0b030405060c070f1419061b08100603051005040203041511070201090e060102071a310302 65
    0x2400007071007902c40d104080e00590b120401440419000030190b14858050505681014810652204513000c07400c80c98440300340c074006007403615030049414400014200d40303043c005942c50034940384d2455001c4020455448c080c0404c01d100c006203a40c048010744802400c0ca445035111590171a0081c0f0a500f0700004403035242c1940003020940f0002c4601270702510920391030700d2a191841d00101c0b0b0888440c810080003454031048101501d680caa80a12761203074000070341c0c3d1076000b00c00c01c03c0003040302d911850041034840c000d03001080c1c1d041e1340500c00020380d542c4800119000d190542c5102400c3c400c04038240152505c2100e4850100c0d003280c60001420384503080c1c40c0b804000b1903440281d1090012045c00f0601052107004090345000083c100030690180517499454001c0d60700203408130f41c070f1150400c80000c00d4422642e1001e0148142c0b4500380d2500401d00100c1d03800d6001030700301840450990200040807540240e01c07030b00592003003082005079815a104402c1400000c1c0510000599 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 546176915 1250 546175665 546175697
    0x4080d060b0d02070b060a0602191703160806030d0503180a0203060f2d0f18100b010f02030415050a0c150906060e090a0b100504180308070207060906 66
    0x406006801ca000c035459480360304410300800380d040b40205842d07402e12100419920304e00540344004942c01500a04000c4024202410003044040000e1f6410845a01d00380c00c03070500d02000b9807242035420205200003040500080c07200c88010911802135200720720040080f500501170380d902c404001c03200840c3c84194401241041c000d000c009401d03100d41401d101d440076005503030904c929229001280300c01d80410300c00750143d04012200740d1042e000008510051508000d41d5032002d030b0720400e41d8000d003050503c40d1400000e00d68004c05155101c10000c05507903c400c100c0460710180c0b0055090900b0442490042284682c07040d082c4140000e107000514011030300303c10000d4000780040704000b07141640308068480501f04413401407802c0400302d03000300c0d100f03910350003140c4003170040803001500c0e0344c2c94401c99405400101316180f881c0c030008907603a50380941c480c1c6a180d084411b4110b04685800b40c03000f903000d0803801c159040344109000342d0340d000040c201200c0f941d241003043e00c0c00540d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 546178165 1250 546176915 546176921
    0xf08010312050c01090b04020f0306010f030b070c050a050609011805060610030b060406110601090509150438010e09060a091104060326090f040207050c100c05010b100804080d 77
    0x20f10a0554204180d02040c8040ca800c0f1500c03d5009035411140f401e050030400d91920700c240950b500b44801d460060002c01d0547c00044e42c450028201014a141e550320780300e1074020001400c0b20140d0001c020840e13030500a005100701c500b1084800c4410900c0d595406440b034200908550041c4801c0e030315261950300c2034121155503000502859655915100002c04118200300382c105a4400d80000190703201d018403c952258003001e02802e003001c0f4a4010382401d0f10081c100384c61091100c004030076602d207001c202da5a11501082080508400f030380001117100c2c4140d000e1080d00c143d16003001800403000c250254800105080010410722514000a400070000c10b401c1c0c010303207051008010000030f080d00e02e1109a00510304c9035120032840c0340c4502480b81b612050303040751305010b040301c81e03061a0b005019a03d1050040d03590032488100491041544042c05100240b0804100b0003031260a11990600d00360580d010141e10150444c0901640d00140005216000000f41c160f02411076038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 546179415 1250 546178165 546178177
    0xe03010f05010e09010506030a0c0501080612060a061403071a0706021204061a09160f09090f02091f05040515130b0316020601080a06050c1b0d080105010f0801031205 73
    0x2880801c103650710340300910350a040c102d4600c050340d86010f012030080c0c6400900000c25035440803500142906010044031448000f0301840d0b005100c028a4043c0000309212951141103085000200d00e45041e0310030381c00089030f40c132250013500700075000d001801a2000c804400000d5480c6240d071502c01d49008402031080a8034041444030305002c3c4001c2200341d4000312504000c12080d0400f1000400c10401c00f104240c3d00f12980f04500703c15032a06600135a40e0229040d65400e01c2e1880541d20035000080d03d0a009501c0f0000780d000031004644c0c5011281901d142d071840003060928000c0d683e01400c0340c401e07802254171844600e00c0a200341d0214404a41282103002049404207036a0184501d042e00141d80883c4d400c010b90708030341381c440e10000b01141282c46d02c40003002440050340300c0303030014440030740180072000007042002080070240080080741c01d02500101454216440001c00040c010303084a810442200541c2c00440c4d801404681582d0700908210032054541c00299402c0c1300d08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 546180665 1250 546179415 546179441
    0x40305030a05090f042f070f0501060524030c40091104140102010b100c121d040b010201060510170105011112070615170c010806100e0301 61
    0x1d81d600d182a4441d000e007599003070541c1c00d620081422000c101c1a50300c0050100c100144208540c078142409030710104070060b400c85001d180545d0754441ca0364503080c0c04e0f803ea0300c0c1d03074591000300030700e04210300c2d00341e09551140c0040b0120103641c100fa4100d44405008241001d401241549003210000b1a070b89840e0821049402010b2141846034204c000000c3d00d140540308001c400185105c0c54011184401040c03400103241c24104400221320310240d0b441d990440d03503980d8030300d0b1041e11120100000d8900716100c031044064907180c41c884032041501200100b1001d003041c09041000c2001d12125200c00301c801040707048814004030700404143c0c1c080c81d4081c48441416400c240c00600c04002034516202d191140d030388900c019904c40b15401c034030314215407110001030314950700c12010741040c0b4410400800c1c800d222071041946551150010a1020b84d021400014404204002505079101f801d04001520307241c1c0000d42040303080c103862800c5c130074580300345019075800f0350028041c8404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 546181915 1250 546180665 546180667
    0x506090a09080d021215030c22140c07050d030b1020160807090c0f260c090310060305072d08030901110102030f0a0c0c123c1404030503 60
    0x41030202c0b502c2581c01c0d202060000c412800c000c540e4200801d4500240c0c0000c9d0445100d0140e840341044031071a00401324a00d01ea61b8064500308013070070b40c05603010380d000751106038840b200c80c10f0407030030030203480001810b141c42e013103a698583d01c4484070038045000c01e060402041d000d43c80504d0101c000c2000940c1113003c1c10500c180c5030f00110308041c06550180048400003611115410110b8101e6441031011900300c81400c1480351044112a25105040020340d0703101e0055100c07008501c0c410340e5041841100440e0041460804120444410740d1941c418854a40b440d103801d42c45810398042c082c6112075280d0511201e1f21500110100f916a02c4080d5a0090f0340e0204540c81e9040360344c80600080510381c21941c0703254140203590140340310984294854035030504400c02030482d088420103200c804280800400c6880348581c0880559849010400d4103000000c20309002140180c001c00c05c10034030f003407521800d019008640c0c0700c290170000100c0002840713600c00d0b80150f48c402130807440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 546183165 1250 546181915 546181927
    0x60a0b010201021b06011a0708040b070f0f0c06030b060a1e021905030307090e011a1c1e0b0d2004060305161401030c021c050d0f0911040506090a09080d02 68
    0x30005030781740c100c40b150029010640c1d001c0d0314000e214420124040c100500a0006010503810b140003403910343d00c111801c01c6030985c9655101e02c406a807080984504140207810499141c040c0038041840e00100e86184c9401001c4001400460f0540c9907410007842d4016420b03085402005011420103480d004031355402000c1c60126a030383d04c21a00d480001d0f003112800a40c2e43c64011016040e100b9000d80300050320b4690040590701d41040440000c000c030841e42c201c0141c407451090b0f2300001300034000c40d142443e100800b2410341d4070041c1014010600290900701103008035100700e90101d0055501e41c594414000000c000d0901500b001d4000d002c1d680d180f1a02601081079482220740b4900b02c040d0421400f030040d02240d11161005c00980c0041d000440c1580f07d000e104003582070075080960a01c3c2c2c04401d40400c40b100d00b103e071809942e8a00100f070034008443c00d00301e91400121014806454118080303021094003034582c00540e0384801c2603c0405c907448054070aa0604110300b1501d0304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 546184415 1250 546183165 546183217
    0x32a07090f0b0603071403070903140a03090605031504051815150904110103020703120507020a0507080111160312020307030f0509060402031e100905010c080a0509060a0b01020102 79
    0x4100204025114a408581551410f028042c0c902c1505140c5a012246256100305820f6500060401080155405000c8002180307204500e1598a9110007005440b400b880d000e480241170ba000801400814400c20074050390090903908001002e88012605499581c2c0d00607482e04070320300e200c03c80d024005600101d03040366603202e0722541c0c0c00b5400520a00d8032038140950b00406035000742141000904006036540240c0040440c41d120f032410f6800d000d011321150b812070780c090307813071800503040a2091800e02c0810012440946440402040304003c035588220061240642d0035080e20f548645840034180142e030144207204140303400395540c1c5040000140201040721802d0440e51400011074455640050158882c0d07030301070001c3c0014240d092804969008100c14482d0030b20070040344415200c00380c091460814401c10010492a0180300302900c139080041084003290301d4841001141c610000c0c80d00c1e00021340d1800019180c410784d0040740a4482c4c042d09450009120b0391510410b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 546185665 1250 546184415 546184421
    0x4080109030c03260105092208030907090b0303030a0c02030409061d0a0c0f12060302180a0c0c03050403060b0d08130f091103060906030703240c090305032a0709 71
    0xb0328031a54a0380c42d401401e90841e0400a01000307001c0d0010004401070096007080515190844812100c010744401c0c40c200b101d2501c41d20a8045507000004000d014000c9002c004490180a0086003444507640380d4006c41e980b030000070b003030110854031a800c6040c1c4034004e0040304e010340480c81040c41075685942c9103001003108400503100c496190746c00140c03c69124400e100e15011380d0354811000c0c4485078400c0340d81c0135510100c1000165501000801603550740750211780c5401c40f1143c00d59034074000d941c407001c40f0305201e640000e01000480300400664040c086a090300da020360700207283d003020b002044180c40020401441c5900c0061036801c408901c59a003811a1202608142d071151500f00350340907079031424206a501501800810928a05542e000d42e001d8400350032a0700150342c03a22103010401e1b0100d510b420015030407500c2140021070380944500d00101c0d00b0408080c0e0715540d01c4541d07030710070262203c82c903081c00a994031400c540010300b100300d03c204404540e80c0c00e48034003104001f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 546186915 1250 546185665 546185687
    0x30c070501021e150a06080f060a0516080403050703090f0617070f1b050c060a05040e01051906030c030b06130f050f06160f020303070606060219260408010903 70
    0x5403084602240c3c00000b820100b5800707202080280c0340400f05a1000b50300614060000c40907292a94408280c42104000c403031401010100201007604100200c01e04032038004c0c09243d19424640360260240340c02c40c1620f9003195052a1403551201c20303003000c44103a50940c000000ac8150004009009644484140081d090310300c6410003a0300d03540c0003641c08281610314440401e18110100e100c0c0c1542d00141c02c4214024020703141c000e0075103000502c00b68007001003070000c1140400d0510908070480c0b002e0b80500300c04e50b0302c001914480382c5410902c042511840c4101510303140e0502030342c1d10030740089074120000391009172641c125484030302081c070440c01031315903580c2320100005284c03410403600068500040d00c11850211400c2043c214a01940019601d03440081e4001e001a281000201401801014000740c0c8500300100241801e031140010000200c401c501c50340070925081d80c0102c02e102000f01c1d200f08610b403518044542c0282d50004210b940303454090000d15030090030b4060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 546188165 1250 546186915 546186917
    0x1404021804110a14041a030c06160c1710090302030d0507170405030c0d020a1106090a030c03081206101d1305011815080601030b040f060903031a010e09041e05030c070501 75
    0x540c19216000001c180c04a1b03024950550003151070303400c28200303580145040054800d8007540c9052585034580c05502c240d10000c0c21030741c1d840140d0100b56061024103c0010448d00c24007050500d510700940c0c0340030b1183d1882c07100c1c1c1c0d2000419a1240a92325100110500070b64000700340c6028100292240c2014800400714010080500b041910100760040c950383d103c0c4601c0203c1c1ca4050900440d81c002c80302068000c00c3c0c80c0000310100d107215021500031842804541d948640d41210078074481c2c03026041501540025004c1101c9030b0f00441818400c280c902d2444031411400000603200342c1c040ca00004646182c03600110b2807034100f003a080c031a142844001e200c1d07105007001e4440110031a115a05558015000510015025020075504940519001e0504440544440c412180b10b807000b10003003039030760304500514200b201a00840d40002d003041e940100c40407020980da039000a000420584010304800080c008800c1d000c0b85458014007200e44468540c04420380d0b51800d030048038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 546189415 1250 546188165 546188171
    0x4030806010822052b0507080a050c07090207150605062b0f021e0a0503010b0901020a1203020307020c1e01030b040e030310031b14041806020307121404021804110a1404 74
    0x100904212170310352410b070541030343d07041c0c0381c1009520b40700a45d800c82019035007004010007480040710800c20044015180d040d5005984180d240b0f84001d40b809280c11901d0b0007401c050041005d5940d07041641e2490114403c000d00b030f5100501c10200024010035441d201d0b600d04481034000c01301d07503805400c01c183d101e00c2117900c0b070000c0708080078a80180302e004400501c04000500c0b2140c48103001c0c02c103164040c01203d481200b20f42c3e0b440c0c5801312060310342001039804001c0180b450360401c5270202c0700b0001d5401c2c8100b000951646c4504800048501c1e042c140c07152a080c4168580d40d120226000210782070340d03101d00702071024000c8400588416903e030311000004505080c2c1c501c4044044418064000e40b1402e10345c01400081d060b202088a0b090b014541c24402040f10b0b0b00046204507020342d40c0c107104900b807440703c60403a0384000b1f8103404410200c0030040140c8070400020106011840800c415540d189000c070208800140c0084d040400d42d40300080d40c0802c52240d000000f0112000c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 546190665 1250 546189415 546189463
    0x20c040f0f06090209220e072c09030412020a050d050706020717060a0b030c150415050403020a03060b0604090c0302030604050c0304051c02010f0608030304020406050303030403080601082205 84
    0x2101a4020042103a0348107440c64585054000b01341c05a50250300c0f4510302040c7c2d1031146154074203041d01640000b4440c01c00c02c01c00100c0c10401c543c0c084d07030035080b10641c1525050941d40950380b80964011081c1c100c00040d840001c0d59558410301005100c014088118201c0a24003176441c1c204a102c0d503c0940720300b01e80440e225031405014985100d00c0d8006007903d13540c00700c60030050054000d80315054045c0381102d0040d6104c0304400100d0010040c6035540e1030340b511810042d20010462540c040000500052005070b482c440000c088a0300702f00c0100300b502c03031480020854801d44e030004886a02d0320307101c02c001b2034064000d94401e0703a00704e400b000590781b1145119078030300c003ca80007070858001084114517650f182c100c8044c801c4142c4000207090031441002d000311041e40d0410860303070740040108411840c1c58001c8a01070700040d4060b40c11420156405131502c000607000c0c605028008002402d202a401001c2c170442e440c9400700c2c1021000d90030301c0e680b101014940c000c0300c41f16030600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 546191915 1250 546190665 546190679
    0x1080c0118060806190b0c0a0209100605030411060405061201180e211b0717030a05031b0f0304080d061a040501030b0301150608010815130210020c040f0f06 69
    0x1a00301100c1d01a1035142c5980d888000b084011200c2640305c00782c07051408000310b40440e209002d8181d4410010040500b4140340c010006d440d40000d00c0e44010000112007070100542c13240589420640c0310f46044540340303054001800500440d001180c000c140403880d2801500140240ca0403a2134a423114080241c10b042840181ca52002c04002c1c50341c4001444c100010b0f4001c8641d003045040c504681c00d040f1200e0402c5002010202c61440c19403265406000b802189050701d1025034405000b503180c212040e80c040c090340001003030f06040b0b015980c4500e1051411908581c1008040c148540d41c918182c90214603a402104840f0402d911302403000c01c65500c44034510071840b0302000340c03e0034145820011805400040010754155403110340e40d0b400402c031641c1c4030000e0000c0b80c0ba490041d60400011500d05410b48001040f428405014402500c61030407132440001c2e0180c83d503031860180684c00303a24110803082d0980d001445c01c6041c6402420f50351054003001c9541030288003d42c1c1d6180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 546193165 1250 546191915 546191957
    0x516050619050a020703020a080a110301020a09150905041514030c090c0d110f040611010903081b070c0806181b010507050f07140405061207051e0901080c01 69
    0x100d51441000d400328a01c0d0090060018203000b03d801d2040740c0c9550f44a03804a00c003000c071540900d40c01e80c44145071600b044550f4003090b0298505400031810040d00c4c007030007860003165105052048401c8812081618418074900000c0c04d000b40040c002d111008041d4000400c0d14481c0135103148540c02400782c603103400708034007121100c000c046c607000b5115250450400e91220007150300c6150380350b0045140d114404094080d690011007099160b620344000030380225110551400d03280d01d440f0540000a40044407246c0040410001100c010b00020485080344100705000d840344403001d0300080c02c80c20004110380b2a6405802c8203511100301ca0794540c0d20108120f1580b16040010a062103c0d442400034060140c0200c4c100d8550401c44404107041441a800448c05200605c200e9951401e150240030740080c829aa0a8540c1c104075110584900b0180945445982c1035a001400c0d40d0050b103440150010040040c130b51135a40380c091580d1400313100034943c0401c1801d500d004240082003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 546194415 1250 546193165 546193177
    0xe0a050d0c0c050315040b09010f09210503010f0b070311061015052d1b0115050d020108040314041a0423010909020f040b07030e1504120602030a1805160506 69
    0x301002d0172035201d65a41803241c140051910355950341e1a010003092001c1d030b0041041403801644490003903002da18a054408c0300310364001044c0036041004000030b485101e00c1c10304540c104002107031502941e140c12550380b43c07140b5032201d86120700c07403d01407100c0250f104c80e011650031030100c2000c0c0010710710a403098010103d03011007514050780c0f18400c4240104c01c07008440500030217586040f884480408503101410aa2034145e0754031070554441c4001c0c50008005018115113071454111b00d58002000c50400602c010100882100d5140031160404251030282c40b00328610a030320b150045075161540c000e8420300c9101507482030711081007a036100c001c24420070306940c1e200d070715420b102205010754851004000c5480c0c2c10400010090701440c003514101d4442d68401164007200700800444038401c0c100c0c00c000400403c8104548140f001ca80b00b08980e0125000da1280d0712070710301500600a9401d00d55610740340910035800c201c400700f40070840c00320550103c03004684031360500c0400d000d48 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 546195665 1250 546194415 546194443
    0x402030c0309060f0c0403110303070c0803120c07120f0306090e010e0111130b0a05040f060c300315050301020301030503190f050a0809101a0f01031107060e0a050d0c0c0503 76
    0x100410707c00b0607048401d06007511b5025003182c0c5051906d41c1d94401b1019982e1102d98076800101d90381c00b0070f411680c00342d42c11280807490141410b1054880b4020094559044002e1140020b02e840c00c1c036010b50810301c000c02c4c05400070840221450810f502030310380240e0044084d480c20740341050040d449000c0e43e0b41c0a0345a46091407550030010085515444541d0050078440705100015050900252540140044da03a8800e03c40142d4503024154045c0411a07090115050951003000c140c144000ca090040034500480c003420005a00517070003c0c19003095415500020020060010000041034031210484440601302142d450480b00340905107014000120100f047c94100362041001d16007016015050342d200100300d400712411148038521f0b00303c811172241e18680c03091901d4036802043c04000e00301070102e8003080100f1004ca20503400000d10040d0344080c0c0002a5030b082003400180c0f03511070220360001e2001c40c4094844150303800201c4000207003003001310303050802080300ba4005440b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 546196915 1250 546195665 546195667
    0xe0a1e06050309121909090903210b040e030405010818100b131407080903040506030a0906140112060b060f2a0727110a120207020402030c0309060f0c 66
    0xd00004940c1544041c0c4145041e1107410032843c604044040102160140251051039071070080d100070f002e0f2186540203048030741c0740c041600c0101c0d0b0450f0f03118041c05080200707103040210444001004143d5110307015040351424884011921000004109854007621340001540d540c107081002d980c14504045210382050001c002004201e42244810507030040403408071456003201c50b001c541c014101409130ba40e40000f4401c80d40d8100000c16044640403014518085c10000896014440030308180302007541c0324107240512100303500081306000e05406102103541d41d03400c260b174141ca644006880d194942030355140c1c1c91030040200c6141126004405003800d20003407808051741107035110034007800b2403640e041040b0282400004080c00f841841c00d81c8078070200380c910403403552814103010110300c0c0c0010300c01160440401e6401c1c06a43e07180101420300858490000380c0180d080c020740103170000c0240301d00c440211018502c01c41e2020119070603956614004040031034203461009103000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 546198165 1250 546196915 546196919
    0x1140112020f07080d0f050907080703140703050d27030c050d020307081015080c180a02090a0f08011404020609040f020c03030c0712111506030f0d0e0a1e 68
    0x480e81c0180c420841c403050001d0030040d40740c440701a1580a80716080000d5600c0300260f0501460340b0032035400480800c010700556003060015076840f406400040c041d4880c4003022603070100104207140185070701c98240c540340b501d84100604071030f015403090400f0851b82c1241c0c007901760303510020404032034000c540b40f00003910301070a2103545941d142c0183e800d030003200000309565404000700f8170384a0181030700040d0b81c0c2500050012222440c0c00c844402d420800d400342c4960b0b181800c07442d48a400960100c16910b528012000034461800007a40140442400003000e0702c1d110b04080403600071400134000c85a0f00c1c5486404c90804540095105030140100e07080c0741411340c42100d503016030303800061034024001c03a00340c07031500101c84000e040c81001452404220703143c495810207442506200c055106860415a00c90070218280c5e07100074140c4000458540d1304100c059a2180850183c90204280640060103030030400b00c11402100c090000062404200c13400c0800c01c80b80d40c59280d0350034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 546199415 1250 546198165 546198197
    0x10c03060f17032205122d030c0619150e04061104090905030a031d1c140403080304110a14060a0e1807030b01111e15010b0d0b010c110405071b05010212011401 70
    0x550030074058603880306200f0350704189d0080103540e00032401a81410074003404c200920007075801003e1700086501601008000c070365a02c1d50100e4010b5801000880d40200e850561401802268015206103007014290414403102000074031040c2900d680034040c090340d40e81c0c4070200d01c030a540c102c00c05501442100603008901c00043d800ca5070b003172030002c1341c01080c201001c11980264000b40d4500600106000070440250414061030340c0a4495000080c40d01a002904910320040c0f02e01402e400164084a0340c4540900c00d64020000c055880d20009015031070780c52441143e981010910703000000ca0258000c1d03062036000c0e40080f0003401e811844000706500000e40c40b006d18140d108643d01c7d910306000b50160207020389000400a034480041d02030510175558064000c90601161044100c0031492208040002d07900513500880d0381e072600001182d18040c4e4481c101070301c58200d1f248008009041d00102a00180c2e440d0841490342c0380e20005110f400902102d40c0130404440c4032100d60 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 546200665 1250 546199415 546199483
    0x115030203070e220c02010605040b030601080d08090c060403110a050a05060901051e0c03251110021e010e1e1e010b0a090b03010c03060f1703220512 66
    0x20603803c4184c50307010f0310114449015511100354140150351204000e0006080a105441c4135503804c4000b0b00555160400051700c40618000c03140c00c00c4403a900042c0042801c01005201a4001e040d4a03038959a134140400b840b10601215032244c55a80310000d00b03841c18019441c01c0e0f40c4c0c01030606d03250030300010040d07855900000707120446244081c201d10340024404080c00859111401943e03840d01d035481084050040350011140f0b200c0e030180b0034404a8a03030306141c3c01c900c0d015a26025a00500c090591608060742c0650040c007048650012001806400c99900001b414046400c800d18441807c1d29200400c0c000c4140c9901c81804500c0c8076030321245c0b29a440c0014400000ca04402c0da01043c0c0410706600b014002d5070303c1c2c01c8529082d040034840c80c40090240d1404101c5281803a041003080c105522400140c400324141811111005108035481c02424119100c80c1148400307035900d20b201e41d07104440c420f0036020000d04e0301034804902000d0740d01c0e410348020b19001c00d0751807600c81 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 546201915 1250 546200665 546200689
    0x3060b0d0506390702011e0c030f052a070e13020415080a0c0608070e0f04050a060f080708010b060c0304150e030d0201151203120f091205030115030203070e 69
    0x2500803507061403c0300024508246290440da112050340d13407103140005880c221001c00e030212881e054010011011358029540311116500d03161090a015080c10110384600401201c44034035010004603038858800f14100000509018007520182c60341d641404045110807200758901401140b0300d500145001d60000041080402050312259221700a075172405400d060215110070600a00788800c1e60000e000707a6114540d0f00d4070041441500e408160005643c061040c000d540752008540c1d008560b8104034043e05a034004011819910020365540c2d1301c8600c01c5100701d518160700000c1506141c0e0441e415031100030011440d2902e015506989d0001c010107e40030040143d000040c566020b01410941079225070021880200401c074030001c0d8a03583d400a505110802841c60000390800c0602c1e2030520190400908000c1c4d00103503002905214400034024580f9550000d19540c200004d14181d42096190141001c0c2e8420141d08070f2105681e440c4c04207146100280c0d0750716107079940244c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 546203165 1250 546201915 546201961
    0x316050102031c060305030c01050405211b0325120e0114030703060e0a0203071e0c11120d051806210a09020307062003030106170a060e070903060b0d0506 68
    0x30030f26503a80f611b030309581140d001c03100540d4550040c0800e0200030082d000455502d2201c10181003c00c00b241440b92182004d103c081d81a60b21450050715130a009072400e40e07442c050322070180110b900904480c0c0700034880c100c030411820714030302c0701131846090101c0d0101e40684450500404a030000526904014040000c0644644010031719104d5a0714850041003103244c00347e143c0c2040c65001d0000b01e42240b02e942c44540a044d0700f210241e00c00c6450100f05d03000450354620303a003200041030824072000003c0c0311070b1280b1128281607a90202c010310380c1d03a003890005490b070f114100c100b01252007007031540e46603882c4042d04030031040c07511008941c00c0307005008001030300000c40c0e02107070800c1110340c0400c0c04038600e602d0611400340003030b05252541c50000c0140d031a56042c0003014214202203e403903105080c1017800030312803240560000c4040c1c042e038501c400d002d140c04803009084908600080362940e003011041c0402c1d04080103d040c9096020300030b080381c1c0d503c904441401b4914010300321 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 546204415 1250 546203165 546203171
    0x17030a1d100c0b0601030b0f01050c07050316030519050a060b0f0415050406140904030c03090306020f0406030b03030c0c3303041406090d080a020d0e06060316050102031c 75
    0x50398596510a12a08500e0aa101c00a40254508000324019002044503050509041300450f031a991124600203628007428916224042c00303078502c0c0b03000020f80001b6014410f14001542a82000c0304240841e88190300700d640ea58030512200c801d401210100504a0b40020300c168001141074200c01394500f000380c044401c8200c8480054103862000c404880800300b032903410b0229042c00d0280c2c4000d0010707502c80703030301c8035840c580403540c076000061002d001c22106400c00c0341010300c00d0041c03600468202c14159112504801150781c41d60082c480c00011070300c2e0082000b2242404410b958501d0304940180c4561007140b014440d2000c1c480300d4501c250281001c40b0100c0074403090170170240c3e01160340d8040d20391600340303000140c4449640e00590710358007420400c0b107007401c0001c801000c50907502c1d10541544454503800080c2c05030b20709406440d400d1058090480c1d900040152007120114119203113860304121140100d40240141c50050301b040049a0364001d8008640805000c3c80c0c00c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 546205665 1250 546204415 546204467
    0x101d13080c19050c03011a040902060714060f10121b0b041d060a05130906020904050906070f2a05070e091608010510060806040905240117030a 63
    0x4508006403542c4503104031405032082414010300f00545564a41c056008102140c08402c40101c03c88011000f14480c60f220924842192250303c15103100f41d85c07000417280d03400c010081c0e00b81c0301c0c841207030704034040364a2500040100f1592418202200c14403031340f040c58135040751500581c0511403008500800c201d17231000201e602c0304400030002010f018001410b80c821040024581c00005030000d271141c100d03040c080c001a07554500c0c0440c0c3d050002130003d841119450200c0182c0a15552103034814501070070040f5400011815901c100910b07901c07440a1105030b10107075010040194041c1d2075000b1a880c108114940c6680306a01c0d40c0120100c8a02c180d81e01603802480c0012248501540c010b69001524030140381c1c03040c009401d01d00001d04c81481c20901e0340051110500c031b00740c01c101120000c1621510303950b1200c05996040340c160390800c940302d2500001501c66154802031841c000d0000a1000c1c07a003d003214500500402840c0341801c0d811003101d645210303c0c5c4008200740a0405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 546206915 1250 546205665 546205687
    0x1413030209090f070b04080705060307020a1505070e1206060f06040e012909131d010608030c0d0504030c060c1a07080610020a15150f03060203101d1308 67
    0xe280c4210345082c014034030314100c408054100b07103642d03000300741040741808144508540801c05000782d40c4c090300c12a072265140c00d0308a203403205c008409000c516104612600c480007a400641c1701c1c038113544401008010300e0003801504001d03480031254942101012075148d01d07000344000ca6800004003d5810280c6510785011400400c0c1d00003456a0044c60b021084548240c031286460482d81e1a0581005420720225007045010000c080340260746010340e07502140545011105054100020044030b40c860300c2c295920342c08400c071188680305074441899101c2c070800440c0c05590b8440f0380c03510158580f0b0410798403005070320f000700d80c821540700c0007516410700d000e4003030300c1405103a8450005060401c24080603100cbd80d15001d085410441c22040400c445682002489042c10000259480b08040d407182405140d080440007500c100400024810650003660042060030808007419595800001804040030404842c0300601000a960085034002180c0c04c5170040301076034940000c1d480 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 546208165 1250 546206915 546206929
    0xc2d0b0d23010801050c0f07060f060b120403030f06050d110418050106050108070f1e051603020106051801030f2004142a07080f0d0507091a090114130302 68
    0x22410407010720000421150000f4000e04e45c0201002c80e05901d072140c01e0000f001148101100940b0300fa40307550b1a4092540590700007030042c400050120740300c51a00e1400c0c240004143c9003a030020781045400301c4000b94621507001103d000030042410314a440d0749000c080c04001d240c1590060707031200c410924491030700c0b50f171003214811800040d94a00f0000050480f0074054240c800300441c0902d1603d83e40e40000c2c05001070002c22124880030480804215010321500381403622442052104a04054054000178265003084a903005102c0d4400120003c00d0003d21014198090b001094070118014014100804064450140c0c0c00d010b18404079042c1c541c403003e86500c0c615840704202c51015903040c4103100903070b10301d1501400c2c00030441c010214040c402001d0181e000004811181c0e1500718101c0b555444284400c0c0445d01d000c0748054401101480f5008803141c5021581c1c90301c407001c1d0300315512040c5c140c644406515102d034a4483c103030060f00c0554008403d44c0c5000c8090382d500c1e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 546209415 1250 546208165 546208211
    0xa03020d0507090c02010506010e0120030c0c092a07080904110a081f0b22090203160503010b04140d050a1b060804080301032d0c2d0b0d 60
    0x200504000e4a03062040045a41031444613085901d00024400341d42c0e0706c2400812180d809103059500c000740e001c44502c102d44842c540201034400094412011200490780c18082e290888184c4460394541001c1e4075020020b0184031108401081310140170390384400a440c1c003601a181850a169080d0701107000c0310485815210b920601081d8a440715030b01540441c0d00c040b081680700083c5141c1c10064503900403c4c01500c040c000d000c2400180e61004020b42081d500c601030b10b50710307841c0d0703207100200c000d40c016107800308000b24000d00c414442c1d02030b00440c1d0480d4801d50345645007510f1f04444610340c02000841c182d200169040725004500c08206804425000343c1c072002131591440050720209038582e010f04140640a0200800b14641000361303411203800c0801201690940f4128101807440b00c88211a2203294513080010b0152100c4c000b025540e45030080d82d400320000141c641000300310140c0f15419080340106000b120026030141ca90644071000109035100305002101200380320f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 546210665 1250 546209415 546209423
    0x1403041e0f030e0f1e122802030f0f100b0406090c0306170d080402060d02120103030e090a02030f180c040606180e010605030411010e0607050d020d110c0f0a03020d 72
    0x2202e0300d040986458203924540c80c200f10b500702c060150507070060b0700419284d44490711412400e03401d031102050074000342c01c1d64400805c7c0c41810312001c0703c200e00e50300c41002059010b4861000c441502d0800000c1154504629400030a01c0010100c64100034102c0c0c010050f405c00d0702c0b000300041070001e501800210b40d0290700c0c081026402d00c0004038882480c0d91040c28554020141b04220b0b60f00642e8280e04250195030540d52901500e0701e400113031090070314210114100d90000400d256000321401110001103a501011740c5800710701f0000d80c081039034044048007a51000c40e80c5a41e40d280ba40d030792501600305a44983c2d402c3c01c00681200c029034424004540400000c940301c12040d50264040e100b8004081c2e00c650404d20024094080180700500348001ca12a18111b80c0c060748111004a50003401160745417042d141194039407410002e02405841a0028118158041e0341206c041e20003482c0200b0403025404100003800f0101c3c50100e400c19084207000c409625407602c0805d07100c1c05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 546211915 1250 546210665 546210677
    0xa0c090312030c0806150f0906121003030807020312010b07020102010e01061217031501080a0204050d1202061302010f0f050f0c2a0a1a2b0c1403041e0f03 68
    0x4031500c040c0c844d400061100c4d00c01c40d11040b0f000040b6816506507030b0099184100c00f038459551502041443c850099540024107000040000250681285030143e078402d9442c00721545a143d82603940c0d0250444905400ae607600060055242d5a0003502c140c500500c008529015105062400c40d207882c1c020b1403c1580c140d030310506012102803030b000e00c6c400c020513503461898655840d406c01c07a0188059410040d03500b0105045a40d03540643d40900801045a094003181b03103810a40380388040d2054003d07004a400190b00c61040500c051951501a101c1140315000030a0032901c440b02c030b908a0050010601520051039004805806091b0304803001700f07044540482c0f51000240c0c15074010b0320301441305122128949590035008126001500c4140c0243e40092840440d40104d060b0b400c0400300762941c0d04004444d0200c94244400701620420840b40303480e504840c5001e10000744400d10700100f000c1000500d60b4900d02440544a11807202074003825070710300c480240034000540010f15 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 546213165 1250 546211915 546211931
    0x15120507060804022e140403170702120607051305040b2206170c090c0f07020f0d0206070f020f030309030c1c080301090c0e010905010f08040503360114030a0c09031203 74
    0x6d00984031004440782040f0703513801d203451580c17001003001c803e14100107004c401040200031525040741d480051121241512090700d094000145581c001d40044003071301030608000a0241007a01c0307940c61020340a0020205615500718611035402000001d5101503501c01c00040c00c000e0200d5403040d00d2200c0d4010b0a41d004180081104c0140d016018001c5600e0030802ea07110503041c401119282641a518590300c0e42840000440405120350007a4000f04002540e03c10013009820314200b6130720860303a05041c20421800d00d41d0303d004010800d03416a00c8821203401c60700d800c2c28141401c011211145a00203020340d40c40a1b03a4000fa409902e17141e44602900030032a42004010000030340c2841d010418501d0b110000701707140142c003101c1c070500080c840460300348401881210fa02c0c3f01d00e43c2000e200405d00c20b460480b24142c240000000520b80325003000190b22074050000800b400043c610b0458403808c0c1510002c2090050385010310400305400400690041500300140115880c00181a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 546214415 1250 546213165 546213167
    0x19020a05090d020a120f11030d23190e1f09050d170a110105070311072406060903031205010f0512010e06040602250302120901200115120507060804022e 67
    0x47c11001c0058841d41068801d4228a039010030310348030266441d8401d548080d4103030f4004c511481000c004a4078407849880c1042000d411a0044003460301c00d0341c0c04152440c0070100b40b1051074800e40d5004c00208510000c0005207050140c1c6c5000ba40607040c20289102a469268007680c807400503100403c80c40504088840d80070b200d0781e94401800d0a040c0312900c0c1c0028060828815003000820040d0036040707012600c0c07400e582404041d40144c10401603a41c8801026200344140d00c400c500290494070a290a00c0d124001c0c68100d454104000b4007540c10f0400700003511111020290181d0340c0c80310700c071f601c07040300b0406103000b28040c4500594503403500300b421140c034013049002c40925007040072040000750b0020b000c84440505084450701c82c903c51004840340c21550580f20900662034582c24000c900c103512009a8050742814102d916503234961503110380601003c00f8003540c0203513500b08a102e02801410341d100d44000e120046540c02654110440c1016165540c82c401100c20345400107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 546215665 1250 546214415 546214433
    0x5040b041703010e040201050d0b0d11031204121202030c0601090614040504210c0b042d0f030f090504290609331219020a05090d020a120f 61
    0x981ea03000320620319030421403103051403440548000e0400c0300016419448404550250300244002009000203e850341002c1094610b94081c4910900800c00d5290154800d01e08450480341a015581c442e6141c03625007410342110f5006410940c00100451144004184010340c0a010544000146c10f420028195403050038074924030f01072464034042c003001c1180c40101102ea0400c2c8000d20700000035400c400c40702080c5400c0010100300c802818031080000728580c2240d501c06c0e0709c45526486030b1011a1545815228001030f00010b1780815040100741b1544040b0385c0f6140fa4140300030403a58520200d4100c489040c032921000360f12129080c190b40394151000201c5000301c0b21a414541000c00285080031103c50208202d0445184111f62501c0c00003910b65140c010340342192501e0800403da945c50030201c2d144078035030301030a083e0341380f10071a403007900e41154441d45c543d802c1c19007910500c2145005a40c0a0303900ca1b0110348000755247d200d03e50340724403a104a0004141400501e800110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 546216915 1250 546215665 546215693
    0x1505100b030f060d060b03010603060209090622091a0721050c0924070302030a1704030c06020309120f09040510031101200d0c0506090a151e05040b04 66
    0x206003810000e0010600e544818690007103412140d4900c22111454160300402e80070440c2d030781650800310b0000c180100e0740d01030120070600b40c5001e032082c3e881c003007004056980c1d0200c0c2080c0494050050724107540c0ea81c0f000b41380c10703c03949030f02010f2029421407100f07440048400b00001840308880c1404a20b014070400040010f0070300500150070b0014003054580503500c41d40b801451810f45001d219240c8030a40c01c07a000c000001a540c80005040007901c0380d110500c030700c0224426000200b19140320f003903403600c45d0f078041d80c81002e50011540c41001a620240c0408d0040c420300018801c034030120b1000b030081d61078250645640d9440c14080c441520401842c24000f6604002c0402c0072a0240c4441c2c00c180300240b0740025505091514402840c8801d207450915109400c0501216a0005810403580d8001c07030403505a55a8480080d07a03840c5c1b41c01008000888043c40c18400d191580c0005040b400070058001c400c854400314102100c20446050321f84051302000c0c031050102825044c80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 546218165 1250 546216915 546216929
    0x1d0c07031b230c01090501050c0c0a060c1208040503070308041118180102031005060c03041e05090a0c0f0305061804080a110a030e0f06071401060504050a060e0606090d150510 77
    0x4028000001c5c049111612030070b4140000000c81c410065400c1c01034014441c00285010362039522200700070a80d04003000304a0f440068000c6110046004043c81442035902400851a04c50196001ca5a049010300110341c0074220410f094102e980d440e01da840c0c851080155082c3c545043c0342424890a04103c03000350300e0344100f09110180c0d11452800094450556280e560b0b0718451845a20314401c981c0007100c1c803c00080500703413007008013003803008481c000c81d40f1404a0316425018400c40306000f00c1100865031a4105a03440c6019070000361740003038000e20601317426a1280150116000855040359103100010f01c0075187c9402c0001c00c5455000880107080b074500036a0040c10351850041524804c80740c03030400c10099600c040440d00182d071710444003010312184e4041a8060201c0303000e41407003075050a0010344c1c83c4182d031040030100c070f80851003162a6200e60f8188402036004464840d0040f0359844158081000404408019114000c00040030310301086054850388660f00030030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 546219415 1250 546218165 546218173
    0x1b031515050f0a1e180c180e040605220c15020f0a03230406030b012c0108190203040b04031205041106030a060801060b0a03061d0c07031b23 62
    0x204140e1110305143c0c0a640034005038000e00300352102c000c98600003076032201841690200e0354086450b25601710f182c0751600c039240c901401032441d030526000c0040e80100404100044000340c0030840c603821003a042100080620400082001d15183d000030b494001d9441c42d42071541040702c0c4ca11282d040450040750b102801c80c80b504101125142c0180324405401c100800e01c0c00020b04c003e10500c0024011903170001c65946503141c9014002e00301556595000c20b0400c10501c0c0d6202c000400c1c0c6010b441c01c0726000d00c402a01c1d40054464490181100c1c80c614411042c03000310350681e200542c040d500039a44403e0f03502d801e1a0041018890b60003150b00c050a10b81408002800503c0d051f2102904541c11a1260344003102880141400d5001880c0e66080500004990611200038001c4200c01d036001d1090b591941c840410160181c0204005c004041002a150010710301c060a2074030303c04d01c0c2406000d040444071042d4001c0701da038283c48c100c814405042e03000715001c441030f280c01c05040c054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 546220665 1250 546219415 546219439
    0x714010212031e01090e0d0806031c03090c030b06101704060504031110020a09050303040b0a1b0501151401030b031b19090204140a03050a1b03151505 66
    0x30344844401100074840080400070580c0414010341071642001c1c024101d0141c0c1d81d4625150015000e0301d910b0f4091400760061104560f40300c2d00d221845902e001d0001d109581e07580004550340254401c0a00030182d4a45100300007500440031140103600681d941c914500701041044622800e01c3e03440414031810191204131f010202e80a1603000303401000004050340c0f1030605031100c182c3c442401e2040c0c01103511207130040d84254007501c401000c558408941030f4440061603500d2142d03025045100754140041440c1a120b981440ca095411114400000b40551744040c00c1d200130036440c039000c0c80d00c54410301c00155018219101d00100b46000c0c84650312000110792148000341800040c804048080c01c9181c44000c2d00320104440d8600c4c10724015a04e0b14441e0080d0400d000c0c010701c0603c01c482c003001c6450f101284a0990f41c001c1d003e410220303070365915107612041201c581003046100c40400030201e81001c801403c03107003000c0b1020803e80c800c003001c010340382d105d508040e1207807142c0001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 546221915 1250 546220665 546220667
    0x801050604060804080f0d050a0501030308090705060711030f030d0c0f0c080702010e1f031b02120d0b0a1205010504020a09020c0c01080c0c0106120c2709030e10050903071401 77
    0x541904150004000d542c0c8080c3c0200401d0f0b90b100300424047c11900782024840c011141d0f40c8580d040b01c3c001d55804d4030584880c0306603901c40106102e0194021402d1100700c021031041c0c1d00010b9001c40090864008503100412030303046821803403590201031f54611141c00031a0700078228401440d168a00030b05240640c1d56900014054280003038104981e007020442c807601da0400780650042c02c1c0b9501c0c03454400f40381c4010054110b404282c1894006c0c0d00c00804101e000240030159070210b209524204020704130b201c80100010011190701c9080c1d00c1d030004140d418894000440e80c0244004a510f05e000d0043c030220480d25800a2182841000b044000329004070f500c04580f6802d19000c8510340765808000100e000f8100152110b5190100005000100340140f502c420310862910001681c2c44800004407843c00d050020410b25000186816280a5000d0354400d886070405450440000c2c0c0807458640c001703030114000c1140054842e00c1c919082018100600c00c4c02d8101448842c4100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 546223021 1106 546221915 546221927
    0x1704120303060e040210140403020402070c151e0f0c12031b030510030f031e0f031109150913090b0703060603150e090f060109020a080105060406 64
    0x30300258603c401c1031054444c3e45c004080c0c461544000c807040e00d50391100c040c15400807100304404001603586101404070b49000e682007005040c01c100c41c007102e0810841100c0180300004642c4101d441c4a003030303804c8411f0301e180790200310010942c00a8804031a9070000900100c20075141071001a49035102520243c03060401e0b058002c000d000c01d500b12141600d00645031002c0050500c0421060395504a40500c6440c2a0454140d08140c40c0c5e80520f40b2003c600004800c0d0402422041c2d050050b0040c003c0050b020314645036444001600d50141c0d00d481c20850900400d07040410345d220740491100858810081c0034844035440c0442008101726444c0020074900800400c001c4e100e485500b8240710f1144140c0210360a00700480040c101c01400840d45100d074807659101c54400340911070082ca644030004d601c0d41c00c0e07403801030954003050300203a000715014001008401d074012 = true := by decide +kernel

theorem cover : BRFrame.Cov 546043165 546223021 := by
  have h0 := BRFrame.cov_init 546043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 546043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 546043165 ≤ n) (h2 : n < 546223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
