-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0953
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:28:13.908422+00:00
-- url     : https://prove2.me/submissions/7e8bc0db-b5e7-4bde-a800-acb85d6fd52a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 171223021 ≤ n < 171402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 171224271 1250 171223021 171223027
    0x60908150906011a0c101b02070302010801051e0907050306030d020c0312070312020d06060e030a0b060915090c090f1f0e0d0f060906060603020403020307090b040209060a030515010504030305 84
    0x1086030404404c140203070b42d844c500b40581c55008804100701031942401c4a40491039480801d4480c01d4220800660011034014000600241c1d070841c9806044640581d0294a10750b204a45c041810252050310742e40005280103004903140e2281c00345016501c11016141e10684404003170741d45402100c20f2980541002d00150b8884518001030300301c4078003a061500400c505241c04804036440801901500f950301c040502090382d1045031407a0030305045c2c0083c10002d040fa12914511400144868412007882d80041c4194500010a48010402070401605030600300d9803503005412001c98580100c4282d242d00c1002c2c07811a05c1074102c5902d0042040e081c100068017242c03014040050386d5000036449101c2030010f9100c0346001b480a0043d0400a8a05264504141901c01503400b40f002c0500500007440076a0b00882c1c0201110298180041c0d140342c040023180103802182c000981c000408205a6545501600f00324800d141104248441001c101c00540300ca0090307001c0600012024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 171225521 1250 171224271 171224279
    0x8030c0105011703160f06021204050307031e1b1b06080109140106050a031a0909030d0b060f0d020310030c0b07050601060302070b0103020f01020a05060a02040e06030a030c0b0406060305030406090815090601 91
    0x6c440d5281d40d403406500d0140c90561103441410702280141c80403102a44000b0340e140505a21411807048001c105c1c07a4060100d100750801000380d4041c0e484000702026070074804003049803030241000908840d92001400c56510800606002000d01c5203001041c02c0400c56403500b0148801e0078141d503c2c603101e50381406488282103004050f096000030000d01c12110b5908150368080c0814418074140c0011035440b448202120180c507a40503c95010380c40a01c020048070781c06409407a05586010401602e80ea94100f8143e0102041da1000d80031602080010544544600081c40703031501540444247d640d907440d00710202e1140503001392000080c14014030062400c424800d21916051040300c0c1c5c8007401e92207440c24000c0a0340c0d2607112640c00a0200409044510081d80c0244210050440c0000517100501456a19980100004002070020b0704110540e88a4005542c00c0400c4a40382c7d9241d01d0094480211801071401c68891400c148000307e00c011209886004d0034006005d05074a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 171226771 1250 171225521 171225533
    0x40b01030f06020c0102040e090d14030112061404050c09010f0e0f09010e1b0a050f0a09110f04230d021807020a08160c080610060804020a08030c010501170316 70
    0x544088500b19020009049812400d001a202604400b00c45840303d08100e1105850075840300c0507007050025070b1240c100c556071000141e90465407000c1d4840002c072407600e000401001447d80c042000040c0300d0501080c07101c0011080b5801c0e100341c0d180a400e0762601085001e21141c5d20038a4180d2043c1000a90814090000c10b0340008803071001240c0040c000804a09020700100d60303001c40710300a212800c1c41d2400c0c1c10444010502950844c0c4000881f0b404550141464040e0030307030507a11303101d0300301d4014806400c8a800d00110358100b5100c03900c4280344900301140d103450851074050000802254035041200740c40310b940c010002102000707480303080251120024071010546c0100d88d400b02c08941c50034000c5c006444150803000e0152428940381d00106400e42000c460360703015000308180301d60704035441000d4a480b41403110b5103558910004480000300c2d009011140004100030102d45015084181a544a2900e9800403166843c0c256524040c0a1802c0303226035119541e00c2c01700d41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 171228021 1250 171226771 171226793
    0x60f04060f0905100506030c041e05130210090f14031c020c04021b0f030c071215020d02091f0e0402031009020406020a1401090f0206130306110403030e0603040b0103 73
    0x191061012038482e00c82d031195402e043e004d00c0000402c035190f100301b01540c582408901d201c4482100c0401c04444100d0b5503a914254840e501d10303403541c0d66404620803804104a007800b0ba40d005011813020114490010b00d4140c541c032905615050002000c18180303014281c0c502e000f030b400780083c52070340e1004c00040304001800c1c002e001503000d01041d00726280c403140020202d0624480c0301c0c08415680002003498209554040d080d190003d0000c0d5044400100b1210100d81c034a80c01004140200e041c4000140809525100c00c0391002520504250032034014003e54072084410324a0025650401d11020104039118400240c0d6101c10364510f1416078050b580042100c1c03850521161241100401c0780d009411942c0036074440c000401c2040398a00c0c80305840100c00c0000e110f81da1030340c1c0d00c403444070030011070007842940301241c1d10004c840c011082e00000c42e0014024000d01c03110380109001d540c0540410f40000321141030750080c2d13040040481c9e00130740c0d028074001c84030382c0b075502e803910010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 171229271 1250 171228021 171228041
    0x1109060304030909050c0403020108011202090c0f250b060a050901060f0306052e090b03150f040624020105040506010603020c1e03042c0f070215010807050111060f0406 74
    0x890b0001010901c2c3c0c4c0780740f0900d4420014031031091794132030a600000d1b00d10b0005900800740d49500f031146000584a6072100c030b03042810030408030786039050303817102d41294041c0f020319410a0030f03205c0c00c001e02020070b044483c24183c02143d00720402e40340c8109004860003076014032034000c1203c0004200d16841410380301007045881c9070002c1d4031038445000954130740c003141c980041c400c06411003201403080c4078414441401142006a00c2d00d02e80000383c41d4a01004201c82c0740086440464040d0751100300e0840903c000042c4104000790702c0341c4042c418120281448003144141485600440e40140700b001c4c0520b8124004005030381c64890101c0180d400092921402d00900c1e0205451140700c0c00700c4c40d6a00040c4000e591211b082403103101c02d58a0880c01010b81d0201480d4000140c2da10b2401c1a4010300201442411580d40c0c01c03050f440c02100d4018901044041000000c14103008100791068980036078030341a034201c003600d06039610541a81c4000072803d4000c00b00780001d2072b90b48802c1080c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 171230521 1250 171229271 171229277
    0x15040b060a0803130e0c03070c03030f09061407080703020703080103060b0303040803130501030f060311010305070504080d030b03010c020c100809070b0412030936062105010f110906030403 83
    0x40c0d02e800c48030703095401c807001c4850448a5081c050142408495520350b000c0410041b203402c44c90106002040c6030312000d40a01810f0352103001e107500d594203800401c05aa04500140014041f2072100b2185201c00c80741c0400182000d40401c05d00b80c400d008030f03610300b40c15640c0c00079664211b0725110020206c0c0144907a03d0f1000304000203c60358280090441c80f8140c48080409a10309800517094401e4075225440f0503150040520011390403081a0b01398000a00c0c00090707c2e038032a0b0701a141445a900300e4402849001c01d4038076220303810303008400203031404d031b00a10042c050344000b44d0350380400500701640b104281e50382d51281440358917190360003c0118100c0310300a6803003202c001180c0c0103030404180007601d0210f19043c140c0201e00480205180c001c0f02e1010038141d58480303210608202d0004200120741d05035503c40480d604183e01901d20f001594103108030f0001e1050304c08907828003c0715554200000d0b0358140090b84101ea074140001a801c81c5801c0090040140542c00200101c0034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 171231771 1250 171230521 171230539
    0x90f13050c03070e0109051011100f020403060b0d08040302120102090a0617090a2004140901050403080a09020f040207020d120207091a0a0b07080f070c03021215040b06 74
    0x2051055010319405850000780072642c0b8140b420004206a81d045804d9050200c40701c02040903031a6041034413104c0343d8500d400c1b0203c1065084190a01c18080c00451109042100d103481040380c6a009100300c03482900c04001c551455802d200032281d943c10082d29003403081c0400c1015091401c00321150301c4261000500e01100e080c00a80e0b80b4202d80c01241c00120021641c140d050140c01419400000d184020b00c3c040500e640c444048101c40703400b00c81d9641b07224403031031210386903504858040341031342d0707080821460021103560081408860640c009404030700410145412480303003030003054001d01519400440f87d800e20020398400d10080740c00076403103800724003c140c10b40c60f041e80420440e0301403e50549010701c180240c4282e055240c003c0244145d8294490303907601e840c3d00807140384200c0e1684500540c00c0c42c12042c010003136580b1002c003000400340d04004070240720200380c5e40700721100d0350200301c11102c190f50340703081548010b032004a080200e00418264481c241d4409030050803156 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 171233021 1250 171231771 171231799
    0xf03140f0f03042a170c040603080c060601090e0708060d0b130201020c0f0109030f080c0706021006090204030506131b0603020d0c02010506060f0d021204050c0301050109020906090f 80
    0x502588407941c0c440c40084040300b4007013048000c02c0380b024500061040104100c403110f88105908695201e0740410003410704c2040400c000c28800d920503482c0041041011580d039040c03420481d88600340003032941c001e0f040040c001e036000d03841d000181e070b101210300e10300795480c12010785040f900580056440704005000d900040c1020b8a59403240c406891035500452891001a140000c00e10100e4426204000f04e400c05980c419011000c494000d6100842000641404030040c4035811490030709010b00240070074a1500012010503030745005904010003076444964400301c1c0240e00004190b50441d5001c01d00102018250410650141d441c2060084032607242002a5045521000200380c0100d140d42c503810a510600100282d1800207000c4c61034584000354140c0305802112000e04e5021400c060765955560581c0c00710b00c229502c0140600781428810703912000f88003228030a43c2420008a83d01c580740c02035640c001c4000d0302017402c0442060400c000c55040c180c8031a0808a0010421 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 171234271 1250 171233021 171233047
    0x1060b04033504080a05010f0b0d020f06070501090b0106180312180b03100e0c032512050709051e0a05040b010201020c060a0902031b0d03030207020f0904030201050a0609090f0314 79
    0x44c0780c454014080e40c5043c1c42d100d0300791400703801c5003403a1390301d0000b510055031592a481c0c800e444d41250b10100720103d02c40050550300896102411a42ca4280d0100070410420034150584880351902160550465031120b0729009038000141400101950880d4960140d910281c04d0502d0103010030803152100251000d9800848244040d00c0e110501000300030101c004e12504811500213017451860542e6120b254030f001601c4e00042694401c02d0886460311500c0403e5894581c40300a01007800e15040082c42e8030058000c1500c5000c0300c1120305000f420460010306000c802524038a8002d2400c0304120080c2034103048107040d550200501a0a164203015041c071500e41c0b00c1000940da2181d0040c11700d000322800341814001302c59036074041c0c05c0d51598840b03006c0d60f901d86070150740e82e6014804a0600d130900c100941c2c02c10040030038041056019000280f06003855141003090302ea481100b0001d1360041d410241c040e81c4840351220100b449901010100e210081446103800da2800c546 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 171235521 1250 171234271 171234277
    0x82a010815120d11070e010b03060a1d040b070f020a1e05070e090d0c05100f0608010c0807030c09060e0618090103060b041407051204023001060b040335 67
    0x180c0d8040d00011240f410751604140494001e200c8000180640780c280380901080e06170602031902159030110000d02c680e569003100f075000d0088009180c4010380d040b03103954007504055408541d02101280055100e82c42b840d0401728680719039000746441c02203900ca0880b2010302140d5280d41072814050071020a00c02c1101000a00c00548040e04070f20701000c3d5141480d846c0d15002c1c00308000c51000001050300043d6150482c08103103070000d07070300c0d00038504031000f45090f43c0036650301c0d400c042a03e6500b50704808001e120394081c1c0c43c184002e03494508121100103040c0149000304000c00d0030f40d5036030700f0301c05c015011440100d4180200540040d00080d240c2074260702c04c41341103444040c9024642091f00500020221b03030107241d0080e00386820083c00314006c42c00042440c181002c0040d0075980c9041051042244456210101100008450081c280d251010070401e6007404000034582c401c0c00b0880d012a900110b248680d00080560154410100c1c202464902c40c2401c3e5220000855402 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 171236771 1250 171235521 171235549
    0xc05090307030f0227010e100e0112020f0906030d0c02030724020d02031204020f0118060306031a01030809060310030c0603020304050c03010e030405040b0307031b082a010815 77
    0x243c0ca07004000d2041006071221041c07000102c4041d2000f1490b000c00c4151202d05603180c0c0c60081056560b0014580c0042840342e1000e110340341404000600c1482c0356084e450202d00036680006400003074414007940107003e0b030f41d01d600b40e132090044203003061298034042d801c0c901c020166290300d5034610a5540307141c002c10b901800b6144800404103240c0e0104070341210116540055801c1c009403061a8000c40b00c014000f03401141129802541b5070311404900c801e0320010710040c1c0c03826465043c01002044140012606e80304c2c21125041c0444030071b02c40030b04881d0b01c0244985003100303540c248100b540000d81022101d48911401000152038860404017802c1a40e60041c1ca0b4901410114904a1a04070450099250185082c0004130210454040d508140c03004216519840007180ca400410343c40500040c00481e10125203401101c3c03003900f141c641c48211101a464010700305800c0020000040d10021a0507800c01c0c80d5000e8a03180b540010b1105a90b441110740801142a828030391308 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 171238021 1250 171236771 171236783
    0x20a050c0a060b100e030706080c0d060b030a0c080405100b0a0801050103060b0a05040e07051504050303130906060503070e0409060204031e050f0f071a0412050c030d0e03030d0c0509030703 83
    0x100d0860142801c4c00859400300319880d2a000c0078003040b01094032084c0070b0050b4810415448001004010700c01c0840b0281c03150010304204407a41c980d2060300c56001030f110842c1243c00c0001c0c020a05114100a41c047d54000010340f1045001016500c002c0007180545a01300030550030010340c100080c42994001c5010314000b144802d00c402c01c00c12815617030f4100c544038070b1a054040c1068180000c0590944505503250030541c03d0210302080c56019507404aa07240c880018400c5000320b070b102c08007084800880c0305000458580e50151101e001c1241d11500044c3c01420080d0b0746d15168221000860048000500d0151aa15000521550500c40403c001c00303131504001042010000001c400d0701140c060101000e0300382c07070755441d8003403407141c0c001030540103030140740058245c02145c000707000400724120320080c2450034a0f10b071009070f80741d28464041c3c2801486d00d28028410b42c0d0609800030065850f001071212104002d0804c00c4004081180502c141a4103480c200700020103580198 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 171239271 1250 171238021 171238031
    0xb010303080415050720070906060e1002011103041502070f080310050f130209040e07180b010905010909020a1403150301050a020a0806091e0103030e040507140904020a050c0a06 78
    0x1003070107020244920003510f020780c075283c200f110003944401c1c200d901120003040e0240b5840c070005154505041a04800110392818000144040d04124100207200702602d42e420302c051084400d031b00325802c40c581c2a8a01504000083c000f80075103161107810307004175400500300f80954440800300070301f1074021a11090b0002c140403000311a50028001458200c0e500c5074136541a5001c03811402103080401d008070b03000300744480a035031507030070004440d100ba004682d165070765140780d50150850802c20016092604115100f42d51080b12841c0c160f6606131a00368100d4600104200294003003104101000001e1205a14003221400194041c01003a40d405092041e520201030865101400a0311b40c0303407040040401e466000742e5125402207040b01c0800c0c16560349000c040190045407210170b08010040b00100070903810040e4042004070a0340d04010030f43d24890709075003240c1c44a40c4a910b64906024142c5c4030b140c50f8009202c0316203d842c142c2d003020601e50f083d51400442180448170a501c5e6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 171240521 1250 171239271 171239273
    0x112b03050c39010203250210021507020604050601051e040f1d0703020a0312051903020d050906040c0b0901180e0a05100e04030e06070210020105071b200d0b0103030804 74
    0xd440100702240c00081121500b41207003001035039900c201c10110589903ca030240d5080c4503040300c01e00210540140c80800d0380d64001500035190418550701c04c00c0800d5100200341014070014501c2e00c91580000213001c06c0e420807040040d8038134111240f00c9110305d036980211003515540641b540b40042101c000c034121907003060518110403001281c03055548036031410805652900341c3c403822079411039406251105070013811229031017400005500004502d0014048030780c190f0040650104041081109440300c20401d52030b00400d942c054015945140300303020344200f1500801005405040036101c00c25a048001c0c80da00d83c50b8003818801d10721130100f0500820300c5c091554406000c26100d03041c6420310320b000a0510003d84040e08010207442e8403101520b81000301c5101e0344c0c00501140a07172007000e034000c2c06007030203c41e143d000850303c1c005240d1400990000000303a83e48403500740c888215041288130051b072809200d5a00150252111000c520505885c5000c0d5000303644802041c80e00b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 171241771 1250 171240521 171240583
    0xe090612011b0807021906091121121218011b0818030a0f0302090109050a1413110a030e0705061c06080309060a08060a05090c07112b03050c 62
    0x8001d00803001c2d50408120011031032014018507041c281c1c00040007401042341c0c00c0c00c2e40c02e182c4100d501604040c0710301071006010204141040c0041c2c42000310341000c008440c04c0740c8940107402200c0740c0d036011031002c42e08000950202d0070080200c2030001a2600305d012a8062041161034240c0210329100e01384003101c00c012a2030303c0760f88243c0d170041d441c00d5640d0130020700c600c4801c800a4201503010500c146075030710801c1482c000b000003d22400489440d201c000c078100800308003082c0301d240b142c00c044681d56084e000e4401e0001c600310480741800a0b02d003007036001c4c00500e56500030501498a002c210756640e5006000c030200c0060001e103280340d503c0080004c440d5035030810707019940b041c0186202075131244200c03008141e0a03d000c00236501e5141c04240035030340c00c1d040150307c60074180401198801a20141034054054403100614078612024804061480c0034498820403201ca22074002090140b29010000d10901d4928a00f5a1032840241054610b42e2000c2c0403504100d01003614100d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 171243021 1250 171241771 171241787
    0x2062502031b18130f050f0129030c010905060c010209040c020d140c28050a0803090714030a080903030d050709033e0301020403200103060e01060e090612011b 70
    0x410f0201c0c07600103003840b0400035000c4d41042d03c010580c610101d00c0208100050264a010084040081c4a01046100b060780c5e9420070035000c82c403146488880032114a00001d10101505068640c1c0d451642040c0a122a541c00b142042c041c40d034007080413003400d03101d038030421016200306d80c05000c0a03824000300914222810303104010031107051054100c2800d02103070709403031016040d9011070390350180c45241540c812820340c0a0594020340c51424240710f41b05004500c50342d5000e0a5508040d100c8010000c9c9415000f0101d41560001380c541c0b000a540c140200b2566100070116402e00c0255526034003a11001c54044002681041c410810006200d041d014036420102c01e204204c42d414003805141079504641c4c0b104a990600e08151b982c41c04c5d812100a10f80000c0e00c1c034000344207096003048002032100700a000a11306072000482200320030340345040c1c8405580305031a440c2c5020401c0580000907018950000c581c00003154056000d208020086c515030001d410440a91503025001107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 171244271 1250 171243021 171243049
    0x90301050c04030b0a0f090819080601020d120509070314070602060a02090303090d03140f180409051504020a050d030f080606160b0405010e030c0304031104020702062502031b 77
    0x12810b200c18000950031101c2d00f039008528920000b00303c1042e4071007070040c140745074000c0e1014a00085206402c0380707001c01c46421683d90340700d146283d2107440049079151081c0940000044140b0600a50440150825500440e403042156580d80e00c0741c9500b0206c802c58450130740c20b984480010803c00fa0144001580101072000460070300420360007003500e900c55801c3c01d0380305074906078500041501420030103000309440307074105407035020161480d031295010307110700070001c1e050300601d1000d440c0502a0150480d0b00c14041d1502d503600300c400060103000034004030307805201c0c60300206003900d4140c2902c0440d1300a0381c2d16104a01a004060300008010b848980501c104000d100c1001d100d144403000e41ca40d000c0210040c40d40c4900300b0a0050225078800c2200c2e000028012041070740020141c030907240105e51003c0002a941c042000300d11031031030003c0d0411424004a5001035001c100025140d040c81c000c10240d074041d900280c103150003204140300090b1803465101450038204840c444403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 171245521 1250 171244271 171244291
    0x30a0207080d050412060608010203090f0616021f0222030614040b13030309020a0e07090929010509030105091608011e021605010e06010303080c090907030e0f0a0809030105 76
    0x9502d005000510910072400380103900b040074a403000400103942c2c00b1a00922813040210344a0a0140d116a1a806148240200c6124034401300e028141102014004ca10f1550014500070021100c265489500d001c0c070804101c0e4240062140011046d10b00f400b500b50010010490074110b1500138101e468840381c0c1c20030745d5079000c10040003d04400d00c2da038015521a2000b52a00d84911701203000e805003000080d005204400001100c1440003c041d004604030386a450166461300d0000b021100038000c559104851941c194008440d460328409502406240061502100d00082070035141c0940303031200103902c40c0e41c0c4280c00521210540c1301130461b41000780004001040203c4041c03902d07404080070f0990002d82080d01c80e15101c1c0041e10182e0000007407006106009040d80c851500740b00943c0482c0e10000001d02080038107040359801c40c0c2c010b040c0300c3c40b03495914044005080f0f80588010324400c0c0108805111000c01580e4003561250010700c0d6100c04130401d040c00d40341c000d01010070ba = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 171246771 1250 171245521 171245533
    0x80307051b0a1515091503030906080c09010c110904120f050403050c0f0402220302040b060c06190608070801050105030c09011a0706020d02030406020904050106140406050c03040b0309030a020708 86
    0x14401036159500c2583c1950301244021413402004160b00c0382d94408804107217031074680010f4000c3c481000301281d01907141d81c40d0041d0b958100703a94407402140d00d074450303030003c00c00090150b001c2c5000141d07640c0038641e500d080c82c20590205000f0301b019203050703850494908000b0002c2e035101450405020440c40e00a040a107583d45155035900d003151424414149501c940280c2e8481d0b5040d1071244d808211800b200c214981e039141e2102c5211f0100b80c0c0124203010a68810f800d040701120444040c4c80020501c559408001000c02c0041d90b0744004129101e6a0004401d50108162000340c0704000000507d03501d050205443d000d074500216002c0c2c06403100400c000c020f0740b03049022592600d200c161742c4025905e800c400910078222946021480402070106000f91a030190891443c01d460030045a41c03140020b890702c1840180715509094104014080b0394800d01c080c052503140d040c1164205603e48075198950f80084500d070810f07500c00700b4480b00c1c0c01e50402041c1c00a121490180c0341d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 171248021 1250 171246771 171246773
    0x160509281d100516050403170f0f0403051b060702010e030f070914090d050316030209090403080118091115090a0b0909011707060f0e04140108241302010c080307051b0a 74
    0x600441c8006040000d000c4108418201c2d820210b400e1003c86400c9c85236200d002c80607a8807590041e001c16982881240d80c098114402c00124205c4200003d041034109600c940c011039145580b18042c2d5014098031249240e8110104810b20113084500800305000b640050b502a009200900189440e480b030080700c0e418a81080c00c0b290031002010b6401032113400d140c400c0d400780c0f2800340c0302c580102400f8100000c0c542d000110328103941c0c901c41ca0125030764101203c4400d9542d020405046c14403c0740500100d0320f840d507124151540c69010032805c00c1d1980c000a4a008410751254000d0f07400001c16148901e0107a600034050140c2e41e034594613480c941015250380740c403540aa01c013840016484d00c058140030340f641440c0148010700a1000c0382c3c17008600c0d01512001e102d4407070703148126180326040944003000e48400404100082226a442c68000c2c0c40e0b00c00090801d1741072100320810603010401101c011841100d064517003076a02c40c0c00325805030700c040ca92940410391343c0003104124 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 171249271 1250 171248021 171248027
    0x140c040b060301060e010c05030409021c0b15160f050d08090f12030a02070501051305010b010905090f0408120c0a08181f020d020c160509281d100516 66
    0xc2c1580e81d0b034982a0f410410a05c010707114461405405001840b011800240e43c0d20750390000c041c004656071402e51174143e043d03029025200f440c2001ca0b40010050100f1202ca541c4000bd4800c4040300300030400c40b880301d0340343d0a80c68005050140c41c903400c901403010b0010740008005800980d9480203240d0213054004441d21115802030b1404c400c10004085600c90180750152109150050002c00039414280c4446a010808080844281d402c1540c072544560088040d10101c4d0009410940300d607450308910f28801e40020300440d2014000d014006080325803006943c415200c070401151b980c545490040c017607210042441d144000646200c2000c01c00100e12000c0c409880b0354120700030100225032201901235040d0944080c0d10200c0d01c04800c10001407402c8000d4400880035298a0301c6005100300d081d002c036010305009030540c0c0729010601502e03001d0484291104400600d0101102d000d500c110321100ca1280c203540041c04610303003203c0724813683d90408011112101265080381020b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 171250521 1250 171249271 171249277
    0x703060c05090306010e07170a090c0b0301060e0603040204020705030c07031119030209090c031b01140c07030201050c0c060f0306040b0d38010603020301032d0204090816140c040b06 80
    0x60314056020704041003e0500230080e0480004030303c4150b091a1400c2d510141c01000250819200984207100c00110320014900702c9041e84e00681d84d120110b200013060052039130000e001260403643c20002c413404914140301034688103241e0800703844820314604260101c0010308200c81c0c42041d0f41034034a00b840f511601741a044039416190040607503204404c090501828010300b64240c083c0500208000e040c13400d402e507607144240c0b40c102400944114a0280b4081c00b03c03e1f280329801108140701542c007600c003900d6092240800c44418001420100e08a50002c450340e00528401000b485118640740c0600701c006102981c07400501000790b06c450011000701c00d100802e00e292102d5041450100070003441c2c0c4c075400b84281c14855607440b88000d0007540f0901c0103a0b507440001d640810252903650041c49105c3c008410091013a440d034003040010000c4101c11640b00710100079580380c41d801000c8085480c0d000d420a000b00d42d0300600c03030509180182d01c6c95442a0311708983c02c240755a4110075 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 171251771 1250 171250521 171250529
    0xf0705040b01030e0f031b15070c0c03080a0e040b0105120103020906030c0402040311040e070b0d0c0519030b01030b06090901030803090703080d05040302070f0617060a05040e0703060c0509030601 86
    0x404100c4200c240700580040c80310140f801c03602d0040c208042c9440100200420b1104d46042c1d07c3c3c011200070311035054135258404901004018801d02040065224500140309103008212001139141d0340d64540c1151740c030070300300c0c03401103000500c454041d07143c503118884000c80c0a081c43ca01c1c0080c0204035804a1707405000c001e103c0e5407201d01107a441c2e101046071081030038000d84215551070701c0741442080c003101100345502c55424503d2010001d180801ca01e003c540690f0809800c0044541c401d80140000d401204e04011301407108a0407850040020844c803071140e14001106041c803c00141581c0010080a00801c1c1c2004888607a44034803c8440c11640c1100129850751280707406c09081818540c0050f29505000c502c1c0c000c4c562081d4416030065210340c080b10041a501c50448034000501d10419001c00c101e489024440860403455aa000d200142b02944464481000030203c54103916003401a03404003005008000c01c900c05d04803070310040e0600c0c1b420b0894620020381e988505000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 171253021 1250 171251771 171251779
    0x11010f08150d050309270a090c0e0703021314180705071e0609140d080c0306131d0304030606050405150d0f06020f070308060f091317040801020316020f0705 69
    0x401d101400f90030310958400074001010341a80c2e07400601094046008074000315140125500400e402c141d2034401e061140d940f20244c40b240500d081020741c040076008003600c00b496000c00c080400070307090481540183c030b20305140110000004082c01044602021545000350340c0c5414801182d4010050301c40d01c82d807080d441d00d2480d2040042d80c0302054540d000405035030400c11244104015441d8052165554400311480100403030422106034506031000d41c4d44c440b081001c24100d0030f00048107070000b4101030380410303400c80a904011080300c10041d80406600003180a0041104a0042100900044a0034000c60810044980b4039a52801c01184141c40c500801410130403103c180340181508042d0464841c0c411185600c0700c0e52106408800250710320f00019100d18014540c0c40d09039038007614036015170755804510141502221403d9130460785180311000b400d01110020700180c0400000580c0320306080180108000366615400c0c01e40d001140204610500010382e4411104129 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 171254271 1250 171253021 171253039
    0x61205061c02120105010602030301082e09050a0210080702070e01030b062404030c1503020a1d0a0909050f0f030412030302131203020a050613150c170411010f0815 72
    0x100c0003c0415120b05040007095081c5000003d54a0700400034504881100701034410350b0984d56002000d0b0024072001e8102c1d007044444a001c4881c01c1d501c0016560302c03800842e51303009010b400280101e1803074000800010005810018207541c14004100140f0740c81d00842e0307507035040d6070316140a18401804280110a40300d07400c48140204003808030920000a0107507a10340c0c40b41091040074606024100e03001c001c501003850014840d1007100c40b0740d5010758a044010f80904d02032520303181c08041b41070b03000710016030105150030300c0d00c92504007074860307001171441440440301c190500c0d24104011103940c03c180020031008840c200410715556241c9401030b600da40c091703800c9450b44200c3d000302c801c0c0490030741d420701019000180038412900500c100e511968500e0b030300070318071007000307400030111400c116409040708031540014004a000707041c01800d98240c40e001441c0c80174210b0b800d0b03600340601040031011396000001c2e031689001510341071001d40b4106107a8411110344d41c0310f013030003031a00e1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 171255521 1250 171254271 171254273
    0x9060c03041205030a030510081c230c070806091e1507020f0f0304081002091c122703030e12060a150b1612090504050c0301061205061c 60
    0x9004a9014024074401822a800b4a0902c6683c0e50804103179000800d00e00400315041414400040d01181c021342c00031301c010004a00190b41404d102e0341c94105000d000540340e510442507000300d0613a0f0aa0701c41c9251503c2c0a80c40c0c0620745880750740076402c2500300c00144101c1d9a4045441c0d80402c1480707059490120010400e6840c20311510150311002d403180c03003070086455000ca034507001c9824400c02c40e14100317003418450791288145d200d00b00070769208107003001030541590080d0079500c2005098412850081a901950810309001240c20b00054549940b00310303001030b104007055140702104462840700d2032404481c44103d010150910030010752014040d500c541680d04c0340072060b01950796078201b4010300d0b07015004800300400d186460b200081407010000c03064555501c0c09950b181c2841c0850340303c000541e9030300d280c80020000b41c404082042d8486000d00342c0101d428250b016982e601d014002030290004002ca80905418078052104590b1014541a0036506000c0180456200f03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 171256771 1250 171255521 171255523
    0x20309060c030d060306020a1215060c080d05010303030e070603050c0912010222090617030406080603120c0a0201030507030e1c0e090a0c09080a0506070c080903061314070b09060c 79
    0x3d50103d107403554100303800882006010b8005d8402e1102607101c0c9002c11013000035070300c1070b540c88610001999400c0802006158810078014600b54054000140342141c01c10701001a01c1c0d00740c0059010a48a0079040e5a0b00002c2004070028515131808108508100e400391000380302c1d070340425101e680c0c3c18440c291031a2007035045401d04850542d140148200307801828085420320305c41c0044113481c2c0303030b00021000385440315000e1104045003d545814100b000c180d43d07110010305940c0d0588903100130300707081070300b43c10041c880b40c5c3c403020062101d42c000384001426201c00030808820036081c0309603c01e510741c0c00180c0000580501283c144909030600080315480300b0f02000d5035008043c1414422610300680c8149403c816a5913950420b540701e17401659100342c1d10800070019030000000410040c1304030094403245120710021444c140310080001c2c501041519044030b03003010000c858003082042009810002c10400140c02068940109100d09006003036a031409081e0005002da940c81c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 171258021 1250 171256771 171256777
    0xb121611160503120702010c0f060608030d0203040c0f05010f0c020303090d150b0306040b041704090c12050123040519050403170c070c06050c01110408010b01030f06030201020309060c03 82
    0x344250031129255205005030000c101d4501c54680a402880780c003010012a032400c44000329010303110b94040c1d00c8942d940c010104945801a29040e0f540d490102d0204002c0c40104100005500d0268803030401d420141c001c9a00b50b409101465080d000410860340c120788002c0e0b070741d0414180924049000d0011030306511030303411560b602003603654140b42001058845042e01031100c481c100701c610069014142c2d5030b18143c0c0c0240c20300d00004000380008484809480301484403402c1d07682066500e02e000e4065600c410303501c04c00308170402440002c07003155103c0c0301e0050002e01c039190341c05044240c15482d0084100c28a901882d00c5030006008804040301c02e20003508007032010031041c58076040040250344c022510b99600480413011500fa0017540c01501ca1030303138100c9102d201d002e01d04030b030540b4030380c1c0f01034000d081039529800c503044046810000740005007984800403036600000707800142151150145244414074150042c00541d1f400400c1c4c03043d02009880c0750f0b9680c3d10541c002072440c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 171259271 1250 171258021 171258047
    0xf0a0605060307050c0f0a1a0c070f0605040b06150a11030405100203031b0301050a090f09050d0f090512070605030405070806040606030606090e0d050f0408070806040b010b1216 78
    0x7620000a102d83c00d54800c004200519a540681d13500504405e44a0345540f04100090941854404100300c805081110180c000e0001103d2a01d00a0b10307541e440b242c2140c000c4150343ca542e0b0b0b40300308024050300e02003032948180300310303090391305a0700d11400481107010714017a4100b0410340c1e02d160b590381c02c0300700b040b0b0b8098003000700304007104003484800a540340e02c11a02c65040f050101d60b449107413540322060b213040e01d500038140c1d5462030600b4003903030090840e500402801134407262010040350b424041403122030143c1d5110010300140c40405408100c02c1d40c07090b0b00808079540d01c2d08048201080d10002c2e82c14a16045999031640d003801da01d040000d801c041c22074060601800100016503020710202d074803c440601400b0b68550001045419081d0484402d400200340c1305c0003140704000624034880d041c0c82e078501301a00c40707002d10710b802080c1d0000d0740181c0c00344082c0700620461569007801040d50480744dd10703015130300c0c040640781e00c0043c004050382d01d25014511070780d60280007600061 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 171260521 1250 171259271 171259279
    0x302071505062214010806070f0c15180803160801060f02030d0c051b07050a0506040e0a0c14070c0503121312020a090212060406080c030a0213020412030804120f080f0a0605 76
    0x156146e400d0b0a45035441078410201140d22050003004c15402444151122504403403803a126a84180d41003000d40000e0040e1480011000c4402d80041d0512000e5401894024100310801603030101c050603600d81070b0000c0c810301030410240a01c4640c004211100d01e00140c03004684014070700c2040c1c440c2c3c0904000101854120114015440d07800987c4000704e440031a000400b80d03940d40188803461285008804241c81e81000242020501c3e8000c60010481440d24000c1d18100c4104868690404501240c0290a110081006142c10840500010100042d25140551300e8858560401080c4104008460b41c2c001007800c1d0365800700e0610040055032019583c03080c1440410500030b0045403e644100d10309400424000b00024001c0718080c80a001000e000b0b40e107408001e080d0b0b03071010352440350356020040840d002c0c100d000c0b56100c40c3c0c401c0e200da203030364140391403c03a9400100341c2da2482003100b05442034080580c000612600301034020040342d0340c2e80310761880d80c002d0a020b0f0045504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 171261771 1250 171260521 171260561
    0x150c010209030307151407050f0c070305070f06080f0108030405130b0d0f1e0302060105010c020d06020c0703020a0909170309010f06081011040e07050903071503020715050622 77
    0x1c2c810411468007144008105c2000342a00404140084c3e641c2940e805000400511448011614020042054041032001c03a40303140d45d242c2e1614a00040c9400c00d00c0203e800c2c2800700b1030740350054442ca8000750f20307480440196060240e46d1303550380a00d1003000c0c824526000a820140c0980d840540010030141c01740b00001c1060400e24104048032800f101d460411100e001000c0c2948043d181c455607169018104991070030004413455079140f003007668014415803011000441b00c2c401008425144400b03040c105d450341c010021003180035400707148c899007460789010003d42c0f500c4030004244040d040c0e26841c1c0d02e810f1480b42c018001f880e4000c908601d4028040380c0f0400c0041c4021055403030942c140589901c46000c0c20440c003d03442040c04110115011480050154010b049618400b800b00c4a00c1c907a034004c5040c444138480d50740c80c0843e50000305042031115032289074004000c0a84244440c0c20a20701146d10510b8011042c1502c1218040e001c40a48468011031843c09040c0c0035098 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 171263021 1250 171261771 171261773
    0x8072a030b06010e0609240903030c0717070303020303040605040305040b03040c03120f0e0607140d03020c010606030e030306041d0f060a0e06091002030916090c08070806150c010209030307 83
    0x40707001400d4a40b940403130740308035091183d031500b201182c00c40140506140502c00e911810740481001e40881c44043e082c0c1171043c65203d4804001905a41207a0001402c103540380c500b09034982041d041c25203c203030700849000c2c40441d40000c1100e40040c1d214000003016521820222101c4c01550410810600c0010601c801d01c4401c0800c1e4055a01640c105640308459a8003030718182a070f200d44c0e90200301c00e032025598034074044019014050060308460700110101c2d590500300190007001101080d4003140c038101d80030091150078003500c403d003410000c80450300c4900b9942c3c040142010b2042d916810300c0303c006000085400742400070101110302c07004e030f46100a81c54200031123013844903e2600440842085001030310a00401d00400a401c0100160a604000e5813008080134002d10516403100c2c00d81c01d0500484000301240b01002a0300d2050240084c550b22002d401c41d01003103040c0d0103107c0c0c55680c240c0c4143c60456403240050360b601850659601900030148140e501d4040815250 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 171264271 1250 171263021 171263033
    0xc06081005270606041d040204090b0f070e03030a1e09030b0709051207141905092d07050a0509010c02040606170702070e040b041b0b0c010b01030908072a03 69
    0x1002841c030410156060b503c01d01803140ca400340d44074035600301d00d11174400382500f2071303080c00d140c2c1081c006000130900c03c0c41078541c204410015100c43c280c4611a40070402c2003a03000d88034518487c4200d01462030b100100c00c0c01003030000c0500e001d81e100c4400c2400101601e0083c15100002c60344841d06031481c1c0380102c0c0143c00c90034948640360080d0500e161b40c4020000c0403429070180c0f076034501c18224031348004003400755901207c40a4000800c0302080410150f0301c0c0308440d842440041105260151031112000603c1450750f4940038141d840800d005001d03800c4001d4030340c007404524106440302010001207564510b00c0a0107500145001d2001c10b84030760050b0810380400c988000b55006071125601242d495505204024885824402040020740d038000495040350160081c2034150b04000040360700208107912003091034100040c5420020001e018280003145c09080802c2a0340d200d0300d07004124891000e000f050a613080b0240162903490380360b16807a1100502d00070100c607480c1d103850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 171265521 1250 171264271 171264319
    0x51515120f2103010303051e13050f0904050703030806010315090204080706020f0d05030c0c0319020708160e07020f07030501020d0510180b01091715010b070c06081005 74
    0x6500c2074010300c40034003000d415000c1000001040d6500b418a0b6a01e59142110950003102c101c6c10710f058148001000c00039044050322265245460310741000d4a40010094107983c0c3c8440107000c1c000c01400c01c000b140c40480d04204030707038050030701030380c25076075400101c0040c000800c902d0400740400c40d01040800003a40600705a0346100b04403080e15890b1041644d440410411039581da0b441820880c00c41c42c07043c0e01654200c820b0702085824106003040d46419034200030252108100c0c90700b0303c4022150f04105020003400300070007400303051040441e14034180700780d405a8450310800c240400d06a0b0f1081062030444503547c3c0c00e5403800d5850f0304c1c0060107036106810b640d51190800307010854007401e01001b0000c4a1000522000c1b40c1c40842042000d0103c03132242a040c00420f450005014880307852002012180d000a0304001e003029010b0410841e040e0450002c07140103101040c000380505800310180c0c0d01501700036099544900d040f0320504c0098101d03d40054000c42e1102c007001001c249 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 171266771 1250 171265521 171265543
    0x519050111041707080304180b01090504050405010903120507051215181605090d110d0b0114151602060c0705130c12050603100e0304091401050a0b0705151512 70
    0x7a41e04180d91070200646d1b9024034003941e4036100b0855101d40f074008150f88181c50020042c1410304c081c998500008080320f104039400e0b60b0a0351100c1c104000c040d03211442d5909043c8010b0100101e05200700c004040e80200c46040001000d40c401003030015075045464501c103100282440098410381180300d15610050751103181e80c0640e00c8904203041d00500944045a0001e0481e140e01210360311001d0801030460a0700c4d800c149160550000305401c020403a0182c14024a00914a8484d13014001e401a0302104184014000e001a02e50240e84d803030000046901220f51a440b03030340c2880c440f42011300035440309a22142004000c0c0001426030000c26401c0c450341c40703d101301c00340d01ca088800d0300c1c01100d0b120b6250b0400803034051030a5413503000b940707540c0031030040300c1c20b190726000c8003070444c1c2219902704800400d4500400c9903143c002c280c4006059100c0d40300d0b081420994510340e4847d8880c2c072041210700b41c48000307107a00380d008400f0791580b600101451208409805819110904060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 171268021 1250 171266771 171266773
    0xb1207050108130b0c0a17010803031602070506090d051507020d0806100f080a060902030c0c06070c03050306060a050c0109032a02010207090e0c0612010513060305190501110417 78
    0x19611003481014100e10341c1c4c10054410f00c81e0341e044000f0010794841c01204c4148800b11019807480c016031248540603040010007959a1304240760101c0d4500c02a0080400b1135001c2c0f80240144c2d10351106549241005440000500e09580303801828502d007603003601032449a0600300542540d001541c00c2c41d00780a43c4601895841e00802d02c03004405806180d030100d80d010802210041c40f030300e2429800640148001820342d11a003c54040c2d910070380c1d00903002c0c600803a0030300b59068103012a541050356424640d020300f8076070340d014185d404010084d42c4115404145050011f0181c402c0b11901c0c100b100080043c2105442c0c090310010220054150403c144481c0001507207400d100c0003049501600180001c038501448040501000110f008080c0100e44040e482503c0b944060043c19421001c5680d4540c1000140000b507046200c4080360035003004801c002190002c00c00b81014070b07007440100d05844050030424050a000c6816581c03d20000400040d04059104803004442d801c1e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 171269271 1250 171268021 171268037
    0x3080c0304050606090a0209030a051c0302120112060908030a09050601080f1002070c080a03120b0105030106090e07090f0f03030e0603150d050a020a0b0901020105062209060b12070501 81
    0x210120418001207a005020f54410000b00f0128901440c450f036000720400070261509421001281c2003007050340089515900201c00c0d0302d0b100381001032840c00c420f800d00d411410283c0481c05140080300c180314210300300071850301e410203106154010100700c03900250001e076241030181c125001480c280e03006072030a015010003c02c0402002c6401c00040200c00002c2115010740b80001d00298440c02d0110341e00c0e1440080011a104140620302c0303010702a071168010005030001407400d403211480381904100b400c00041c00900d802c4040442515034240240946565616099902d003e031a00a48600c0902c1540041c4c03400c1455049410b6922070741e250701c00d0b07116440a2200d80c2c0801e0316480c05442c0c8410405649060681030b26040c03900801c02c55140d201c4640205600c441c0d65048031601c104000b49003422540c09000752500a4410360742c1c1c0170503002c45210414200140c6c035959085a0300d80307201105210803600a2043d115009002c01030300200071079620f64505040c0f08950200b681c6c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 171270521 1250 171269271 171269281
    0x20f06070518040b030a030c0b01120804030b0a0213080d0f1403010509070207031a0a14040b04030e010504050303040909170705060c0732070906030c0512010605060d090308 76
    0x10401600805403a19458142030902c0c08008222082030800340d009541c80c207042120740e504105410b10701b4020b848400000b00541485070a1b16416004003100131104800754001885c82011202141d42011514000b921811a64000b0784103007003443c60322015610020410050100c1c20360304112098580c03500786120b01034241c407401c4480c0d00d0075061000c10300c01004241060a22140d200010784182c031a5107440b40c0c1c2c1c50801000020b01c212807407000c1d80402c40030100701e02c5004840306803148000304603c1d181ea5407101d0303180c009000a041003100269075000b80d01500990300a04001000e89440d04d40321032941008100781d10f000d840e40c2841c0c81031121480b0810003150400754000020b803d40f9a01e0410101043d805040220b5505040181c002c0c010031f032441d801c800081101c112187e843c0200745103d890306405800104080b07260201c200001400c5080c490201ca00030341b1002400d52030003a02e603004180c0d5034092034100e04001003880c001c5030315034000b2071003a1203a01e4880281d154 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 171271771 1250 171270521 171270523
    0xf02010f0b0603041506051e100804200f0d03050c0d050304080703180e0408090306010602031c20040f1e0b03040308250302041d1308030703200a020f 66
    0xa403181d82a00700b6000c00c0490003050740b03101810040181460040740041e5507001181804045401148204c158103d003903d803450040071000d0742c0003051030401c81d6424103445a4002d800c03060b40c0640340701841c01e0140c3c855100d00342c41c20300012005003152800005420003030203070b074440d501c04c0d4240d004640340260711a0007041a40c2c0129001400682080302a58060b1480d0700b004202210440301500700103865403421805030302c0340c2d01c03401720380da160803204040c1840e01c074043c2c100d10b0554009010002060b030900c05004c4001020300c40200d055002e840310381c0d11584e03114000101a16000038041484e001c601d800710101c1c0d28800122100c2c0902d01540900c4640382d000d1285840e10420100f00800d11034000180c128500f00d06298040c4020345240e070308881d402083c0c50100e900440c0130440d8003084070944900b0380101866042c14a0182a00c4010406138440200011004008a036025100b54000c594048100309881150b0100c1c0300d240046410209848005200e181840f00508038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 171273021 1250 171271771 171271781
    0x3160801090e030912010609020706290906041a122109010507150e15010f0b07050705010804080d050109150510120506040e01062d080705100509030d0f02010f 70
    0x11400c005542000b012500b00820549001c5c44042150349400c008180180188004c0400920a500c0001d00c001d03040d80f0048410141c02c2601c0360414100130184a513110284045e60208041344c00080f01d48209a1043e000341c41000038a8014610207a08a0640700001c1c0d00c0f001c01e5030f8410300d4042480130f100700c1d21480c460520041c1c0010801c1c0454030000300c8941d10b40002d00201c103808118140b116076100d207882c0b03658901288101100c40100700c150003503c4040003401e00d120700e80b440c00360a9102d983ea80c400303e02ca80c50411066800117401d010044059400c0e21004d44410302465a4401101d00904148204800341020044001039540741003603200b4000307689c540710150743c40c445c2c034560300081100074803140c0c0054950480c1440301400380700c0c82c400740c600d9590b01b95502c40c1040e929a4005c00b0094848a11103c40000b4001d0203000921502161011910911009400003088440340951555181c2510842140c5240aa00f015083c0014500d40d0b0080058034451030511007034507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 171274271 1250 171273021 171273041
    0x30608011409060c0f0708300712060f0b07020103150305060a110304030c06090c0b070602130602010e10020a0e040203040f03110325080f0309031b0102130b0d060503030316080109 79
    0x5000c00c5506c00141c0000c0140c1001c00344069984418050503031240303203681000b020189501c0b1420304100085401c480c0800301000c807410200034442c10013588400007802c1d030040c448010300c0401c0c0507086a00c60707000020f2000017500458607035641c03860803542d07800080d01e070030805034182180c040c1e5501c3d0704130036203100305e8050340c0b0086000c0031921110f009200c103590540b045000c22401040d0603004c41c000b00b850328070038840182e0742d80b020700980c00400d0040e0042000c6904000b41800c4030707640040c0c41c01c082c1d168140010380d40e0000d4541514500c2450180d00e400c180080100420301000411070402c00c0d009444080b01502d49020782c50f240d100c0e9400100c1402c48903001c18482111007406440340b94414001e652601c80242c0494400d50411a1166034540c000901494000781007041340c500041824025400d00c01c1084d4205a03171fa031980241812007401043c010071254440e0000802000c024043e43d943e4100040d020b0000f619038000003010440080002404040c1841241648 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 171275521 1250 171274271 171274297
    0x2090613090522020d030c08130302040510030803190e0703080c060a09050304060509060c060a09031b050d030b03030d0f020a0e0d0804030b0726040c090b03060610030608011409060c 80
    0x8603d040e4208045c0106101d01070f810413850052540002d20752038000c001d0403094240c4104181d1840c810071050b40d400030051518510f0300001000000c8600c0d042c6e0b50802c81e640e41d20b00a25100111403401009402a86000340c8540c1000009110b0445e0040011030459030a0f07d100e50395401e9480c050b01c00d083d800412940c0100402c200452058016005410300100518a064002d0f1101c61404505807204c5038055507951144041640026110115070030746402900c01d600700e510352a03200d003c0e1441d0720044c5500c6991700a0b00d65000d1049445102d2141c0d0200300e042e01030656000250440c1021001140c541c14040b10103281110300d442005602400c514030f403500755910074055003800344c55801404004220f000e64240b18004100501c892304a10010528080c20203800d544078590112040030300d0008008100e45010074140c1d40b00509440410040c004024110010a00c031380c810b030129403034803007d120751480381d40e0310070b0045819a0444609403200750002d1824801c0d44400b0480c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 171276771 1250 171275521 171275581
    0x6030b01020c0609040f2a021501030b0402120f0f060108070f1e0807080f0d03060806040b271f0c080f041e0b060a0602010605030a021201020906130905 67
    0x10f1804000a1076090303000390000c504000f40c00c2c031010982e00200c02c5040b0800d0303804040c01080c144c0c0c2004030105080740c401000260b008010440c10752006000191599482000140a64490461642e00c14010104407805100380000700381d100c10292090341014000c5400015a24000007040415190941608500c0c1c0789846032212410f45200c10128807046000800250940309005000c018180384001d4081e07052400611401c00398940e51301c009051402d00c0c284448180011840d03481a803040b0204601d440b5004141ca960907100301101c108140062101d41e12800450100400c1c100017482109458904880c01d05407a881640d00e0001191078002958202100905a0b0002d01880d11091600d408214681c0100c041c11f00c140c2d1a010b000c400d00519051404d1000c000f0b21041c4000c0000a0902c0d000030f80382d10703550390060f22400f00304007100f090b82001c2d411922418401055079a6a2074032303118901000d4864070030f18030107618103c000340038810500c40d480a002000c04549403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 171278021 1250 171276771 171276793
    0x41406072c031207050f0c01031a060d0e0106060908060108060912070c031a07110d051603110d0905030d020303150d210e130b0f0405070c05190c06030b0102 69
    0xe126900d100c1641e0b407500c9807074090729000100000814816008002904c6c00100b01614a890411410407550406103020100d0007100105210441d038440100c40c03090781c03a81d81c1401c96002c0c0000300c44450003540303020310000303409402100e640120f0388001e090b00c0131070703070f03101403440c1c4420007151148141c0d00f101c0c07074480b0800c02003c010441644a5080075400c5900c1e034031201b00760a07205564054504103541030020403608059042c118070070501c0201300d40101d03100010002e000341900b5111486203038041c00c007098082c1e02c0d054000198403003102e0200c145003400900030082e078801c00e4064081c0006000c030491020044030304c2190045ca0b4a038402d129032083c8049820400e4090f544d07190b030f400e100c8000c015800400359a040147d610000c860156600b04900462034840c1089810b20b406100341340c42c2c0312400c401c0701c500000c030350014156490010581d41c088000b00024400c1c05201081d01601035420701d4a041107008208a000c0340c0e850327420a40c01c940c1840925805030340101fa0b426 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 171279271 1250 171278021 171278087
    0x12050703022106010303050d18021003020a0507142b0e090a060b16061b1413030b13060b0405090303062b05030405030c010c0b0109020901020703080304140607 70
    0x142105076921055401c48000c1c2010b0303428810203030001c500040c00001c1008208071107000b21300f40340381e016110900d07032251680042c48110714041030005243d000325007004400c1c0139100307441a4541000c07111050901700d00c035058079040d60420086101c0d00e8407610740c00c90f034010900404070100a03120003000300145e034100103030341c43e0043c079907001c1c5600d8150200c0ca5100410250002c0020242054810100ea20b400c100792220000c1000604031402070f1680055485410402c12416880f04940d5030940c848800d800914a5003000c0e2282c40b41c0c0c814490022110006000c40d03901811042105d20021030800c13050b10b0301901d807060316500a2010841e140340005541038003080108442c0c021207201c100b843e69654550394140c0f1030f6003011508104078201807101e030300124406d2801c980001110350300c00740c40c488180591880c0301d50109207048144d00070807000d07015541001e10292680b40a107060502c42d0f2084421100d213006074000725a140307004e42401074500d102ca501c0d20140d8081d100405c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 171280521 1250 171279271 171279289
    0xc0e090c030903210402011707090501050f070b1006090806040f02040f0e190c0f120312150f05040c020609030313020f0a0603060806010e04020d030f02030d1103060a1205070302 78
    0x120b01180010020b00c1204030581504003a812044040d0380034070f240c14000034140c081020315801e018000c000400005592001c2107074282e4009003800c0341c50b808440d1701c102050040c44c0b40148680381a0041c40301d59404d01c6030100490b4500d03070718184102e4580c8612034543e00140c1d001030541140062032001458250086000c500b100100004c4010341d0228451070103104424101c01c42d03a221040b801413100050031b00c2d0141085c00440910355180062607280188000405002c1140403007945440c19600c3d00300c0105089041d41c40d60042c0d44076008540310303620034868144154644030020003400d0021441c24030450b241c06c0a9411544d401034113250340246403104aa102c10b08200141c55a074624051002506660350002803142c14401014603068040c1c20100b03070031112608100050340c07003400f41824113925140200c07100e00b010200341e15501440007860a81030a05004100c100807910140d44561022114041d60658410301107038000d0114070701514a03084881c0c24070144c245610a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 171281771 1250 171280521 171280531
    0x50a081c080c1215030c030120070c0e010602160905060d02040b030316060b0a170c060a0905040507030905160b0304120c02091303090501110618011b080a0c0e090c03 73
    0xb001c0d16010844903202c04203e000c4411807070709072007614400050b040070070070b070680c0341d505a0003041184001050b035007013121403070711604002ca40001d0140410001580420007413046059022080d40c440c00041d40707405582d28034400203504204002050743c401d00485002d1140070b01134246a202c10340900c40a8000c80d10807a0300762000704003c0a65042e1140e54180040c025030000071068030220410802c070343c0d2035110400b2034040b5070a844158401090300c00c0d41a0040314a180d480500e00d030107903040460f41d0f0049a00c80e25000400080c542c068111100d158403d0701590681000318205100080140c010301e0f13440c0c1003e0000a000030b29800d2900000020b42c00e115803200000c0d40059a284022030755581032515498405003010740000c3e042c80502024200310403100e80c4852000d64800303005040d0940340303090314003c0010700c0c0300303601c04040f0f88640c10094200200c45a0302030038410b4290380034030391355180071205410148502160010624000c2c44804e1300d48540c21200349076040501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 171283021 1250 171281771 171281791
    0xc030f0807110304060e040b04021309020702010306050a0e0f091b041806020a1d0307060c03030504030c080c010608100204031208070512040b06040b180a1e021201050a081c08 77
    0x10b089515000208050b200a10240d52085480c0c4090014001070b5841d441d00d0314040c90042c080d0f40c3c000e19000807100e040d195003e000580711050790004a010344800d9205a42085100c0c070f0101d480400941602e228510f111220421500c5d00d0b01c545a903000c1042c5415403005060038445200e2a241d000003039000802d091000c881481512510102c0e805a580c4602203400601d48404120b8403003203505d11717407500b20050101c0c54a8850040c1c801d0740c10302001020103035910006020540507101e0391100a801041e841d86a6100701d003400c4c024005402101810321840012800000144c0200d0b010f5a90190281d45c034110141e100341d921181c00b43c4103031305203c001d0000c007248000100d070b6035110700e01806803e6070a0030488148402c40b0490001640110400c5074154000c000c180c2001382c000c040b41200182c00c00350400c152086400905495260500000321010301c40030902020341612001c4520f4000580e8031031b4a2036684500420220031081c4840003500001e0181035580c1d84246814 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 171284271 1250 171283021 171283037
    0x102150f010b1b06090a0c060503070f120e060103050d110106050609040e120c030a110c0a051e04050f06040e07030506041e060905010f060b2a0109050d020a120c030f0807 75
    0x65200381130010031641c1c07003201c0c1d212080320310030702c0980b80c140d030010400d0303081c00362950070a841c000742842c04c22a8014144185c04c14149001e400c0395010302d010409030402d980c03041d43c69290a0361a8016a0350140008011030925040c41c0d0341840341d02c003182c0e002031506107080b000300e050001074981d4125603613403402221800147c01e4050070040001d00000c1000e135554440c00a0064440041506d00310700f59409406c50389031940b0350301e0700007080d0307507003200c40050b4110b000c02c007858001005030680790040e0910003403040c1c1d40840b29003240110300441d41800191340d12a2071998a50b1144809061640040701060104542240308042da0811094101d1008082d03210207058480c0c10754201c03516036540c2c0003081214040d21940303015100220581e441c10845200c0c2680d9512082032881282c1c5241c198060124025844644403d074410165600da02d58024041d480b141415400c1e80c4105082c480384203800d200700f0f91404d510f903040e00e0384102011441011181e0300700040c004800c0c00301c3c40d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 171285521 1250 171284271 171284317
    0x30f110d0309030b15010e150c0102070f120309031704110603071115070c0b0c04030204060803040e0c070b070f02070513020a0e0d0b04020d0c05040212060102150f010b 74
    0x80a24940103800380e00d4480b00d480c42e40c501011031460041c08000e018004507210742003070f0707800308034541c0d10030048410035143d101e034810a481600c20000201884c2d8400180a000c028070016000007241c0030381000001030780c4442c0154299a14010010009284860008042c01c008441c1c1900b01d4000c81c0c0c031000300181200800c0090b031065441c000400c000d0700b030484005504200269200f40429040c590605000c607000d002c2c5034402c98020190304c6250000350151607a0380956000b0340c3c0081090007600e0ba41c0040c2170300c070390140c0194288045c4103c001586a20b0f0b5070110f40006500c4104100c0c01d5840082c116a00c40400381850300310301071024000340903581c036800d0300502d481000d00103039224505100600381c1c29401b85018024009403140c81d0100e240b0903541984150141c9908503408001d20348155044015000164807900c04201c0c0d140d400178008800d8440c030b03c00e800f00d07820381d0741000c4203540454007103c64050790031400300184800941580640309080e01c507000040f4600c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 171286771 1250 171285521 171285529
    0x1205100507200f0703150c0e060f070510020706021b0102040506090409060b0409050102030105010e0a050a030311030f040b030a050c0922090204020712020606010c0b0112021c201207030f11 83
    0xe03417095643c1c48110042040740103e903c030390480250141031410680412a012030501d000302c2c0c041c82408075000c161081405400d000e0244007141c000c1003103503120b1042c54004029006058590840c81c4007034003000303007078805100316420344100520365814800c3d640b080201502c001b0404860316a103654205442307032628011807590900c6440050b840f903060400050000044e503141c81d200d501c4441e42040030752039500324442600d805181c03000550781100c1d412861032042882e1400ca412000600240c00c0855401450280ca00c000c0241700036140c42400c60041d000b4001c62590040c58407448400c124000c081e1050145007000020454510503000201283c00054003074403070701451064014140e5050041c55840a001d0034034280c0704420343c48040d01c400b814003642001190455140c015551200c2196504490450203402000b1903447c01c81140c00c02c400000081300c20b000701c5100d0a14044030780e00185070840000704501c03846d40c1c542401c0c186461105030344401040c100d840c45911 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 171288021 1250 171286771 171286783
    0x34060504060914010b06250206070309030c050a270b040e03040f050d050303040f0206072109080d0e01080406020904020f0315010206012d08071205100507200f 70
    0xc0541c1c0000350160241c20300e2100c5081801e041c90b05a45000b450402d15a259819124070440c0250501c0328010744070485200f0150480303001e94459400310380b07070b401c05074401e950348281c07031240c019210303026130710703c20300c00c039603290303001b8070700c0000c40c0503260580784580b09940c84040c43c1446010405000f20b10216040320000f0050036100e410000d400e0006003020742000d00200000d0329132a11011107520361540b00d01000d0801481244e01090800656441c0303400e9514403600200e080b2040b01245110410b0400c40d8011440860700d4031034006040c5201140c246481512a203c8100c502c0d526401112481c0c0f0040045811a0b400c0c0b08115050b161440600301101c0c3d50340380a0307a00d04091148000c20303805070fa1007604640c032040042c0141071840004d503514030f480f004c141156420300030842200e01c0480d0002009803240d00e0b00042c030f21461409041c4480d00620556100070071040ca00f40903a501220381c140030580b002c0ca41d01241d030059110300541520b01e41601c0034103400c4842030b2b04001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 171289271 1250 171288021 171288023
    0x7050301050d031e020106090b1014030a24081603050304090e070306060b03011e030c21150b18040b15130903030b090114010206070e0d0605040807120534060504 71
    0x2031f5544006000803400c601c42c0341060701048a84a541140d540c1c001413010f143c00d40e04074600040880840c084000580207070000e105a850380c200e00d120096118a03540665114911040c400c1c0000c1c455400e4102100c00143c0c0d4211001d0b600e09410000c0760006081e401100407418402c0881c0000850820310a44000d030503104005c80e640d5140003414012550000704c0406001280715041001540404c3c520703040310180c1c0502c1881c00341c0300200204058001d500070f00740c1450b400c80250300d041203500000b01c1c48422650800300340314140c82e012607080100ca008100d0104c4001150102c003100003440d00c88a40286810801d03d101c0c030040e401d641f80d405086010079150b070900c492500d030060308640545111401242d015840000003543c550300500200e0500c80024030725206916400c00c1d1f2256160400801d004a007000d14209075540e011203019220312401e040c280d02d1080c03207507089541007003240c141d9000300034501004440311070489400b50f0740421401c100400152250045a100d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 171290521 1250 171289271 171289273
    0x6150d021f0905030601060f0807030902060d06032a0e090f1e01052206052505040801050f0403140a0201090c06180807060f0318020a03051e0607050301050d031e02 72
    0x1008001d440540081c80700e8100b00d2280e0001d0005205043d4080882400381045190044468941030b10a0300244001c4070302a40100c8002058040e6204541000d170859104030080c40f540b2218101280004c0c0d21086100c07808601180104800d640c40340500c3c1e0044d0001054540c000400d041c080d1030603860076514040c12109856602c00b1900a101e10f5510546100b82d6000c8445a074074000000403c40000800e0141d03210301180620b01e0103210161503a02095040050351a0554042c01a4005110307410040d0f0901001407504030b856409140940e40c0f40e00c44a45c813004032880c481458001000c074408640d41c48009901007203201c49000014007554598076044020300380000641c004030303082604650f21001003044110391186440040c101c4910b000941100304040c85c143c0d5001e0054003941c40501c01a006c03080c02400700e41d040d00600c0700120804091524080359031200001c507400340224001f0f00042141d41401c2c9110081e1500c64030700480d10103001e05020008032010080a001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 171291771 1250 171290521 171290569
    0x1060e07020a0606050d171303050d02030405041817030901091e0201080f041101050a02010b0a0f0f080a050a032708060a0f0e03030a090201020a0503030a021e030906150d02 76
    0x620109200f22000391400395020b103007100040d1190041005034047c001001c41001414030b146004051065000c0d40c0e002c82911145c1006070b000030f55070742040c0a103912861400e91200d2a081c914034804402960107940b80c4442081100b2045035034100403c2e00801d5500d5643c0d480000b00c0005541c02000184c0c40103802d50302c500c4c00014041c9030003c2500d0301d4034024600f8400440c03150482031b0b04c0b40c11309180c1182e031200c8441c0d0490140c0350103c0081d4002003155030100300040d2a000300710503101d10310f801552496692031110354840007810082d00d45d0700001903c4c1d012902c1241214100354014001c1b0a03c441502c09055a248144e4414034003074201c0b009000c0d1190741400fa00784205d084260510641c03400d032a01b95103034440508100c20803941c503c9014116402400040e01a85d000b5003a69160b2500703201a034065401072030b2200a642541182c41440c0b41e800060384e01520f107801c01402a641c42032862140c50640d101c142e903108a07403c06940043c6d94240810001c09081300e41605 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 171293021 1250 171291771 171291773
    0xf07031202030910050601090f0305010204150215070c020d0f030806040b0604051e030a0b0a0515011d010825020102120a050c07030c080d0203150a090606140c01060e07020a 76
    0x11501000c103a0354464240100103100e0b20100016035100703250315840b400a29901d607000103a40b5407036036070301c10708200b00d046100105024065002e002210b6401c47e01ea01a011403003402c030380720703007034001441000131030f08000c540709034071401000050620241820700c2408a0761103d0b5490800050100e0008003203100300103c1c0d00f494000e0381d21010b8242d503410b007024100f02c00282c100c40b06440410501c40500420240c0d613404100340001960444640307000341c1000f0394510080d000444001c406d07400300101c2c60f00780d5407051070004801e1031404034400c82c0700b00003401102c8000e00a80002c40c00c600680500c1c11004c001400069080855000180d840c040d51028070034100000384014a064a40010405203000410445100c1b40d03051809500c04602e03450010f0302d500440d040400d86074400302c00c0020f100b240340140c980300d6100f200c90042c8070365a0200f40090f075829010b600006800300710744858602c0310101900c02038104100106610303403115803074240d4400841e606001644411030b804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 171294271 1250 171293021 171293027
    0x90a060f050615040f031403131203170f01120221010f050906040b06060a090305150f0a050c16080c030a17150d03050c0f06010605040810091101050306010909020f0703 74
    0x90702c150740201c1c41c00c0c1413510b4030321200c00d01c12103440040e002c00b11100103520a81814011076040036006507100103480e45074483c4403900d00302c445080380401c0410b20518034800078440e03a2440723000402c84141950b82403002c4044a4035008604a8000340319841042003075241e4495004003851070400001e1502601411b02d0035175034017402c02282038108030180408580a42c0c80958408000e80d52030380d8518182e60110b4890841d60b001801e43d015104e60f1005003901c0c450100c2c0204022031400c1d201c3e403284042c1d0412034a003502c40b86014041082007070030300104811001e0f00303c0c0c0110807280c1070110f0820040c0c2123030b001c0c40e50200003981c80b60018001c481640d083c01e4010701a85100c00c58010391354003050b42d80c1c007001c401600740325000c584003800940401642e03a40006200a69929507503426019045030014001d084d61030040c0501e440204401d842200d0340c042e04601340034189200d040065030503500127011103041006c10300010038680054001418080c083c40c13081c40d80ca20981c2001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 171295521 1250 171294271 171294289
    0x60906100603110313030903080d02030406142404090503040f0512030a02070501120b030a050a050f0a03120504081201080a0303060b030106120e1f050a111c05090a060f0506 76
    0x8041850b1400c07414100e02c0007441e00380da90081718541c4902c21031115090554980c04141d200030b0002c0d03000510414024000c3d0061401507224941c24007602c0014034500400e424200c40820324a0140300c9904200c040b02000d035058464003a2000814032402e03202c0504650164120888001c40752204102a00301401960104201c1c0c4019600b01115880000c2d01c840c0544500c0d410400e061010408060a60344600c03d6444000d0407110846094503050382c440c1150482a5440d000e00e1014001080000c42c0403044a03506590b401031300d20b0b140c50085c1c010700020307009075846501032144610100340c009140b03010b401301c94014560920030780350090a031103094000340d41c0745030240300421075960800449028910282000f1a4000d100c038580e91810804c9808440000304030880d12404c0b4500760300550103901440401d005840c2c00403076000f628861500f640b503642e1190003440043c240e45030312180e0401e400342c003544d5a0800396201c600594181403041c1000a55400500849160000032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 171296771 1250 171295521 171295529
    0x207061d03040303051204030210060e06090a0203011503020c0a0606080f1b01050315040b150403170412230304060f080a05070e3601150e06041208090306090610 71
    0x1c6140c20304541e001071441c018400030244800c40329010604240c000d10900002540c000420060996591000781c00004192102c1d8050302c0d00c4004500415101c0c000c6a0680f2100300300c44d205002c510004800942c0800e80300305903400742d2160071000405034040c1400402c002e200400860811030b0140f81043d00c0768011007054100e04800c0c000c141d070041c0c03c0d6a44100c0000b1102071011480c00814040c0c01c01e40d40f510303408000c1070328403540000400c0c040d0095902425a49100c41444403804405102d50300556017040e820854100000d00b000040303a045581801010b1500c0715140030980c07070350300700390052070210340c00b00e845411055005c84c10a9000004030003e000506080740b0141945000350701081c0100c4400300c40c1d00d00701d03001841d07160403101250b9138900340064061162492107001c0c09118503510341c6142c4040b10307622810b0f445c1c0c661000106a185040d2808041071026070281000b2544004103104500ca03c0e6018400c1d0751081045101800c5945008680c0d0b480e04030345030304 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 171298021 1250 171296771 171296773
    0x9080a020a120f0207051c1202060a0e0a020306041b08030403060b0f030105060112020a021203010807030b010b03151311030f0103050c010f120b040e0706050405011b0209040b060609040207061d 85
    0x1070003d5403e900264120032190141c90303c2000c559466840541607c1800d005014020b241c10721200103a40050721a10030b022070f0204010098904049039111402c42201a5060748110041008602c0f80f41e00c10000100e4041580201640c546800c1e04540141c1d1040e190715a640c8a0f8038200d04040c00ca00c0d15020048001700040e28003900060303d401c4080115420342e0341c0c046a10b6044a000b040f40703031100b45599407421744940e942d003580c980d900070750302040742d282c040b1000000b4014414025070b40900440c40c1a031840e2800b20042c0400c900005c80c07852640e42d10b851001c820486d442c4011402545818a000d1403036045042c854940181c0720f40850400801e040405001a4450b04404c2401c0d11900e01291002017500090040e01e00f00c0c10209141c05610700c0040d4442e002401042158000c0e201c1a0f0046101110119500c803030030f0300a50040c22800c0040d00003502150740e1544040d0041406080140040204040780c001e0b0b4803c0b0340f02c0d0b0b0341d0811384200702e502591084401407590 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 171299271 1250 171298021 171298037
    0x209042021070512150d0c1d090307081e03010e041205040b2205030f0f0c01080103020a1205120310090b10020a02091005090406060e06011409060d09080a020a12 71
    0x540080142c481c0071828101e0004c0840802c0012100442c4441d5008008012901500aa04209070b40c8030440c4144854084900e010018112420008a04c600c0808001c2d508044039500d0301d08460303200c12142c00c408400381140c580060440000707140a4100c0711b400c2c1c0700034074291400075041c003491080300081c003005003c1040032082d510100e60303404032103640b002c0d01c0c00c1d40481030520b503076a42d4004036814080c0b0101d9500640c000240f607802c10301c1d45400c544070840d080e0010b541442c02800007039001a00444280040c004602886680324450011146c4071200300c00c42e02d0441d00159081c40c0b8424034084104610300e86805000340841d0201c0d0150030780c41841074041d40d02c03109202d00078004d078001400583c18a10f030150710001080e02a20024007403505251002c0101118010818070f0041600420010b51084d42a200c204a81440b1301b807621204108003c0c40d50800d0f896039075810785580e4401c000520070340280048034050740051110080c41e18080712400c00178221542040540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 171300521 1250 171299271 171299281
    0xf09030b060f04020702060307050a02070e040209070309111201060812040b12060d06050405010b18190203150a0e040303180c1811180307060f0e040209042021 70
    0x860503440e0480310071200981204841404140a801040400b9600c814040200840c2c1c1e50024020b00042d2101d5081e1800b0a85909030b0a03501d140c1654040d400515403800611818000d6000c81e120b18000d54892100d01110800203407015580300280c00342d65182c0030708000120381004800d180400c1c00703000b00c1c1003a00305940c06400e1300410440708005003680c004178102d504c840c00343e6181140c0155060180d0b1401e420424007030682034079203d0080b040e03042c140c521a04104222406480f1901d001c11905424054040213508007900a01a2040303041d0a84034966030b241450b0000d1400003031044030303454181000f4003150364610660441c89600340720070713000441c2030b030008094925011010030402c4c0c1085100b0010b0138202007102210200003040200c030b5400102c4120007000450458417200d855400454071131140025000101e0b1050440034040d20700ba40160040200260002401c80019150039034118183c480740401c002c400078918100086901e072400e001c41070506401154104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 171301771 1250 171300521 171300533
    0x6050415050901060509241e031509190504023705040e070603020a020c0405090c0901140a1a0903160609120f030e01090e0a06090b030a1e06020c120a0f0903 69
    0x9032040700740e00e00c7c01e4156041912042d1020b80b50155021900d40c0c1d1070200c0d0541603030690380b0680f110301c0700500441141c41e152a0810513548203200518800d40d1409040545002808000d00202d90010751100c90640240041030b5108404542d00d40030701c0313460490607028441e80d440b030b04198059410554851408680042d00380203c039a10300d130050340d9280c000c10890070481c8a1800742c1d4007908103824005030140c0000d90384001c00c011561100f59990b00c503910b5070700402c50710b0b8954004d6a80282002030244449081c0c0c1c01b500700000261030b0201c2140004d0918144008100c440000c02c1030a11206500150ba2405080f0360808450510340540380c1014060110000804014420300700c00050390cc01d44080340204402d914550381d90900840f00300140101e0300580c80e40615200c5820590710340003940031180e90f0080c1c5400701008400c081610302054000068440315004c00040c690b100c010400350a88110015407503842d4940301c2c80080401d00300350300110400034003110038004944 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 171303021 1250 171301771 171301789
    0x30d090b06151e0904051005030105330301060312020d0f020303100e0a0b0409060506010210050606090405180a0302070513020a080106050a14070c09111c050a06050415050901060509 80
    0x20520703000180d120810396003003c0e13485503a8040b0b40150414007840022081c1807030010079140110300a0101d55a101a05c5410b105850f8004442c000c040513504002c44601c24015030019014002045140d02c9880c1c050710b007844101001e005a0000b005010459405000d400042403d48090b51460070030002d00341caa03102601680b01800703804008956001a40e03808409801c01c050024040340c806410301500a1008645690150040c0c080c2821a4507441c822a8810603000b03204608100901007400000d04006261a016001c100c0003086807100411603030841c2da209900030542030341040240000070080c1c943c401001401030040da901d49400c890070a05490030382c13801c0750712025460300c1280c1050002c2000b1264400004500c018000080c80c0407041d281404002e100100e24401700201d2440380f4078414407280d40c000c43c030f802080195007006800c140c0e445008115551100001400c941841e5120f42d60f40001d00b10401c19420003900081c0100422f0a109003010088008989420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 171304271 1250 171303021 171303037
    0x1060c032f06070f030c020f15060d0209011820030601180f080105010e010f0f06030b210d080708070e0114120106020610080111040b03060d05030d090b0615 69
    0x44400c1008a440720100300103048160200040b6401c50030304200282c009030100300342c003000034100400c8000c0030f07000261000b03c48982500404061040215500710648050880c0e9032021242600c003000da6100540c90380601451120342e202d00c045840d007102200d620403c0c01d01c90905040e03031010f28496500c01d9030780c03011081c00c0c0007200c4065108425101c0d4603d4018031010808868045051401544402e06a80c012410030190b6603c42443d070b158450346102c1c01840340c4002c2010b01c00d035032082d040151521000781c80780c1c000354001c84000303103464540714001b40d003581b281c2030b959a00340e40302c81d10640280c50303410070340c900f41440d900c001d065481e040160f60602004030010a0031120420803180c14503000c01503442c00c2e507141c810094550740182d0f00000c09081d041070208403564184511341c2303240c420411051900d4a4070700b46903003a400040c21594030086d40000310021035401d000a2166a1035150b00040884642c6491340081d0710203015903000b504900185003041c0c01d6501242c05007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 171305521 1250 171304271 171304307
    0x51506030a020313020402030a0209120604020916020c180723181807020a0c09050903030105090402060c0105281112040f050d020604020a06031802060c01060506030f060901060c03 79
    0x603540340900d5003003004c103004009401c9407002041190130401035025203001030f0100c0700b0001c207510401559075140d20a490181d400292407000c266510081e50140c03101100e10300540c0c905200364400954000c04412580004910010400092992000c3c0c0d141141600d1501d10701c034940401407400a5010740700c2a0b114001486440800039500c0c2c0c420b00001d00c12390025a01c0c24a03005000a4035002900c8081365034140300440455804032500986100711080e0009500b1030b03280108103c0c1d2500091301c00d0b070700100708203d021070f01c1c00f00b030085d42e118202c00b414000411074800d00c0b409034501401d50301e50410b450100c2e00320450a0140448411550500d100350b0581c8403820b00c6154401107c030020002d00c18040d0008070715070007240040c840c0340201c4500d5012552018143d0030360398809044a00074944922500052801102500004074060000641c607602d520100c0d0b036030b503c1514200d400103a032600b0029149000115240500b0a80c41d200310201c103540e401a082ea05c030307030000c0c21103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 171306771 1250 171305521 171305527
    0x30a0c060b0109090e010212060117220812011503060b04050409030e030d020706200c010c05070f0b070c05040e1018080a03020a11061b07050c04020a12051506030a02 73
    0x140b07038428507030b220107840e04103002c228401520b92214001c1d408800092003030f161041c0011300035030140084081d0005402485129a929101c24449801e81e00e6a0282180444012180468400006001d90084680129595504107001d500500e9405080d0f0420103040041c1848100c0385007080e00c00710360080c0c502152180f21407800b95440203c2880458143c8100e06800d80007590004101044420b2602c1e04800304181d000306120740e040c8083c400d40140c0c8a902141034a500c507a185902a5005405a840c0b00361503109045180740140e1240203040400328402050058520420008100c04c0b58100542c0000c1c5940948800f0074542026240e070f0b651410002d440d1180c030806265a9128203900c4d61000081d2001d8000d400401d070107000030b000ea100c0401e01d10300009010340680c0c88580380d14040c1801c600d1814050380058070031645409000b5503030501392143d00207010281c0082e11014034101c60351b8103e8007102c800610481c00ca406200d1410080e1301d4000442e5000640c40b07201507a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 171308021 1250 171306771 171306791
    0x1c09330506040f020a1701060e1815090112140304030506060105071103071215090b061201020904061d0702160b0702060c0a031e080915130b070807030b03030a0c06 72
    0x2000501c400c000043d0000910401440e44842e407081c1c1b41100305040405a6241d41c82142c40000c0c001200d40c011946072442e410789480b6145a9070300c0742581c1c05500e0300c1210b4601040c4044821307070010340313460240c1210000700305e00000302c00c02ea80008401181400d00e152945a52403001400d000d0500000107481c0c0c0a000c1c9481d429250080301030304a480b141d0f59038000c50901503c500d01540c500384d0644103180c041000c1c0c010794910b240c01482c104000e40700e0500b0404a0100e41c0716145e1199402c00c8150001e8a50380a030700014518803c1c050040340d1007000c820281c01c001801101117401281c0841000f48603910120281c800701d40e0015202e481510124131144070b244105901441400c3c0b10604055005103810060119014070350790100c0356140903181244103070741070981c68000030511800040c403401340960020109180c012016060b450f0814404410345200d4005000d21042010751905409901c503160410b600841c541a0310f82c40c001c14a5101c803800500c8541c072070003014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 171309271 1250 171308021 171308029
    0x90509012d0c110a0305030f0108011803050f040306090c0302040c08010e011509170d1209080409050411130c080f01030b07080417040f0302100201050606031504021c09330506 77
    0xd802c41a0982c04c9a04048440c10050100d40007143e03202c1d41641040000320b12118180108c034081c987c189a502000501581c0c280d40341d410070883c4404180080c0400804101c4a00450040502500c0342001d164114010f12041d1030141c1240c0c07052054890041181401d5906054112001d5118074a9290204036003245c1d4024a81d00ac0d803801e00c2860300101c4007410104811910880c551507440c0d00b80c100042a5099850b02d101c0030301240320500c404c21180019070041c5034002d106508031446c01101030001082d400101b20006603585e504c003e046052a000410389800c0034001c90800c0f030319803455540032044c035801010141000071840118080014406652105001d00350384603450b6600c0d0301900d042d48510b0311082c0d11030343c4038a010003400350044c442c00d8024803010300600e207107941c0c0f1000000201c1c4a01c1c00e554010b40e081019032a480c02100c001c4880ea8000c0a01180205040c20404004031702c540b1401101c1c0048482d4034a543c580800002c410a144c641c0411650388070b000003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 171310521 1250 171309271 171309287
    0x712090206030906060f190501080a090501020c240f011401110d0210110a02030318030c011505030609071401121b05030f01060c03140906070c090509012d0c 69
    0x29040307a4040140819508045541482004280c5440540040e41d03000c0281640c8030489100440150b16420701070b5511500c41075034403039104e00c00400d03028042d540d050708a922189a00e80241c00c03014189020f0543c10031002082c0d080e035180c000d15400c120051142041c018405c075100d41900ca00c0c44030b042d90260280c02c001e4541101500c42e60070184102035100d0b40207240729204146008418001002610241c4103c4090b03540258110340c0d50001c3c003006c0d02140000380100307120a1000c068030031424060050103010b00c10195070701c50b181209061408401600c0f1042581001200303000c1010040c408050070007003442c0034003c0e001c11403590801840134010900041201c40d0b000e4150310380040085015040d0045a506a07030799910007111122900c2c80c004000802440303800031100318805c09022014002440c3c0d9107416a143d0344e20790600ca140c2c1c0001c0207903403144204040e05200b840b030010001c80790100b04903c0704500107002c0f01e0000c60858030940c0c0750f50701100740d1500d00c00d03040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 171311771 1250 171310521 171310523
    0x90609150c02090103051b03011506050901022b0e0906010f1412040b04051612151803020a020a050a0506040e1003050a03020609060c070f06110919140108090303071209 74
    0xf40c0e90b40c0356100d082c800e03142c2c81c0120000024448104130300f000e50a0520861001040f0940c95901150508008403100d41c007102c0c0c0755045106482d088004007130340098555480d104e900f19500480991200900800c1d1070840462061001908120640e6080f8103041307440700c00c2d460040d1000001960354661401104035504402e01a002007204020765000c8050040740030703004481d4088100401c1e4130a202c4c9a000390000c210701c08180c50001004140010701c607c40420000c211034203c1d50030742c0c01b242c80c00003055005a021610714400d44c104440364101410301500d404150030300303150110312035118522600f00c003d410b1000050101c0a07210b200e0001e19407000c1500c00d0380001d4100207580c0d0400b81d818100354068500400c00964501080750034141d400030118094444944490005181200f58a034008404010040981c0c1d036020543c05100401c41a0080190604e04412041b1007008e0100b4140074641c0c0034423032009000030650b0b92016543c54100b2400300701141c1c01002d0b04e03800744 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 171313021 1250 171311771 171311779
    0x7021f020f0d0507141210080102041508090a060908030f011401020c0d02030c04092003030711010c02030c03100903020705030c030a0b0a0609020d0204090509011e1802061305010f090609150c02 85
    0x2006c25010385084d82250180850682587c0d0f56500c1d0400c55080384910301c242140c01d144079081c0c0b881e590040b96615401070008043d56020003181e1101400e803505401c048807800c20000c10080a5503500222601500c640410714810303035215000032f5030342c1c01c417440c80c1482038488640c07100071560208009840d0b83c5014009122245040c9008189800f0710305519038103036200900701c0c043d42000000d5404c031076000307011080303443c85250040d40c03003503428101aa054001d54030b104110751020070909050300507800000074500705030705000303040500a40000d03100c0e810441080203190790000b8284522508a85108169200d0030502d100a200755804042201d001003500580c2100c0385d80640129000c0950900050382e6510b001c0382200c3d15541201880c42441d05414151011070348031030000b5140b00f00321183d28106800041554100035030a140200c07000750207100d156803004c14600410007900304128020b04009024004c5001401a400980027800d00703030030302c0c2e8801c13100b00186c1a0094 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 171314271 1250 171313021 171313027
    0xc0f110717010605030d0503041e020d0c030b070207052e0908160e0121060509010906051005030c0613030303020f090d03030b010201061a03011401110607021f020f0d050714 76
    0x52801c034081c2c0703620302c2418481d00401a0140b0311030b014000303c0b4461a449010440904045500b4005000000f0320580c2c10154030170640f03000408452072400554083c803078038800703441c040b80000e140c070085400c40b60041d00c1400c640040743c042500780600c1d80c02c642e912401054034010003195040040da0281c401e6110341d100c07656940d43c80d0b0303500c00b05031501c01e5500c0ea045d0b0707203800303100200b10030400c0c03080000e0704a1405030001c40d01a600254000505900200708005141c13a0142038440070380b2030314400d20f41890f0410640c901000107a0401e0f00c191100c60410031008100217130341c6614800034080c1038001500e110f0700502207080717074400c640050911290000d5424020002c0c20407400540c0591f282610209080044120302c80749008c0c05860903245071b082a9a4030128040100c219052140c0c0c068070305800c2c00144091403003200c00f07034020032200c1c41c9d00f8041c1075282d0711076100c0080944100854000e0041d0b010407924100b9080d040417030796071500300088076000d000f00c1d0701740c005203008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 171315521 1250 171314271 171314309
    0x20f09040f0506010f030303050106030e030304060b0303161a0601030e120903070b1b06090303010b1c0b060313050c0105030402100305090a0213060e0c18011808070906060f030c0f1107 81
    0x2c1800f0650303000f42c8d0304005aa8a85406a0864021144003040ba0b0301c240f0000c5e00041d002d40213280090005070a4a0038064000d503954020b043d00e000460321008943c3c004202407682003222544141c0034601440b44038482c452907501e454004480310061040016014515101009400010701400801c103581e024180340341c992401c0c920f427007030b40d05000d2840800d030550b40010560b416180b103400a54588000411050f515000400394501c1c51500c80e00300007500c2d91000040c501c40c2405c004c4101d1510303400c2c5000c2d420000003114086c1408000c1c418007000d62a4246044010710b518180041c0c0780e03c810b040c43e40740100341e01d4000e500590710126000c0481540e084581144c0888c96041c4c0d2070b894001510741c05001c0d03407424102c2a07544000920056206001c80300103011515031241046844440d164100104d0390040304250341c80b68401c004c019402803012400038401c2c0340801c140244584002c24070490804c801040010190703e00e804000180300d100c0c000d0106541820000b000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 171316771 1250 171315521 171315539
    0x102d090b0f010905030705060d1407050a091e05090a090b0c04080f06090d03020318070906030309090b09010311013c0c030909090c03080307020a0c0f03020f09040f050601 75
    0x4103540c0d001e8501051403440d154021480a400d803200240603000040c2001c3c140600c0340c1007810140ca4482c1c07225905025448a46074036030080100756115aa80c481081000d041c40d0740550181d0161045441c009007140c54402514055800403a8100704540f96002d1103c0a00507038600680201d0001003800001001c1b000200300703ca00c00026103408180200e00f49403181c0c02268091110f400c140039004095105e9402181d2100d007210070a041100b00d0884c1514185254200040c001d90700c080034024143c003d1300302c03802081021403d115041c425008240351040610000b0030100c0b042c0b514140c2d030383c0030b1120489040d403803a407030926160254441e01c821060013280400710b001c0e4201d4000c83c85109101d803d07007071070f0992a440980d91400072204c00400b40802c003030b6145d448030100031000586030703030055010720ba05a009004945041c10000c40c000c2040d0300100741083c00100400058440980703100510310704271400c403255a01c80c102441c940d004050004c02c035018030000030641c814 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 171318021 1250 171316771 171316781
    0x705160818041805150709150503150d200301061d0103120f1d030a0b0106050a110c01020c040209120102070311061f050616080a0e0117102d09 63
    0x100b114140002c0c9440c1d10300c420207040c5100090101e070480201809801e01c40342285800000b07a242c034a0015a07103042c1c000041c00384807460030001c1d40c000f0030301c9034540caa240320001da01d50446112920000c0351f500d643c8841c5018050440c803100200b8003200d5a5401c1d48080000c08405030001010b1440380c0c681d210400c0240000c550f80b0410101d40004c0c14412001c054410f203482d192000701070704840f1041e0301c1e0780d030841c00d040d418400d1070450400101510b24090091803980c0350691030710050400604400f00c026a0000c45038010390620740141e80c00104210000303019100107076120810000300c0c583c840c82c8821714005600024500d0101540640510110f00141c001c2d2401130300d6054101250126800315507406088081c400c0c0401c0c5484801031890518514011400c80d040799581d840b641c000304031003008200000240d60f0700756084031590020011071412064580392130b0703041d00d0898140e4080d100707800004210601c90741340c1c522032203410501155485c085040d079520011000e44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 171319271 1250 171318021 171318067
    0x130906060806040c210f030e0f0907050d02180607120807051c0b030102091003060602070b0c030d2003011203111902010e041415010305010e010e07051608 68
    0x9292400000301d0000108a40d0300a961100c2e4941000345403012800010484d000e02030800820000580000f5031141d481c0110188203440706c01a9080c3c140422000d46078000c1400d025040810400c14034503031010441e400300082501c0103844000c500140413581d050040001e0b0402c00011b0132005100c80c846200e03510607102e60b0307515a140c0d80d00b0740841d03a0f030203035092004100c8035000b0111107041140d000282005405000141000310907000a011043c100e9521408260344081c14044258103015a1003d01192401c1c13501e8092040b09030750b940e204807241c48011a030341d40524040340c8080010088801491569245c907940c4901e0318442c40b22180e90101c1c04155801e00421a201003c656803d100c0302d40d140e0540c3c20255070700103503984003420740040d80c0607640b201a21544100d0580302400f40985c40c411900c80300070107001404a03030040c2c0080101881c409e0041000140241c005a4014500e180c81d03921214081450100101c81d10750040c000b14000c40e004004003c040000c3d0406 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 171320521 1250 171319271 171319283
    0x606040e160305060a20070201050a030f02180a150c1e0c0b2503022e0915050705041208070f170306100306180b060903060108030a08240910051309 65
    0x490225100448101040190000b1b1041c003c8001542c0908064400c070302e424140802c08078500354040c400c9138080139a01207844089240c5103503c1c10b219240b840a00103948110400e40c040c4840a0104100d604e0b0003441d02008410070f40c04a801e220f08242402c0d40007030384150107511440f6210080c0c0100d400c1c00203584509441e94090103003821030170b90ba250580c002c1d14415110740c1b0342d079040a030003075240041007038020581b200e0020144a01d4403010b004401c0c0d81301c11500705000c1002d464000e040801040f205020504c052190103d10324049a440510581c1d1620b15241c07800c032044400300080c0144940c1e8a40a0603018580010741c450384007143c141d1031940e22210150111002809080303040d04040c0c64501c1036a445601079070700c0c1c1c60b0007002542400404000a490440241c000c8215900040f034105002c64210624076005440085a14400762580c041c04074a10800300c0940d00c0790700c401c804a1aa0309011040d24050314000d00084546503800f00712070080e2100c481c00300e441e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 171321771 1250 171320521 171320531
    0x20d021002030a1b032c06040605120604020408030f03070c06050109050f0901110a0c020f0a0303090501080901090b0f0604020706090803070f1409010315120b06210606040e160305060a 81
    0x132400d2441d5454040c60340c513864031400010142c01c207900d820500880d448180f10401c2c1111000d69460010b07000804c0599101940e030404440c100605142c0030789850302803030051009100d0300c070011094a200501803900b00d500d80d91455021212030950380d2001e0f16082c0752400105a0030201c4d00640d1150b56071144801e0303541c840b100d455088514112007590200c4052100101151180d10403030203c1c4c1c0001c10590402400400081a0400310360049002c900c000c00200015604a69202e07480340081000304171656052303e41c1c20001d00300034246684d01802500140c1035660f90750558040c90303000081005124821b01d0070300307000e030320544ea1030340859510000c000781d00388200c400d0810b0009054882c0c5c249400709005402421010101e41d2411103100320104240d8200c1080a10301c5021f60300c0010b590a00c81d092204e103c1c074425412a03007441541c60300360314200004800750000720650340040c1c1110402d40d85402c00c150b030b280c00442d540000900000744000000c055004159540c03040203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 171323021 1250 171321771 171321797
    0xb07050901021507020f01140106180b0a0f030914101a1503060303040e0901060f0603020901271a07060b01080720010f1e050108030307090306020304020d021002030a 73
    0x14140150040e49006a000f1804118035070807414003150081034500489200c070050280007801c0d6826264900c1020103200d0042096a0f0300a4600700800d24140032003c03e24182042d0354654462580d01505001030545807800a80c407030361000c003690b070b0003210b401c01100c54500c140d92600b0990301c40d61455810a14500b80922541c4104045844003c0a11350312428a03030b000c8015420060130140d06000500c0b000580c1401d00c61501c0c440d141c940c0002460350f091540c60303001d40c80740f50000c00406206004031800c590300804401d04280301c0310815650501d052094015031451500581c0e4000b144004001492a90fa00541080c51080b5410310074180514011a081d160485180b00080c0f11103204c00202042580d20300d2101204200109410304459038074415120406001064100d04040c542c299001c148182d60260074035402840c40c500b00080d00a044c4840f40c00060000d41d400404101107560340745002d840d0a0f07004d0410302d014010b0781c42c00384d203e410034025080400c4034550320344 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 171324271 1250 171323021 171323027
    0x60b030412050301080a06110c0313060825080603010f020a0e01080901020a09030b040309081b0102010c14041a04080105010e0610020a02061606090b040501020d0e0118020f18010b04030b07 83
    0x80c3c140c0302108000c10b10f428498a13003401508c005c1c545044140700c1040510b0b403402d400d10003011b6075940030001074103581c90910000c0505200409030583c11285105104007881b80c4041446480070b5880c16100685841000030f0040400301c0c2c031510fa040c0b0000c0d1103807a5a03001111402192007d0300c82d4140c41c1c0d0790302102402e03845141d10b51000240075013000d00003d0807211625030454024500250403d4a500d8407920b00407905044030030681090034410210b41c0d09010300e6410480c946465960390800340d07038009050280f805402101c80c0481110100070f160b61007603a004003102d000a00840d659100890200003080d41d405029581e0400324200150000030011b8105902030320321031034103484440480c00303001401800c44a40351242c41440208210005c0079015034040c40006980e121900c0ba6801111410981c500750750341009583e0400f0048007204e80307241a01a180d014034505540006403072400000500b5800240344c000205000720030074041c2c02541c0c82800255210b8484040035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 171325521 1250 171324271 171324277
    0x3090807120f1e121d0612070f230315030a0b01060302091c03030b120a02030309270a0209100302091f3605010905091f0504060b03041205 61
    0x14040c880c09012020005503640c02c803c8908400c107205a00c400039a545040d50072941d545003074000b400b201c07191340560410322441c0098840481720145003c0701e0541c6544c1d0784600038422070a2080002040310740c54059200951012403407610010821510481c0050907081070b10303e04014007100302c814640b41000261039850720340201400c9103da00e081c0c801c6029511081100e600446c11944000c0000700c0c00c20703200d020328440e45000c40c6505001c0244442c0b4403041505031078a500488107000940c402204030360300c4110550349041c0284c40c868030798080040940018014054800c20040c0700792071030b400380c00d4042c4101c42049103500881fa08500380e001d41e481890f4080910200903014000600c1a040b03601d0031400c200c20b40c9450400c446040802031001d42d170103680da009140d06da0b81001d84000014000c24281a101503040c00041642080c0041640b01c00c00c4c00501010705081c0c03480505d10040c00010f005010b800c1c1c49010401c1c4980003a82e040700d002c0c000c486e5010300e02d0301403c15 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 171326771 1250 171325521 171325523
    0xa0b041a0702030412020a05040e010c080610050a0e0d050a03020a0c060512060f010e1302090901050a0e0c13030c0f090b0d1736011d01020a0201031a0901030309080712 74
    0x110704285c2811264440c024012800b02d82c0301d1100c140016140d103c07030007460761030403124000040d81409508080c1940c9801041c0714825000e0041c1c0032442c0303070003406840d00d903d16894403a095102d014041030255243e490090454801c003510081019130004000101900c900140e0070841e5451406a030b0314000c50030124a0002da4000240704c0b4200094050200081450329030001501c085c00b0800191010790074050444e00050058000d062045c0f150340104170644600c56810326000b9100c2c20f189016200b1114154009044039042d0341c44116100a03503084a18501050b0b80c8088050079400e031b91043c07401a03410042440407510b080000854550340103607818110700c1801e1a007030741d00d5022030b02c8108404090003010102c00c0ca414074040820340c01418411410f00075400250105000c041c40ca05003110201e0b40031020f03603000c290b40c1c0c1030513428280410074005148058540701c41140c100741d00200200300001c2495032098004080341c024000ba1400d4980361500c003c1c80480d8240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 171328021 1250 171326771 171326773
    0x80319020f070c05181338100509060d06020c0a0803010602060f0f06090106050a02120c030d18030c060f020d020d060f15021e0304030c03030809100614041d0a0b041a0702 75
    0x41840c0824001d6048044500780300f404e42c04500c0e203071f40d40c2c002e60080651840398005030355400c015956240740080409000c00700c031107010a181000000d6210941c41e000180b0303054001c140e8a10445003000440c8050f07500104554980d80c5408009548840403079045142100b640301164000f01c1040c2002e0141e4005032541080e0307802c2c0f96055940354084603101003140700e9040e01807540701d0206d001d40104120100515900c0030f200c3c240c2c005540c003c0c4c032a464101800d03200d042c00290080d160048160b0310141c04038902c18031000c808000d001340104550750500004e03001c800302030554810015a5080354503050300702d40311280c1c2440310100340324000142c2e01c8034503080c0c0074550507552400481000010ad0386010385035980da8050104540c82240030402e40020301076420820700c05d42650410040003000102e1801d810144501180700c0d40340d018941d1110b5918210b4001022510042c1a8404864483d0030700d15054024660803907085d00d042d6880011030003c0301c1078444444c0501647d82c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 171329271 1250 171328021 171328051
    0x4080c040b0105130803030103170901020d1407020d060209031c0c0803060a0503030c0303190c120e07090501080c04240501110307020a030c0501110a080319020f070c0518 75
    0x800c0c080103182840361141407100034450842d12015080350000942524009540c8a51461400804850807820031042601c000e21a441c0d0345c0e6400205c80c40301489038a803038400d410395403600308020700c00d000b401b03074000b0852101c400034000590002c2982d14425001c0701c0207840e181d280215801410000000090380c1d083c43e00010822040145030484401803d03003500036030f030b0b50000b85168840c1c1c01e10400758002008000f0f40502107022001c03131001241040c01441c1100344c0040041285a24031700c1510303965402291411800c1003400061b00201d04208203d58407841000d54031160b0307080d070b40e00c141d0030300400e0202d4817070000c00170420034019581c06481c2c90504005694a04a0301c020b000180f000340004005642d8084030350004500034501c242e20a405c100005010741e00030014040342d079100d0700c5890000b50b07070802280e5100c2406454854800c943e044400013a10903102e861100440c003003105020b010700c2109040803114103c48000701000001d1101d0580340049442070f604210b46 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 171330521 1250 171329271 171329293
    0xc09010803030619050a1202011101060e06060a36051801030f031115060108010501020309090f0907080a060e010c091a09010e0315090f01020c030301090902060c03040b09150408 78
    0x120103640c9501c00300a082002d110b1701e4801190291040780e00540104144251203030555800042d812903480c0389100a01a55060031100e40c01040e0141405001d0700d00001d407400d50300e100c0c201f040520480a440503840781900c42c0d003c1d000030340c11080f02d07030840740e010800541868946000c40318200005c4804a645e07195071900e100002c18094107800341b003132100c0170900201c2d00707210302110b0350b0060b1a0b441003820320380d0006020b520141c000505550041000f45100d035200003050354051b41481d40c2640959612103110300740600c0b58409526031080900710030410100307410041e080603441008100300740076030500315249041031017064201c21015060a400710a0300c4020010084103040540c2443c2402010038601061301031043c22684e4280f06014a500d01845131101d1000e4480c0258203000c00248032507101c1c4418801c00200540d40e0300d000003107403620400d41c0d1780c10450724140d90f210f40c0d6440078640c541d406082400c1c451088074041d1108180004191001e40b0011002840f0715241 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 171331771 1250 171330521 171330529
    0xf1c06230a020c010e0a0c140423070e180108060a05010501120c14030405010e060c0a02030a0c020a050907080a060f0609030204020a03060510020d02121207081e0115020c090108030306 81
    0x1035900c9910341e5485040041c2c01d04400c0101028007841101d4147c0e1003840c120780b8030b40c0382c080c1da9200341c403403400d00c0200c1c804540110421500700c3c0301400782a50645074500d054404032a50440030750049078060188940181010a141c12981c840c8103446a50340c8a6500c441155401d0184502080c034800c050401e100c0f00d41e010030310001407410a07041e146208041282030360422181240c807603440740c0c50705144200a110b820b4024445800703003824040c0081000c0d450b8040d0701c0d403540401c00400b601c1800e40d903c5043c60002001c0144c440211402c00352401003100f03208849403030800b03080410002e46040d410070150308403032103075640c065044d09650802010b5400720740b241d4100745d00c0305408203450340d41d4080c0344407414540d0010110b80301006030107802c018941d00c01d04070180051001040491003003c500f5800b800514085445980d9101c45001c80301c03c1c41000d1581c1114180081803088a60500b00001c1d4135a8013210500251b240400035aa0341c2406800c44e075410902c00f01d250340c10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 171333021 1250 171331771 171331777
    0x10e0f040f080c1903020d081b0a02030d050f1b090102060109020f1306050901021b0d02010c05100e0106030b09160e0603100e1e0601081b0f1c06230a02 67
    0x1c800c8072810700e0020102e0002e441c1003840c1c2404c10070344410b1080c841c100760701040402e00015440c28043c8947c607100424001002104c3c403007281148d0005101941e0510900844800304442e21040010f0304210b034560585000840f80041001820408040705a94500c10b4580f03001c0140e00500842e030074603058001a41040e1010b040c0d000f4140807820040940100c100041c1034159906a1203050160009183c11441c5036481c0010640e2001e030489a1504032010410f00d40a080c003248542d25031a10038680340c0d0040440d0f001d649007074170080e0050f00641204085074001d11481c2100d0300d5040e00192a00c000810b030000d4990b02000402c00f050301c4802d03c41d80540c0090940b100040c1d00038054040c0c54428050300e1141e04800c80380303a1904903000c42c04000b60902e1004010329030400c424155070715140405402d0a50383e41014450039990000400c110030005030510034464803002d40368030b80c1592400f04441490400101c4034041103004c1a03940000b5203146000071588a00d03240c000254 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 171334271 1250 171333021 171333023
    0x4080114090d0c0f2a12050c040e0a0b090303070305071b1103100c180602010207050d0e0607060912020d0806030a0b04021206010b0c0705030304151101060f0603090506010e0f040f 79
    0x1e00c0c083d86078000304085c00540c114074201084819192250050030a80b405c4a6812520141d40040007050105400103020501c044050b540003480c05540450719241403200c00c40100389185803410000c034107a000c0702550080400e92428081621070142c203951380800d40c1203042010000184480c00305030080d03001c03000020090169000c04c440542e9000c00e64554100c04404110162015404900660181c100030f203105d1000b181060741d00d580e00b5860b10280c503601c0042000d4007802c218181d0382c403030440c1c01999001c030080060301221710f401c0d02611000c69042004d801031100e0024040c6c010385405108400080182440c00d480f5030f101244010060010b9800c00308100c4152042241005424040e100580009480e059040c40803440d1013444e800c440d000f9001880f0411808074502c0b01441c00e20024100704840e8680e00c901140141005c0d0b004150f11021a00d00084a40d09036001e0b00400c1e00400542c5c00b541e0301c42e07007245041c440c1030b90040005800880000c000c6810701c0060340c807403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 171335521 1250 171334271 171334283
    0x60c0705010b040519051b0d020c07210b0709090c080402010e040504050705100201020c0a0507030b010f060906030507020f160617060901030209040212071508010e060f040c0909050c04080114090d0c 87
    0x317400147c01c0680d40101d000c1c1c416165002440f0420344a08001401c01821701000c01d509004001c8245100002084402008104014040341c280ca00907410040500383c100400c202c1c50318100ca00901d114030076102a40400c0c442c90f401d45690409011f81031045030007200500c07015290400744800e14602c4001d600031554244000368400c1418444003604070300500090000310f042d410295228801a4880c0380366128040c0100201900011a0001c50304181000200380c1e80b0403500368204102110034005a00400000e940910030300304842095030001e980c0c001444100c40403140f021341058880c941d1054107100100010301c1e02e1400e05501c548003a04036040203a18041c154684419a00002c980c00e10314040307400c100d80d00000007401840601420800c81c2045400f1404010b10417803510302a50b2207044000085002c2d40d0080000c3c0f111440410079454000e6400d01550040e004607441ca50901c0c1e14907816901007140d071806804168050314a40514801c03d48001095100031100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 171336771 1250 171335521 171335551
    0x102040f030c03140a0b16050424030e07030809060a030e0f06160504121104020f1b0f0a1a090a0204090506100504060612020f0903060c0705010b04051905 68
    0x190008200c0c011449198000030140c00c514100521070382203541c90801d41c2c020b02c3c8101c08141e841002c9604241c00e18104104441400300c1107616204030740000386200c51100c0624018440f15005a44544056500f0403908100c0c00710191140d00c1488058020345040c0000743c414507025004103104941d5050002e0861a001102800d00e8800040b45c1301c16003041003086040350044214254440651a10034501402c1030701c00c803125200341c01d001d00040c1009080f03811544440d4101c1e04403603407400c65130742c0311802982160b2000c039031124080ca01b800f40d110145004c171000561800f100f0340c40380c80d1010b24000d03130300c0c08100400c00415030b245500c655429075005d6120ba118405489020301c01801c6d00e0f1074503144020079007850b40c0c060ce0003289001d1041200d01d901002181c1d141e003110401680d075404016200091380a803150f4141e16010341c07414090250405030082c641140b144000713002408d00304080004507a41160f00e046100c82c00e2050140e010215031003158011407511503020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 171338021 1250 171336771 171336779
    0x10120b0a02071202160608010509190b1e030f0a0b160302090411030a140c16020a170d080907080601060c05150f1905090c0603100b0a0201020a030c0201021303110102010204 76
    0x800b082c21402c43c2d009038000354035003d054400042a4006410141894095945802c0128a91203001040c0f106520440b40e942121280c1d19008031381402c0c4000d0845040e4686804900c00d03804960694510900c1356410900707603003801042d0810140c2e003101d91740303485540d5038014400d0030684240600130554204403000c11542c4a00c98403100d000f040e210350f61680b502d0703d01d070b10481c0e0002c030005100810389001c111641e00d0080480352440d52140302e43c0d890014a1000c6401203030345422507032031000b070000ca08254803000502c03040045030550398500303141c850b403c0694072a0518002d110b21a04884010302c21240100301080031244510b007201c5014504814038824140c069030101d05800c038250602c4000b1080100201d0015101441041103040c168401e03a6108030740d00c00d49000300da002c0000785409004076250320003802209215a610700c1e0000340203000758003900021001c0391900c000e45029074814400e0340c6203d581300908000c0d581c216141c2d008461003190368030341150340821000c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 171339271 1250 171338021 171338033
    0x412020a15050130030e040207020a08030903160f06080c0c030a08010618060813050a1a040507061e030e07050409061b0e0a23100e0910120b0a0207 65
    0x4258031403055800100d5506003807003540d00c42005038040b003140d291007004c0c043d00a801e0742401e40460b450700307000391000c0d003210105020f401281400384d403240030003c0008440c20007100070010000120240e8030015000a40740039a180c00740101085802c0601c818000709005a401582260780607600605107500710000910f990f1280b081c0f03000003400f25004000c410340240f10a84580d68140303140311403605124004040c080c5c002c20700c0c400595040413060a0090030b010146080b500b101a003e0380e424512905107580000b41c60845403882034000004541d4480c807041e0352007140c4c41d003507045101460007007100034040142d07840341c0b527006043c80021166a24414200348511030a0049440081d2883c441c1941c9100c2840740c05201c4a49551009540ca90b8151811342c0d80c2c21440708207150f078406107140d008042482c7c2c0394102595031007a11001d50400701074680d802d0126401c1620365906440a40101b1040c03041804401e0010722800c0040c0021880a9215511010050408106840b4a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 171340521 1250 171339271 171339293
    0xd030209011815080702031e130308071b05090708071d031906060b0c0a20030d030617070509071209020a030303060e01080a0206090f040b041a0102240412020a 70
    0x28160543d242451654071030704031500580c80b02c924005107051103c0d03069130350b20170101c402c003906940400042005a00f01c40350506d02c042c42e080758580781c4400701ca1034001c5910040083c00302101c0320f81e9800158501d40300c0d4040b84140c010f84e40b003405584802e04161400c1180c001942460822032403e01003035101000865000c03103414010305020f0100d0308014044942c80d82058076298003c0011401c13090000800b01080c9a100c5c480001f507040c200d0002c400c1041c545240c03541030003500c05150410346e148d0449001e5510f2036001d00c007035824640000703544d100305d48201508104a45c0000d000b260042003207400400401a002c80d14034036690004240c0a03c0d03400840100e03594103030a01070305180f010f581c0c1c00b41c02c000f0000d080004080e00040c40710f014401e41103116200c29a10380a09440d5500400001d24000e00240700e124082007811070820402000c40740184120840701e034608500c0000c8650b400e0a040e41035100f61101d0b250b15010b0b500030704040c815881040b14003030004a0744060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 171341771 1250 171340521 171340529
    0x1e0203011103060f0405011d0606070501150f050306070207061803050a2901060c08070314070614090a08030c0f040b0c0610060e060a030e0c0d060b030c01110d0302090118 75
    0x111582d074901542003002d03500c1d45012860103245050010320103440502e0074845503c047e101260869612840040d045101d4800001c21031350800343c0103499200750712014025144e02c0030b268070400da110300038540e0703940c01221110b00582c0322000c100701183c002d0710382c022a40304841d4034041c440c0c0c03241c031003500d0262008001c48001c55a400681300a080c0d031003021a14858030352003610594580880100311156243c2c0c06001c0b0300c400a420310405014001c503000c504c4600650350f4031440d003070404500a0200e0505548002c411000182f10141c011403804000703940820f00a045865007640348085401035425030301c0c812002c1002080c105001409800c112898400078005031428007000001c02c40568000001c2c401c20800a240350307607916007078603a058898500041d0480c50702e8221440c04501175200d40c4c01603c007200c0311040c40480e801c2000c40c004142e0803181c031454500c0045030b82110b464080c160719041184c59100f410721070740040401d410145000c0c6843c100c00600c071001d131125584 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 171343021 1250 171341771 171341801
    0x6080a0c030c05030a0c0306020309100e0a061a010507110d0f0b04050d170601030e120f0c0c030601050d02010f020a080d02030412030b090a0b060d0509070e0115020a1e020301 77
    0xe010410088500c4a0101604096014282d00d500b00c1e503544903090b210b408010000b075004800500c1d00b48081040840301d60004405015048450782281d842d4240020309580e0300342000300d911200b02240724222020b00069464902e040600d8075100d621103a1041c0309036101d0309140b1010301141540401a00440c052814522141861315282c2d14011395807030030605000c2045082d100d039488044045522030700c02e00f8003144802070340c03080f04d0401d0780d0300c7c0f8801001000443e0103000500d90b000a070400c1e020450454103c0f0104200b01035481209115041d800030b040489800154413554249065401500440d810104550707a102c40580111400d503500300d6020081005101c1024644000514030307081c10000b5403017076000300b1103014000b0328134880140c9400e0030304801e8640500301c0e03500401c039034400c10007420524141501c0340541d10400805104240022035441c0740c0350403604205219400a0224840a90b10508040c4605031200c0b02c10855000b001d02580742030140c5001700e90121 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 171344271 1250 171343021 171343043
    0x703060c0306050a0e010b0304020d02040e01050a0f061a04170316030c060b01211503170307080601081312030209060c06010603060f03150e0a08070501060e0a05070e0904020406080a 80
    0x10013441038090150303210040714002c0c0e50040295041080440b41c0143e010b0314007050705100c50000c58050190441e40f04010b41c89c0c8020012168401d0340503543d4660a072205101c42951030404120310444004580d1030b1210402c410400c48800051152644101c90152410803a00c0e6451f0f003801243c0c00016000f14544000a01c1000194481d4080e0803509090016640c0750304001c0c00442031003801c50849260340e40c15404030001c20902048002d590124107551183d000d5038a081040e003044c0d90700d80200f8862404954158040c8161b02e00c03a1090027084844003401361904030720b004100c041d800906038200440c0e1990b4a0b46001054001c10040c020012540340c60002021180140d100c0c0d83c0c00740ca1003d080c0001500b0b01d0180300d440702140b50200d00c542c480f1200c1401c098548500414041b000150102000f4043d00540c08540403c00d5801161b0380d102e80710425078404585003000070781c604900101c2c914110f460305030003500103000060701d65240c5019518020040303030181c1d90181c1c46 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 171345521 1250 171344271 171344279
    0x301180b01240c120e04020f090306010e0714210103050d0f08060303090d080405060c06040b0109020a050d1a1e040b06070201020601050d06090204060902070b0f06010807110703060c0306 82
    0x10390005050b0007141e80c580901e100290000502401404000800c00c40300400c42d41a070b6407103001004101840200115510300c50302e001549a9401500254060301803c0300003c0d403140460800e0340320340c0c610b8844d4583c441402c52000c5059101c0310340900d003040f100030070b65002d403a5000034501035132145000300316810400e0409481d4000002140e42000081020041c1c0c035200402a15074011090b5041a4001040e01c1c10072494019038015036003000d40414025900e6400050440c015405031001501130b0740c132617544009902c01c50f00e1080c0420000c01103184a03507000d6110012510701c000c024035112105c00c00185014094925000d0348a100100b4a0800e2605c1c0c800c60b080c2840446020349041c0003a40040d4075000140b007103138800c1520700b0100051040710341007220f0130f0381e00510400202d512100c417000250001f02e0300341d440001b00b5002418004c49846c04500440050b10740c49116903d40c00129998006803e0f507089a006940340000001c5460280444d2231030182c8020400b1820 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 171346771 1250 171345521 171345539
    0x160f0f020405090c0a09020f04080a0302030417060c0906090d020306070509040e0c030a03050310091806050c13031118010e090c03060103080306040c03060506120604050105060a1b020301180b01 85
    0x409064070034560850b030461300130341e07035540400ca08880a0303002c05622500d0758043c0e8101ca014661085019000f041d00d4001050741c00300060065400e80b40d8030a9030401030310700613075807507d080f00c04100c003071801c004004051410360041c25421000501d102614445580800d04280741034130b003030021030404a01000340e071425000701d22018043c80b0007002c13581060800655241071510014042c01000008a01c0da000f8082d4010702900180c0c1d0705124454520144c48409a0701c0003080d540d00d80b52070081551600444102c0d24401c9141d15626245802d58481c4110302034a455070780d900c000c1e4481400c03158010328020724000c000c411042842c81c078045103014103200340b00351764601c280c1000c1c0050001501e41340950780c10000c00d032000240000305000503001040b00303420440d44100041003880700c1c1540744d200284510001c1c4c80900180c2d03a0fa0061028901030802e617000451480d2001003907070040101e009803038500003000401c40140d50340c0c000d0307000340d07841d2002d41d180c820110040c0301c4142 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 171348021 1250 171346771 171346781
    0xe060706180b010602030c06160c1704030303050601030203040f02090a1508071802030906010306230906091011092b08030f090d1e110607020c0f0a1a160f0f0204 71
    0x81c001b552604a80b40c8036551640d10045c02010075004101c094210786200b007000d07039480d41c2e10003240b014800c0d41501101c0190050303c42100060300300f4000400b0342d4400e0003a00d0080e90702545041d032041480d401c21488102c014000c90076940c1d24031080b0400b03070364444406c0050a401c0007905d80702e42042024191000c22071112504a801003003401003103480000d01c1c07030440ba0405000100c01d82c2c01c840a001c9155188090310740852810140a0b64101c0030600b40c0c001c088040c200c8100d030840d0f940340d41c1561944a00245e8003101841000100e0070042d91455a101c901203540500c41c0c2e10341c80349504482c4280047c0c3c2c00e00c1c0c0210410414500c1c1c10034481d000103462000b06200c101413880148108100d40c0717060511380c000418241d03424050010800110700400540344c6500e00b160009503100300e08440c00f48565100526107000d403c1410000080d01c401085250a8250b4004c1007000ca5201808403132019a000070b60001040f0b608204401051044c0101c145e42242401080f013a62 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 171349271 1250 171348021 171348029
    0x40e18120408100605060702061c05040b0601020f2a010c0507030f020307060c0c0b0a0302070605010806070e011106070503070c0c0806042d17090312090108090d0c02010e060706180b01 81
    0x130300d03280c070611842d81d4402c181d5481303c2d4100ca02580d40c10300c00c141c604821032092118120181081b090008008040d01c60b288500421ba00300d94400340c880d18a90b41e039400300c10744c0c02840d00d21074006034004807140c40703030761503a04041c14006841d20103623407110301e0100b603a40305840d0305508d0320035941103107000d00822005114a01d00080710b00c04984032a00c003940c00b4032400c4c400620015040c107042d4005d4060380e201640081d01003019627900d41500d603c0703403030413252400020b03007051441a2640c003840c401c48151a40500805031396585c140d050b10160300c0a8050030038000440441c40004218001000c003a00401020704103a08140c0b608000ca0060400d13442c00da0700550022a07502880b0b03407482420315400c104440c100c5000901c0c0b6020a22501d001c007505801080700c404150750300240180f03856a003c1c2c1c1c40241c99074400c8606a16051150500c200160b01503900c5800340d8803401a492200b0402001c4900c1d090642d035405d0201c4512400440c401c4030080f19420a20101d03400700d80c014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 171350521 1250 171349271 171349303
    0xa02060c04080c27090a02040e0102130e040f120201021312030c0f032c120607140c01020d0c030c03060504021306080a020d05010e040b0a0908040e18120408 69
    0x1080c1000100c2e80c590007038030383e02e03805541229400a002c109128103059141d186441d02c0c11a81028421540c4581d0a042c041e4007550400d41341c00b420701c005200710f407031148003071064510590500c00740007180d55002c0c0c02560103880b0013840c50041446800d400302c110b1500d4000580e03440700c20030740c1e00500c0405c0e4804818010403031102c1001c03940101011413900c0e4419041052041c0c546425a51001000e180b04082c10000714403032003801c1d013050001d11440003103c400c05074405999000c0c1d51110100c5e42d10b0001145501c609051a502c4c00c060001410941c0c005800c0030b081040c020116080070030750000207511107092145403501840b0701c5020b0002542c0540c40c000002c9240030803100c003071081c0300801a180000504903c0c3e903030f06650303821960640900542d6507407802c04800c042c05582c00d440c1c1441c03100c081012400301e4490b05c2012948220510309040c545151030702000d0009100ca0321500400070000b6043d6414085001c40320003034002c00d9111030070304001e5450481e0318041074441d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 171351771 1250 171350521 171350527
    0x70c060e0c041e0510271e020a0905060301030f0b040f0501051e1b0901111011041a12010b0c1504140d02033a0f0f1a0d03030209040b03030c030a02060c 67
    0x600c818806d070b00e0b016615a0040303101c10700d124680d82c80205424120b02c6088203200501c1c000101d80c540051103c0e01c0c295807015102c81c2c5840802030310348028480100291038815400f8005141d01241d580d0042c000d19069442c800591191400d54070300b210a112026201a0320321113031120381c000c01d9002050402015800710074410b034a0064480d000c00c150601500f03e2603401c04e06410020003084c0700e042001800b140c688900b031120103030480d01907001400700b820f4404001c0802c0105440310040f020340701e0f02050346444100900c2d80d001071851107282c0036814502901314600c85940c0d008620800c240401980100071050070001100420800c54004101400100b600400c4000462003e40361080000d81e817408a14240b500140504480b0f504058014080c0085e542c0402e02e0440850000d2040c8400b09680b070900d41c0740c090323080c1d0f0300c85d0a000c5a83c0c0071074840c0e1301400e0903000140c000196414000d000a25641001c80301d1803ea610000e0350600b500d40c1448600e4114072412131b8142 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 171353021 1250 171351771 171351779
    0x9160602150103031d130b041d0d0e04020405091e0702161509030c1502011a01080a1109030102220518010b030a02090904050307120206070c060e0c041e0510 69
    0x35000d2043c8030240400c446001c500468509451614400500c000c010441403a103000205024202400209204602d01010b540131528130596943e64050f111000c1c21b0074841c900400c0c0c468017016090190032940c280030114003911005d400030f000b52250030128800751640031451454881c003d00c4002107410500d5440c0c05410b0400c40c02c000c1d210050348810201548000c00c4842610303550019260340314290002a806001d840c000700c140c4800c2d40240b00e500911840c044940f100d80d0300160000f442c840001300202000da10901200c507004034124034100700100004d099802103101e070305448103c1081c900743d508100e520b80e00285015902c0104281040d482441000d0051003012021603000001800c4880305034101c6041c010001c0c0303440e00d28181418040d60703030780200030100c41c0709100c04070700c581060001480c107105089641d90700758a841e9517503d403405455160f050703400c0340c4602401300c1010760b224081d1902c05d00140d804110903040c4840c015080e21405010703c18071003c1d10802380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 171354271 1250 171353021 171353053
    0x40b0c090a2d1d040203011404030906090509040308060603071202030c040905010503060106081305030403170d15140d0c080a06090b07051e0c0a2109080f250b0309160602 75
    0x40c503610f01508a801079a594008207014040d03000004440900c400200010950000308840903500503540e14140148c40c1c00901803412025200a808543d01000240321460b140005580c403145914000c2240388600001d60240d030400c4e1030800b08100003080030302c0090060f00c521401410220300400b141e524200002c0c04410014100045001b001184d00050003010003c4400031a07004a1050040a600c252043d09801c445074105200c3c0c05d0038403c1c45000c1090301401c05a40461520254150a0604209038460440000c80f81e1484094000440c00f105201c458102c5000c0e42d00400c40d030b43ca82c03901d80d02c070210040c1302e5001d02409100707803038400c0c1c051107281c502c0b405a40300e020358071283c4903612860114500001003401d2142052000385c130810f04854113000c0c070300d0707221101c050b5100c02d40d180d191120040d800300140d0001c20310302c41c0c01c0c11149195070b02c407031911076440c0460b8456440c90083d43c003c0300c00d000345511a0310b08904005c2c141038088010700251010380301c85c0c02e030450300d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 171355521 1250 171354271 171354299
    0xa03021f020906030a150305070b0a0e0306040231050a0f0e0a050714040e0f0a05160803071b0e0a09020f0a271107140c0d030503040b0c090a2d 63
    0x901c02195842d40949440700c0d0011142c1e000d1608123049403455035644140c5002c1c3d90100090400013005e102c4171151358140001c225002e281c0c014100001400410f422011601c418400c00007515201700422000d6606842403c0c05072511030004650341c1e091603941400d940c0030768243c20991f03208180600c0410008a1140305851040c8045043c01c050b180016001e4240c041300340020340078000c055000103200081e070584103840f52041e5503422444102c05548440140305007400b0741c004010100c0060078050705c12070580000f002100100381c41e90344408148004985120403190f44911002c03d61400710748a542c400800c0341c0004220342040600b41c0c0703280c01031101d5066031102074698844c05c41160001184044500c039080c4e15114541401051441158452221400350100e280c003103003006180e03001841c0d0161201da00d540ca46545042c6c038820020078070108903d0a011550459440c444628010000c1c560f0403141d20300f505d041e80345982c040c010101e82900d2032900c1001866a03144030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 171356771 1250 171355521 171355531
    0x3c0b100b0d0e070f1409060f010f0e0d0c03140721060e07090c260403020309090406091e03030b01020705030c3601180c170411030a03021f02090603 65
    0x1c0418a880c1c0d54004624060464000c006070034010140400c4240550320807100c2204129800c280d01d880720000d0100414201103404e000854900b100741d0014001e5201000098018000b50406961510744200f05030307aa400889800c1a0180c6559240e54204800005481f003c41c104416100311182200d0304100c0160040840c2d48452001c0300903041440300d80c0003806901009d01c020100d0b880d000340b44194400c5c200800411007a421101201f125002d180714641c103800441c6000c4046040084035040140304541903074903007047c1340004854011200700301c525040c0d14a010401403030701805450b016500641107601c0160204200e1740c1c000b40c05c0c2d5054130295882c01440a45001039607000c2c01100c0311160303800450040550440c043c50609040703c4840c405230284800082484068559801d2180d0000d00c3d00c0300f003c1e51080d1001e8140b40c01500c07540600e01032903c404082810003042500580158200144410f41d0002001c0241c561104080c402c62416801704c000a416000143c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 171358021 1250 171356771 171356797
    0x8091b1806060c330606090904080408010207061406030f060723030c0a14070f11010908100e12120114270702120c0a3c0b100b 56
    0x804075449440d030074101d0741c800400c682650891500107424040315181e00030441802d16495482c9003030020001c0c40395004000007045585800700c103c003002800c080207030068541000030000002d030203009200900086218500200340b00d2552640c100305040000c04207402a000182c40c95132190340422182e6001d005401c040102c100380310f4054100380105442c0050540380041880150843c0340f01515604122395200003124401c000101058050f0940003001c50340381042c2c1400046a056a0320700d4002d040c07508203805079030381c800d1a03c0c0014254056401c1c560354010b0300e080c09000e00000c807560303400c005010720304650345607000f044180c14460490404504600b420f07a5594041294904880b6001d051100504001807c10081d0003034480728098440e41c04501c1c551401d0320f050b04c0b01d201c070000242c42d050001d900d03024405100300301e6003c00d0890075440791500071401c3d125000c4c203160101106000786010300e4408403640028010310f001d00078036203007045503e0203174040324801d0031884 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 171359271 1250 171358021 171358069
    0x50f0d06140f091807170a0c1a071104090209040f14010507020c12011113090c0206070909150e0c12010806060a060f090504020403120e0a060f0f1e08091b 68
    0x200c44203003040041d8015a4002009500c0015640d5001543c00300d87c500421010032425035851503c603844170f0101d10024640e009001c1040854a400302e0400b0007038000c3e00100b2040c8080d400140c03414000c0b9011a80d42480d805000103001000c54241ca00c5200c0300003c00c01814802c00296407aa03001d03224611900f43c0751141c1c0c00c1c04100390031404183d00294001e0351601c50050302c00c048601c1900500030b1b9503103040010159a8400200346008401d56164504054100b01e01c0c0d10141252a081100c024038548002581c0d510403101180704a100d250003a071130700100300d00c080501c141030b0f2140c5520f5020105004071030f900d00010500729942da08090312903032160324007912070364001d510442e4000d1001c0307400000d00884288004100c056035583d120640d0904c4100036005019010300400601000821916980a901010f4100c031003428810b4410200e44100c00e2100c50200b000000140d2440910402c01010000310031184800c80300000308140100c0412100d6114254500b80d8912038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 171360521 1250 171359271 171359311
    0x6050a09110702090c09120a03090303030f14010902090117100519120804050a2c06010c05030706020901090b18132a0206060103060b04090903050f0d06140f09 70
    0xd10110b4641a5000c2e02281451405040e03080d0580c00105a0500810840c85c007007001c8000804c59070300c695030607203032000d0741411620120000c1000d800c140c501550b948115a4a6415080b601030090505810247c1d40b034012800040145c0026180e0344a126400e40600c806644888101803d03500d00392032440c83e040d803400d1001c1a0740c0255110b6201010f6460741c2e2400d001c94240104195507050301c0d08980199101d40c10b02500304800038043d9900e150107213074a05e41442d04982a04128140b40540340340210703407035003070456004980850304030303500088403401560003881c090003c20400390b017a4104101c1d4506402c207400103412651145032004418580d5051a074440b10740110703181c030340348240c1c80c58510518030911090102d41c0580304100000c6d2596109008100c1a5031216051500303240c6064040c1001c0c0403101e1088043c07040a003c45812a881d400181026840e808000315031039140c800f840e5032601da83c0c07070090301540048806102c25107803840700c99003100303900201101100c7c035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 171361771 1250 171360521 171360551
    0x13023102070819080f06060702010804140708070e0f01080a050316030516050303042102071205030904020c0706030b1c0b0a15080709050906040b01050904032106080c030106050a09 79
    0x240304540c40f0032510086480c80055100840394450b06404039480701584584003041070601408078020300040351400001c00040201c07900074040c50746032040390202900d03000c480c2d051600b15002602c01d8142c00f020031229201d0345080f2401816141c001c3c16507100180c4601e612446030413441060b41040312446c00c105441030049841ca182800b07000c0d03d0340700143c90400d480f81d100381c8003520b42c501c9030f8070002d028003a084c06801c0c40800c260003d151042c074203060012524803840080d40c09000c280210421034450740010328880001c07001520b0218144903018048030507121340507004220130b00703a444200e05c0e10024980380f10740003c140c1401c0d996200c0003601401c0b0071040042c501c03c40c0c01c4002600a000601c400c291101d0712400c0c440d95031002c3e1032540d1408200c034050000015080100300e1400d0180e142500719003c1e00d0582101d0024605644d240c1030f600c2074144215542d41070820901c5401c3c095101e540704120001d000303440c41c200c000740400600b4040c8000d00303035446500d1440c8103a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 171363021 1250 171361771 171361777
    0x609030b100f030809120607050d0c200a0203060c0304050303040b06120a06020301090b01110a03030c0c0803100f0506120f2707030308010e090a0609030302070506130231020708 78
    0x2049046006036543c6030318080b003868000c56000c90280408250140380c0400101d00d5a00c50400703561841e0416501000f20f9000e0440000ea0f1800c1c4070310a03001c0d4004652421b00141c88005d414001c00c201c181c0d6106041c500b15004140c0c2c1140c2c5424802d10000031000300840b0340041e00b1800481d195110030b400284510341e04200b01c04d06105451084080202c00e8006c3c43c12540180e00030421202c00c0001907440500040307182001e900700c11500d000103802544a030340003401300d10785600e4000065603221050351040c0c0750020440c0031058104440540d980c2c24a0203030800755145420042030f40b542d01100034010b004030583c3e8401034006100b0091885505012a20b00c102089101030840001522004103001c00e9001640d07600010400040075081280520b1341c5100034402c095058507410010075000c10210708168082107101c020560800089001e0098480c0300030503e4024810440f40e507880155040c0c9401c080d031070001d98500301c40400d403168120140c2c0546e0b03d10a40c0f416140d07501c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 171364271 1250 171363021 171363029
    0x3060a0509070f2a03080103030206090d02070b0c07120809030c010c0203030901110f070603140105030d0f140702060a030227150c0708030f0d140c07150f020a051c05010609030b10 79
    0x424410f5241c2172503806000c0d036040324003d80a0351044d46600318843d4441c14850032920159214035400c01110f0101e20092280d000d01c1070550784103a440d1112904c241c07400c0070701512a044086150070a500d02404007140543c0e090918021040895000c01d84074050400d520b4180031103654a00130844017402003140d0000e012003603400084d01c1d108080c2c01040032980b0700c80c1d00c10198001040314240024118000c45407030701c0e1454100c00703c0074201c07040802060400c2d031420040c84002c0042e04c0c0c0d80058200c01b59941c9025840b15140078140704964150607601011060310503814506890724005010003543d000c0119940d002c0c600640392800100340e008040301d210004e03118100d50072000141c015408980d03018080504224044101c104080e580300c58285c0c8100501000102044070a408450400c080483c2441718003241d02c0490b0400452030010030b000003491068011503d10340e402d44001010204619418180c005102c400d1502000704241007007000b20b030059409420300d070010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 171365521 1250 171364271 171364337
    0x20702031c03020c0601080706020601030b090c1f03200d0905030f0d050405060702030f0f030612010e06060a120b011a070b090307020a090c0e060901030e011103060a0509070f 77
    0x18082941c070040095200344074000e407500a01740042048000400c00c90111031446d0b000701405e0342140c50b480206600a480e031113240c81000344050300c07511400c032242d00c0c49803824440c148000c60b00801500b52183d030f0311010541c0714001045460719101409449000743e03d0403000421441e02e10f4a00e00c0e51140490704c42c040740c00400d2410001c0c00f5034114520a502c01e905840b015210b1000c00ea0307517030142c014a80a80710041c0003144546040c0c0d40a0b40d4013000050403100c8c00c2048000482c00c45819200012140c0c201c902088021700b806101c02b4005d189454501030303200e000d074071000058813042c010070b00d03540d02c0314850080c1401014103a940442d007160249860b804d02c4040540daa50000100703d00410070300c038001130f6040c094803541c2c500d1a00ba4440b2107001616008004c0241d0040125505040d034079116100f5845d024130880c0000110001e1a545c0e0742014410400c0c201059804180304040f82e600b040441a0b129581c03070f07408aa00d0038840b001c10445002c2d030108010240e07040c031070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 171366771 1250 171365521 171365563
    0xc05032503060e011203030b090907090915050f0714070206040510030908161b06020d1809020d051b03093f0d0b100e0d060b2215031502070203 63
    0x2002c0c03440910038170503100c3c0d1020417008641b1010f10a511804554000a6400c1401c0070411034116401c21801c16103e0803404a8203803070a2a010210346041d1041c400e900c003004100b00d01c464024103110382110b9030000f8a410f000c070130741c0003a2081c451405194007a0f4060309200e4100d40c069008082101d1307101420b00e445140a801c03d2500340f150300b8082d208215800f031440124841e00c5452401e8031403d41c06054002d0311000240d85d2101600b00b2400b039154014000a4840c0c418405080062640d49010600e0304112130b0042d80c4507046440c030b102c406010030600c401080005484c1c1100a026061710fa095812805038580030743c000c3c8c003600c81903552504554401140a4000d092205403508100100e07403a5900340f1001c1c1140b0a180e00c041109110032006628000c02401e804901c82d043c08201061030402280d12000b00d165061200b00510300d07003c0d8054494029030021140760003402c2c80c0549191a99603090901e1007014403480e13400a01c050542d01d06105122500f000492400c60f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 171368021 1250 171366771 171366779
    0xc040608030c0d0311090405060d120c140319080a060308070b0f091f0b040608010c02070617090307060903020a0209010e06040b0d0b180a1a01090c05032503060e01 72
    0xd16907101003001c0307003680642004800c0c00c9000748170351000c00d4008804a800d0104150a000c0280300107440b2650140c0c1007210722001070041c054629440049642c1c4100c24010352a02c1c0c201c2a0303228a200c3c2044d042404000680c241d0440c1000110000e0300c0c103000c0f02e48a0551840051107144c001a1400e04000786060038040e0382c1001d5401560741070f0780410243d941e110320301d4507648615040f0540c0e4054940d002c5880c2c0243d0448080214002c10000d40300c0c0e902c800003401c40d80210010780142e00017500c02c025868000e8144000305503c001c00445070300c0c1090714a0b840e841110350052410303907070316648800c1c1071082155105841d800f401d4501a0758407101d0741180c0b0796045600300d2145060080c2100a4102180304800c2c00c1c0c1d2020381c1d110075445008071140d0312440780300e200d4000c0c41200d024030045801480040801102814408140d50401500b0801e0350308900030705080c00010800c2c40a0714014510300c0c551090124684501001c00708800c0b40540746503030121400c00040e0300086 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 171369271 1250 171368021 171368023
    0xb0304050705090105030c090604020d02040521010c050a020d35012606011206141302040605041e0c0306080f0c0906010c021525030c020a050a0f03030509030c040608 73
    0x409540d0111140e200304e0781c3c0c80040542d111480c01c4203d42100481020440703904042d0007400b600b002003d409410262a1004107041d00590303004413441e000c004501c0c1c01016000c0c414046900807d02c1c03c14648256a24040c0d5900001d4003089c0c208504800c6541d401074040050036403420300300061146052001d500c030600c000c0e0a001c0ca11440e80300d41c02d01c003403545804a0320005010058090107903a803a0020103c2d0f8000b1215081c0c40340c0d034030740070a50060144114018030a501540300742d218407520780148004c90340c5070340007507000d03500c3c0c82d6124030b101000400802d60059050008100c00b04610343c2280900010b90000403a4851a06020b81850f07001c201035080301420388070b00244ea604c0b24011600e030211402d020b03400049418018840024101c01406030400c0300140000c0c008400c035007400c403003801c0541500010701100c22032045150800c12100204011103d141c88142004540a01c3d00454070000b41841307800910030060340c90502c040c90030f80c0710060042002666a408907 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 171370521 1250 171369271 171369283
    0xc0307080408241012060b040c050703120506090606090111061603110f03060d061104060503040b1303021f0e0f010231120203010b041b090617070305060a0b030405 72
    0x80c010700844051040d0030507100c1c03901c1602c00c8662803c010380703040c40c041000101500c17844050340c1030360f1111841d0717080c0d440300e0081d8612131542c0d507a215501c80c400d05005042006903585500d4030307400c020500c11650707240780c0d030b041e0400c0d012070b40e0587d14175108005031424013904864440714010b038420002000450000701d240e030324203030f01c040c0200c0403240070f05034280c810119104170030030081c00490024203010015181315481a40b0010340c0e9940c520462103030350400d60240c80000c100000304002c111a808566030048420b80c180410003c007a0b9001e0348540c44886031b811010a1003100400c5500640c0204400100a23001c0c0c507040c40f69804d445000c0d44c0440703846903058010041e0240c04602c40504008543d26134840450741604040c2c80980d8582d01a10580e03140d903d51100340c03426500c07031142c680000030089450840001101002d007a40c500b6a2000d000d01c02111440c16071141d00301c2006610401c00d1900003002d913590780c0050043c009c2c3da000424004404020001000400030341 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 171371771 1250 171370521 171370543
    0x212c040f1103060f04051003030f091d04032703030302160b01090207030e03060c0304020d06060902130501030605010302041a091224010510020a14010204170a021302070b0106050c0307080408 84
    0x13112011403240c800f40b105940702640c510707101440000301000824030400c01c00c5c0c1240c0803403516405069541260301543c00e0b24001c119006049041400101074209624003c0780c03100541462200f000300903094011071b61480007070245070300011174044c42191003204520569000c110405656110007800000750407566080700400d480e201c01440c0c0f0b2500265445c490400c42c540d1a145690b5642070250042c0c01d10000c482498840c00d0114026800380042c0c40350b0004090035100781ca00d4480014141e44403030740a2411705104100500a1148000303805081080030383e8615556060403000c150b540024076109a11405a0507013a8501400001d0440082224051890080c0d80b110b003080311924008074140017503071044138080d0014407844170a010303580c6008001400c29540b408003810341501c11550b504290415040c84c42149080e5841031203001d8250801c604060007a40c81c070b10032020600560003444408103c80b1000c01c2c04200301d80203942c2c080101038507160b45804caa035a405503210 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 171373021 1250 171371771 171371779
    0x3040f090204031e0c030303180605090303040302060c0301150302090a051c1401020405060a08041103061603060e0402010f110a15020309060f0402010e0409020a08030304212c040f110306 82
    0xc0303104e54440b03600180351954224000c4079010f8a150703410b03802460118100c05071004d5030314450000c140b46100b820300ca40d002e81c003e59628602868024100900203003072402d021414001408407000c4014095102c500c0c07405c0060341d4010b0840004d65009180c1c0c0042d034071003c1500c0d600b4614074000007103402e4501c07a030010f101c0602c0300300613103090740958004c86da084170b0306006010f406031103210b40c42d81060080f803007081080c5021000c45d0411034125155200100044a5184901e601d03201e40c600070b04010304010800d05040c1d00090a24190340045820002605242d8110901c24000100181d90217144180041170382d41c800d01c042e4000715502d0165009003030004490002c0055840c1c8542d81c144d50382840031180c00b00b0000100312429080c1c0c0c01450f1008041000300080000b94003480c0140780c012410100140000705105241804c241000080e06129200c03a241540f0079105912070010a044d24110700d000c01c2c010401160b82600080c10403803c03521514400c40194010300083d6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 171374271 1250 171373021 171373043
    0x30702070513060605090105070f02090a05220503030103021018030f1707030804121101021201080c01020a12030c0e19060201060506042117040e07080a0c020d0c0503040f09020403 79
    0x19102c20880343e442c4201030100b0010400b00c0403540c424001058441e10964000380f18480f26004601e8010003103e144a199940354180b261010b04118403580204507051501170501ea42e5035a01e840c0d00041c4002409450b489640d1402c1d94054030900c00350304040c018500030306a5a04005030072030301d420001c0e11000003484414481c403100d5030444041c40d40580301c1e40d040e80c90340d40c0d402c401d5042c840417030303410019405d41c42c0b0182c4500780002e01000384100c04c41d4401e941000c0240d4180b5084070b940034159408450094005210b802030340c0680021402c00081e0886100c10940315041d00c480b490f075004c1c0c001105117991031f40c0410000c0980b0f40d03070780c002c01405450f0428030400344154002c03c001244811174100c6580000e40b0360400851245a4000d80195081c03424100703038000e0380003423440055071020041550360040c0d501e9408400c2076410301900d481d812001e0746425095a00d0020020500300503c00d1103401c20445000b0215003d414032900e544068100017900103010031035280d0410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 171375521 1250 171374271 171374299
    0x210402010305010f0819020301150e0603062a0306010e06070b09070504020c1e0c0405090a0605070e010518150a0207170d171008010c0305010303110a030206010b09040905030307020705 81
    0x216404406440c5c00720010072002d4040703a412a0601140e0000300d030305640310140104110340e501ca4440082140b001800e220303003032071020541000001000c2103001d50045c3c070841404101840d400c0b12f0000c0c040f0680760b4948901300100c500b1200040496000038000400400300300b00c01107610701c141602820f856110703032140300b044180c1c42503030010182c0d07511001100c000c0d244900020310700c211105007103500f0011840007180c141c68003192402d2568100b407143c9002d00c5128012598445424035142ca0b801000d0400a400c9008002d07000c605203500300c0e00c10b845511480c00f020080454400304a444001c0040000c1d5075400324042c1e001d10880c040c9a100015100003240155403841d41c440e154007022716510320b00d10b03501c010198480e5613000c0200080e181030030711509100d940760355000304056046003006080d5088203547d01210b540080c801c030f0003080d030201e1050305560404105a80d02e40c40000050098020380f000600113020010a006440b84c00140000444405a50440b2300c2058 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 171376771 1250 171375521 171375539
    0x612010b010906050d0f1b090902040b041205010b030f010c230403031803080a1e1106040311030c0609010603020f060304080406030c05070b04061a0d022421040201030501 75
    0x945240c90218900010901c00940142c003d08034103031029500207a081c1e1401c54000940c0d8601c07481c0341080d002e1455200e10a0381c8190202c020703041c01401946081c0c90b242d02c0100c10301c5030303200d09a5040c5140c06650f080140039000b4100d600070080031203000c130146031113031402003901c1056070020900d00205441e040072504003890881401d105500d00741440c5813016502e418880c031b000940480810808000078a042e0040e014482e0310366070703040c01c40c0e44940c042c0d1138015403d03008009000000d01d20911280000460640c0301d5407624001c40308512262041c2d1030f5004008840059009800800c00d140a0541c048801c60f8021500540c0b40008071007808814030050314054140d41d803c12003444443e000e034100002949903440c10300d1078180b0701e40300d03100e60440545084031510f0f181d0020707034001c4801310440d021407401102c0b60040a82d4039800100700c0e000d8143c00d00c01071004503072021101c1c0c11010544480840000d4181e0308601034a8600307062880c120b40032400704c2c4c07906002045680e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 171378021 1250 171376771 171376781
    0x1030b0d0206032a03010905070c0203030706090c050a03060b0a0909030c0b0403021f020d06080705011205060a0902030c210601080c0c16060e150a0e0d0f02060f03061201 75
    0x100162180412449a8003807010365070008044c0500c0d051007032504c0550b0076002d2400841d642c1030000c000c0d180d5040920107002d850025018404000c44861003201607500442103540455000c10001250449881e00301200351465202030703440401a800001408081c0e0042140c1010031610900c480d502e8804610440746481000380000c4c2280f42c20200150b40e00c81c205030864080d00440b110181007100801750611b11225510703c041d000703d4004805030850251601401e000400f400341582400b00081440d11030709016640740e40c81d04040743d06500c0d501d092038054005035009643e41e00d880c0f005e0501640c04002040e24040c021840c0a50301203c40b0107850144005035290481900c9281500311541c00c00ca1000440d8000c000026900e03000e0003485500601e800e80f01c11141c41005d20401040600003050154404801c1103140e407500d6220900c80d10210048030303400080c01c0700c0d0178030082060600308000d4100c1400180f0260b40040b40300a14030542048036001101c2c1c101070038403030a8038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 171379271 1250 171378021 171378041
    0x20333091006140307050409020d0c48060c0302270d1713030308090c030106030809010315090c080a0b060c0c0603130b1003050f21090d080d1a0103 65
    0x340c010300f402040811082c0045800203440d1504908154952900904030b80c030441d0b4210150b50307203242da4030391241c00c440740c903850180e51841f05640c040c10702e195030610f041d00c061030030f240442c40c2c900300d401c51032010703816000f190409000c0203100c80100c4040c00035072050401d051003480100c00c80340c0e03014550a101ca80c0d01005070000c0d103081629030300c8a46482800703c0d130460000040c0b007001d0440d208142090b0085000e60340301896030402e0344a880c02e000e0325004940c0a03905222080c80481c0080701200c0545000780380000d0080c2d601300301e900d55420190440f150311400c2482e00819994001c1015004100840d0f0030450311042c0b0b000c0150600c640c000c007005e26007261225401c103140450245600418050031011030b0503446d81c9089030514112001d0298820b01d00092040c0b1004008405203185084c004001c4200c2c180c118201c60550b20741e0368002404001441d02c4580c84080c00d51801c142d00841d0961680300b00403511000e4940711901072709a8500c004110441d6100c0c1c0203443c990 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 171380521 1250 171379271 171379277
    0x8091e0f0312040c0b041d0402010e0d12030b041404020d08090909030c100209010c0201080a0b040f060e060a120f020414090c1005031902070f0210120e0a08090103020333091006 78
    0x1110b001d01f10001a920040084c0e040c843c10382c0c12211a03846007600b0207241c600c5240740c0d90034400301c800c02400b1520502071080c0918548885c0c0806c1700110810281c20a80441d0000202c580e41d19200b2250303c980303280b90350000c1c04407003032042800c3c00002602d448600141602c50700301a0110b8030040b0b00172000b900380017404440d540d00140d4068000c0740e400c44402440403854042170004602900e4011064520440d555401001080112968036401031021910020194a00000102c00200d03015015210440e5007019000b15590703940520b5440ba00001103240b03074501280d4407a121a410400b55000c1c00ca0380c0300b40c6e03204511a070b08480c402d8207048410001e0000000d81c25000b03401c5818210b80c610710440716200541d171001400e40c0362a00b2540c8031640a10a9011074040d2910300c0c2d01311a0710f50082d003141d0b000502d25420303180780c01d0081c81d00580307965038403541d40a4541001e049500350751002c07400000c0e0304401c0c00840e1410344e06075003003540390700c40d4110303c1501400d500c00d940c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 171381771 1250 171380521 171380549
    0xa1415040b060a171f05040b07260406050f0709231309080901090f030201050f220605031816030615030503030705030406060608091e0f0312040c0b04 66
    0x1840007510540044000e003035548200d80f103a2244a509554028000803648640c0b003040724a02550a8144000d048020a000609003030341ea6000721000034050740240325058815003c0301000390b0900c081645154400040c1d8105420907600400043d41c888003401c0030a00040e00d55400341416000301d03a600000501c805016141c400c82451000040c150302c60594500424500418069100c0050003400020f646854003030024240e804030b5809424680141001000541e8002d000c0e03c4112070340030b000380d50f12003040d00b05d441078402c10b00500c050031204840110380c0b9640040658411140300303c60b200400c0d8501449591440100020200c00006120501c00104a45c1144001602c00881d44607442d0701c0350b2741d050440e04102e40c0c0900148010041100b441454003c01c0000c1c80380d07040c01425820311015040d160b01400b0007401203500d0580510801c2d000070440c20400c0919903080d6074503101e1180e18024002401c0c1c030282d0311200ca5440120300060b021049504552107090a400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 171383021 1250 171381771 171381773
    0x320161101021504020f06120103060f06270209060d05090a030f0c0c0b0903030f0307020a03030623010806060409020c0a02031e0a0b15090405030703020105070810031518050a141504 80
    0x34240070246040e40c0c00900038008c1c80408005407880c18040c520840c000306202070108500c504480c165808a500f2a92208070300004545840d00700300d60041200300503955000c4400800c10714030038001c3c4e1045071450030080240b07044000c1070048280b8400d070340c0d03802c175a80900790442d070381c05001001070008581c0d00007c20081088070018092090302034152030a02041c0c030810052600112071100140c5c2080407500d00300740d40741c85041e001d45034181407803040180300c01c401240e54a0103a02c4505110140004c900d00355545815500101180107083d9175401c84403800302c1d15012040000ca009110b8483d000000030000c10740140c03003081707810050503d0982030b1215480f4820290145e010241680748022103074842c14075032840b46000710000e41c1d407840c50b46002421244003c0c040c80410003410b0030300103a80d481888040c21240c000280308a03000317225221600a00c030301c001c810500d9141c00e404908002011440304100c50040341a00c560300040d501c45c548414580c1400303202c0501c03000c0060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 171384271 1250 171383021 171383029
    0xb0108010f090e0a06060e072303130f0204050901060501080a0501050123091009061101060b1c0b090a0501051005030411121c030e07080c03030a032016110102150402 73
    0x900c85a811000c690b00b691458440000302c0780b054001070301500c551f40420500c580c102ca6480319150307015060441c007a01001255070140806010001e2120306101c287c0c0900c140300d802200c502c5c0c0c009104003c41c0c01c0041c0380030b0003001503202d024041007015001908400c81031089a048840684600112001410445a0b1052000e150fa00400b10521040c0002e40740c150031006051a60b44803807000500b4003a02500603071801175801e555030b040c40320900103d9102c009580e40702c602a400c0d401040e40300c05c2180c0181c15071100c2250403e46980401004111503004941215002d580307100725081c07105005c80780c0d4802141c010b410b50281e13120740406410300000c0c41c4064162081500d04100da8460007580303120b240380c40c284c00280c44106400d02200188542e100510ba000010140c031041400420b44134000c88003480b090658814404e80c54503480c201c4540c00361410000550380b268428144070b00081d000070280d43c105000e0361240c00c154000240d894548510b001c02201540d2540c1c00c01c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 171385521 1250 171384271 171384281
    0x90a060e061f0f0b130b0a030507030b030a05070303050307020a0b0c2a06010303120b03010c0315050f090c03100503030d021905071a04050705040905010509190201142b0e010b0108010f09 82
    0x7085c0d2040c2440001074040c2c05900a05001900d42c1d501180c0b80c00c00740c00043c240c440c44040980709800c01a603160000d040003a8481c1282ea02d070405984981e5a0f12080c0d080c9414a280504000c1300d1008105200c03805400808035030304c0702c07143c440d1009484a4401c1064103107844c0e20100743e2086005101190040010001031014100007150740035032a4046401d4606452101000c0307512020f11014103103480d460b40015000540d80032800070402000074003c1000600b04480168001000c101010003403c1000054040941102e6540031200441002580540c25091800c41c030701f040040140e22034001c47e945180c000c02c0c0b0f121a010703465100000410090070494203407107540c8000900b5152405200c820380c0c01080005900d242c00c02c503050030b01002d00c103080b002c00307102820640140e8000c0c409200d414510002c680d00c0d003025080c4c064903104a200561807640e40384480223900701c3e007504440107201d00c2500038406041080e00655503100207000c0c1010b810a158018082d4411540c80707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 171386771 1250 171385521 171385537
    0x9070603020c0a12170609090c0409080702090c04150f0f0f020c0306071107081c0f030e060c04090f0b06040b090607060207210503040c0905090a060e061f0f0b 70
    0x251091600c1503980c100c0d0000e0004691070100702c446904108103c0c50400c81c0364481d00594100c8848d00d40703505c1d00d50b141c46200c0f1207030f0b1056507035001510a0041e140190b0307041903070240000c0254188048200b005400920800400d00880080521007038030852042c1040c100c161512580038802c001c0c25907032980c0c1d0030310104c21442030b0920090181e070104046e0b405024907856850803c00e580030201e051030b81a03004070081c0d90103252481070019a080e0541182040e516026401240b9100100d02422107080361906506c10001030060300d03030f545d8006004540d2140401c02c19004214001000d81e0740000c4202e40c010030a01081180d10500c6004001c04140140b2280ca45a403668a8008a070055a0103565802e0902012801080c07030504000320b4072150b0600c14203500d0650350701c041c3c60509005116200d074035000803408002c402c02000716130603441030007071044034040d0000f15905d0340200d0b402201412000621a00007920b01013480642c1c002c40b40c0f025042e801c1900400455200c107070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 171388021 1250 171386771 171386773
    0xb09010315021c0b01120b060909180303040503030610080405060403030522050a020a0b04121104090501140708180a12020a1407050a06080c07020111120403060e1509070603020c 78
    0x803200182c030000000d5294610400f0b4005640c20313404000410469100321300010351860040e40c800c9560340e00301518020350b0112030180e5195191007100ca40100c403a1458800e0f41b0010042c0010404084081d621400040c1ca21070305c10b95040f402110808015640a41b040d00800b01180110703210f6005158081210710f50b6042400b042c0000941d008400070040c2d512ba0080000c01045203011062000100740002d0014101410080d03c0b0400c1081024002c0840c201481d824006440c0c41c0c11011034241c20000800000c03d25564a03240ca4a003120b600000803d002d0004803482d40c135032100b01134008210002c3c03125000b596a080342a00002c803000d81548030b2800200002000001641010344016028014480c40c0c01c0c1841034015080d0001c0082c070400904019000b0608010303034441c02c1d02440d0040c254002c8903c0641030407c0000c00301c0c00344800080100c2482465000301c48448a040e049889440d0000c10021001800303443d40d81107900219420042d20344240c010303003110000d5034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 171389271 1250 171388021 171388027
    0x32202030705100806130c0f111204031406060102030a02100b04090507030c080601060e0607061e022101050402070201020c1203210a050a0b2d0904050a12030b0901031502 75
    0x600043c0854925207040000201210204130007420405141030000344582c5050080040c112000341004c0e8408040b4400c101c908400203000d540c04111444800c0502c40005607981d13200d05040a40c805880808003a038428000171500301e510000c11100028280c0d400b514400843c100b01401404200120950050300c0f0711090b000301f041406180002c2d4442c041e01c6035000c0c40c10b1501c1d8200a0160700c6a41403b1175485e500c540c5407100e40443d41c0480c1c6c0b01c400050500411152000d20705500c10172040110700c0402c448114007141c025904419222110164041c0e03a140200016407007400ba000f4010782188034514403508220118100445000301640d0418280c002034150355100000c1e030008001c02a4180300703460312030307120b25a000740030540e052001d214100301141c018034211090514004c00c0c00300300c90b100d184030070f0080c0c021a8020806941800c01d0b04050341d480c80d45031b4054a414803c3c20760314091900900c03907030000180c040e0542d141d070380c43c42c0c035600e6000003100146490244c0070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 171390521 1250 171389271 171389279
    0x3030705030a031d0c01020a0b0903120103110f0f0f042007030f0e0d0201170703060b040b120f0f010b09060906070309140a060e040b0301060f0e0105040f020322020307 74
    0x184042c1c54003246980d0009003a8918100100240e080c2c00000d9101e84c2006540b480c841e40c0c0440c0c8111100d810543c00c1100c1c0d1940300210b440d6100702c1c881c000c03510003d00004000c03c0120610040489812260b0000f9821980304205010743c1d02030102d5801010518010503500301034018520462070304214190425442c50814020f6208100840004a6130302c3e1001c42076400032214003000c90142e4441f01c5040c4190b0001c1c001001040244035550800c1c0000340c0024402d4200348058821486801e0711246d0318102c0a4a54010441ca043c0c40c0c15101c0008a945501400842c414500300f41c84001a034a40300d8002265032200c101c035908030104010000c0c090b2282001017802034440e64800c0380036850719031200000040c940c4154480d22490204002c1c072075020001882c4060f045800080d05502a00000e004211507072150900035104000058528020900310f4103c8106982c2404205090503041d81248402c481104030300502800c1098019500c6107600800303440079089600d45515 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 171391771 1250 171390521 171390523
    0x141603022e0c0e090a1a030a03020115050906150a03150e09010c080c0717041208180a03030503040807020d050f0109050f010903020706180e100305010b09010803090d0203030705 78
    0x1514818038112460400c2a03619580d582c86440718800d0203140000400d43c0c1d14000031000030001d094101500e072280446541c1d01960160ba0038015001002c90b40054140c0c58064003030000d5050003840d049210b000080c0ca42446000e040c03082600919582c21070301c1ca8185c6180300c0d04407000d05420140c0c3c1d04c01506808140461400c09840b41d401c11144501c0e140d0070003400c0d1041c41044808100302c08050041c0c4407510300a48000507440a02e08042c810903020783e26980c09907a2107200c40c480302d0074010050103018001006c0b02028945042d46016407a001e1092440d15480014009181013000801040c500750103010a684000c0c00001400040d0300d407240317030000040e46402a0b1355143d800d6010400208051040d50881c40024000c10415480281d21110329114650900034184642c0d02d010800540c50f002900c01440038071030382d00300150461408170701800200d91546c40c1510710350171443c0048485d41210043c4005500d406090030901404065072041260180300030300c062400640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 171393021 1250 171391771 171391813
    0x1030219050a031406061801050f010e1306060206070819111c0b01091a1206011e0f0e01022a0d02040501080105040c0b040308030f10030506040c1514160302 69
    0x200072a213140120800b003180c0c1c0d0070100c02419551113092403030903070000c0288420f00c4604641c0c007100c9042d424007003040103860035115216200e5108409204124400d88158800d5003a10308590807a09641d80b500b800365003000c2c082e80d101209000c0403031307410544885030b00901e401c100301d0039421307082400c4a5050104c0c21115141f4802003a26401c032455117580c02441c0c60020507881100703502032011254000d4103881b6000a150842c0040800902164040c1590001d480c02c10700c03100201509414004140816407040d140c0024510484589150310004003000003907041e003448a149031100e9241c4141d04039100d280307074100390586160701c0940e4031486624001c0080c9400403d540c034241c0703400840b815907900f02501d1140c2c1840f003403010030356080c1605c1c0c4c481e90f41c2a5900f46a250040110302c220080c0d80b00030320a00c42c65080000b0000d041c211001203815903020b02c600b01034400801d0300c0c144d000250381e01103c41b0903c420032030988d12402008106000340141d44030304480c0399840000131 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 171394271 1250 171393021 171393023
    0x171501080a111c2f060d05060f09040606051e0105161403070b0a060801090503040e06040204180c020d0905030c06030604020c01060f080d02031201030b090c03010f0c0306080a0b01030219050a03 85
    0x6107a01a0084111204c2003e06914020703040480f83d02181500000da00d80665080d86140035540c0000584644403009c070030700030341d1004020000d28600352500c1e00c040c0c0028000c990003031158005100c120b0490600e10b507059001612040e0a1036028060301e10040003034082503c8240781040220603c5000f40002e1442c00e0160070310494a00d4040440390170f541c09648400500e82c034100321075012900c003109950a5503a4141da41c03004e40c84800024001e401035400580f40d21003500c41550b08684c0c50303803282400c0492a000d0b0b441401210009403a080020311405805030000b0707006d2107a80c40c00074003c40d400540184014100318140c1489800c44805400500d500102c0090610020344c0400a290101d08a48000c52400509015074800c1060620005044100340c1c00400d078a0300701400014040d04010b0002c1000c484c481c01414050000765450002191400d4004101c1d4840813070030600d6160400302c040c180d42d05e180e00b4001d0345101c01628200d61641c100c0080740030b9490380f602e18019 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 171395521 1250 171394271 171394283
    0xc0b03090a0b090309031207020603010b030a06090c030c1205150d061d06070909061409070302160b1b0f0712050d1503060f0c0801060e01030207020604171501080a111c 74
    0x705c0e20038091510341480c4404080c40940b042c0034600060740c074842220705680c0182c850b2516507d07a80f0089010700450782102c4d0006003461710300d52a80340e142d0701408003545183c0c1c1e04000b546071301c4080e0341102e409841d0907c0305032511a080c510b0303003844036800302803910030b1a0010782d05a0b0000005200107042104518582180c410b01c100070342e10050380000740006080402c0498680700c1d1050b40e8a0240451078011405880040c4555000350b041d84c0000c1e148010520002d0350070714150088080440b0400c1000c1810031428201d41401c034240c899540e245054540307041010b407030b030040045040301c0110800504000000ca01c0105000f0020710416271282d15001600390f00c0c1c088280e4025100c44440c2514007048244074550160865044a000b42800807001d01c0e1140100c01a01c115200650040b50000e0b0024070550b00c3c01c414840c0850010642d444144081c802c2c080e040401e00c98080c4542c0700c030200c0e50110700034000c111072000e4018505201c0f00349002600c00c540071144025940 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 171396771 1250 171395521 171395527
    0x10305190203100905011e06030b130212090d030c1209021c06050403030b0117130804090c020304081603050a03050903070f03050d021005010b1e120112150203040c0b03090a0b0903 79
    0x642020b409170a0140c00301c8070782e0010306102622001c101180360301c038900802d5100c5440d2803481e11560032801c03c4a00f59030080d50780da0400043c825281d5001d941c468400d00c0340c00245012240b2904c240301061030956120780024140310f2a040251102d4203050380c0c0a50030440c0b80500c0e145101344a40001d02c0f0700720204042c40d09090280803117117807513030081c18003c1d2010656135000141466030742c050302c5401c5480d2281140d01b0144194050f5030070403a040c42c40c0014460b01d481e0008003a008542402c000c6846082e0300480100543c8494403006049501c01c1941400281c05240a001141c0018080714502941c9020711216017803264070541d40d94003d2604040141d1f414003498081103c800010312981d4580b404d20011031041d00202d07820130700b200260521064074034080301c84083d0149294811947c540120720080040c3c1c00003120050003000343d03c249290307103000b5280f04503003003803042c070926290150b44441a800109a4880c0303006005001c40040c0300902c3c001d00a0300344d8002551 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 171398021 1250 171396771 171396779
    0x100303032c10050c04030b07080403020109082a01140c03070210020a090612060f12020105070f0b01050907030b060304231f0e0106120602090117040503030a0605060a0e01030519020310 81
    0xc11280c004d0002d0807040740c1003200b4400b06481c051556049605842c200c1d04e1342c2e4550604034010440c0902c010322a00001071010030143e5440014090302100f224010451101203100d40d003224032882032008030072044000900d83c8850740700655401402401a501c0c0032000c000d0120491380034141500100714814410f000d007650094410540309040075041004500f004070382c1141c2c46003032003610b0b540c0d031502199800716407051043e2594607a000684601060041c500101d181409029580c096414103001420240c8240240201d28001410240c51511a600d803802c2400108003d00c1d40024441305402c0181410800995800d61900450030620441c890b81c03000d80307111110310304460381840310030301405400c5140c80c00c049a000f400141c0c0c6070220743c0103071a01c100795040500511201e0342040144100400210b204500c80982044080d460300200041c030300800300294001801d10020100950007903000340e410060900302032031501c444402d01c0c0c080c0e91081350001440041e24070100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 171399271 1250 171398021 171398053
    0x30c0803010f2612030709092f190503070c12020105060a08010207020a141f030c35090102090d0f050606090c0d050c04050414061503100303032c 64
    0x105000c8640343d05034504070303140100d00341d44000241042c68420303000408a001c2c0c0c0c0c001c016030f500034160320406110684a01c60011016014000d00314100c203e0f1804400c00686000112800040c161303004010840d0000f900321001d0b00010400da0030f00c0740b1031f5040008100c801320703601042d0049900110381450840217200c0803809a5029144680c01444100010390301c414000c01516000b040d4203900c0c1e4091000915064400240403d440c071004100200c01541030300f041c0c400e06255201e0321644155860384554145001580c0c01701062403455200c600890b60076002d4000040f480054109030a500001e0311100c0744a100302c4010190301d40b414104201400569072008048648004c00e2501160b00c0e0007602c203100b4503041c41550f600020305410a0b580940d001381001402c100514046d040e005a00340d50180c80c07007446442c00380001005242c2c054116889060800e0324014400d1031a50b042e00a440c40d1082c4c1c02c01d10804070a000f1030040c1203101200742c0e400c3e2000030241c4281034030000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 171400521 1250 171399271 171399299
    0x31401091b091a07081603020d0320040905060a05041508070e0f07140c070311180702300a02070f0803040b0f0a020a0c080303070905030109020913030c0803010f 71
    0x40c4007407001c0702d00c0030804411001c0c0210006036a1004036a07440002d032400f00e04911441e88003203c00c2000903014028150300085143c44903070700303480400078095000c2c001614042c000c94040d80100041000f0f0003404540c0d0040b82c0c000070060610890103807640f000906440000441c0025042d03422020003403000e04001040081039030301d0801145060a860804c9080c1c401003880c4248142c07941d400080e051110304580b02603050005035580070792a407a000c004a080c50141c144541d40f070110520810f4002d040950180301c554000380030142129003801d40c83d00091400005010046455490814078540140f5110545030f01034482582050030f11000c842e00c0b0342004400c0c0e8800d000034092421064101c9001e1750710a80010b8850b1080b20080b4644075208000078600343c0020b9000460ba00004040c500030351540c2c03514a04552106d040c1422a07160300700c041d502082c4071000c2080002010503903025036009181082010449444c0c50780c02f94020b070f100c04040c2414000030002c00e041030540e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 171401771 1250 171400521 171400571
    0xb01110f1018020306010b070507092a030507020d1101020d020706020309010c0813030311161103060603150a0f0e031612050309030703031a0a0b0403061409070e060103140109 77
    0x2100c602a00885d40c0da42d0140144280040000303051418000100074940040c03840020620001f480b2003c079030300000780400e240001d0340e8071490348a8000c1c000d008180c0300c0d5071554020120404070441c100d4002c4500f0700c8110265508003e044e50900183c0003c20790a40582000b40e960b0070454541c508440c41c2e500280e08204800040c04001c99140030105481c50f00b40c5004918604001c2064009219034209180c01c1541c0c4416401000000c482c5c00a00c084120b060769600d69402d014541c03143d40d24074821207091030200005502440b1030b0f00000994648400020705508041001d914540c003074404041e001c4882181076040125054000c4004c604a180c00c5045081c100e00541d0359001d041402800d068440104800e075410301d003005409440020584002e803940c540d046000d0303130720a00098540b9030429107160034601c1c03000c00321400b80c503404c0c0040c41305510b44180c8810a00001d408e0700c0c10180c8031145040d0032428600d06501911070100b0020701d4081280d41d0340803051514413 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 171402877 1106 171401771 171401801
    0x309010f14091005060102030406140712090905240907021f020703020705060a0e090406090213020903102a12020a081f050f040b01110f10 61
    0x102250052005000b41c6051107424920f41d030503500112082405a4070400c001c10000c0e10441011002000801115062010316a80d4900c2d48441d07024071710010303050000a005030b1103180309441e017002c1d00c21141d00300040c10800e181050850b0804951045a2010000392441e000344191007607085104883c0c0c42806040b6641d0009410108007600140716111303010445007006030071904d58899544030380c5520460710040203480c50000304121404e903103c808510041c0c41311007810100824469000d62100420740034140740038a1148000c98413410848d0200c84040c407054901b03620a640092000e502035404401d5a000011014414000e4800269580b00c1940007000d207000d0503040709802e881ca018248007005181c001e0041907440b15403070700305110710b140560050811207810704221601040070381580d0700f0074805030142481508001401008100e0500c00d03da1151a224 = true := by decide +kernel

theorem cover : BRFrame.Cov 171223021 171402877 := by
  have h0 := BRFrame.cov_init 171223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 171223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 171223021 ≤ n) (h2 : n < 171402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
