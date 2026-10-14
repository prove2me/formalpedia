-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2482
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:50:29.181677+00:00
-- url     : https://prove2.me/submissions/d5f74830-e332-4d87-94db-e2221caae195

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 446223021 ≤ n < 446402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 446224271 1250 446223021 446223061
    0xa03120507060b0301091b0504020f03150a03081206151603031109030f0a06050a110406030b01090504240f0b070807020a050a0312140913090c050901080d08010b030609 74
    0x25218180f50720b003070b00c00340725280d2400d014404014000308400340c0f21002151942c8418441c0c0d0040c002a58808815030499401180b4550a005204031003404140440310302c0d8005882100082040040607a440c461140300e41400c59940000c11394140d00c02d8000c0c003842e10001c080600c408801c000090080c1e000115102680303404505004000300080d103800030421404100d500300301c0c00700007000b0b6140181900101c03039213010b0241c50303500700c145002d0780198070130f0408041d22201800c2507a4056192013015140190045c888481629403904222040c44c950f081401401c500002d0b14220f070064150a0360300f003c0c0c0c140d142c100c3d140c03a00b01c0c840e0400d0300d090368020741c500b100083e40d0780c840003128011032043c0c0c1a0202d6500e254000f620310340b507080f03e03040741503000c11018100d0b58618280c00090f49101400140180450a21028140e003e403c05030b00001041c0021410b400000b940c140c0140e002d40d611032050b070b2a001c64103003a0205407201c41e004000980400c007080c40740c20840c8502 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 446225521 1250 446224271 446224283
    0x1e060c021306240e0f090627070801050f010f080a020d1d1f05010b04050402071401060828021f020a060c08040606080d09030627080408010b0a03120507 67
    0x240d1034600380c42c1101101402840c0710200c0e4030b403d03046140c0000a5094540c003c0f03400c03445068180c40412484440100020300c116101031000c00b4958101048a2900110300004010f07031416a402074600e60003801518840d10f80c0c034008848030742c800c050100c920051a500c4400da03440d20219a0041c0d049502c60000385030f100c1c00301200300800c8040c085022190080140300c0074410800c40440302c05a09a0306080070f00f8500140550744002c000c0f44c04480095900681d0381c9407a0a240c00030348060703650400a54200400001c4c039450000d020140c180300c1340c0c06403020802422035034010485405009411014080c010003545240709d40102e00800d1900544a075064540d0714041226581448100400c0c0d8103000d120601c401446260007030074000c0300070701c0300c4500648042c024401600c401810941c84140c00c58004001d6900c04168034980350b40c2540f04c50300ca1400c800386800a0050a03242d41c80c000da981003600d840f410300022607412600c4841414000314080724544d10009013900c3c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 446226771 1250 446225521 446225531
    0x6060e0619200a0501090b010b0304050601051009051c030f02010e120a0e0d0c0906150c021e0604030309091b09090506041812020c061c05040507090509071e060c0213 73
    0x8600b4025124103611420000506c88000c1c5040d1a5003d41a000021103010a1007003000241c0c0000c2e805041d650211030480344d0003c410360480b40c16a00c1d812564011100d400c2c01240e9030205010322242d45d21940f07888050003184d02c001c90032a1025074003004180e001d20f00e40c8903600c0d01c01004021a030b100e0701d810303031030000d100002c244110f5450304102c3d002410703524104820640382c85070b600942044007000700308001c01c82c4000d002d40328405010b4481c035104140c0102240d64003807500c030201d102910154480b662420007401c4a2160f218000312907050084c0c101e101c01c0d11252039040d4809a460300e5240304e09000b0307108002c040040180b0f81041e40d6092100603102881c1022105a10498840f002c40d200100003e040c40604034026004a209003c102400320001004990842c00e50500280c5603945040c6586004070540c4190444c2d4074040504c40310642c04610f810039100c0100542d02c0c4034658a00100702c40358144a080005070b005030300708005241050382c410b02000321b2030011407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 446228021 1250 446226771 446226827
    0x21e15070213060f08010609050402060f03190e030706050a09030807050c0709052d0403230415080717040201050d4206030b06041217040906060e0619 66
    0x843c0c00541040c001c011501204010784c8800340a9a0702600000e8001e11a03401c02d680800d65038040c11b6140c885040c8080009482c40c07280d403880c40303c145440c9000b84442811085110340765031260b072007624480d052100085019280d8001d4003030f02503059540f254240d8415900300c501d0b0300310a0034907005000348203000401250b9402228003c420100400f03052107a12190152203600d81c045912108400d80708200120707400401c0d00340685c0e031006e001c2c02d0792110210404031601c40d13038100c0c01f005041c80380c5400c2e5140e481340e174a0b071150005403a0140e08620520144e106080304682c020700041007082032000c40341c82034010041c6005107074501d800c80e070055007000f00c008151815804c4482240c0e07501038103001c0115a44c4005102d207040c01c000f06c240440c0030458504c1a8001c0f00680754120803018100020800091510303040030489903207484c0c43e800610301412080c42005d000078641801b450480c5400c40480719000400202e0000c14084001d0a44500c0c11518441203055440c540e40a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 446229271 1250 446228021 446228059
    0x1a0f1c03090501170601020607232701021504020f010908100e1b0109030b0411060301140a050103050906070c0c0510080a050a090c030f15060b07021e150702 69
    0x202188251900725000b4200800100441000d01000d80070890750701c184002a41c0114040d604400c5c0e500d042c031022030741c040609502c81384800b07070588040b100103012060341034660007504071600840300e00107140400c031004a0f0b40f840c9264180310b800500801090051904010280610ba01810410700480da42c0e054242050a00c0780000724482d101c15a0b00720000c02844500180e041d141611502900f070100001e00c4c4880034000100416480d502140034052004940340441c4030081281380d8070341e114000074034540d1030001150300542c04201f010980b503000e4044c0501c501c1d5031300c00820b010f030389500040315250440001030780c28181e503100100b001c1c1c540103185a9060400c2e2141121800e12024480440d980208404440c40c940311541e000a5201003401040740d4104c0940d10543d00c42c0d0030001e40031041a9040101c403450054000f07602d409107801380039010b00803103c0c80080764881403000b144918400d1501d901860513043c181841856a010300502400030700800c4501c40306201132 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 446230521 1250 446229271 446229319
    0x60c0309010f0c0518240f13080a05010f090f110a0315090b090a0201051b070506040f0603140f0a320405120a0504050f030309031f0f1a0f 61
    0x10f90005000042c0c5480c00100ca040c0440c02004203544500c3c0814407050030300f101c1c01d0002148140d109001422500001147e01502c1010707080d45606107941c1c0e502c400c215560a002001107890b07508095000003c5400c0c0d03c5000b035001e400008000304907500c2d5548030040e1031898211640850085e80c04004100118034032406014039140006c0c1e14412401e103042c003c0c1d4001c04000d030f80c0d4440740780d140041c0d078084162014030395801c0440030b6040030380b0201da003050850b41081e40c00c800c2c04203001400302c50340c0f80305204481c80754404102c20300858150011500d4200d907551895031031000032801c0403070a64055220044881d403460000b040aa540d0421340b0314400d0700a9a401e00c8500780403c2c46000d0000d207a00318410340600386807240d0000c0c0508103016a1080600c40c1e03008071505d01094800384103c6e40d0b000001001d4070002c3c40e080c0009103604451801802c00c03d4502a405030403692a486403003c8444c1040b95884002e600c04100180e0030380104941d0f400c4400c404040d1380d090104a25 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 446231771 1250 446230521 446230541
    0xd06090f0b1801091505100305120703090e15100311040305030316021b220504061d12031618090c0806040218151b160611060c0309010f 60
    0x1d4048a0708210b01a801c0b000d4608040410300d0345840034101c000b41e4004c3c401c01350120354050110382951031030761520810700035600107092401501000100e4562000080080c103109486a17441d441d240d528503850720004031408584481c0e52042c681f01860617980285001c2800e02d0085481100150207600030707003240d4000c490660020041c002d6900390307207030044243d1145100410344031443c0c0103038201c500243ca000074090104001c0301580b0140c140c007846d825002c071101c2886030342410319109004103181d200c840115050101d6a01c0f1080e8086510f0b440014030000c154150b4440c0c9606400342c0040724881014450462606102121440d210500030200500001108125840b0182000740020001d82c442d5204128503031212100072800c4c050f03107a00b604c0081d040a0503072454046481384178a09802048000559101c0030000201c0c410381d240c01003112440282e84010039605a441e00d60303500f02c242c100344001542c11194002966105400c2000842c007081250400c800719925004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 446233021 1250 446231771 446231783
    0x40f1e0503120c0708070605040c1502150c1303080d060302041103150a0e180f161e030302030405060c070506120105040b0f03030319022a100204140d06090f 69
    0x16040064004041d81d07035804480c40f0701d503500d0035110740c1c2c40b1002c40c4207a8070010b12685d560008607017030008076610700002d4010025011136001a800d00a0354990400121114501103003000540411010040d01c00c8520440030002400d41196076000c1103411400c0c0f020622035450600101685d1070b80524021014240d40c0c00d940c13414035081d03002c0c10018104940b805040031130410013112901c0c000a5501071a12420508a00011401641040d005024500e81d0348189514648088103803041c03c0c0444002a000d0005d101ca15190110720b000c403844054003680092004025908082008220284204054035101038a0b900041d44035001b49000800304019000148182d00b8144120400a8001c5811110203450100003030f9480c0b000030720900a0f0a81d089060100d84400c0e0107541501c4115100c0c69030100c94555180300c00f44103031000703070228440d1a051400c0140c491086a043c1d950701d08150081200010500990645a0108581a59940c9841c0020400d20785100482c144159 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 446234271 1250 446233021 446233027
    0x30b01030908160b010812070b06180a0e0c0405160e121606080a0b100e0d0c0b0d05070c030f0f27050a0602030c07092003090c1c030503040f1e0503 65
    0x10500410020058110500c07d80c48002943d450b1421803060780c1d041c941c000407a40141d550600411405800380440f00305201c031240c18889140071075003101140005050803102d040410108000c00c0d0744003075a01c402c5280701840c40e03804551045902c003140d24030282102c1800e4040d05501480d06000900c00b030984440c522092080300c3d030110005400c9100d5680c2805404140307000034036a581d941c1002c1341488100c1201500c81d8540e9001c1d0480385070485109490a640c0d81d500c0900c65203c03108801c411446d000018103030314040c05840035001d425070341d82440500007001c140e0b90f8030480e90100c07003402010492080080348041c80300008c0104214000d10700d0380350005000d0040150340115055400c24040103914141c00214901203174904003010605003030301e40c80441a241c0580a0310440100001000f1401e840003035099a0302c0801d44413040a0620f940800840c00700340b01d00100020410401f00300406c001084500019000b900c001d201202c074000c180c18241080c00088503240c0000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 446235521 1250 446234271 446234273
    0x12050a020d08031b040506031f050d030305040b0105060403080d0209060910030b10260a0e12070c0e060d0b040311060118200702011803050115090e120901030b0103090816 75
    0x80c448840000b0a44c10b00a0521b400e1800041090100416001030010301c2e01c00650800200c16421000b040c0127048842e11004908004015240c202d806030b502d2042040001b072a410f2007404c07207048980141c103650902201c2510300003c0d602181d982940944144901e01c41907642825101c44441251000110300e074070b00c01404a24000314180c2818840c8503e140e101c40111000842d541402018140800b80e8800d5041c00060100c070344484c019200c0c0c030010540d0042894001e1001c08d0003080c0c3e1590941d5560b03a0001c402d0f07000c03142e443e0070086a05c201380009034140420f0b0b4203d4131a092031107401d03924003962441c05800340d10409a010b640602000018824442d5010080e5020300e154840c0780308800c070040c94400d0400081c1000424090904412075200d4034a006d10f521100034070810700c24025401c0d24604502a0081c550300d0803000070744118002806a0061101048807400c11072404019001003000d00c07803643c10305444040c1100060040c000503c017078424550121200841 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 446236771 1250 446235521 446235541
    0x201090204060b040e150a050415031a010602100e03070f030507051204061b0b07050f040905010e0a060501020c13050a060b0c03030f090601080601090c050d091103061e0112050a020d0803 82
    0x5c00742020305e0510f03014480807007548803100d10800741c0d2070503540806c010a249081600c506040c3d0310290a115885e25001074401c50080f40b541242c1040e421103046a540e011980100c80100b084c1c000746a208001060020701c04610424403140603003030581c105143e6444036802d215441c0198807078410009020700c28681c02c5440c2c1da0943c41d040d04410300e51841a6030740c0c000c41c40e0107410a414410f001c2200003400e15400101c030081c21600505100070b5941d5101c401e8210410745003100518108800802d45500c00510302288000041452080400c40018403008040c050301c01c40c00309031151000320b01a4040030003090300c0d401500c01903903a0f1419128040c1c210340e020780482034a4201c0801046103080000c2d619054802a103c00151030a0600c0141c1d401e215103100c41202c1410801d148050080c501040505800f0075410782c2c20a0b52905001c1025081001540d0181c11600c0014848800382680c40e0074030f9131180303084501c0094a80c00080c640701c0307030741d84c1120007843c0082002031241d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 446238021 1250 446236771 446236799
    0x11131e1505130b0621160309050d1101020408071d100f1502030910020c1201051936050c0105040b1606060e010602030406030506030f070b0a0201090204060b04 70
    0x884080c000000c0c0d0611000844075080c0c0014000003980340d0100010544d00e000840fa8003041101d0882841c1c803140c0c010158603041101c003914400314501003460380382c0c020701604081643c4100600440007003031400f51086c050040c4001100d40d804d00000c1503100003001500003418024a0310501210f42070013070300031400c006141c455400042117080000400b602d405c4c4007501c06001d10401c000c3c2140b21304034518058041440e500500c0540b90042070b40d008260301e0309908098540e494041c10821026003611415140802203800d1641100503200550744502c40b80c4a0344a11901b4000400343c0c013060b484000f006481419176211141c000b0040d08001d150026442828460304080c540200c0403860301411400c046080c608000850070070400741d0201000d0b129241040c2d6955842e520001d64070b400038003800c1c02080c98140440c00c41c0c6000203191100020740801420014100194042a80c001a109400395034981c04060016074480c0281d1014200e02d060f0251a180381201d0031032869 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 446239271 1250 446238021 446238041
    0x140a090204030206070807111011160f1203030914010510060806090606030a14040b070912020a0b1b0d02030a1d1509030718020304020a0611030711131e 67
    0x180c41000100b0058440d0740030303190b4541d08400099100c8075942030014810034289401a070206031000021904e641001c440108070300c41004540c010340d45201c3c1c108a05909000300e001c82c2849075800c22045103a6100d8a4960740301c0d143c0400d65102d10781d0740c12103038081c010122803983d4483d001c001100c21000407181c000c0c4403503d040c0b880340c06c01c1004a40c6c0d403c4080c1c449406140d0000c005904039405811403480e40c01c001007404450714041c180402d000009a50010004c0d040160000d841041e00c00c1403141150014000744440b1710b08400c0c1d1000c1d6200c410203d403a603040c020b000424050a1140b10410001a000303140d9400790503130b0080c01c2c1101920f4640c0400b070034a08240e060749824444162040154009641d92428030300001d180070000da1001c4100c282d10340502c0c60540540d00514040e40c82500c010340b109484580c1550030140c02c1881c042203901c18004140441d401ca45035041810001d0b10740da804a004040762810703542035000800d501d0800501c00c80a00959100703101d804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 446240521 1250 446239271 446239289
    0xb092d060609010f091d0616080105030304060909091b0602060603060705030c092209060e060c0403120503061c060203090717030906250f0312090206040302100e0604140a 75
    0x55810704c0f004c102d009826000b4030240075a24141e03407848010150a8544400001044030080e1922503e840b8408000c40c1c040c00010b8010400058075050001c10b9409030f40d8952107113000b0900b488018002001e0880c01540c85100c101810349041d90243d0a071400380c1029805010940340c80414075180c14400b50040341000003c2040208851a4405070b84450f00c04031031000005a81d81030866500000780d21601c1c03818580406d000030841e80d588542e00084640c415509580d0b6140700e00400ca010300d1101820b80c42080581d00f00c424880d000550380100001c101c90700c0c4050701d880743c510000d08000f04403107241e400001e01c900f020007002000020010500101103440c2003031041078a0b4010103600c140a1a80031035031043c042010141d1341d030740600c5541140703040c00391030400e140307440440c0c002a00850003072401d104556415001d000c0003560050801e03464a450760f4207000e15180043c8814040049584070722001c0e03601c1400500060608500544104540c0303010801340a419511a401c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 446241771 1250 446240521 446240539
    0x90615010f081303020106080105090a06060b0a02060601080a0e03070803090c091012060b04020a0903021f08040f1e03090501030608030306090a0209060c0703030503160503040f0b092d0606 83
    0x420b507100c1e89840c1d200c4112021064903581c54035059025000700e401c8041c55500b031a08101034003400142c00035209018072000c3c0856030340c640d4005540d1244819400058120000141007035000c2c4201d207030440d900010014000e00440030084c2143c00410782111010000400d021070400304021040c010001100e90090314140a910078443c100103101d0090b540c82040110018403655070b000c16417025000e4029540c909190200901000c40c50000328070400b640207a9030440b1500c07080540c40104280c41d43e010381c0e15191210152440403001c01c0300c07402409a8000c5480e10884039100786140f1907140c0b01c5846003082c0c00582038a4113600703e00300c5a4004c4c0208449a69402c0308940c010148100c0140d076103811038041a0917208483c0d01c0f0300035208000c00003003016401030086204100c03040d42e190318481969802c54203840181d030040c04107a040590700000c030b002c0322030076500b00c3c15043c119900051031400605101c0d03205038148215001c0d9082c040e078004001e1042640c001811210b0320a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 446243021 1250 446241771 446241797
    0x7050a0309170d0c03031a09040803010f0b0c0d1b080703120c1106130611031914060607110f1306030203070806070f08130206030c090a0b090f1e04020309061501 71
    0x1a0166200d0058105030b02c7c0e6a0070100000306260f003950100c0082c0000145151a0800402c10b03030085c820114881d040520000d66600700b4800e072003d40400b0005010000c1c103c44c811100e03081750031261144040301003800000241d48100030403440e482500d0340004086c2c1605810103c40388100c0420600505820b500c01c650804102d113a8081800702c40388000840b5810a0401488024407a04c00340a00005021605002c4a03802090f00150001880700400011010b04100e8080d500790ba048038040c0711040000b00030f10441d0126000c00361407a00d80c00c0e5654002110444d0350300381c15206554480041c41981801d0000e500503003044ad005000034100340d00010514076041481404200900303022600748051042c1c1c11031041c0d0001c210b503459080070100304101d0780c8000c10181c07007940c03101c1e00040d051503000c055541c0c04030010b1040c1c04140c2d1100c280700030500500712460500c10407015815480d5154800b8500071100600203010364680b040503442c0c003040e0500802d041c4404100300d14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 446244271 1250 446243021 446243027
    0x1503070f1203021b031009080c01050f090d0216121406160311090a050d06020720120d02030d020c07031509030f0804080307050904090b01060201050601090504150902030c07050a0309170d 82
    0x800f004480c8600040c60222800e0140c0c40303009d02a1401b505500741818044112052403610380074040e175100b522050307144511300b665501d40c011080440900201420800c148030b08080c410b0382c3d0700550306690001c2e0040100e600f011400c0304c081d0b850800c1c47c10b04480301f070750622612400d40d820f20a080d1070010840001810b8092500c10140304a104450f04020040150140c80301240d200703070304024402d40c98054500c0103c801c42d02030b020301c074422418101d40c40c00007446400203850b038010b1440c1a001203901006940444005946031190010000001c1d45104010034001e464603800034448100d80f900800e501300c445070b10403c000c4000140004644a081201d41003030780381c10b02e039584846500104024140c0c5100c00b40805140c000005802c42d019000603100d01426614070803007580b00c4040104507000307002603440c1c0c1e100c116401d00100b0515030056802840c5411f5050070058103a841c0352a05c031020101310b00040e0012820004204420000501c0042102c00b030b0164000c012001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 446245521 1250 446244271 446244283
    0xd02011a13020a210501090c080f0c0c0a15021801090312030c14160201080a090507121407080115060e030613061107030e0f04050f1503070f1203021b03 67
    0x2658590b00040419010b405041260b1501111166030320304204035200d06001002c00b480345449040c182000900c48601c565179407071240210325444009516582070310f8050b0b0700401c2c0114680c0c8101d40d54403000c00c0c0c0d40c5811081c4d9030440c207005640d0344440c80b0002003003550300c00d6442c140700507003100f880061b03c900c0b0ba40d40d0740e41c1c892a000410122070071044411075080c00804103848070000304200b002400544070480c041c000e880d401c80a48900282e502110300300400509186c00c42d0109100d00e0300410011910540554110300c3d4a0030b4142c41e80e81056500d5001400d140e64613501c810441840c00101002005a41000c40c0c0c891540300200340c03100402090841c1d01c0c128000e001e000c2009580c84003050040c1200c00e161103079594135002d4141c40601540921a282d41e5095218900e0940280d80c41043c402c000c1d00c140e901c0e030340d0320b013958110041d10883e0b150003a40c101081c2440b0259400009043c03010072442220224107001c3c0c2840703100c2d1002d03c180d500d802024050750b1000204 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 446246771 1250 446245521 446245549
    0x106030f06171605240306040e0303091c0c030c03030209041509061e1413090506150f030105042402070c0602071805070206190b030f0d02011a 63
    0x201049030020148900010020340d007028941212001c94034071032040010f680615008244048800d050300ca10070040044c5410081c26440e56642d6210703910b0000c40030142d904043c01810116005284e400014210703001150b40d84108d0303001900390328450074216248100c00041d410300411003522a00c0041460340d0a030005828075400255007d05900c955000341d4010b4180f01c2c40104440d11245160302405540c41040c5aa60800c402030f028101500741c083c040340c41e101c843c0801c1070a443c0900101c000d1507172003031103541d540e0401c40300405c0c028024684901c081949041070300d41d0074410842c42644000300d981c000d078548010040000c6000018030b08800640c0c9030b402d02c1d000390000300d001a100e440c100400c03000b081c0f0000220300390000340400c2901c0400b68400601c800d150003182c12540212074001c010f030302480c04500b112010050301d0303182307034619880030442c103146001092802d0340300452030b503c551001c0003200040381d0a10075003910700c00c240c025040c6034140398001081c4290350f500b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 446248021 1250 446246771 446246777
    0xa1b03020a0203070f0f0203070303030501081209060403020108060109120b010609060507050606090612011109090115210f020703020a02010f0201140103110d0c0f0302041109180c1e0304020a05010f05030106 91
    0x6250081c0310324130304106e0b22942e0050858400a4032803900801414081c41840414850f081a01b20010011425a1251003004e03040504092454004407a84980078208a040c00400352000c6103c440100c01c0500360b50049940000c1035151550007000401554880c0d0200f01040c4543d9002a2000c81c401d5001641152100a15214600020070401a00f500d0bc40950710340303d41481d005003100040c02c1c081808440f00402a80da40016056580c0070b002010001144000c045080c900621960002c105005800041100500380844105da110700030a4025030f121003052411580d000182845491444c40240040b2030441d04040c98082d040c0070041003030050a001c0a59611090001c60f1a103803c249041c10156072041d240303141402600003680242d0a208044581201c2d26044401d94640640001114014444145001c0c840613180540d0308608008041a4880391030149644c0d022880b0840d035a403e041c41000394100d52540010305008152140807030480e00041500d0444546003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 446249271 1250 446248021 446248043
    0x90605090604050a060518100501050c060403030c0201020d063203190501020f04150e01030606080708070918020406261803090915030609010b0306160e090a1b03020a020307 76
    0x44c0307404c0645030a030409500006581081d070109404090040d00071150008405101610303075004480c544590365091005070f008102040c0001d101b54413964044840d440014181500d081c810f0b0252216980800c218003c003540384049158441d4800c0082e0146030b02c8039a80c00c660700046511400140142103065900c4010501400029012110800250140240e03200d03184c800c402c0d00e1406240c55200040d032903a80801082d4001d00c52030b0150384036500d42d41d03160343c1c8581c4104c8084500a060400701300e1a61000513a0703008501c00113031b90350060980980c07500d0070088020030101c0741d01c90850702a04007060a540c1469026407403a08481428001d0101d407110314041c40c9035100381c1481903003158040e41040000442150200d6010038101c06561050700d4000046080e51010091182d05070401c04c003145040d5040050807500f99424100101110110400a684521704552a541030b0343c43d850140406414840311112800d03090404605061038500c000750b4074052140002c00404d902 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 446250521 1250 446249271 446249281
    0x510020433180504050a090507080c0d06050c071202250e041205120a021918060806031501080c010f0c0305030403081503030c0a3c1a13030909060509060405 69
    0x244942c400307844003401c10b11460421003001802044031030300655040c043ca8402151815021419520700d45000b07161500c406425140c5000030580a00340d01240c02c010408200060800205909c0048494018080d1702079400020b404060010309103d610744d09018041c00074124003102c103600300385c01488044000c8040f18080d60b082c0300b0303801d441c4070b900724100411804451640051510800d07604807021210b140307110136a00340103105040a42c1c880300300b2040c0900da21413100c199100c40d00404035000d09185041d680039000e402e030080c21081d006241c2d000002d581201c481c8403003030710600d019900800c040d24000d05d14003000d040141004503007800300302d81608565450190f0140241a65564070054280c1130340d4010b514011034415102040c1031003020b5035001d56002d0300b40c10060243d07803035103203107004000040b0009044801c1d144454600c01010240000c4134030401903088100a441c800e4100900340c68119449008103500b40b18083c42951902151070b90032001c20780d400b150b40d440b2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 446251771 1250 446250521 446250557
    0x3040506190306320d080d090627020913170307200a0b0c09030a020409060213030c0603061406091201090203120d05010b0f0a0f020a0510020433 64
    0x210754403001020030b100d60f0180c560042e240704050320340041c213180c403a90a010320070b00c501c6119400028007101424020070746075201c9500100440d510074000040d100c0e011034005120600200803483d542054001e10208504181041603002100020072070110b150640e00d0490a00403007000e10680c070004000304034214083c0740480c4040c5034201031040121004000683e46141a03c2d06a4507103100002040311101000120380c042140500a840000380316000d110190594070001c03103259600f0054190141101801c2d40c000d140705000811280d0b1902c5002400d0f80c229400c800581c81c0e605110700310030b0b076540003202c1e241d1506a035000c26402d60405418010106030a006c0e4160207035130754140c1c0d0f01c1440702c020403e00008800801250362226907820b0311340580301c3d030b45d18654804c21040d6076071070107180d101c001c2c4912841110104681c65075032508024100c100034030701d0390300031806000300010104c1940b51440d0040c11401e42c041030711852030400c690715070308005001200b410000001c02c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 446253021 1250 446251771 446251781
    0xc02010e0a0302060d150e13170c070e090d14042603040602031b060717070201090c14040c0201060537180506030105040c0915091107052103010308031e10080f030405061903 76
    0xc4010142c5628556a51030908102c03021101b82c037041c0598550341c000c01e80245030440d246c18801107120305140c104000c00307041e045080040040c407100150300c00c2c4034420402c010b04c0035012560145441d840380b051003008c0700c00042200c26070344d04120100a0007a42c012902c0c242d468580d1a61038142d1104c01c4180e004000c01100909905e14200010400c50510036081000c3c00c03041c1c4040000424100e03080b0b08070b0304540180759002c80d8401100d48405041000110b0075a0784490000703401482c48007840401001c0d9026460400c800220f80703602c41154414503a10042c168001e020610342651800c030506407d0152551450381c43c10344031140b6040600340c901078900b81000300503908959000030300c150009241110584581c013424000648c80c2c65610031008030203040d803821642155603c081503040203020710042c00080038030202c001d012240150140400800142d2514107084840c0d0402d403100c2c03080c0c07401b42d0081008008a4684004640354007103251001008a4120803040300646 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 446254271 1250 446253021 446253037
    0x3060607061a030c06040b03190b12150a0903050a03050702030c1e16121101051e0309070f0506090105090406030819020708010501060c02010e0a0302060d150e1317 72
    0x25180000c914081c5508002d4095840d03400c9003200e0b4138114400402885110b10702500c1e0a540040c4045800e0144c01203000303048005491380418029180000314076229440040c0380d2072940700c02000a0801d000d05130b007603040704da0348405001c40321068078042d00d244141e50501d41010b54030800500d84510902c10b4034022400102510384c051048580589022021420300c80980a4403042d0001c000b0002404011209049107050034410326460743d0540d01200000030f814414108500c02203c8105901c01c240102c2000031242c407403c0ca4202d40d89800c90b250007400c2044182e8405001d01c1d0b5030070b403d07120f54003003d190250343c40d1301041c04a030180a02d035000800c100404610844401080e401107150f02c9000d40c00c40e00303003a070341b03a0f40c0d5800e807902032103950046204185048055403203028031f05840c1c1000f50001e101c41e030341c0360302040c8168405c284040200b999a28520001c92a802c00e000040001c084041640d0400c400c007a9040301031a44c0c0180300241c070703590300d180145c01e841c16a0005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 446255521 1250 446254271 446254283
    0x30e0717070f08161e1814161b0c0b0a081602010b0102030d0906090804061e020601060903020d05010b100e0114040e010b07030215040b0103031103191202040b190806090f0c03060607 80
    0x1c1b20805850094a504c2d00c42c0403d00610b40001a0010803680c0100e552022651751b01c1500b403900c85150031044040d0704280c2d80d0000d01440800d0b2180d50034000c2600040d155620142440c0603000d0202d0704c4e40c0344522000b1641030441fa140160303400020382e10755081d00d800c001044c81d042d140000081403401c00c000d008141c00b2400103000d5811110045011140c6d010003280c11981c1c84080340c4500d0309004010104813284400d1025042218011104912480c000140c6503224000140780c000b40c0f19001c3d00140d40d04500e242c2950707010114210401c0c42605e0a0300705810490046080d903014010280d020001003040340901d4030070403244020b042e40c500c50218904140c2800c00001400340000e90110311502e01000c0380c0c0c1e0707001045904601c90824100d03000d400a03a803c5511800003114458203d40a11010504440c100000d000e40d034911a410720303195515400103003400c3e42c0100120310942c0c40c5020403082180a44c007070756200c1c403401000c507a0f0f0399030b05001039110b0240480103080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 446256771 1250 446255521 446255549
    0x240a150315060e07120506060c1b0102070609050102030d0c0c08030f0604050c0301240e12030d05090105160302070201030207080408010914010e030a030e0717070f08161e 75
    0x2444a200c04070858941c01d100d0910119442d050f06060103001075410034009404003d03001c844610a5001c00c0d00508000c3c034481c505034403074901a1a00181040d03400d0204c1e85a15840c0c151b6804001c40c10040c451401d0405e1000e18050020b9100e01907010b5050078581c4070381014004610a070420724905a01c2446103480e410040f801070840c0100b103860702d014a04e04004900c00704407110560f4103c0b4002e0000007485801049180e0700c038455041600c040c0724107290f04080d195940d076032a00003018668001c603140d41241c0c0241042d100090920380140e4034240500c0b1a84014510200c1c1d4600c00b820050f96641007840100c1c028032400c00301404400010030081b661000642203141d4260040f210002c46403048001c03a0700321140006095441d0344200030700310045000e40c000300c03907130300442c0c040d2100c0b580e031502203005400700500e6655198000714400c4c0b11078110001c11001410031a4020b01d00281003420300340d5200340502544158100e8014071000700412000403c019000012079041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 446258021 1250 446256771 446256773
    0xf1c08040606080f031801080115110717010905160501020727060906060e03070e011a040b0c010207050d170c0d1b08090d05091c0212071d09240a1503 66
    0x141301e810240950080e080c0c9459541b00300e41c4210714a505850b004640192a0040c242c41661900071910400d03e440c010403900089400309031065507518028480045030f40912450200c0c00c1c484010030039050705200081c20f00040e64002802000d5640c071280d502542da00307008101020003da11040f07010b0a0500c80003086044c1990400021140e054940f801014944810181c03198040c0c090440514168001001071842d07840311100c840407400d401c3c2d86407a07265007041e24540d020f0005a0200e0b90002888401c000c000c1108500c003110514001465460789001d00341d003428084c0c580b0340c201e2004190f081803026281c0c064800fa9240c000f1440c8942403425000e070501e901280c019809000d003000d0b0742c0a16004008480350401c0040c40000c01040d40342c04a240708626034401c0e40c2042004404c0d0101420801280300904200d8618440c0c134844109103012007100204401c1042d0041c030700d02c81000e20034085510b441d40d2a00d0007000e442e55440c85401c0241f1030540072200c8406540b10001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 446259271 1250 446258021 446258023
    0x2040e1c0203040e01060e090a020d09060612021002030a120b270106081302012309060409020c06061c02010309030509041d0717060415020d1a030f1c08040606080f 72
    0x401151388861081c0105d80c0da540707060740d01100180c151a084920003000034900803284c4c0c0185400c82400354001540640c90300c0316403c4802c0ac1d0041c3d00c0c0080c00311162015803909908041e01d03010184015442c200c001c01000300969a05620450451b840c0c0d1044055550790b2401c10cd803507a8030892055800c440c46070f1400d0382107020f20400300412880008941e50900c078240e405445901a1100079a9100064090400130581501d80d110007105006841041d0783e460010b1004101c1501d0160f2601c800c0404075042ca074015240b20b100381c64032100e10080482c0310b020700c420719409080c0007405000a04060754544200c0d18030a1744249000d0b007024240004e1001407511390800d0b411a004140c0391a203027115445003082d035120941c84140064005142209808408448504054101200c001107401a600d46030440901042005541c503007a0504000318940544140020705c0080b03244058045400020110007081081040000e410301c10300d03802200092024208032455042181070807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 446260521 1250 446259271 446259277
    0x3031e090405070807020a030c0c05040608030d0e010b0a0306091a0907031a0606030f1008030f0408011a10030902040b181009290d020a080619020708040302040e1c0203 74
    0x1a80c070503454400807038103281c842c07441680728011540041c4a41611a20b06659490400401f25581e030080d02010546444034012030f8003c28000d4000d6490b10726801d1450107642245424070140c2e131501e10507c0c000d0740e0343d11809044039040540003520750014206940850b100c80f4038410084401414002010b000042202c1200d00070156800d0040b0780000700748407a04103541007a440030061001c41d0041070b400f480b150300800c048241d20411680c0d080f440e030035600204c0c40300c10060301c00b180070004e0800c00c2c02400d8000c07040000c0000341c0f1f07460340000b0380d00c1032140c19608101a50303064400d0454a956001c088126801001d500c00415002c03820403860100312181c038603403030803c040091101518000c00c01c001002a002c01d00d04040d201c5860760101c000c0364032943c4404904911405130715211001e0002d021504041c1c06240b9000d109848000780c44400855a0345c4104075241c0403407016002d40f01a80d60444001c10200c0d0b01e110018913100c184c400403d03428081c96141c0d44055000001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 446261771 1250 446260521 446260537
    0x12190303020d140f1b030105060a110a0f03020604031407050717030904090b0a0c0503070c0f111e01020c0d03020c280f1d0603060f09070b0f03010f0f060f050903031e 73
    0x48145c140c2004880710301e00303000a100315500410284202c50201d4040c0308609070298003103040b100d1240e02922840072900000c3e9003030307015820042c00d01042c1075010503810b16520200402510f04551030f030b9055501c2e0524801e180c0111404a01205401c00910407545100710081c0280400701aa00f012426850152008c080b5680f5002400172124001d4007036a10031a05034550309040942c0b500d4080c1043c00541049841002240c4100156a02c0c42300c201d030911001c08441d00b0081c20341c80064900105c1055491040741030172581e600195002801801c1e0480036245282c07070700c00d078181580b000081500c41c8459004070620110b060107aa142520803149441c040700020105601e115188150540c1c02d10b8044e0010f00006170b1008590101c907400c91a9142100d07000d550b10714039006c0ca0341011441c001101c00c004010000b48504401c400042c0003105280c2d0902440d02d00d026140204401c90001072150104101020790360034800c0e103c0c00300c0d00900071100c00000c201000883d80c04440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 446263021 1250 446261771 446261791
    0xd020c07050a061218060c031a09061318120507060b240304030212031815070206061201060f030606030b1f0b131703070212190303020d140f 62
    0x4002030300d40b501c0781c20302c02150040c0e03c0c1c22007001084100540505041020911012610005040000d20300e200c0c407440516140c2d8000780c00b50030644c8000451041c4111144201189020720050340da442c0100f50b1101040710740050805051030300000c50314450712000d4140f095070480d041c5466000001410700c280300e160100035128031117042100800c2c901c2c2500200920760141d201e20116a40019600a40a401180d001c071040c2c1002040035401214401c107941310800d042d21503040208040d48443e00102840421440c6c100002950b8000c01498a03100e0006241ca00f11101030079400034020b0049102c00074a01d03501da0900c040503003003620086500c035465000154080c418100c00031088900c49000f20301540c900241c100140d0016410000350740702001c0300151382a40d540c9482856034241c0051603e0340310b2030041141c20f095900001903160030688046a407056401c0f00341c00c40071f50604006844403c1c0c990031400400b003190388030300c9440a08091206c810600802c0c01e1050b60210 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 446264271 1250 446263021 446263033
    0x703060921090b0a02160f0f0b07020603130c0308030f190207050604080a21050a0e030406021203040c090513020307080a020f0636011706030a0f05030904020d020c 72
    0x1481d00c210341444071124000041100d1400e014075103110b4010681c404451045905103c103080c90343e8141141a0300c848000e401c400c100308403400d1003403141402401050f41031400c1c030703103181c01048082c400108190301c0d502111264404120302030440002564105a005480c0d14104c0e80061440d04103071200080300c4000c0d198040700b80c8850007140d034003c6e80240070f03040c06e40740d41d900d8007030603000002c004051008410203031152096101004071081601c1401281e2800c01c0000030084030a00305a560f000d800400083c01841d80000e0a80c0c05c1d00d003c0705030030340e481d900d07418262891900c48d003145c0d86031030030441449050108044440d007150b008030f0a070389103269030701006551080f004400035040110720409000d5403401c1c2c8050802c4a408401c0701c4103800745480c3d07130b40c1584c448920b25400843d100b1280125542c0c012030034200d5a111036801e1090381004800680e42e903d0104008100c0540e0100f00020888140141c0314100005041951101c410691820294202c404038000502c030340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 446265521 1250 446264271 446264303
    0x70201061a070b060a03021003050a0e030703032f18210c10051309050405070e010e220b061c1b0512030406080402130905061005030f0a030f05071407030609 69
    0x1440701e05c0704490f030080429a055001031019005000000c1003070000903942d40440350700c00003d100400100c0e100e550000740700b0b600c0d00c401214485140303d1081c910000314103501308400c036407012038824035480d029002c03444045400007040e09040b142c040c07244144d244038200c0d845800080c507000380c2c44200d94084a00ba070b00141241d00d030069040903141c004581c942001020b010380d10aa810a00610540c1d00c03994036980868a9a2000c1c0c4c82806100e10764010080918400500b10000e0440c0700082845010301e525280c41040e40901120322460500d844a03098503001900d10340c81c81c1e88401d848550491681401c9401c21491082c14000d04048214940c01c04020086609039015034585011320f0701e4039000c0c010510707005048410300642c2d800035100420b00810280384154160b00151001c00d05000a160030203a001444442c5c0340c2c01041500d0009070030a28418040484d480d2540c1c90740c1080c00c0100304420300111400060207041d00c0030003032055a4100201c050b0140b040e40c082c0e0094 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 446266771 1250 446265521 446265529
    0x1608070c0e01032105030a0e0717030c0f010b0d11012601140111061302030a06020301090614040510031118040f05011404080423031c020f07050d0209070201061a070b06 74
    0xa00001310009401000040c0075155207a000030603500c800007c650089444e008074600441f030030104001d0f41c1c0e101140e05120014200420080c200380b80d4000d20014000300003003003c40308284001040c08622480046299100d64008a50a41c40511107040e284c0c1501c03011140307045c00c3c01223001e100c001c41e45d0402d865028010001c901080c01c0010442e940d5184038200d400105004101d03894050855004007040b00350000d54041d0080312000103039545040d101c1c1e84a0804045000d01a40c205400c01884030750022107130040b80d41281c0300d03505400e41c101c00034402c503090483e104d20200380081440705200c4403940307403802c0900c244001c010342c2d2015085c1d820403140c11a002040703607404000c2845040001220744502d0602002c0c84140144840000784c18066201c0320041903510f0308916000483d410040500120000b402901c6040d040c00040b0b000d403108000c002e40241d41040215100764403d50010b8001c06841d00480c0395080c01c1201801d8603070201400f0307200c1a2214011030f6281c03030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 446268021 1250 446266771 446266823
    0x1501081902090c09010c0b0901060e0703060308090f04061707050901290c0705040c110106061d2101050c0c070803180904061407020708060a020c031608070c0e0103 72
    0x207001486502d441d9110000b43c10303160711a200040c1084240c1c100000018400c800040c040c03607480c1c4c004038425040102c06103081e000140300c1410542810707420400b090005044401d401030554616240e100c054001c100580f049034042c5410412400e1100e40c003000108010040e030f00111a41450389c0d0340c0d500141d8041100221400141d40d0302d9a0046400c514030300209400c1501c0801da4001d40e030b071000083c04071100300c480400454060400e030007003c2c80038403400e0041e02141c00d24070003100380d807842001c403100603817100390040c800c503681102d0400900240902e0120440004c1c400f034684004071054941003810b915100b423295480210b01290b003c0191980c3c000c1c980e100e600e604000c0300400840d41c0003d4016540960703190703401810640031074411480307015079030002c01d12585461402c610303110000b08024505407051180b032040d00d6011049810204160b15420614602410510460f00c41c1e844001d00300f130300c0d03040300003101e00c48112880e040b2400391010780d90f03180c4081c5035040100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 446269271 1250 446268021 446268023
    0x50307050a120c121202161413020c010507021f050c090906060d0f0e0c04410a06050909030918090a0f0f02030c0604062f15010819 58
    0x400103071000e0008158032244180d6550007000840342d0195100300000100802080554180c200848403a180540410600d00c0d0382c103808500c1c840451920701e200e8001103800e030b40c40d445484131100c1550780b00f007150140d40005a0301e0713008100301d08100317901a5803624848551040c3c074a601c070101064410502c150342c0700e6072401c80800d1600d0040f804000c61110b008200c203611413010b2202d0358510b4102c0c0724114102103050000503640313075998803052425803198681e9101d203050200411103030010820044d090342001283d01038044002109480d1800010425904650104100443c580d03181c1c101030102c84054494180741e07291102c1c034a0300c0b4411464902d03040900103a101c0700c4d0344058030710b465224081c00280d0b00040c2c040d6681d8218100108070640e0303c0108200c12109620301030140650084044801c646042c0c94010081d129070484810460140d1100d07901003010120900c10800e124031000c15103c140051000b1440c3c0c0800030300032a00d85115080c2c09441040000840718442 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 446270521 1250 446269271 446269279
    0x806060403150908071401060e01141c0201032a18080d12020c01240504020306030d110c0907110d0f0c0b1308120406180f030f210b040605030705 64
    0xc0b000501e8840280030514400c40d5a00010011600072410305001440d65100b1038002142e090b1509803070310031071001038001c00820901340901e0050350f5204400007948030303100d02c0002c0a0700c21600068005103d0748400108103401c410710589a020001c2c607041000040c0e4541d83c0840b004001c4035461600c0c2400b03240d40641c40b00c41d04020701800f9907035043c3c141c18a40c601521f04404503001e142944d22411000036120620b8000e54498510340c00140c01600042d101181075240403000a552141851709140901c0b0310070455a5942c2000c0c0030403c030100001e0143c1025061010005100d004a1301c0001c516001d0308980c2260320b8402c0201c0e1a600d5000d980307582030710015840d01c107051080905025500c1140300b10a50010705c151015200e4040800c00b62401450a400c000b01500c06094158420502a491013070000302c00c50042098250076107461110f0542e07140c0c2c10303554450940e0120f01c59032510308000c40300031090f401c030204121081c0d8003400015a41d20034903549152030300405500c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 446271771 1250 446270521 446270543
    0xc020108060406090f0e1e06012105010518061513020a03390f08010b07020d050f011a06070209041e06090c050f061e160c0e070806060403 61
    0x5503108580803034118100800014030700780e0b14a8454101d906a001900ea00c4e929224a0b84d01c19200340301103128052030002c8030411000b5995080e4a4074014001d0203404410600318240c84002c01c0109a0041d0780180208007a0030103054684c0901090701c0c0c0e02080c2c1c803034840003e04c10981d41e2240c203072a400117009188412209026040a5001550a44101551281010030000c40340b090b80701400107060750b000c15915031a207203402c1c000d03040040c20140100243c0c420142075100707442c0307070441d0300c401340058582c03242e440050707400c080104010341284a9200314411901c8103600000180200c0404140484c0035142441840c2c0079441020703622038800300001c1c000c9a01441030100c0c1c4408041501c00321643c0e9900d000440b03030310000a890340d680440081c0146e0600001400031944c0454400b400c086044003441c0342d101d520108050342150108113490074a4400140301100c1e40c0c03280c000303013601d40c031040720701040d5208881c01800a1510808146103041c42c80c11541aa0f03044034000795 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 446273021 1250 446271771 446271773
    0x2030a030e1305010e01091118040c030204050d03120b0307050d0618081b060a18060e190602131e1703040e0c2805040501120b09070f03050c0405010c 66
    0x501d48099145494000c03080c49207101c0d200e1154800c00703000c2c0c10605c07200d20701c40d410300042d0f0044401038502170301c084a08001c02403554109003031407903d092089401003030301d814001084003e405160700054000104401460801d41c00210388450803c0d04181045912517220405540d4110b1703106890700a04010b844401003003154020107460400c8101170000c0169036551000e550384a521251920700401c941010460303401e0150b41d4014080301c0045c0310681c410305d5100008000000000c2813240c2d6000d01200002040c44035150340c001c091030144a441c0117007000d4000c0d40c007480083c00c940941040220b210864110241e0010030036000c0710400031304000c2040310340e80500800511600c0305100000300c04400030b00e501c0c424410540f83d241c0b1a8400c610072103140303185403103070010f01d11068503941c94147c1c0300e410b98003200d009181a01440601c211010002d091400146410540d41001c210829402c07100d0052840307110f40c0c0402c4140e0340c41c105c440240c0141d015090000300e0301c201d040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 446274271 1250 446273021 446273027
    0x60b0a120209090903030a0b010c11010809010b0a0906030b060d0305041811210f0c0a0f0c05030705030a090b070b0a230103031e02070807060c05070b03090c040605040902030a03 78
    0x318006241200146030046440008100610480e1071102d164000810004010b4841c003801e00204400c0c20304400e961240c0d078078600c100a842c2015810012403c0029140d41e0094008442e07201c0c0c042d000450f1180c5411103e0054042c5010541c0c8500726180030651608019904000c0503406599490510b42440d030442d141c22450103029240e02e40b99540251800e8442e000bc0c20b04585141c089034211149540803041440c00500c03100d80200710f80c040000c1ea0402c402101c580341940e1601c03480e240710200058074144507280c805004c40c803020400300d0030040000010405001d160b262070400990355441003000b44241c0c1d0006180b40c0030300000c901d4641e2107401020961010003400603419603569914060020264415000504244604285444440101140c0704134a2014004540c1044140341d40e031030380b600c61034040000341200e40d07091003428016080034110941a00d5540e06010841c1a5201004480c0f148281c0c901a80040c045c0b4041c8030b0130940329405401741c114619107440079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 446275521 1250 446274271 446274287
    0x6050103050705030d090f51020a0f0305090a0806010308030403020c10090603050a110706090c15020303041101051603030605091305060f071e02030c010b01030b0d0807080d1a010f03060b0a 83
    0x1a0400232102e40c100c400a14030141d0300d448250740320031110140d407088407400388020001c4d0803002550081c08203030300840c0c86c1158421020f601818001d42d2603801c140407500c0b0501551001c0901d003d0f24001000700000c032802103000d64002d40c01c4a20190101007081003010a00007940d012540e020000c1020601036005143e100d0895040007034621080082d440e0355601c400c4084407081d9540656100f04844406841e0141c000000550109128107034065030300c0c407003e040600341c05044100102540c0c81102142e40641c44d192030300c03035000c149140c09405071003103000e5030b07201d4ae06680c002071106800c0800501c00f02d8010004040700d8546180c0c0b0201c8001c098240f200700010704022406403010001c20786010310842c1c1c000e540c0c800440c8041402c4503107290440b4101070a002c1c07210b91503a600010f41061940040c102c503130f02c0f00980780181d85481039060301100d02d0305100c0203d64010810b022038100b1032003038070340040c44420881c088040702d0084c0192a980031003445030180a40c03103400d007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 446276771 1250 446275521 446275559
    0x3160813060e0931060b030f0d0e0906040902150a02060124030c1101111305060301050906130b031005010303020c09040c120602090303070b0103020a151407080706050103050705030d090f 82
    0x51351250318402e50b801c2d007608840d54080d90300949507007500990341010800ea00d01d05504034040c00c5501d40ca460003d0011015250030303841440c5e403e0104603580c1d1907a22005040340e005114650b0f5032006515440349400c0105084054010200009041c918484554145c800a980014040200c016090b030040003520740ca8410400a00e03130210101c074003445481c0800744d0000c07172143c6408803070440500000b039540001c1e000d410188010841c03038468601c41500110203d40e030001c28984005444000d0041400c0c036035041c0f00b0080032501c1541e03254000c40c10b90340a0342c01d440c400c1c1038850601030325110548004256220b43c40301001240451000d900d0000d03c2400003503e015034900010740741d50001c0d00e0a40704400708600400440ca0510841402000700f43ca89400b640c0500c0e40280000061001d16107034140300040e190108010002101c0055a2041007005296101d00b425591468140105802441105000c1d4002e5010b0030603201101c00c1d4204851b0454100810380600001d0720308 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 446278021 1250 446276771 446276821
    0x1a15180d1103060403030e07050109050303090108091002120a05280c020c030a0b011707060c02100905030d020a112b02040615050a030c09050f040504020303160813060e09 75
    0x60241ca96052010720700442c040d56003c503003100307102505410000aa0700241c188442c070401004103440100990f40b1b5000c1c24208160706d66501a80d090400b03142c0c0c4c8582a1952000901e000d0300381c401c41400b80150700643c4200000d41d209103000b0300c0640e9060a03d80d44055000b405440258543c109072130040b02d900c1030b00c550703107602c0003c2807901c61103440458848603002e005200d010f2002981d000c01400100003014650324007000500b0064004cd0041d008034600d01070208068040c98013800140f10142c11078041d1910040e00070745400d11104205c41c15521802e111141d4600301c0c4608544948001148100e80402d0502c01482201c0c420103e0300107484100008034440601e956070060300c03041d2680ca40d60445460010121441140a0b1040c000311140510050302c0340e0a2101c0c25602c26038000440d5125030001034918000d0f076102c6105002d0b2250140e003001210409030040d03440300c3c0308000e4a5a1110340a44881001501254016a0a10004450f2010401c1088641a07d01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 446279271 1250 446278021 446278043
    0x40b030709090809191a031f030602120a0e030901030e0109080a020d090e0c0f070611030a0204050901090501080a0f0303020409051608071713050106091a15180d 71
    0x8074803141510b10807542035510100c08a0000766078105402c00109a02e080301090100d076003030015000b0f020803000250032142030044001050310105680888411403030300d000c20b0a4540d6858005d01a50045031000c0100f000d03c00030132100002401006402c41b0503001450402042d500114002d0003809450850b549d214610710000c1408800103044040d003a5002d00a034011161300680094070540c0070804009401003000342200d0845c00780c070804a00d42c1001c0740d6806640c106840501003180f1018120b035800402d2103000038980d4024004c4030415201d646044e0380c0c0d04101d104a50003403007122540e0f04120f40540000301e003500c070755214900c80c0c10b0040c1403540b6100c94000b118411200d01d07015490840030307400ca407500300c20306c15400806403030486a030541220380c0350b0791a10043c00410b000d01e1500c0050301040000e400a4000d130050110421800c5041210900501032210300b0350b000d064a809481c41400e41c000850700403150124141d10011400803d1080c0d0f441c4240043e16400c444c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 446280521 1250 446279271 446279279
    0xd0c0e3709060306021914071e02100206090708190204020702011704031709210d021b0303061801030b06010507140f0604150b0a09020a0905100512070801060e040b0307 74
    0x34402d00c0b01071801030400603194042c9880440c40d607015140000c043c0203203020100200c584180450310030591100c0b9020b0035980d81102c5d00015030f011940294442c06140460401641c0007507000c0c414a070030800c0300d012981da040e000d900e401c0315940c40f0344078402c01d58445000d400d140d0010240c451061400301760307802d245580c18a04840a0380c0c01c40c0002c034501040c0c440341841850350341e004050354001c1d149481c440c40540740c03040e8031041c04426148000c50110542c0586a05541c9800c1d00903000c1c0745082c4031040c0d1300d0f44079441280e815228600c0110240c00c001c0366180100d06a0b640320704c8950007519203038015542e68000000843d01159040c0800388074503414408410894105802403800e820a490710f03d8040e181e8900340e02185103004001d00c1e407030360344080300c0040b111442401a590441d102e011070321594207402498108401e9510780444a43c4400204092468403030070716040c1d19102d8040740c1003c420b200b0b240020b4003810741c0c003066261540c000154201c0080c1261070495407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 446281771 1250 446280521 446280539
    0x10b1507030c0b0619060309060c08090303161404090e240f09071220030f25030b0c070308070806130e070e0711060c07050303130c08030d0c0e37 64
    0x305e13400200002e45c580c40c1340c0c41000418082c40c00c00c0340c01410120851f14012501c2e6036a400010f08001240741c9070740841c5040c0f406040c0318403841c81040d080591f2142c49410840c00380946902041040c411550800000000b40c4803601140300909205c00c2c0c15143c0c0c1300038003007000001d4686c4040f80101100020044080c180345400329119034030402c1440440403035000441030700c0d0000341c044d1300944000c0c1c0c2c5010011035140f05003101c04412901c0d244d00451003080d00c4030503400c0185000f21003428000c0001001d0060f1480c1842561440030700d94680ca401c540c43c0d041919201c2c0c1040416080018603c01030b0071017a0011880300031148095900c8440c407624203002d031050780124603403880140140605000e6542e0044c82c0c038510302e2800303203140d50f507903600c1c84010300140e2043c03c5034041c40104005142070500908060080301c0c5c4480c00441d00c0c0c80289598001c180c0424002d014083c910701713025400e0f0318064049400080030580200082c410010050700641e10318000d81c401244004e8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 446283021 1250 446281771 446281819
    0x80301260a0309050f0d030509040903050c070902030f100e04021302070b07120e15010611070b0c06060f04091713050d0807020319110d080417010b1507030c0b06 71
    0x2c000d95480440c1850a0103002c2103643d02d11302c407030007030000d600020080b03a000012110981001da400040841c01c40c181110b60313019201c1050694000c541002410f42c0c2203401850081525201c0d010315602c0c0d0141700010386045124203404106c1c40310000d4094582221540c0140405800251411009d55290901b0050444503072020544410b10450580828400c116544408038000d000140004102903a003100c148034060402c942c05422002556052003108020b00f100c1080070f0300c0741d056421032034594a0880c0c925010b10050070308980b4618060081c1041c3d5908036801100c00a2520302002d0385a10070a007002e02040400fa0000c0c10351103150010014078081c0e40900e40340c0f0024410141800805000f8115070070003482001c0214101e10f55150380c6082c1140d03040361244c02850315640a0007550300c080364034081010b0031240c807481074010f910003d00464001c2c1d07000840312061003141c000e05102500040c0c0100d40c0c0c0001800510207607400c0780c0d0017041d540e250b000840d404003004c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 446284271 1250 446283021 446283023
    0x20409050d080c04080304090e0f0604050d1d1008150d050a140102090307140301060513050f070f0f080612062d044209020a080a080301260a 62
    0x2501c040e44001c8070540c080c007455041140c03203525510b000c0c0b8000710f095485c007031703070103040c1361130ba55881c2e041b5600300204465403262802905803030300d40c42d0504100d9102d030114288000800c000e4101e01506100840009002c03400051030890110f0114400711a0804020200e10b03280c010003440c48078982e21411a08030840c0f084d030040c4001141450f120074419060000c0f14040da005010b42e82480d5008103414007900d0304000c4030403010051000003030251003140d101d980c01080c0c8448010400c0350341d800203841841d00c04050fa6140e00c41540c102c0710100110052000111603200000c0b0051180a4054005100524003842c08482010103405e1650644054aa107000800d200b82c04510026076188814070041e201d0030181390031b45518101550003242c0c3c51300c00143c41e00c800c40070840d4055030014a4484a40c0c0001e9425112030000144620300c0c05038030401c0000c000290083c0e0009500d004030354400710050a5904e45000ea640202610709459071000085140391401401000030503581 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 446285521 1250 446284271 446284273
    0x9060e01021c1406010804020603131707050d11030d090f0203030a02010903200d03050a0e0105010612060902070f1b030807081b0307240b0402130608010f12031b02040905 75
    0x49800c44901e04200c401e8100c0c503500c9a00c610701040140d0380c0080940c4e607c550140c650b260b0b243d07200184086030b001c0d40726009010000e1610003100e0801c45102a1000612030021100c80e1004240c0c10303503181d50315065105195204210152025007145c0080d104d0503c00c0a22500c042025400603040d038100601d1440140c2d501c640301418035600a19001c20307070701482c6c03810304580c5021081988504650b039880c1c003419101d00125108620350340c04420112298002007096513112180240806101140013881c01c0c00d1a40c00b06941110f40300300d03030031554002400c00e01034449070366072901c10104012100c00801c20220000119014800030b165852064215566a80800e00340500482070403142d01da540d482800000000340a05211880e81c0c07403000005260482040c2404010f400b01c0c1c1011f0f41c0080c008039103030b100c02d19040301c4441598031b00d0700e4009890380c07140c0480d1440c2405101e446255050194618003090294084002458411003005012101500450705454200b401203c503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 446286771 1250 446285521 446285557
    0x1090b100605040608180d1e030e0c040c09030203060a0b0316050f01080603071d01180e0a03050306060706020f030906010e060109050f03070e0103150506060f0d09060e0102 76
    0x42008604446500c1200c1291030300685040040007800d0b40220300600b024004034101003900800b0701401060134040c104202c81c0900346044005102e1005480710b50041c10680c000500464042c1c01807040c2c0880150040034080d0401c0c0c10880905288500754040c0103950802002607101403204511402c01410b010030860848010b05140c121301e640401e90080600320148a1655070705001072818800f4600221b04d03483c0d02d8002410503080e90301503c05212280246000700d0a1400e955040701c00b03c01c2d6680200584001010940789038401c1c3e00b80c282c100d42d11030000203001e00e006d103402c8140074004504105156950100326400005010204d4401104101810f0020010f0a0160082c000d21603202d00302100080c050035440c1c05058030032001090303840c189403000c0019200a2250050a40a55940b4100000241c281d0024401c50a09120014515050100403601b06840c510080e43ca04100300d8031800041460031002c0b1107168a8010f032400d0f41c0300900203000d8154884a12500c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 446288021 1250 446286771 446286773
    0x1a090d090e040b040b0411090711060f011d04030909021c0f270201030b030604060b030712020d033e07170304060e03100203010f0510050304211704050109 68
    0x4110019980001d0040c80d850341040000380300d1400d550303040742e401031502c000c584562500d0700343c401068034040c5e0420344a50400511a0f4001c810b500c0e02181302043d0344580d01daa11030103060f80c00c01d01503100340c000022080ca2440c0003548210303038440e00905d048150300d9110101601a60701c03d6002d42d40d410400360400032511060320410303113510740f411801c000c035103d9190411103c4228040006507c0c0c41c0034084420740e4040d400c055111030005042c0c48441c94145072602c002c0c440714043c540207208071800400c000e560180e100000780e40080079404035145035038045440e040c45600924030754411030725a0940a03810310f072030740b00313901c0c01c810690382031400c43c403c64503106850b440041050041c000a01d0440c802004441c1a80c04070710b44404c080901c2030201e07143c091451481c0b0040d600c000000215842c041c2402030035107404403045861140c6150080740d6500058502601c3c84c03507013401002d2540b119400e07248441803542000c0d2100400d100c0079101c0500704540039a2247d4581d481c0034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 446289271 1250 446288021 446288027
    0x3130602100609021c020a0e211e1c03181a0603010618110403020d06020a02012313050709091b0f031505070504030209090a111c020105071a090d 64
    0x44003502e03103001d0031801d045c480c003c0714607051600d01c02d104104c2e500196650505105884c03051014070090020142c460000540e0189044040781568050040b03084a1700351403200c144500c8151a100008e014007481064890255100480304509040d82c402071000c1d03c2c01c2d850310021200d4004d030308031090a401a106912541c0740104900c1c4203034500701d8240101e40084d40e1500c066a9030080c0060000c0c400c204040c0c135417180b80c00107076103c01c41801d401e04000140d0000d08900415600034404105681d016412152028003039101130f03400140058280a082294241c0240c007420444928641d2900100101e80c0000350541e0650504100c090320304c040c00080d14014030400e05079502e2030b451350700c806217040c5118031000e00321a110004941020b2041c815034004d1500204518451700b001d68038123545a04440c0100c44002c4a042c1c181c4503440c028401c01d0110650418130307611081d0380da004481952209a04407040960b40008400382c0a1140e4000d1007560713220000d01c80d499800c8409 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 446290521 1250 446289271 446289281
    0x14040602030402010e01182916140d080c0307030609020c0a0201030e06010602031912060e0103060c0801050f0103020903100501090e060c041404020a020a05060c1b0a0503120402030313060210 84
    0x840c1400022101f000b500100c04131124101c031000400c04c0102d1b464034400442d614100070910002c1400400c0c0e020103456810041802e0510031840400d540003950740190311001c618085101042c0c85e0000aa20b1501c3e4034020b55211003140360001e0101c0e1140c444904980050594110356805000340c01304550301485104000341e00c1d4802407205600d4074400a580703100d41041141e030131006030b402412590240d515a0f0110044450030b0040039158140f9012600091000b91482410032242131102ca0107031900b00c0c1659000341c403038480e1880382801036020303610a00d20160140318043c0072480300c80d6944111800fa202c3e60b40007148a5610f08081da144c41400740c0104200c1401300410031900000c1050750003600b405480240e29142481d600b6800e14004d4a0007400e03d00030502040070802c41103004100000440720361413180a007a0100c2c99580c1c0205100034603a034420410002001c543e0001281e00502c002e0480f443d101008060a00c28480396101d0b03000f44e8081c1261511080c140d00030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 446291771 1250 446290521 446290547
    0x32403011a27040f020d050724030c020c01080702190b0a0501050105030c04140607020301020c0d0f030c020601180603020a0609050301050f0424230105120109050a0303050a1404060203040201 84
    0x55610401255801441002c0c00060038138407408109002c5442d4600070115550f08101518612956010301580c1c600d4190b1600c0117401c40006000e1146000f0320070140420040d03801046038620480040d52004005030001080d8451511661050040c1e00110604684a41c95826a90614003142800c0d00c00c1038100703505002c010b004001500910009480c210355484981d50b040e0140040490104d20503407802940550001074241c104603400160101042c00b00e645d000b815580e031b408110100d41c01c010350341c801600300c0001008a100e0340201d4016610050600080c280e0307403680000c1031181140d01807004140d104200b0049841c081c07007202e90090b0341000e14110303460566614100f1119020714540f180c0000000d45c0d1468441d40c2c40600760b18a00318003110609180d0701203c00c404000d114891140c841c080e0712414491060088802d60366020f401003406201541d01640030302070041c41262440c0c6d40e11150f0041742001c00c0042d0103680034000c0140e0300e0402d0b0000402d00c5c5030b6004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 446293021 1250 446291771 446291809
    0x305101206061508040807170f0a231e030603071508091203011202091801050106660c0306150302010e0120060106050a0f020d05032403011a 62
    0x1708408110000103c90500c1e901c0444c0682200c081d452140700d90042601c4ca40000074040ba4408065800c4405811072480c0100301c4d50341010b5000d6149010f22501c151100040403140c000f0001c1c1c0c0d036100c059a00440c0090030790b0004d039100d01c3c045d041c0c4030490111000081d00d690500c2000d04080c0038040000d0f00340c801c143d2856040c100c11141204035000000d00403d8070030000f40c038800f81140b03c021400c00a2000b4415075958a0000304982100f00b0103000104070a010200c5400e0401c003101c19080900c650960b03980041c210349001e00004003500a0880c2c81d581905804806450350481c60900c2050000c4240d0f045041090840d03c901e61154905d00e851041480947c0c0c01034186040da00c001d10708260000d8a0708403450320740d0002489000719104120012846540200250880380303910390380c40700b04a020340400ca90311824070b8000001309004001141c0f44000c0c00c491000c50010b03c002c6864605003070804242199851820038482e406a005440b81c58648009040352000e1164 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 446294271 1250 446293021 446293037
    0x32316020c010203071103010b090a05161815120c0504140d020a05090709170601080c06070c1208070b09062e0519030b040f0203160b07020103051012060615 69
    0x20300041e6032032103640c0021b010404402c025040325907007508481840e83c0060328101d114102100c0c000054607041c1c1d145052401071048070707a841403280d285403400900c0c600204072800d140081c0c0b403a04000d0f1001c22001c00181005000b4428072034010500d6180159555959451a04000c0c82c60780303000505007885021282d800c0c80160341c842e1410f4042d281c1c2100c00c40c41e55282c4000035102010315900c407034004000032001d1030650340c002c14400d040341c0c1800191f034509401030382008107a2140c0725000703082441c61501130105940240300080b603244079019591820f403da44851b041401c0895020081e940902e0400c0000c0c02109441c00c0d05001c00099800102c07100d081007070a0100b240282405810600c0e804210800f20940101c01543c2248aa00301400c00c0c5c10014210344003803a040c0d01911491644680381145800074000300c603040d92107181420240d50046000d0103019040c4482004122008a1250b0000d940d6054140c030801c800200503140403070400101c0e201c1506003003405034807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 446295521 1250 446294271 446294293
    0x507030f030b03010b03010608010203040605010501080c0a030c051c0e100e03040603050402033c0601030809010c0303090c0803090108010e0609010b0703020307050d1d1e0d020103231602 82
    0x10050a100d04145424046849410b80020900400d082c5a040754590f00305038001410384019401540110b009a405000e240e03201c0c8015a2440b80c203076402d9068150400540301d580740b0030380c0925200e00c1e562402c1890301000130b8814200e40d88100b01c2c0b00049554100351000d6032000c0090442000b007046081c40351606503081c16440340254030620040c1910380001800b151b5081c01003401c00d8211030028490202c0b4584c9248100850070901351600d80350902e0613540c01c90004100d4107e0313a00800b694a843c0c000d1004595410030400100d041c95101e0300c81c0c80008885251080c00b42401e500250788460304d9000040c4080810b901100b0407180401c1030100645640c08090305403040c40300d45a6a485440c0740803491880368840184c460702412816507082d0340c0c03000c0f043c41c038413512031380d0320f82c50031052000c02007003009d0000c0d00c0328140061280640715007031514188510a00504000031140b082010404043c0014004110743e85103910401c800c038100001100c0340ca4100c0c1c4010050a964 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 446296771 1250 446295521 446295527
    0xb070c0608180c12030c0a030801060f031a040b040e0717120304020d03111006151e020c300609061e062101090f0201030e0a031407060b12071401050703 67
    0x1503d1849402000c2012036800c80420800c1207450b046040d50407104000d0f1941801002c0315000e00403180090002603100103582c0c07007401012240420341c5000385c41e112007102000005c00d2182e84294000352540c054014420040c171924009004204140107840302c203e40d60350502440924204502c4024401d000c00b603220084004031a03a03050600c502c01d0581c0c034014034a03100e09803a16901c150304250002c50b00d150382c100600320303100c169183e00e8404004a0361030083c81480e01240f40050b40950000c808034901209204000609148054107070140f03d01107125140c089004421039a100d00d09104511408103c00780d80090250b0b226101e40001c41d451501148005d0300a40c4a0301c4c1c0c000c0c2000700d49000600078012420804004c00c01ca040354602044c1c4003a140d1001e0780828a40345c07182c600d6010124010350440d9041ea151030181407280b21360b09d01500a602c09990150761030020340d0340c0380c650902110080705c0c2c1d2402040c02ca0319014602c1140d000c0002c5c1c40d410400b0505c26000001d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 446298021 1250 446296771 446296783
    0x40f09050601151b03090e0f0c09040b061b1b0904020d201023180607060b1801031104020a0507021011120d05180a03080903040b070c060818 62
    0x50050010510b8203e0311000c84800c68480c0080c12412009a8050b04040d00886842e0446600d4032610f2001da807480720007007044900b01d4116904040410107166246002c0c2e1080e0f00350200240400d060402c01d8520524680c00c070855807660347d10500307002d404600a4200148502001c039540b40c01807805501107000283c110f10011b1281a0140c164500e02045000c00c62605c00c0c046c20705444691042c200074000070300c1c4e0300040d080da8070380400c0341d241c42040d2045076090404038503211555142c40061040380c1e4010700c02a2002980c4000144e2542d44000781040e5414102400003115415420526081440148024441c510400040c0c0c1159006001c1c2c505c100c4d011a51555001d140960503584841ca4680156450159541408200d95000013400c20318003412002c005c0d66644c040128040c10700b02e001050030b03034050072504000911a096007580306100206503401d09940d0a4201c0030b0b600301d050122070381c11500b0400e01107140c1c4141c456612001c52076541002c45645100700d80c941c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 446299271 1250 446298021 446298029
    0x2a061b0e10091a04080111070b0603060f190603060608030712020309030607121407030c0e0d0203031605120a050d0e150c090f13021207080f0c1e0a0806040f09050601 73
    0xd4411a092031050625409a0313005200840c02030001c407210001c5848154020a0116864614038000c146a4100058440d1180348403812901c420f4807040c07001c44400315222000308100b510b42c040070002411900400005042101c001e60721001203142a020341e0000d41030b000e08550040c0010606540d00103800b0f60024910f061000b80c07450407400c10f82c068002c1c40c400d0074140a07101d05102c58182d041d444185c0101c15540c507030410801e10310410000d08654040a581039005021501d024070303040c40e21001480c480d008031105001540342584094120000840c08031f40e000c540c203001401c043c00b5070811040e5a401600c0c08030b800200184902034081c200241060340480c003140e00341c640701c40d4940340316001855410990090200203010f5880700d10710f8003040e00240d0104a10b2802207207110301490f01c000030042c155aa0845030803154106443c80720001e40300c0151820003200150040c155540c040c0d80b00e02c221702d4041d0074041a00e8a605060744940c0c41c04460002040e400300e4014151 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 446300521 1250 446299271 446299289
    0x70b0c0f04120308040309050f032d060405070e180a0312020d0f09110d1a07090f060f0801080303070e0607020a03060203090307060e0a032a061b0e1009 67
    0x206200e1085449902540d0800300701a00020020810315400ca4036031485144aa03841c3c00115444009003c01caa203040c0c5d00f42d805910118110040d958107482c4c1500848413078558860f1a00b850039101d1401c882542c06554507049040d05001b0124901800d9030700a241404201c4200034800b085583c90003443d02c09000c01a05201c100c801c000a0340444054010344d520500801c030100c10040020030001c41d04540c00d0300818410003c40c1041d8032030140c001d800080d9410368400d10a016055290b00030000010000b04200110f504a501e036010006090f043c0c1e41c10748040034001010300406010f81110480c2e52090040118007a8800c44065036810180c034840d488500d944003041c404411504018180380c0040100420210f000004d402041d002d000e00b03010100900a42c0c0d074032105d404001a0000d60004440000d44c0c41c041d0102081052500d590588440e00c1d4440708111001b00f61307000081030100040c0400d480e88800e400b000020120b40082d103101201102601812451040100f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 446301771 1250 446300521 446300527
    0x9030a0f050c1509100b030a08090603040501150909060b03070812180604090e0706050307090504020306031e07060e090f04061e092909070e1906030b160203070b0c 72
    0xe141c00a10105100030020700303940100d800c10b02a0141c50740101d0040803101e40c98204045411f15000642c1070072590880c072a54941030494060185650000308255641e640f134601c1d00010031042401c4000501c120080001c41180030312b8000141e80021035030074403a910801043c0602c0102255040813000319400a030380d1110340da401403c81030304044d000c545c46036011600080208a43e0071150300b6100100230348682c2610b949060311580416602d020000d031044c141445903080c26401940c1100c0c004040f10035000030080341080008044400d51000c0e006041e042007101c2d04000c4140803041c003152004203e14040c0c41e0013801c1080208060402500d0b201c148510081d0100c8199251030403100600c004040c0d802c020500710300c42d0141e2413520103c4002507544d09034001d2840d0150a44001420405240000641d135224014000f50218030461082d4840307012180714640065101c0c001c0303c1c034940303080d04400c2c2c280305003804440159002044040e0025039002e807026480020200202d413 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 446303021 1250 446301771 446301787
    0x7021b0a030c03080409060b040b030a090f050d0c0c0b1e0a030b120a0308010905010b07020d03030209040f0e0c0d02090a0c0c060c08061003180305220f030b09030a0f05 74
    0x140040d95584094408103140e00003109003c0c001004009950285400384074103907856002d050544035520502c1a101001e0022491840b40f036040442c6190088070708172101c3c101c81c1c4849080c140a106500040758031010200c08005200d04250300802342e010129040540304c22400480c0d011181c09035100a800150690080d80658002c10886e88060120918210109101599100f15490683c00f244c096000051030310400e00440d411f0315001da500a06002855003840070805040c8412003e06400b400000b00360341340c9115101d42400c5501c8080b50f8554060001801d150001440e04d001d0801030b200c40001d6110b5000300c9412411110000071b0301404800222680c0d402c41000901c0c445c1030139518030074954000301203801014201c071841c1e0045e025281c103030200c441c10452007070034100b1001c01c2d1004c40d000c1c00c050641c10000490209001c11b404191000c1d594042e0000d40750310390701100034004d000c0c9400c1c56075030180380701d0300441c6040c10b01c6202030001c1c0d001c490b00104026001410328 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 446304271 1250 446303021 446303029
    0xa06023d09050a05011a010f300b040b06070b0417040815090d09060206180309030f390402030a02070501050a05092505090702120706050f090607021b 66
    0xa00000c0c918104000d001064a0716a407a00c10390742c0c0660315503081424a00108500051070590300d08161a02c6c103606d10012002e5500d64180010910b807c0501098001002c0c02005034540c0b2138880e01d0006105a80542000101c1c2c400a801602802e0140b140d000000d215800301038100d07400030408441d0001043c6005c482e03100e2034000d0340a134001c00e143d410340790f81c1002d80140518240020384d841c40650b2a011510840e59204100040c0d00101c04211125010111750780b0001507007003680d14042e0f8010100345030031b504062040c4640e00c4000100804c10300952200300301003513501d80d40395450140462074401002110018032603a03001012601182c010f90407126040e9000009108e41e141150658005050807602d0040389c1c0101c100f07500c00c0f0f81a104c44800c030325a02d10f4072442940d04100a000c00828014a1081584240e01c1d007044180c2e408400b4107a164402d107400301d000c1c5400040000c03280c401070050360540d4000018081010f40228500b01003006e81c180034805014038034001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 446305521 1250 446304271 446304373
    0x12200703032424050c1507090803040f0323030f0d14040f051b1e01090b130603110423190803040e060a030209010b0903011b0c020a0602 60
    0x1000840c0701036100041c22802c50280300310703200b1014556200300080c043e03090700d40d882400703040c0310305400c810040000400c502c801250064002d02d800051a600d4400c142d29503400754002d90b5031400c0d900713010020130110203000d0b440e460012840142c28013150071416501c4c041c0a41c07a034500341000c0f6174150721105a50001d042d201c80c2c800e0500381c50505003000c042e03800c08a10f003500e40e0f00800c84040c0e400d41c86c1000c0c000c00f000c030107030090300380c04180001d001241142d403003164108450410001040200c0c0005040d1040494002e48941c6140c260007500f22400d21207001240e0300240020894000c5020401009169640071400c4440300074001941e88038107031050404418140703101207072045000001d0001c1d107143c20030004507529003c2c10001c11510a1100a501c00c1580d001888082804406001e02e68000f40000c07034a0580780c0d41d1640780703101e40a00342002540f100c40742d500350b1800c90628401000280013420854141e89004080c814101d030140c1000c80303c80030f40c100030324016204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 446306771 1250 446305521 446305571
    0x21509011803030f050c040b0730181e17010609020406020a0203011409031c090c090902012303011205030903030307022425020118031220070303 64
    0x705580824a8035024009000c0b100c0d01c03070342d01844c00c070000b0400000d040031641a50720302480c1500340801c658880c0317040120391156018066004000c5010210103003003070300c51071400c0e458070100440c0045c142403281403190300c800c1ca2500c0d030070f00d400242c13802450b858041e034260045c100c8410500f149501d001d001e0a606c0400c2d030300d1001900054843e4045154441e9510860003805108245441803445920507201420150401c0000d0584416480100100c203580c445000c03a500c4102d8035032215010150780f00f0800c164132030100c0011581e00c800841c4242040d4055103000d811038442c0150315000501580504050400800701805010410742c1c0c0c0c540c0b0001c04a0303a0f80e150401c4000d44503510301c80380c2704810858450483e9068200380105100322640c205030425a0010b0060444d001003000018007555030f280e2a80e41ca021400410039585802900c4620604002c01d41c05800c68040c0d20068201c2c2c0d802c1080d8092048000b411103000a8042c43d022400034801c860190010604840c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 446308021 1250 446306771 446306801
    0x60706020703180f1a07080a080403120f06090f050f010905130803191b020d0503060d0b041a0601030c0806060d15080115090605010c0609080f071a0a09020102150901 73
    0x280008180400280e00003d9175120459400d401210300e076100458014807030b000f0b10210060101c140b14500c280c6070541d025010386050001e8000d601e801d5405c94005c0c00003544619105c0c002445840e815001e400036103c103284003080289040303500302086007418098120220346901c040f41003000c80c02150950786800c40036881d6642002e0081400d800300055051020324240800c0446030354201501440824854020344901e203600349013110240d1000b40b010740e000d88084220b00118950001d003604c01d52060300c1050900090901000150800900e001d040506003000b2156940c5e100360901d400010a0f1445912503040f0005a0041c0010104090341041000c00001c0c1c0d11005400112148450f03e04220b203558a1391000310695545015207404102908403a50004000750b20600e24140268413241c1009030700c070640c1101d5446144c081c0c03082c0c28825804a0340c0050a80965042a80310300c1c2005000816070000c4d40740e0305801204508064140e000449d0b883c0c0c01e401648003982005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 446309271 1250 446308021 446308067
    0x210020f0d03090203160503060a020a1b03121a030304030f08070812040314121303020a0632070c031103040515071a0f1506070501110903100b060706020703 69
    0x2007401401080000030980c441e00c107803040030307800000803040c01c000e9407805409061950b80e035141c8040a03600031000c0b50200041840c1d44c142e40700c0c9507a0a294900d10a0f070702d1514260b0081860303000d46400c0c080c0c404045000c0320b10f014032594008115400ca0781e01252140c1030300c00c01d04207030f0254010303024003a00004000404401440c0c958292a2060f4400e41381c8201c5500d0031100002107000303211587c00020b0307a800109a41148506981080d140300784110341000c1101d5484070140e515542010081e50b18000c500b43c442d10727582e451403000300074101c8a0b80d154030348043d000308007008495019040c049580000801c500040c0b080320080c3ca40903125a0854a18100040807030340f11900c2038408007541030a2220084100d81c0960081800c407030102c9450b103d01c400300040c41d40c0506030a510400c20404000019003c1c001c0c1100e0307907a880b00c40c40e15103c00c02d05150074150041074800c5058901070b41101da940d18201568100d640180d0b0041e1102c1d414942682c20201003e0f6101041900c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 446310521 1250 446309271 446309293
    0x1e06030405060709060507121d040f02030a060603090206120c16080403020f121e0106170f010605030304080a030e1c210f080a11121006030507050708070210020f 71
    0xb850a000c2d20090f5640d51910f651030710111064010f48000030302c064140b481c000141485021000c0a400498841c000e074440588001400c1302d07008045540501d0b004001c000b20f40f0564403a1030024000d60400f4040307829240d0010700280328440348150303803a000e8000308215803c2e4a087d5951030b01d40718840d96007400182054a40341c0c10a21003284601d810b0b00b03c030506030400401108040080b83c0c014280303071385000703010005900041c1000900b5035848000003030074250403000d140307000e8040010703041c80a9091107032400d40352190003c0e03010354801c10042151250009414130300d01d030140340c94890700112030005680da00c0c001205030040311804030b60005100d0644070821030a81303810303101d003c0702c80704c41002c3d51143c1e0800031090200710700400107160403105411008002e2100c55080f441d200084403c0c07500810195000003106030400014404103802d4071803076810500d079040c1141040e080d40d840342e03510b12910320000d000312040c4050b0380d1924001c0141e0f5244560410903941049a9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 446311771 1250 446310521 446310523
    0x16030b130f080705160506070f0519060b03070501020102070305040b1303020a090c1e0c021c0f0b01060807051608090a090216050615060712230d05060906010207051e06030405 77
    0x30030f074001d03070761030042000007001c8042a8201d401118170191055041548580700d901d07955800798016642e60150100301d00150110b140f42d405a14031980340080e94060b4203081c9440c05680d6000141913a00c108440004039070080c040d502198101300320346680700d44004968600c2103151b03000a4005082d070300085140c0c02550883c0c0d4125820360b5039140c6a0380151481d41602c058080c0503400724401010050150505404050400d0014614035503000000d541d510301b9000300c02410b58241610171b0050100c15030003540c81e178003d402854418140381000e0406c05140041d41c000030101b500000c2c0042042d120150a600141600c180442d2110300c800b0340c401180300c2000f0103c80d2805941c0010310100b481240c03200000364064401c9007070030030035611215000719810558007805894490320210141079034282c9240842a5441c3e921344442c0c039030081c1602d030058102c0e48500700030410800c0603680092000e0840c4c0d000c90b254001070b001d41008943c4c1805203584103070480c03400020001030101c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 446313021 1250 446311771 446311777
    0xf130c03050d080919032a05030703090501020f010e0c0f3c010216030303050c1c15120302150705040902040f1706010b22081905010b0316030b130f08 66
    0x118a0054581e4080c02945003405c0b01d0146800130040364640042e101c22548100c0103001d06d580714011a421140303076407075062941e000441c00324001650160140000c1d6810b108120b43c1c0390a140080c03144420108409e03031181c188aa17910b01414a642c522501a40c40c100d82d5500740002c5061010240820803400804411410b002d04804524a0311410203510000b0084195088541841c03011415550100d01605020b4040d4005107000c5c080c40102c800035000143d120400c0440008050b0030900d61040c09000b01e074862900e510300000b002c0003080d000316000b0851201d100c11302c40c150762180e100380c44601854100420951001c50f012415118500030b00068840d0181d1030320560450814103a40d40100340169600800140040e00c0d1039050300d0001e0100307440e800b45000b162600d032441d00b4504900501c01a802000e101c005100f0b10000380b191508241042c4d0180100701611411400c00901d40e22004241d00200b000180d02210344002d00081c06612036400403071071106041041d6a50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 446314271 1250 446313021 446313031
    0x2090616020316230d1a072a030e130c020f06100602030715090210080612010b0f13090803041a070f0e0607240c030f050f130c03050d08 60
    0x101c110501020b03045180c107000c2049814203010740780480c002c0446514041c028490f03a5400c1400b0050003030010304042c0c43c2c01b10129022110941600d803811004042c540f01c1454041c0b0340140004400143d850041c24109036601801d14003d0400d050003c9483e222010301704030050f40c50504144072980d070104a50f0030680f40726007103800340d442d00c1651035000c01e000d100e0400503034010851f00c000903200c800c0b82c4491040d80308001500e4009034000c99001d20400010b0701c00907280e00b041040502c0d2043d102103031450118001c0042070b20317850215808030194000d644c4180301e40d1004440d451916004800b555034805003160302d90901c0d26100108800400e61201038514031000513203041d10840d580031360f01c01241c0d40c100301c820004041c000f081d80000c800752511003601d0b42000b017400d1508240b4007030140010000800c1010104001d0445090b010500c0f240e41c1008240481041f101e0540d031340100c86000c0c5076510303100c41d140807100802580d20041840c001c100350600e009800500d6a4410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 446315521 1250 446314271 446314273
    0x6071103070f1e0f15020a051b04140c0a030e0c120105060315040b04060e1501141002060c070b06180f010501030c020f100c0201021b07060f0c08030a0906020906160203 74
    0xc1e600446120703c4200701ea000b646241d40018900700310184001c20070500113185401503600701800c9484560900c84640000302028960510603001e0307040a200312025022010101d04e80360429200c0f4100c50f100310a2604c04141c0c403114000e58185d400e00000b64041e0004000340c015115a4010714041c00c011180c09100b40140c407441229101e052449602c2a83e01803402d0005a40d55a0380200070446400481024840d002d0058951141c000065011f8000040914600e1482c10100070016150ba00c2140840d08003c0a0083c105411000e071403041b64086240c081036501e0001054001c03910540700c2d0500e203401d00a0113501a02810360030f041c0c40302130740c0620004030100000d81c5c3e12282c0b031560011a5004000184001080e944281041081c901c00035240c0340b04180e110070500840f020307a50361500a0b6004100054101070080f00301e50031402c000025100c59101ea07182400001d10440200d51203002d03032410021198100c88151000404035034031140011a143c0c1540c410200803402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 446316771 1250 446315521 446315549
    0x11a0109120503040536010e010f0e040f05030c15040b0105040204030203060a0902010e060a021506101b110603010905240a0909021309120305011406070206071103070f 74
    0x14041c50031400d4034000d07006030066207043d150209000342e810403185808588002a0ba1060b56035249103046001c035110308001c00c10315410003038160502030041e0310a40500202880800c940c0c07060311886a40140c003c8198840b9200c00c5c00d000b403c41c400c400c0f42d00c1c00d0b030059007400058032107507450040c052800ba9441400c2aa00c2c1ca050008030311540c00003030350540c444400500442d0741500000d40451061500d11020710450b40030608039008071a4080168100b0240b010502d80c0740509554044011110300005868192016049251032140d03406044c001142210900c1403041e2048409a000b400582d03072981d60b0400383d0700030700f4140d0302600e1030f04046607500c5070754020100c0c6001c410300c002c040750380d9589003440600042c8080740040360498140d103c180801c40107441410f4400380900d5140b01d01c0084950001c084a005820104003c01c40e80803e10032900c40070150381045606881003517840340541044102d44a10201160f031500c070300d84020403070000c42001001140d42003550081 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 446318021 1250 446316771 446316779
    0xf0a02070e04030503010b130801020a05070510060302010507080d060e0403090e160e0d030c050d030507020d0503091507030f0c0e03010b090114010f11010924020304050c0103050a0e011a0109 84
    0x1c01d60209a5010f8002181480180607140300c480c01041a1004120382100b10707a0340f08019030a98101591100200340c01007001d809202040c803141410030590b0004101103070a40d400a00076015680c0003800350384020804040d09071455005801800c2c10300241401480e142c43c004202144a00410010410340d101040e02074920300c4103c0f2122909444400101103594180210010036043c25010809443c04080200f1800e1001588928aa0381c0100e02032a15050203840c041c0b10005850070070000300b041280f001c6c0046021006c01c0c1e044c19000c0380ca612950000c90213800060080c030300c0c45150518549019400950842c1004000d070001d0210a1600d8104042002d0074401c0640d06014904c08151039807050001c085a80010304045c83d4040e080c2d42c40034212001090304850781807002c0c143c500313444510502218042800c0c1c0c1d00750714502c1e06a9a55407140461101503044c1501e03180405c400e045107400c12030380c3d580014000c00c02845c4000403400030626076010705000c03070f8032000042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 446319271 1250 446318021 446318039
    0x2208030406240302041109061305090f072109080307020d11030901090533030411090c0d2c0601090b0a080a202e02010605032e020f0a0207 61
    0x6a0208410302c110749045203190207002c05040d444100840c1000e040040740d426a8441c4041d0403003408154a4480c01e038201018400c0c1540050411000c1c0300314402000381c90307a4000b0381d8140c208008014181c020203910341070b230094100540000e03e403c10200c10000500e0380043d5108085102c0d40d1103c2e85a003010151036260b1050241140c00a241801c0901140c10100c1480080355101c407654409900c80106240d00c68600080e00324400c40000180001d000d4460000380881008464409940c00c21280404c20b5214101d03407c02265101d890081041c0f05400724041e42e19035028102c01076030280340415484000c2401154012480d05944804c075003800c41c40c200c160303084d1000600c003613996622100441c0700b6010110103281c00010000701e45459502c200e1046407841d90a95003404444504880155250079045046a25190302040310340e600280c0d207184101031001d405021b000290300514000c8240510f5040680006000301240c62402c000b480540348075420345030025100d205c64 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 446320521 1250 446319271 446319311
    0x1090b01020d030203090c04180b0604150311010c080a031409070501020607110705030307060b091b030106050a0e0a14090a15060806061308160b12010e2208030406 72
    0x540c016072080441004503400fa500940e01726088108445404a2100009040c0e0740c00e070026580c070f130382075410074000c100200000316000003040320103009090740c2081410002d0140d101c090180754003010740d103034240d0081003030105250b001980c056490140b19406000b0b003030a10404e01ca02e18215000400c5820301054a00507542d0503405000c0c81c1d11381d404200e646036007003000744031207008510300000e190340c0c20002060308601c520300100707042002008002e50000010103140c83d106a01c5a0f09500080000440707040d19020b0a12980720488030301c00f180ca0441d0342492507000483ea250204000e401051a24490a03048072054036a940721403c01c41a6000410884480c0c19403500c02d01c1041e018804c5594403c001a1949080072070080f1600c1c071150007540100100d0b0409204401d61a9542018002a00c0c04a0340d903813824419010525040701c2c14800c00f4568118038000c200000582e05007458a414a5500d290340c40d42c860030010700035401600c0807100140f402c00f20712402207060000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 446321771 1250 446320521 446320541
    0xc0d150605190e0d020103051b0307021506030118121209050f1c1707050c0105040c061e05390d18032004020f040e090f070503120d111b060109 63
    0x1c84c0c00300e4010f5801500944006010f465607003260782124980195500051840307052654020b10202c200903503409040e1030040d01c2a402a411b114038125206004801c1b00b041950144e4504035040c400d580490b140f030b0300c040605c46190308005000052050015a8094400049058a00000c02495000b40c0c04410b1001403021500405c00c0100c10b0040d0341c03555501c403040d0b0801610f050b120200450071603c080717034115015011900103024035075009881e0115083d00f603440c560703c0015410003800b0b41c00340d00324485c2d5500c040d210055240000091a0035110a0860411082d05a640d5107a031149c05482c0d80300700059050601c0c0c031500c42e400090300100e079001039100c041034020610b00c00885003d0841785802a4080100c540104c500c54000c2000b020745200417001070500c0e555041c1008107686a00f015640585801d00c1155000305c0d05030b2000d2a1101c4566032420f114003210007800850802c04d00101e40030400c4880d00d20008a5001d01c019a81e0585910340c1e203ea600704121202100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 446323021 1250 446321771 446321779
    0x5030402011704051002070f0b0105031f05060f0a0602060708061e1c05030c07030c091b050703030b030d0309060b09090d110312070c020907020706080c0d150605190e 73
    0x4021102c9890924455420900400c2915412000715840000781e9124000441d1040c804c00c1c0002e060200c80c3c0c04241c05440d04401800010301682d00390060900d40b242d880404681d81c00106038a695400c050b25800700003e08003242817965018081e464910848525001c44e2403000040ca0320f141000f40301c0c00140428002020401d59001801100740b1301c241c80001003036244a540f00440c0082024000c00090007008101a030700b035203810149900160322081e0003034100040100800400102c5840910300b03480e20b15183d18035401c00b2005016811400c541500035191502000355040d0400341800b4040c0e6020b0100c845a10184584001d0451b1201d42d5504013010205c0c0f4a0701c1a62075207507042d40d100489041c14840c144100c11000d0513070343d49021450b0b0340b14882c11410f05200c4568000d9180c0064500186040f07406800180b0050904402102c009440955902c0fa948440100ca4000504540054842c100034103154080800c01c1e02e028480c000311200148034014100c03603020013030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 446324271 1250 446323021 446323037
    0x30903041205160e01090b060c2112041203050106020c032517060106021207030806090c04030813061103090a171e01090b06010e0603040b0907050607210503040201 72
    0x10441d00d20010303029404407141e000d0744108501c0455851284409414102440343e03003035150014083c11070b080e00c070140740103039400d100c000b0101c04041070302c3c0c5c4502d529100d103402d41103424404103683c0c404d002058003404440c44c2800f0500c400880030b943d450350140c404000a90700c2c2e0200b030703a590030440b1200d641a800235126149038080c002400610072103620034081e6090f142c0102c1d00c2182010200c3c40810741c001c5004010f15581000607000d0700814241c0640f41000c507450040c84400c1c010030f803d00035440040416101c2d45504100e9006580011a5945130030500b44580403050492060300001045140341c5480c1d104040210341000d00000c0c1152286403a03d003c0d240c0514480100310f07a60b0003450320000ba1100600b04041c11040d03400c0000139040518a042d0420b4003029210a04014500348628910f4849004484d0850341000120035030f613480c5c0d00d40714030307195181d040329410580c089801d800700005400a0a070b940c400e40400d1001060001d0210b80d280402c4030701900042500d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 446325521 1250 446324271 446324279
    0x70b04030207081902130b0f0a060513050111060103030f0c0c120218010b0a031e0905060f0a1109012f0309010210050606090d0501091a0618040525050a0303030c09060503090304 78
    0xf9070107d840c40101a0441880c0180390000481c104802d03441035002c01c0000900c05c0c0b10500e0508154080c01003400c1041c1c2c100320400e1041d98460050000500f030002c81707408100c1c02c5004184041e01103a04c017046041143d1940317500c03c1c04286030701c8102d01a600802c0b01540005041121030305035010100c0b118144540c0120440c05040d01c0102203d0140c075100e540d4121000034090041018041d000a192a040407403940084a0006004000d0726213015101c10f2001c4142c2c044170001c400c24a40b40306120740800b100181c403807450b07030704210401c0c0d151030308000c4840210241001920036000c0e00c0003504101c4a64003520801c89400d50b2108040102034514644200524243c1d4003c10001503000f81a588240c0b4106400d8101c012003c031250401c1014034181205240c02e100221094105e420142e44c0c40e07603200400c0e00c110b20b00300d404000c0241529980d402c03613030042800a015100d421fa4a0601600900c01851080b0008540310f00100b106401281140d000310003100046140c04d1034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 446326771 1250 446325521 446325559
    0x3101e0b010e060403121b0b040201030c1116150302030603120703090f06180501020d020c0f040b061605010b0d08030403050a03020d15080c041806020a05070b04030207081902 77
    0x1050441d041c01403041407030940303803980c4000c0c001840c4038400c1c44c00c60483c02c1c840030b41024041100c9035060500d55003840c0018485441c0c05030015030a003004503c90348145d8040d5150544856a0300603486164500000740ca10306007a441254034000385891310710303001c0f80210140c1c8011912260140c2c01402c01c840c120000c2070040c01a24064540004c10a8075912052907000d000c0d0301040c00540d0081c08680340c602403c801c2001080c003400248a01000008080d44401101c1002e511422403203548072415100c0b504103000302140104051348d601c010190080c0c5c00d020401c01910550318200d03120300d4a09000c42c9407030300079070083c04d80c9086950b156000c40d8035a000e150f40a007010340a110081c1c00001502407401c5003001c0ba0425251a41003400d003d01d00080203880901c1181081d108501c0c3e19109140c3d8030500b60040805655480ca030075040c0c517103200e5100700a0031038500030100001d0660100310075041e41d10101c02d5401000c01d002c0f68240d01e501e120f101a600c44018a203c65118038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 446328021 1250 446326771 446326781
    0x50d021c0201050f12100501030c1e2a140a170a0215010803190203090f060706021213060605090601050a03050a110c0a0510091a0901110f04030203101e 67
    0x44140f500e03030300d0440c4500400400d50803807070b05240401450320a126550340800c1a0030040c2c00207103420004499261380003802d4092403855a4074034034035614202444c600c90301849003031400307041c40214510860041e9144e10300f0f26010585003840706202010710031202045038032406821a50b0780f42e010f881d00d4510300e10380e845564140150710800f0201e0203080107049040307000b4150b13038020319201e1088217401000007031103006110440d082000b80d0740c2d0603650080344004604082c2c0340b20352510694600309000303101d440620300a000c0004204542010414081d02106100d124184851507803001030000c07049096405a0100b0814003a656525210f94407141d800f06202c8804151003001404003030f25540a41c10741983c03a0000d403410800e00404219a0300e41c050101d80400c01c4d10203d840c0d0120400f0301c0c0d070b100c5042d02c1c22a4013141008100350820401504258081c0307584007416412003526a00a100482c068002c00c01c410340c40b01e125118011282d99286038201405550703d1780d03100104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 446329271 1250 446328021 446328023
    0xb030f030f0f04080601092c1209150d02070c21060203130b0f180a0804030b0408042711120a0b0d20040e0303090703081305060a020a0c050d021c 64
    0x403d01000480c501c0c03c1201c80c1c000c007060039001031000c0c42c0d89054802004960300300a03404102d51204d82c254000082c0b1501c1e000c00c6101c02c5e035140c0a01e10000b5038004000070760f1201c1e6880104501c5013201c81039001b0005144280407e982141d40c55190508030200d01c030f0f989424503070300c000200c003040f015001145d00026078046800300020f2907891751141307101030720f007444501052401c0101441141500840e101000c400a100c1d402d16903841030458400c03400000c201c206240045010003002c20306440250170000e0844d0414503100c00702c00380f28101e9084d40002c082c2081480d00d5030500d004101c0d0b18191609a01900603030329490b000d40980100416242c010003070104500209015080c01061544086846411417035040100004e4481d4055400ca0580040050011000e03002a000d0210780e400a61940c1718407803402c614081415030783c456a0003000000c0d042d91010340c0030581d04003591052a900c00015103c40c103000c4c022903000f070000d41200300c00144500d5500403000e895181 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 446330521 1250 446329271 446329297
    0xe19051e13080a14190f14130b07030201020403020a060f1205090d1d10050d0c0201020408150907050909010213080f0703060209030c061204030e09130f020d0507180b030f030f 77
    0x203c001c404010301004800d130417000158000b00000b420f2540300d03128400e42001ea40b849828900ca400130b6202e460141d02c92028441c20019010040600030340690340295001401341a078650f0301c141c0941460010340304e800010300b154040c1c1406002038854035000300d1b0803034014405501c907610169000c650b80070341d0002a504e441c1c100100c90703035804000c0190403020782d507054a80034a90b00040645404e51341c20030659005000038032045030002640001000f0075040c505440d1960b080941c00d141e09504602d4200c009007040102010054001300b0f010740e0003203402c412948c0d54840d45511039040c0840050140c001d074004102190b03180d00501040e00300142900e0190403c0c50006066a210900035007803010384008101c1407603001401c214218105403029a80391a045842c110040352a21008103600d414020a005540b104480c00d400741e90310104841e105c6071a03014208120381c3c0d544204034014101104441c03d0308001c2003d20a40d90407070015070400c101e5100014403a008003c000040b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 446331771 1250 446330521 446330527
    0x1050c130e0604110406200601060c021504120f05100b03210c06090a14030a05070b07030906050c03061c080403060e0a15091208040b010e19051e13080a14 68
    0x41c140c0060000d00041131b0649070080740605800b00d560882880c41299010380d00004010001b0719089102403004560441d899541c080280051184600503508080000e001010708281006032580400c40720501400c1116122050016108183c50b2440b82d000d0701500f1000e800c164107000c4210031b82111008054603814521000722440c0b400307000300c40e80003083d4828001202841061840c50140003600b030080c6107041c02180025040b8482c440c4001c05400701400040c60041c0300c0d60201e13081c1c03030384042c00b40140c0c140300d5000b6145400681d0440c2c8281080015400c3c0390704090101449160b000e00c0c41e13810f0a02c0c40d143c640045c80d032070180800602611860340009120400c640000c3c000f21880000c02142505012040028142040060100007424040401c445800381c90440d444030f81d4074940d643e62221442c6400d00100d00750811035080600748039001001e60140303000e50301c99400401c080c0d41c03008d109440c82c2d00042009010b40c5000c000c0c4a01c50391085100301c00e6146003c6110b45 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 446333021 1250 446331771 446331791
    0x8010b010e100c0f050a030921020f1815040b0a060c08070c0302100908060109022109070b0d0204030209070c030c0f050307020a08010e01052809140f07060201050c130e0604 76
    0xd40c0181004d088034540c10803001c0c2e5017010b401c40d1287c40902942c2465030b01d90280794050a4860480c1c500c041d1284256000000302980c410700940c800d400300c2c2a02c0c5000342844502d19060b41106584548124188203c10f4102c0c200410b60008981c69a641c13071481c0ca80544030a881580001d40c2990000d0700c2c410040090780310f01070742894964050359402c005c249050081c50030720006070021034485004200039007034007210320905c821108403401c4100e83c90720748980703070ba107010610f40c810b0480c0b10f000f207100d0445504030781c0a401100d00035180c000c0d0395500c641040314900d0f0100b4000b8085240500c154001c20f1200c1c1203080600e22039400c8070716184a540004030495215071142d12580e44507180c10341740e10b4082c040c2d59080495600818142c00d00c0480b01d901804417103094100c10303030fa21400c031400c1c00a03000c1d0080c015403400c41500c0e9011160030a0a48410701c0d4014070000d58281004178004210000869800c00c40440103891454100200d114401c4c03c003410f91607001e91901030240c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 446334271 1250 446333021 446333033
    0x100203160e030312160207081b042406050a12020f030414010b031603060e0d021e07050d06050f22020904050c040615020c01020609151e0108010605010908010b010e100c 74
    0x1703016805001c014a10350b101414001d180032080c4e00084c5107500306e207000040c208450400c46082c018202c0e40810410441d4000080e0072990340384c400b0032422030010014003c3c0d0000300505c000d1109581d005425041c01c0d001c42d09038895550004880d113070030400a4046103141d8103080c3c01c6144600041404030b03000c1c00080c0f4141c5c40d031040a070809a603100c2001008190710444802d20060f0f005824401c040d40c0000e0349880c29080400b08454085022000505080c05600007905004000030782d41180ca040402c02094211801c04500500308081840d91030620408503d42d02c5c40d0a04450344031580e1700f4000040f070b0142040310548213601c4510665500d5000307040c05032441c4114224165031905e00240b6140039020004d056403c1401405201e0101203903082441e4040c0c854850356858201c90000c61511511545001500080022603484010b4210b8800c8920903a034050074aa103c8105070700f218a0b000b24540412100344008a0038105060090b40c550b00f142032004801c003540e201d071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 446335521 1250 446334271 446334307
    0x3040b040b030a06290a0306080709020c0c030316020d0602040e25030b0307120f0b04030509040c031107030e040e030c0109060f0e1905071502030705100203160e0303 73
    0x810402240402086a449030303c0c4134180042c000103d020310160103641e4000c12400f07802070111910b4100051b0050140c0c000c0d04608020b080b040c00f141c0e1016a5030b00d140c1d00035003103a00e401c0d04d14098600710600c145130020540380c8807402d8820048100403185d08100300c1c441d02c0c840444000340c00f40000915460740e011142c0c4074001c50484c1001c428000c2407078580f180c49400c0041300b454580070054019480004440050380c040c2a454106101142040782110080d000300804d921003d604000c105540000136050345942943d05100ea0718075000b0680585d40f601c1030380200310406010708400f2130700c034003d4000c032240060000110006180c0c0702500b90341c080c0b03250b6140c41e07442d400b1003420400240708840c1524500b800030480480b20780c8074107071500b010301514606913030002c0300041484001c3c40594018042000b4000c0100c0e420900a07440380c00810003501c06008a8038407240c114014002c4901c1144925070161107070030143c0c1c060310015054000e071070305440705025042d210352180000f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 446336771 1250 446335521 446335529
    0x190e1f06020a020f190311040b04110c010b06040e040303022209020408060f1303050f1303030e01021009050618010f0c020304030c14060f1b0607080a0606030b090a09020303040b04 79
    0x6440c948041d80140312100404e021264056070304400c0d0f0340c2907541100c080e081640c0c1c3c0411904025a82e8500045c040c16040c0f041541c01880c3c095000c1e2020009401441015099002401002c101c50200b061134043e42c4521162680700e2070004000a100385d008102d001c0d6030820046004000040303600c61001c180d00808481d40c0e001070305214007070381004607680c4024801689038443c0303084600c05c0e2005d1000e46d0002c0030301074041800800c0040c0c3c0001d50344009144407040c41455901e0030000e00945030b85d00c5180c05801852074190505425018898103950004014195511100d00c480680b03480e0200891095596481702d43d544c0a59010b21085004103600660300e850541c02c06030115851a4004034030b089280c02507d2194a4035001d443c42c00e4600c42e0500e4540150100c0822804400d00e0003408a0048108100c6440c0c1c003d002c4900500e050306003041641d0f00d83c207040c4c007103e0307280d40d0450703115a491700011441305554020102c480d102505036424a9920408880307a5041a04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 446338021 1250 446336771 446336773
    0x60702191502010f060f030b060303070f0c050406140d030e01050702091006081602060a0c1b030909050c0702030a0807061104062c060a031a0d03020615190e1f0602 72
    0x1280c07a400c607424021803100440501c0c3c00c002007860400c020803450b0f420320004051000420014500e90f5090090b18002a001903041038144000d26021010000c14010548681d2805401064080760900c04c1c00c2c074440042c04010010080e910169a00c051890000307040000400250005845102e07003a80116803000c0c81d05102c904088000d4184d600060280c2c400502c20751401c05c541c1d0b400aa819040651080d001480c81505002150201100005001103540d07a90201c0100751f40b1043c1c00d012141301c4841040140c03101001c0c0c00c21807003410300c003070340c035170f00c4402030001149132100200000d6104000005080034004846040c1d40c2040d80688089040c001e041444500c04001c0750b2024040c15030140000c1058900013026400ba02011300209507403212143e024003104d03510300f00204c0d0007e041411b40892458002e40e00e082c00c4031364002c3c51460031400d00d40e6007015415010141107000032400341e24101050b030322000800a1803443e1680e001c0c0c0c5814240480410b00d00080d1140364 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 446339271 1250 446338021 446338049
    0x406021902240f0a020903100e03120c16080c10091208060901062c03010f0c030605030a03050306010f020c10080f330102010f0f05040b07020d0e06070219 68
    0xc2080e480300c40c10311000541c405000420400f141408103000f952010703100c0c5006859894403400320b45416056520802c03a03d180550030070303035100c0000c040c1c41403000d90007800c044c41d5a007090440b0349008000c0110f6441c00b40d0100700c0002803d0740c000e0030100201004480c214400c07100b0000548625420549210260341400f04081398046d0b0042c2e07000314180c0320118203516000d40245102c44c41c0881c5004c05116440c0c2026540d092130708107004031001002408122410459400201070440b41c0c0e80202c1d16003d07000400c1d00300401c00070320442d0141c84003821540d6080042d1241607042202408501441c0900865035440c1c03481c9143c0d01405c0d07a03820100b0300e0101085c041500c1c0150410000c600070030700d031190b4545540103503801d504041c035071000488031860050b0301400d02001e10036195070a10300d40e041480410f80c00765100e607000d60310342291038944031070580c0c4a03101d00e201180040d1041c0caa80105051040c01896001d2000d04200b61041c80c0b00b140c0d0b02184010f8110621800da02 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 446340521 1250 446339271 446339293
    0x1a0a03080a0f0219020d0302030d09030503010602070504140a05040201110a03050a08220311070e0a050411060a0801030303021303080d0b09010f06080610020f060c2812050406021902 80
    0x80554100407240c0000c210030360840c00ca59184c49060840248155031a140d00c00c201482482511951510000113000c1c105052030060902c1c3c009000f203400512034407030005243d01e043d024420144d00400c4518039907441d102d407a48080c0c10018000d17414081782c20384441442008200100c1c4aa0191f51402e8954281d6200113104000291010782655241d410190828001d4046581856414285000382580c1034003800d041100390f5105001d04140482000103400315074004600c04d602c43c2c800c5904408c0810b040040c6030107444488400100034000500002c1c0c000da00800c1d400100030b040100340e554035682c101c51503104490800c000c070345407040b80d0498100408603501401c0c10040a000003800c1010043c00c60394002d010758800d4030b036000c1c020030b05402440041a104030660503210700f850882c08a07e00d03a40702a040b03070f40e0201d0b404040b030f9211508041044054071955254a40e81c0d0001001102401002d0004d5a500303600300144000d0341a203020861030030001703801401801c060 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 446341771 1250 446340521 446340527
    0x1e1e0f07260109060e27010f0e0f0f060702030301090f02040e04051b06090607080d02040305061008071d0c07061424091314120403030c1103011e1a0a03080a 69
    0x80703680048094040c410600204d481d0f17084446c1401c0d500c03000d02d1103d501c0e150390880d000d0300c0042c0002103480e00d0b0080100038810301292101e04444607a00b20340201007031141440c0d540c5011176015005802c140010712101119401108200d05080c401505044e19500310390100b0390295030840e001d80c0461141d0000c0100c060640d80061021624a82858005004a626031241c44002080c0500001d021003042000394181d401450304a01107408c00d1801340c150349001c031550b005124440c03003855800510414208109541205020480000c54035145002c1c54560031100080b01d203e6219401c4005000e03071040782611555080580941800c082848000c0083c00c00d40c040c0d02944052041100d0750910030712085009900a4407580c0c4214180003040c142078820304250340c4180e001600005050740f10002100443c0600405600320703104600b01422503490346101d0441c4e00d000c58103100c0040e41395101c2c180f520080748401c3c4905c003d030790002d4800b80080d081100d4804010649401d03180e8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 446343021 1250 446341771 446341781
    0x5160f020c0114130801090f05060f060a060c1a0c030a0e0304031106210f0609090f060f0a0209090a020a03060609030308160e091e1e0f07260109 64
    0x5498006000d80d80c203034100007820701c80340f0300041200d50f02c00158404c2c000d0071100200002c0c04080002c0003d200f1a00e03100c460a10302110503500c1c6e02c0360340302061400410200c0317240901e40040880c40080d2400c1020b82e050003600800b9a0b0244903564110380d035440c09540907104880720403203a603503440c15601c184102d8520303000c00041ca602c2404140002a43e0490a29400f03034121151601c034488009540c2c900c0502c440c9a55003000354105200c4c4212031401e410b405403034100e410558a68902941075075940105580b408164440300c040b40e800c0c6d00d40303029a82c1003985610050320345081c92000c200c2038003041d60060401540000c008441c03d40c540b16400180c001c0380340c006216451914000c00c03c10300038050300d0b449180d00d41400700103400b842641e6101100a080042a40303020480c4880000a1a01044070300030100002846580880008082c0f0141c8000345413954644071a00b840c030410040c0f96005020521400d541d40c3d415070040f007040c13000300740310f8092590304240c90b4600b954 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 446344271 1250 446343021 446343047
    0xf060302100c051504020303090616020a0b0304150c11011e14060607080f070606030305070215040b0a0813050703050a11030109021027150305060f1020010516 70
    0x2c01000c81c00003881c0441c0360108080312201c403040544840c00000d08610600b400340d03a101000103803d41c401c1c2d183c44562104a4021142a00e00540d0380d54480b00034801264020001805c441d09512008955448041100c00914190303484090074000d20b400c40d10841269010160f224a02081c810090b01a0819040e00ca059503407407814001c010608074006c1031401481c841c004a03460407948003e00a4800e115009a41400603d41d64240600150300099050b4011441401540c0705541624200d07001c503040050240c3ca4030300011411903000ca00a40460115003540740d052022800400c600b00245010702c0160500c1202032403d1840d05400014240c040e034100a0204050b0341e6034000c903c440000ba0400c00707400ea8400043c0d946000519001d54002490328038003241100c0c1d481500414242161020001c94490034104000c000c02c841c81c1aa0011010016004451091840052403808544809145070764001401d0a580c400c9442a0340d01104402080e459a4070580302d42d001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 446345521 1250 446344271 446344277
    0x7120209060f100f120212160903030e010e060409060824070801091a030d030b0102010606050304150905070312120b0906090103060c0c080c0601050102011409071a0c010f06030210 79
    0x100c00c1d0070021560044202c00034406019402844d645654000d59403095000141c3c0340031503039200351440d0b50f80c101d0000d0307880c20f40c411103036254281c0d090b000301651016aa05a12603080c1007480100440706c560a69602540001c000e100010751340300c040c01440040c002c030300050039030503c400d20103004e003006100241007401c280304c01388070700d203904000c81d141900d0542102140c912028403403034001c459140380d0350303400d8403c0c8003800c1c50080e41940704101c152826030091019650300c0208072082d0006030303005880d0300c0013495041307640300a90780425465442042950f0070244e032031f1107a02169084503940c5001c40ca041c0d2107107005444500c20020034000c101d641030058100003010071210901408000c006954030018040e1050180800c28440d9502c0074445a0312041c0640494a841082c41090f0141d130800300e0b207441882012200074820b451600c02803101610300b1000205150401104000180d4200554142c008080c000c0b0481251010400b14019140d40b0501c903c460b402c8011000f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 446346771 1250 446345521 446345539
    0x5090703020909070f141216050a090e03040915051005030402091e07030902150406021c0e1e1305040506040c060807020a0b060f03161401090b0a120e0712020906 71
    0x1041c031031850407051380c450406c410780380420305001c6520100740948807001c40c440d4008001c84d0421400d010411b882040d611407401c2541c800b000c0c015a0f0350761100c1130f02600140420700221a080e071042c84403803c0d9020718145143d07034070b0205004440242001c400594000100000e504001200d9504003503a03624107038601091408038440c0002c094000300805071074008180a650b1100c0008000f140150f151650301c80d903a00340030790f030741e5054075007044d103584a100c1d07621f5054001d0000011b140005448201c0382c81a010b402581e504600f008251701101e554003180329001a4410356100c0d0b44228001c00240c00e00e420055a0080c0561085003000380c17200801214036404035408078450740c41800c500e50341c1c076508006030101030101052509489000711645501c000c1c0181c2c1001c403000400e04000e440700c0e0000451703140705240100d50b81c0f82d00c104409015203204542c19903000a86001c002149019411441d0601d036182d80020040c0045c100c03001c0542c0703820692660403480880b442c51b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 446348021 1250 446346771 446346779
    0x5030d08060d11030d05090111010e07050d0c090f060611070f180b1309031103040308120601020a0c030302010f0b0a14040b030a0b071e022d01020d0509070302090907 73
    0x9241401080603000b00145035400c010031140201184401e000201038900082c64500010070503040354180c0c42c0015141000c9400e2104184107514141003170801800c2c2c0c090601e4144a01c101100d030b0f0440e0035420340030000a2103503852007800b00b0040c1080002c15094030b4941c00400d51000352064065513003005038100f1000004c180400100d8641008401900c008004244020300051b8092a08110090103640305a09154003030030580c0c0c03098441810202d120321a2558a000328080103008100801c2610525880d4049203540400b0510446254204942c1d0314031040c0c81e20350084001d07070745819030702462985600440021610507075130203a21034500781200071341d03081c2c40c00f07100d004076170380c2c81d042180e41c4081c0440400c0d1741d0440070041050400034001001400109561110215000c6500c2103641c80800d0407101c481c1c890000c203581c00790440070034914400c100070440e45590700700007100c11028540a128444d200d0000a0540e46243d07005200c8517060082c4056925041000188 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 446349271 1250 446348021 446348027
    0x10603140709090c03020f0304080403050d08130305131205060a06060c050714010c0c080f0106060c081e04090c05030f01050d0c06031505060403120f051e0c03070c0806070905030d 79
    0xb4007207420010700412411014034040d80244100c60741c0307658842e8000100b10900035040d008208aa03c200c00b1900410760b003500855111f58240c030300092000e00b10a40384003091080c0c0c00751591001e24100b2003009070ba200103180740703078020340011522034000070308010702d04605200c0c542c0107001d24208064860b416540390b42c2c458036a8059884004518440382d101d5901c645180d00070a81d1118840c00c0480d11084290f6aa03641089500000c1d800e20f28007260b01441031035681e2140380d1181c206801e0103406121818003100500841c0c01050080c407001583c00b1860045c0740d107204540e140e60b9035a04010208890400050700030740d01031842141c2890000308104002d20172141c0318540003e80d12815100e910b250b8240b6400326a105402003000300c20b00010848070202002c590301d5020010000040c26522400751404020038040c4100070a43c0380350006008004601c0e001d010307249001ea01c1e65a1800310700c41364000e401c03560700110030800d060360001050805441c0440042c1a0043c21040007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 446350521 1250 446349271 446349287
    0x16060e040b100512091608030706050703020414120f0d090f050a1208030a2d051f1502010b10020c12060103110126010e150f0607080f071a0106031407 66
    0x4c4030206044e400190b112081400b8800d4810100d400a03001140e66401503507907038000c4d60055a0143c07070800480c1d90075004c0d10881d0229940003000c040100744201c10050342040300d03d035203d002d0184d4032041403600030602100e201e003030b000d48680401074100241c0340a01111904918040c0315604401c0c442c040942e90701f440c100e680441c5a41e601c1d1b81d2400351a0250180a1801c40d00a10718000b0070024110010342d039207000080d080811403607486117801c02d20741d807011000403160f00200c5024081003950105c008040111400041000700501c800706040711200b2004038018cc100a1080102d80350404425049110090040c0025415a20307641c40c4c0c1c0000070042c6040c4002c84803401100d10386010181040c0d03d220084003140d6940f0f20710724550140441c0c900c000c0600c8003684412600d803a40b062258050040d21050504820303039148074599000000043c040300d0b040c011240007540c81070a00c01244103c210b0b404042d45010000380c1611803000404551104240801503403603484a84 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 446351771 1250 446350521 446350537
    0xf030c0303040b0403090312030603061a010c120c08030423030f0d2c010f0c050406080103020d112110060e06010c0602040b040b04051005070816020316060e040b1005 73
    0x50881952a0340c03400b81c85071b140e40c0e03200030300e50540101114405501039000f00d0480e0702504003841405007203403861007070f554403403422800301e0910807103180882d80705200c81070360604034106200380403415203d110103a00304480c100c1340042c0350803041c00e00d1800305591a0b04d484100e80107609112404000310300500401c3c41141c4069900e02641c040c1c50344044070140700701003d0a5400012081d515040d020340f07a0070150148803814501003201c494455811201110701680d604c111690840c0c0c00c1001d1100425010b0f01c480201c002c0b840d000e60380d110301c0c0e082a890b40100202120f62020390190501c1a081c95040da503528202003000b4140b000c1d07620a902020074a46002c0d0400d984c600f6000038083c03504030b41c0d80d125000c580868074083e144024003c1d510111079030003040c007103a01308540600c1030820052014000b0310402d20003400c0c4020b80b0715228401410b8071060a1601111910f004555202c400081d0380a02802c071982050301c42c00400c290701f510190b07200703490030402070080d10a101c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 446353021 1250 446351771 446351783
    0x5060c251a071104091101020d0e0604061206150f02010b0409150b031f060513090c0b070602040e070503150907020303011208120702030a1403090606102304080f030c030304 76
    0x2e030b031001c00c1441e12044411620040c81041450740b40e0602062030304081c0b904034090b11407612540307115401410440300e6800d008005502d05820080221000040008a0008540c40d10800b095412002c1c00200204607641e40349040307400580c00007400e5408660308036000e2071a100c11140850f070400880417003044142008524003a400010901e840b520000359608101c505138005075180464000340c0032506d084480907030800ca640c3c04641180c24090008068400718502007244082e41005407040502071440181025500c8899440b2000211403a00002d0320020411007452803c50022211a106607240001460981c01c040c4d0b9071f00c03040c00340007044928250200d0401c1905011a00f04103d02d880b54141400c040d00c02950f61f82028850402040000b8858914948207a040d2485110507000505560302c51000f880b40309460880310008111010381240042d142c50050f10342c000382c45441e000d41e268034003011035003000420590445160803c1000f160000303c00002e494010760054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 446354271 1250 446353021 446353027
    0x7090507050904060b030603010e0f03030708040f060f020a03060b07030e06160f0602040e072c01050708030907090c050c10020f0702090108060a060e06030307030f030605060c251a 79
    0x1040580301c078055480780075441403c3c10004141d800440d0051030103483c0903030091105282141c800ca4803800542c40e01d0407294000d000240906200d40c4140b46c0060040d000b450314020035880d00c07000c0e038004242c1d0096042d00090340b58501d039414810703400184100c1d00d08604003c6243e400503c41c46801150320b20541d800700e90252005800c800440110b60b11900c200b440c44058502074010f5009031280c1d0450805220006020b20b00800001148a80800d13822134000088441018084400021141007107020302001d00003851542c0218019113030302c230044c481c0c0b5103030212040c183d0711014040c1081090900c171455481500058094851516100142c0c48080c4907032420402d000303200020f035109007130100000b00480046030090194221010502190342c54030002c000c00201510310701d80591003040001c01003841480850f2641040303240100311641e80b900011490f0300702840043c803603040b178015000c2c5004400c803000382500350121100701c02e0345000951114080200b07070b0b414083d0000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 446355521 1250 446354271 446354281
    0x1080a031202041e08010501050a0b16030219240c09060507110a032301050103020d030c020307090501061101150f050d05030d06090209040e0109110402070f0507030b07091205070905 80
    0x360183c4000d4461580e510121039103000c80940c0490892180701140d5207408004902414500d20f01404e54002921684c91b01010940c00d8008000d06a802d800714011280c9205070000721454030b40c40140581c40480c52951041502c44000000d003d031290100e10b45400540d0690704100c000e0115000c5003840703900d48450781490071b00188003011560340300012080200400c0410140034420b07084180d4a200c940200305007032800c940c42804040c2d40b14049210080000f44151950031216102405407021942c3d0b070148241501c2c001c0c0c000c8404620503480c8560100307000d1150015041a0201180a440c540700c0382c4030512009001d00c03070103400c1e0210b0140520408004480c2e0700c036158282040a01c2e56401480002c0d00300c0054070380b00341e081c1000000c800d2414051041a03e0704504101403c19450003007200a501041d8110380b0a03248141c43d20220390140720708c03801140105043d211030324003e07400034210003041d004021110003e030844000700d200040d0b800c059070b00e0350800007840d80320 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 446356771 1250 446355521 446355557
    0x71103010f0c1b03090e040825030206060402070212010f05061c21140406080103020f0d20031002041409100e0610051c0e1908070605060d05030a020706080f01080a03 73
    0xc1500088140d461800504c0b0412503904000c0c007001027000e20400c0841c07400880040d111420780d40240c01a4840d0011400d40d203081e6004241c00380c402031010a560004101c890300f0b5540605102c0c0789156103600b0000030f401c141c003000120020014074140c840b13000341d07125848080321407940c0078115410b40f8420301683c00399003003e40801200320003a844660315440200401800d01040b0f008511042d21403030b242c20002c0340701900719405440d211045103d08044026010501402ca905100b0045a4038100c022440240080c012024100c04c000d1008000d01c900e0030300141c035006c6e404000303900030050b81500486098001d40101c90410a180090300100d8441c0101400040400301c1d80b50321100d04005548030710400320f4060700f0789503a940e82c43c550088100c0f28103005060b03141d0411550b40020b596610080d807103e00203104080a520a40b80d040c5190400354003e009070340103020500c1034581207040e030303036100182da41000c12641c18804490744903c001c9c44000e09201c6814001c0a007602 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 446358021 1250 446356771 446356787
    0x50709091709040221070e010801030b1501051603030518030415120b090114030f0712060b03070308120906090a03140702030c030d02100b0f03070302120a08071103010f0c1b03 77
    0x581c81d84219040520000c5446018500303030f406c00003040310803030013112650041d2000c038102ca4102400d06403507501d01c003507a5682d01c14540303202d040000030021040944c2602d1803510016000b950006194502036403400140c920720100107650754428841040541c0c01001084040c02e8589080c554811441100c1c074081c00c0300040050f4000030340c3c0008110010800c20440c01428104c0403603040800c808107454032a10303540203050140a8145407800400d055822291a12a0140448941a54944948403181c0040075100940324105c001e004040c2420840a03030003001800c00360601d0381302542c0c080c04a003401c40c601c40780c58002080040940d902440310008044005d000c0e00c000a10441e03000351200c40c08164000b41914040800ca0a41401145400c15140c0079000b000700ca800c540800c07000d00421414900709120320720700240007030102c00142c0b1710b9a11443e20300400420903020182540e200840c645032551070310003044c034001e031f01c0305c0c0724102585235228030710700152241000c5640c60 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 446359271 1250 446358021 446358037
    0x1814130b0601120b1005190320090a08010f020c0f0303070203030106030902030115090e0706030e030313140106060903060605010e15030a06080a050f070b030f01211203090507090917090402 83
    0xa28480317011005c00d41c2041c0180302503030191200004c07071014110145e00300c810000f81c01580c90400044500d030590108014402c14000510300c24010380c0e5440090b0948090182000002c4c1c1c02241e40c0803948001c210710180c0854000c00341d070452600c0b2100944ea03020500c107140805844805140075510203500009044407403030180f0b041c2c80d407900400f00c0940360541200c8068450341c100060140e209118400c907058011000d940343d0f07111900f801141e0414101c0a8901140d00305d4111001e1a00340304d0f5200070481c0e901c440310710500d942002e104807452580003c0c103002030007490a01e95551080c1e24907660164508050310703074540035001c0c0000c001075003014820f4490b044100c428400f000800d5401c04101004640803903407242c0c1d8294071800142c2e8542d1480c41a48018881c2104102c619289440085030300d0000c19042d03103078030109003890b0449601081c1d41d06100130601c4820310050001e0064610f0511100296544003040c0c800d413041031f220300c001d020034444003503519034049885075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 446360521 1250 446359271 446359279
    0x17060109080109110111010209010c02060306011e0c0b0f01050d2319020411070506131e0311010b010206090a0f021305010807061e0c06090203071814130b0601120b 72
    0xd900f520300744030034446414151340811810f44940c0c00301c4005000700d5080020695520600c00800e909101c2c0940021717010505001084001c08416011405001c214100ea59145880310700c4500308600e09030006000c0168041c00000144101c0c1c80302c0c1c1c40103080a60201000501040059072a80c00c84510f81c3c9010381809881c1e5000a60206d00b1f02011206008a40401c00f8044c800c201041034442d0003c014802d070400f0000541c49503e07808442450742c011100410720640a002004180e410402c007100411515800481005402d10032003981032401c0c0010308a80c208008266030300c6c000110300602d0310280482e0780b01103446005088a01c1c46007600c090246507180c500d4240c541003c0d000c2c80c0d0002e440108402c5c034100c000a01041d814106803107003420021141c0712903019010441c030580e01486101d40024a119408110304403410300d2840000d10401810140104448054441301d01190760070000c1d404244041200e03504190300342401c0819038030203000350002d400581005640 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 446361771 1250 446360521 446360531
    0x30108010204030507080105011505030c0d0903080906060a03050715020c0d0609050d0504030b0112061418070803040e0708071211031914010306051e100509010f06170601090801 78
    0x2020015005407081e648a40245c40c01e85444140c01400ca820034490307040180b01c258030300c0304560b00039001160444030303804a6a01d0115000f42002c10b445241c0c1084000a01d10820001c8124090203a150841d00448001c100389255845895848a0600600d442c3c028002500130201c0c1c000c00c0000242600901a0702c07401800c1d0418500602004ca82919140120b00c04000024030880c01c48040c0ea900c069071050590a112011180f42580301080b2209030799041100f804028045140c0c2c483d4400a030040706031f5010900150618125910848a0307500034003050001040510000d60311250a142441c00ea907a603080403521038a10032800740e810f510b44034011006100d0400258400d50200703282c41d280c02503c20861048840c50003202488141110044c00000c1d6141c0149401103808a80c054203810b002c4041a6518001d444403640fa11807108104072504068500034010038400c0c0950306050328010000c3c1581070750310100465800359000241860f8050030b00c0314040c0a103800200a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 446363021 1250 446361771 446361779
    0x3110705043902030313020f030102070f3c030e06030a06090c05040602030d0e1f0f0509010203060a060c0201140a030c08091b090a020d18060c0512060105031306020301 74
    0x1040800580c24420030070a004552095803040803404402c01000d80d00841c51684d8020502984180c03102040342d00035138180b00700c0303000d50b0240050008103014042500041006181040030003d1030258040c501014106418200c40c080101495100b40e50711101c281d4031036490101d480d03240c45070200341d00280100a000c80c1c060540d20007002c0d101c020104005054014909840a00a501c00c0c000103074803c11030001c2888003a0804c100300600e1604880403d6260f103d450b040461004078242402d41d240004d5008000300c2c021160803035800e1000718031718244000070072152442c6003c0c0c01c0c02c0c4607001c0101c10441e486113140340d51500302c289845844549201008024000071505107000074910000304050003c00719200c11600420310b070380c8114029540500050560017410310140795400e006800c407a03a0746008000c0003012607014400b041c3d5003840c3c40e408035048580e02004100d424410402c6503040405da0300d40085090808540300c0d84c801010710300c510343d5800001c01040c00440002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 446364271 1250 446363021 446363051
    0x6060b030c030f0619090c090b0a0203091806060318100507030c03051602210f070605060312070b0105041802030f0601060f03090b0604091b181b09030311070504 71
    0x90b00582140b0100b0105407600740c10461000903c5461185524201c41c040000740403d0b4400045487c246c1084140c030b6555212143d03883d080009264056000001c00c81624500031944d01582000b03d1000e034400c5c20444d000c1500742c00002c0c807490a0200ca0b42c074134410700004000d0040142c84403030007401240341510740140601400d80022020034100703804181d504074a0b540c441d090390300701d6004141c0311243d860900a4018240c1b40c80070912000c0000300c40a0300308000a086aa001c0c010100c0d050070410185858608840000d0410000500803240020554440c160445808a6020a00b88400c8202480035110418002c2d0b0600c2180d0411440403004a200360403a091916040e040141d100810b406071075243c00010000300780f80001482503c0c0070350011402d54028650191440840c400c000d140d54456044030b840d4590300c482c502829007190051481c401d00002140c00540d4229002400c00801070200a0a008140307043d00030800b000c004820040000606c140705c00222a4020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 446365521 1250 446364271 446364277
    0x6030e0709090c050405060d020d060c030b03030706050f09070311090c04170f010615050301051009051503060319050d03110f070f0203060604090203070e2d1005040b01021906060b030c 81
    0x1584c0154100400100245018810323075414680203403104100c03419a44d10030340141940001c2c2c0061541d2185142ca0f10780341000a08401c5100700d90005590800c18200240100f0080041030254000e01040c40081c5103402d24240c00d80302a01e4001160311240c03400c7d0110300580d040f80041d18030008240310006c000123840c10340d0000d190001c20506455500c1c004403008036030001004208204010041400c0507145003072910060315001d030b0b4281c3c0f01c600040e21a07189896411330743c0800300c2803044524003444040c20002108205842a43c40c1c0d030350702c075101c0711030307990050605a032101907000d006500b404890140030f00160103550f80d1110f1030035280c040e8881100740d010348280380c00109103003054812080c155400400618115140072201a0700c04001000c828041e44003103885203400c0c04e0300b4440070034032140c035401000303e1602d0a031200f1034109950210744603c1c2407a4680d402c1d0390300802c1ca49045174500314000b0400ca220300301100600150b900c2901120400010404c0a81c480d40103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 446366771 1250 446365521 446365529
    0x510050109050106091802070212030316053103140120090303120403110d0e1f050d09080f12060901080d050f090d062a0201060f06030e0709090c 64
    0x10410103662900c40890894209014030004110740305824814100c0d4914240700c443d0320010054030303100c130710342c0414690f81101513507000551010043c801e80581900044101c0c81c0e4030300d4841d080a012443e00c54885400d260800b1805110034148150014004000f074080d5402109014658103403000641c020007140404a4a842448000c003140c200303042c04403104513400500035414024120f0260200d24006401202400744207180c003070100a040c007042c50400c030301e500c07449115100b4900b030124415000f480011584804e401840c1c0d400e40280594022190740e03070340081e001a59240100d910300c01d900c000b029843c4045080d00050f00458665442004152040151030340d0311a030b040d0381c0d1020b00d24100f021800c18000d00215403003920240c02c44400040c40c03d41542919250b210498440340c9e030200400031180130013002d4000381e40c60b00403134200a1000700b0203240f8144015500250078000c1008142d169034100f078400a04000754006800316503c10040102030b494000900301176071103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 446368021 1250 446366771 446366803
    0x331106040b190501080c22050a02070209130302061609050901090209040608030408120a031118030d0203040e13140717070b0910080c042607080a020607290405 70
    0x802d84032201282c0503441c129018180140030005040042040c0c010310110112690b900724402032a101c0458001c840c01401d52130401642c40c2030b20b005100e010ba0005002c10f4840410811900000b86d0004004c0e0340311540c1c08100b40309032039034501110003454560086a0242d03d01001042c1d409031503004021207007088400300305080d5542107098a07070280e0b2003510342c0c030340240104050365440c2d9802804038010a1030000780c00b8108030140d1145030801000c5a86035441c0c0c0000021700d0408000f460390b0740e0036038001503041034a0f00070942100000105400d5001210000c1d6800700b02986012140102100e03054951040e00c502e950310404032140303810f60312071003030a0700003034050b0f4508111010ba100c05000740f2403801c41c2c41c106507500000075091900500042200103500141908000b45240400b840501c80034500c0c3c0006150460540083c5180d4004c01c04150041c5d5594003283d51040c3c6c0002103042c0a9111200c62503200906202e10603821140320070441003000200308010070b101d0800c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 446369271 1250 446368021 446368051
    0x905010b03030a120e0c13050606130b130e13140f06130c0b030f070e010c0c06090f052e09081204180b01020601230a030f0507331106040b 61
    0x1d000c656480017001da48a40000c04580e0001d8100347c25001643c0c4060050700c658078141c4a006170841d000490b0b40031407900c0c0d201040d1040090034100c050402170803080c2000b291070504402c1208800b120040c0100b840a04107a04802d00109009140c0000b014030300343c50582c54a450000c200002003101200c22822011022a018a569040c0d0340078840201c1e0b00d07400395032001300035186541c9480c01541440040008240040c1d80310400002a0210381d8402080c64a80303440b441c1c4103030203500302c2445a02410150140b000c038000501145003d1400c1080e40c050329204c0550f8442ca10707400103001c1f80a00740008051080610007402101c44520b5098410b62180344591304689941c1c40660040e0404001040401c3c1c42c5801d100c0740102c00042d049100b41c2900021b00030282e2a1303c21104050304111520500200707010000080c80c0c4283c4031082e400503015011207070446000c003605041420350001000501c142915542142d48800b260002d0400341001500017204030b844900c0c0600203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 446370521 1250 446369271 446369291
    0xf051302070308060d0f0f0530070204180606062c09041101030609140106091d0615040302030109240b1f020f1b1c080d0905010b03030a12 61
    0x14821a5011901035030380000c644c540034200500744c26074450a545002c10125401c0110f20404040415188a800200301040c04455140f403803140c200744504810914801c03828481d00420212a01d842c1c0c110350025912000f811061403c21031410040c141500e40040860280c2c0c100141003000c5000b0b81c01d13440040c01d88201d401440c1424140d142e00000100c0100d00001c111b14101d200e80c1c84141004a07411340c54a886000300d801002c03500040b10017840042056035000850003020f0107040e10000e801520400540c0002000542024015400910241c80c0210b4030700507140690790081c02070103400300c94140340c4480051004c200c04d00d00a281d4030039213404842e1042071061040a40600551000000042c1c401c1540c09011410b600401c0501018844144040a61142d40b14000e92581d5104010300c49039041c098a6140c42d44903141c107050104901e84180c5216428000d0b003c58038804500d44540075042500340c0580500c0f0114210080705c0d00114074510542008030104040014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 446371771 1250 446370521 446370559
    0x21b01060e061c03030b13020a0323070219050102073e0a05010e0301060e0108030c010c1701120203010e01020406030e0609011802060d090f152d23010f05 68
    0x60442d07800043c244044000d030010340281c005090880c00201103800c4000744607020000d170b9100200e84270010707640340050000100214400c403d02e0740100e003107244520f4107a4010303580c2c44c1214010301190003010000300403c40c003501140d2640b68041400c1d821a01c00000c901c9a001c101e60350b82109820aa05050202d01e47c0112510140d400400070104c113850b110056940341c0c81403003640d4055480341c0010035072003507090354107000f819020006c65941d1402e004042c2181c403001000c60400c05010004000c180030340300380e0f60566003040f00003103c00781d8520000f0300409844192880c0c1d54008079000403820f4140e44407035035a40b8018166440d5541e1003c1c85401c0350091040403000361043d0740b078900036060031805000e03085042480080c0c403a07040c1c1c5500c2c038550310200d01107400c0051290708802c0c4072018000c1001d060103a01140000c0d0f2282c1c06101040c24980b041d01054545c0c8a4840c00c002000c0c1c3d5207004903030400d07011a042940c41340c454046155180c081c0130b004204903040040c4800b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 446373021 1250 446371771 446371789
    0x311010c0e090c07140a030c03201f0f0e060603010b12071205120705010203061305131209050d12030b0d0b1f030b0a0605040b06042601021b01060e06 66
    0x20051050480e580c52039003c0107160043d12059684040c0710f00c40c02080003080211102141c0a5104c41052821340c0c40e0041c102d111610f00e03022080300710098031051050009002a20040e6440d0345030302005020f0f035a1004040300c501d500341290a001030741d0b40040d00482c03c14081c4509800a010024160003400701542c6503032400d0b412a030107010100b06d1072500e5034180f006640b155069405610051112074101e0300315580603034003a50f0000503c5400c2c6001c140c02041c8441905081c88607160548458554032380d0031101401c250078035040718084511441d040001f800004184c04840b104505100f01c07a01ea001c4040d801013480c3c50b58074000b5240c10316034003c4240d8007640981550740c5500b0b40d0008500251800c014507d92404080005114103101c0b0744100f410a20002d030b95440c003c01c000540307000402d44d07400f480041000f400b00c2e4408805041d0202e05501d282910a810420220300900c22240c4502d500011490705600140b4190070541c104c4121440e03034040c0f40c64000c02c00c44011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 446374271 1250 446373021 446373047
    0x408030f0a020109050d02102009010807030b0d1a1012030f020307060606110c010e0303300f04060c05040b070609110a0801060603050115020d1d06070311010c 70
    0x540148001541a5040e40c01085140722510000c04c40c1c1c22103943c1c25151101c2030740404056000a401002c0d03014051107120f001e4020400d090101d40c000d40c0303408440d40b05400502c1c2c104084200001c3d0040e0181d082507403403070009481000b0004082c08c01103036081b101c03020144030032481c0001c54100d0319041042c109031007071149034800300d1106960585c1d12340d406002080a5000501a550203d44144500401044c80c1c0d02c40d500010700d424074040c1001d10b80380400f41440761599030b40025480020550301060016030030351042151580e0002d0010100308079102040000b00b042054182c2d090044030700541c41800240b100e0541e908041d2410302507400740c030f0403400c030911800011032826040010514081c8802130f5544840c01d0115520380590b400940c0d030340e074645908000d519454801c0a00401c550320200601c2d00c0c0001000391030380c04003403411f401c03c0b841c142401e00346070f000c001894600000500c1c3c0340c1e884540d1b280c06424040c40b0340041c50b6651a120200f60341c07038001c1c4210340643c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 446375521 1250 446374271 446374273
    0x501081003020a18200a120c120e01060f0803070516142e09050f060f0706021b010207060f05011707180b03030d050a0c050f0f07170a0f090b0408 64
    0x40b42003446000c600d40c034155030300c00165183c5c003040c20412003030b50650070810403601d61a50b0ba807590f45070107014031500e100080e5500d071a00800a20382940a0013104e81101c82d0300e4007041d1021809862030241c6480d40010098624184c000a0074420020040c195a4400c1003911307aa2107800c00800c88800140c411b035039144e410044000200c1c03405240020036011048410f0460b00d21016492100400c86c1d4a0180800c0c600001030090307141130503550b01d0001040700c0d1140707041040c0f80d8100f0940641c0e08001d111680100f040000e0001100c030001e0880307003020086440380000d04201c000351500805500c4c1503403034140081081c1140e0248a070130448018020040b6510f440d80714011071052800c81782d142952042d0589090740c042c00142500d985681001c0741e07600b089289201100c0300d94221205202d820130903440c1c41640c01043d11000c0551500d2a9100c003200c1c14240d240074008660401c1e69000016980d0034941c20611800141c100b40d52581a60340d1500032260961085004510071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 446376771 1250 446375521 446375539
    0x302090f070f03020703050c2e02131401030618022a0c0906030f0706050d05010509040312021e1c0e010543080f07050a0507030c0c0816050108100302 66
    0x410f802600240945882460561b142c05c280014543c14504016000c8180241f040d0400d00d1541c0c03280203807004258080d0701140b4151304010342c071714000d113a0f1150701442ea20700f404605a6038000e500070401050581d4030425190f03180039811009500510421488849a8410844034070410f01c601c2c5000c4901002400f054100b0700030844402c0b00201841d40c54803030f0151011a0203c1448248010012502c0b80e6440d4010745d0202029190305070081401130f8440b2003080f003c00c0c0e00c07650409101e0a0401c0050362148d500300035410400d0721100041318221f0000d41256440c840c003804058404a00c0010817004000700b000c02d0a84070250303161500108600800301e881802009888405d003803581e0088030280320b50782c4644030300100c41105d502280c018020404020506c002e80e580c48196864041d140c40c02c4088003601c113000b603070405803c204c0648150010007940700031031409041200100c03012070041c414032085000090184a001440141c0031a1003981d40381d410074190307a802410303002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 446378021 1250 446376771 446376797
    0x702100b0d081c0c020c1305040c1a090d030c1203200a09080a050a12050c0303010b0c0a050106090f0c08010e0a0b01050f070b040c0803032503140c040302090f07 71
    0x10b150032800840300c00b80e142c01a640d031901d44038071a100600c4090740180804801c0c403010403560040034003103102c4c0740342003408110000798000402d4003501e1310704620500c98400b50803240158010b00c030001d0340016100d05a4002c1c103070098043e04505124007004960f030401030a044054a072402da0078200c0e680100909503e15081e10040c05c410202494103500300350351421070b00c2c684000d81505840b41e40010001b9001c1c00342c1c5e100001c1401d0306606095141011021101c0d945c1c3c48140705458161101141c181803000f018000c0020490300b00000380003031900c84010f000144540c041500c0007074030300080d42070201d0080d00014100c944207036085402d030380c4080141700507140c0e41d80818104003007080911034514160700a400028040c01c04618103281c00e00c2d099001e10100d801c2001c0740e900a10400007004003610049000e011020101e040d040000318043d0b014150024040e184008241e040003144446407001d0800c890089602c03050f15120707040c1a4240307440c29603405e0001209105009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 446379271 1250 446378021 446378033
    0x518060105060c031314040e0601030807030305040f021306210f140114040f03200627030a0e040b100207030602180a09050f0a061d06040905030a02060702100b0d 71
    0x5143c54858007070302d03d0b01009404901c040801e0742c0003111407481002042d1068181803291031201801503000b014035504584804841e809001002810107480764002003c00805c1119446d00c5a070251000c08042c1a0406100150000340610301500140740540701101c080c12540301e0410b500412208034241c500e131a03580312404400f060496943d255444000f40c111b4840486202724011658400c041d1220300c4c1c002c01000001071038072810810b000203102d00d4180411015007180d03e41c131101c0004181120180045030705056a907034140030120340700382400d8000c2050318810304100c9040114040350b44c20092a1f8a82480c058010303441424244001201076000380a4030408076120802000d143c800034911011703e03000000415141c2041c0520b1400000d40950046c914980a00680703003031a07100b40c101e410032408101131030b0308079000c504541c035a680680c1c800f03900901540c1e540c1d030070300d403002e5500c00b020380307260340180300f5490744120500681c0f242c00502c0d8402804c800c000c450300d460b00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 446380521 1250 446379271 446379277
    0x60f09112b05010f050901171510050103050108210307051c020c01050a0b1f120507020c032416051c0501180902090f1012050c04051806010506 63
    0x8011000c4100414501200c2503140101411158003650560540404100056030350681c0059900b0103d9141800603075030b10084c05042d2200416100c1141d2080c400d19860111f41c56040c401850040040c01a5902034024070819070b0420389050100b40d0303960701d0031030341c0b5040070109004102c11980301d002c403154810004d680011003172410703500340004da4410140001004c48100e2700c00754002011540b4450a006840d4440f04041c0f04028400d03070040415128440c9156040820301d1300c004114425025029440c45042e21400421682ca41485c010f0b55a00341401c1c00c5211703108030000c00b040c280d41e43c844140c110504040240c1c183d00c1c2c0d850700303a0700380a85c00b0500d41801014480784071042d60128000a501e44403280219080d45000498403411180b1103a0a03607040c09c188501c0c0c09078031000341c45504020101d0108030255502c0c0b0b8007075400716107030f0480034078035494501442c20701200040704407061400312410011600d80c250210070440c0d000b03074441410703080800100410f243c0318000e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 446381771 1250 446380521 446380541
    0x10f06090b0702090915012702090312090105041d06120d020304090510050d0b0709080a031b111302180901150e01090803121512061b071e1104060f09 66
    0x100d03034900f02121188140c00009800000d242380040903c6030b540c42d2005031601510030000411450036003c500425200c3c0b050b904409412100001c08048a0b4401d008031401400d500803600e03a0442503c0d103020090030240e03006480b40d82c0c8a40b10680f05440810748441482190700154036042c900105a0b000e00030090030082c0801100b02c00280e2901d50554161110744184903039011890000c502a0110141d9001800d20340e000081510000e0780018210760f04211071204c0200c0c0c040d01d0b15200c1d0400c12020101ca13004454135181540544060b00a442c56a040301051110100d2000c00d00c81c07081d01c244200c851201c1801d0a107903500380200da481150b44418942a180d160b1162190f80c515803041c0302d4012010146001c1140306084040000d4018804440300000c20311034041565035210043c080c00000c101404a00c0c0c4103030034410031600540e1f03200311794140c40c501c0350114021a080240082c0c401041c60318015110349424450803003550b0609000f000414140940c0500414490807 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 446383021 1250 446381771 446381773
    0x90c0801090c120903080f07090f0b160f030504140d020901120204090629060403110907052101060e03120313030203040911042603160312050f010f06090b07020909 72
    0x803903a040c590703c0b030003050a1203002c0d84070202e003410100b190440d10040280100100300c503202060000612004007001120002d14189032612501c5060254980c0b40c01c0c401071010713100524043c20541c11901500403501203201f18064603d6007403c5c40f40500c0c10080c002d51140005005001502c101207000b081103001038000a074180342644c0d0081160a89052503040100820610842c901e4400074011941400e03110181041d1840d6034011146400c5c0000300d110710b01d00400550350b03511800c140d80d500202190243e650003d03000c0c000070810028040d000006000e94510301039800c3c0090381481401e0260005031556031002c3d15060740800807803045046000411002070885014003d00740c60a88011240e030b5607610382880d0410b4800f10407040080e803d0039a044041c1d68601200f92039541c2d10103014442c020341c981c6802c8039040740e02c40c81c0304901444c00042c0a4000008154103050b01d0b4080d92159015454500070f6501e141188200c90716034104100c00001424500c4680b81c1060b0990 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 446384271 1250 446383021 446383037
    0x206010e010503150a1e020423090a0504020111030304032c010f0302090406270507020d0207030f020402190801051e06090d06140a0b040b0d03121e0c020109020307090c0801090c 78
    0x100c2100c40c035540340018142070700030074240224280341e01210004003011a00b408114009c0001c80c02a580003801c01ca46640c0e03d000080c150f900034120300103500042070640740c0d6881c2c10b1a01400394000c41600051174a2401000605005d5a001034408117805849142c0e400e209424128080d6100e201810f070815101c0000080001990a10b8501007045481888091015202e580215040140040c0441d808048114912074001c83d05000b03a036008806190341606c28008034021703200302205000c80001106980400300c2c1d102d203034541658000c40702581520b05e9404552490310b84111415031112040040c042186400c5900d2031404d032268a0105030091191207203001c0340300c219140e040312921004104110300d802e214491404100f211441b449501755200102080561281401c8140d0f40b101c000c00042d0380e8203012100301d9081c2000748003180f0036400c024040c240045c0d040740244280da001041c03c2e8014019503c101403141c0d41c5645580c40c0c00303604e00c003400d8200710100900500c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 446385521 1250 446384271 446384291
    0x18090102040504020703020705132d1506030c0807051c02130302040e03180301050705030105010507140d0c03090f060509010c060920180603061302030f070e070206010e010503150a 79
    0x24000b5151281c0a034025283e0030380303080700740183c4404507400011180d01d80114159560361990303201d003540200214000c0c8a28002f203054000f03001c41458680c50707600c0943e00046407a4143c0041040c0c0c00640d440d00e0080e1030302c44045e5050b02404503060800161030300c84004007040703603020348803040c03400070310400c1556a038000c2801c5400300ca0300d4801c40d0300300061344c0d05c0c0c2020200c0882d2801800b54000c000350f2403d80e4008010f4001030140c0d80c1003010006005040c4500d111403902294080c0054505618003c9c0700038040c01455501200440c00500000940c07098081001003221000d4407100c0c60000144011110b0791042c45080f1001e55440d45918042038402000d140600001002c2e200c4000b48401008004580460004207001d0b0381c03030802400d600e010824075040031003895414074456280c40046c4c10f0400003070082d40b0b40d125051000451701c03000c03000c2c40d01484060f000d4501c9030340c0750308860180341c409008881e0541d201d0b101100c010715000446503800480000001a11166 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 446386771 1250 446385521 446385529
    0x1e071a072a0c0620030405060412030507060c030605101b0201050351030a03030b0d14010b01090503240712021b0f1501030b0403090e070c06060b0306180901020405 72
    0x240c03c101c000401c3c1c28544500c2c8a8002c1644100300c01c02001141000d00e0040000c400d8400c0c0d0046c0840c0260601c2c481c420180600181c80352079a010800703020b030b900065401001006140b1420380310b01c02d0441c0c040c20880c00341c9407c550a032050100c2c40400d5589030019900b0358000b030800c03010400a44183c0c081640481c078140b405a01b1107243d1040c85034009240c95555032440c000b40030f203101030a5030b55110754002844403080303581403c0103e00303426148000381e040340000707001810004044884480150040d8410381502000340c80d40e0645a44035020b05548840341501e0600c0c03d20100b1003031050310780401c0300e9944405a0f191600d15042005056001d1fa04681c1e001c0640c54040320f842e807184281800360010000c81d49004005c414814443c04d1808001031102500454251020505062064001d003002c0d00d01c0102d40e00c1e00d828601401031048040d2034094840500c0c010740400c468403680c0441c1d024480041c14241c1c01402c40320300c06142da034068a10142903508220029460722 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 446388021 1250 446386771 446386793
    0x1a070203070e0f0c040e06040c0e03010e060109200d091e031211090d08070501090219080c0303071a42060f0703050706021e071a072a 59
    0x31507900b0380c40381014180c01d001220040c001c080745400910060000510720043d55074032940464020980d000325801c140d0781507101c00b00c00ca401d5405e0000c1d411000d40c0018445040b54540758040164240401d1100d60984010703801c180032060801000741c801c02c260704a02c16090150048801c01c01c440b00070a542d00400b00000c5010814002e24010005d24911a40c4100c01c3d8624a8918184040002070414500603400410002c0040f03110000e024095100040310355014044200c4030713094140c1501d00d4801c600c2011080c0c41881921615410080140c41c01154000c00141c400302003842c01501000d8010540a80c030b907000c180c81426420007042808010b40300b060001039400c0c0c030146d860b4000c005a4180760046008000158080d504141110f0070a84c1615209031611014a400800380c420803a01da17908200303142e4045032840c40e050041410f41c2c46441120f080181a00324280c1400041b90184040346400300c0d003c0000c507c0059141c013403840101c407408003408580e1011100c1d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 446389271 1250 446388021 446388029
    0x41502030f0a0c110705011107082b0201020c0a20030a08190e0d06051801050106020709060e070801050405070201020f0c0303090606060c0604030f090308070614130b011a07020307 79
    0x1454402800008801031158840c9503d851810020f1544007600141d078440c424819107041010400080b0452001442075a0183c071003041600c40c4000c4c3c440c004101c071215030b400c140136403c01c4403088049030300500c00c03100e07019040070180c280701c081a02d03080c1007248010429840305504415905680c0d40a200751843c1c580f0030400d507a20340c8804241b01d100f00b40303a2090103091104000e038428455803009503101c907056006801041903950440218044100015a00a61b6080000119015801066400c251000410104400ca43e10852183c0c07205042e9040f02c08250b0300c4d40148441d04003600410340c07010641c00094600740901038030706010f030f004512001c0030350408011321060260500800d900440c04032585824410b403420b00e44d40304c0c0342c040c0c402403d110224007840e06650264900b180219042048551110041c1c10504058025210481102d6043c0c0c070004080d400d0007031051001035085a82c9620070b81c207000601803c4641000b40c200c05076014800d41c001690104140c1d0050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 446390521 1250 446389271 446389291
    0x3040b04030311070f1e0c0b070b0c040b07060c030b1005030f060103051e060d0b070804060506030115211b0f050d030c110a030501050106030608210306060304150203 73
    0x50315090900030210381c1d4030701084104001c10400c6502241c00c00f500d400c4980d800421600c0302d1001c000512042d611101c3c0000d01182a180c40015490200c8000d051f40c3d030300a080ba0f810750754902c0b55100d0320744031768001c50106910501c00d01010407583cbd0300c0001110203508002a0356085180040c080e038021112110000707074000100300d6500614241c01d904a18282814006400c1901c448084c404078040c00031400b000c91400202e1741d80c1c0e0303110805509a008103080c4060705003910010300c1c46408035019280c1c80e0521000c40c1250030305101f0780004200540f410301a0f10300306900c0e803118681d20811984810400c01908010884014030420715500000141c20124900b8060104440407079009030310480708180c1e1100400d40145241201c0e6900c1600242410740c4403000410300d041940001d0650343c601000410455015413041c001e0301d21110458060301075210004100081012070802040801d002040c4e490400001868100c1d1207600b07001803955180342c5410498200f200c4002d02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 446391771 1250 446390521 446390543
    0x21020127060905040b15130902160501050f04081b0c0411040f0b070c090e03070f05010b01090b0310062d0305100b12150f0613051005030411040911060304 68
    0x180380c11002c1c000007064295814005420041c0004a0b141c525410511481c2e40024107440c440d80b1829110002e05030104085441e4091516103604644441c1c0c011030300c0c0c0d840c01e004a0254480303640c8442c03007280c4c0602c020745098242c85800c1608a0301e250304000e107208203240b0f01600d9079030b4015101c5042c65140072036161403801c4801814510356900407101c41d10300b006801d000c81c0201d8422000e07240306040202e40f410341c011805245203e100e101800c8100380d02980d40800c441034010035901c650990368586404e464207501409480250740031f122144c4c0d05981040200e00410315405c8443c1004005030040ba40000031000c2545480c44000c0001e5840c4100400c0800b051071000107000e40c002e81d58106a180003e843c1c849401400c242e60704113182c100c3d0b1090340d40e8908030000c1801c01402d070589440c0b158560568008039406014030850b01041000100c1d8460800d0f64400c54109001240c01003680003400010521284181c0b00b26510207030340c1c00942c440300e0045008074032410103010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 446393021 1250 446391771 446391779
    0x60403061d2401120212031810091d0711060709151d13150311030d0201020c0a0f1104020a0e01022b03050c130e09100621020127 57
    0x10034240b898000c09001c140518181e12466048101141552411880304041071194000030b42c1c09544042c5010503840700103038801c09501445840a80c0003401d684ca520010366841d8107403844035103405100c00c0c032820f1240f940804cac448120501e0f0454140d044c00e402400342a1440e90600108490070000b040b840d03c0c0030054500c0c0030340c0f018680c04051402c402c4100c0341c0d04206129408022155100f000b1f00030401c840300e107003540419841c005004181101507568940903036240e040b110001d2180c0a05864501c1d00c3d0b00600807106d5400c414009006114182e685034030810b0503d83e07003034449142e40b0000c028651114401402003070303243d48031403c4d0042d07040c000900c1c00360701e003c0700d403246100305d0803605803130002c1e2176402c0054103075090105980c0e031040c4018816003d9400c8440842c80088000140309405040040c000c142034001e8404c03a000c8010300c0025036800b44542c50140030580a102e00f0600ca000900404520500d4100510400d1b800e000c5035a0f8200b051400b4002c581003c104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 446394271 1250 446393021 446393023
    0x120f130e04050d03050c04330c1a01030f081806120402091006140a03020c100b100516020616051005071808120319020d020301061b020d11060403061d 66
    0x481c400f010b241c1800039142850310700700c0134000d038807921200a481c40401d10710015408508000c280320494821480500560001e000586403c4140c480701c2008072000100c0b04032400c01c2c0e050ba174000b81506456034440e6211056948002c80d010b113500060010108545da412004004a0744034030080e031006e00b06801081520354016200c814400303500c2030200095500301d9441001921941030076504c503070592805802a00c6041880f4a60380111420403400007526480b1081d601c0d003e0b920b046047c101c804056425100301c0c880b884004c40348400345001841c12000130890215210400301c903094075030703454600d03001c0000002240d05440c1d404000400d0352106a60044000c0f5035480700c015458400225201c4855159000c0c03004000400210850b0003801c400e0418610903c04668400b01c1c042d418000703420a005060000c1ca150443d180525604200a50600e030020f202c104803110558910b0303104ca644a03c0d490f00040103010002c0840c00b80d00c220301c5c1e0200c4061000c40300f510800021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 446395521 1250 446394271 446394283
    0x1060f0906060e0310020d090203030c07061e09180603020916020609010b0d02091005091015030207050c010e040b030d0201020c10060807030327090b01030c020c0102120f130e0405 79
    0x55410462591000e100a13540020400744440081c1d00041e583d6a690758404080c3c50040406505403000182008001100180442c21038103c3d60f15001c41d140c0100c0d202808802c0d0300090b50000d4422030007400300d80c864410f02180c00108140c0080d00954903404034042c0341046440d03d84103030170b0125041d074540d014802c0d01c2e40080c204000304494509400050400b440c1120b0182c0140a248001056200f1a08540025180040510032685031981440654074618024554410074462200c0c03540e0b03000b8001e80c0c0c1417983c400050a035207017103000111820143c021000d540942ca541d143c3c48991800d20110204554950000d80d480720700d45800c074a0000c12540c0ba0440501d03200c010022020089901c0043d240d0500d0f1001c0c21400340c41c0c18201c94412080c503920030004401c0700242030300c6250b02260b41c00301e082e00d0038000c0c440911002c0c2e0303e034041c40100b50701517003000c003074000d020f4904c10052071503000c04152141021071900d40b40c400c5424980002c6408140b110600003407001c10801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 446396771 1250 446395521 446395529
    0x712031206060513210614100608040209190f020a090e100f1206022a100507140c070306090f0b0f09120901050c120405120c0f0d0c0801060f0906 64
    0x4980d00d0a41048509001c00c11144a8281c20904190441004a96201c440c1c817405030808801e00486105414040040000361200079100e46410000607946014850b17051180e900141141e142d681d8004d01019805020603880144654a50080c0c41c03040320352002d80440807065850f0440b048c1001000c00c44004042d003040c900d18160b8900700160224120035006580e040b044804042e00d0303520f05980680120a00c617034140e040000d01d0f0100310092070034580589068022074040d546108030b401c1c100c5000341c1d90740000031800640e040c6500c5900000f040707031501c00001c80e0f00050717680c0c5890044840c8080211002e151040408003840710040806400c501c0c0e03074081989a003800400142d031006882044e0919020114441c502d582c004d00c00e44100c44580307015a040903100c0c0100c0826a07115019141c420440b0096950844100203104e6603407103000b0344200c4501000c2400c000d92425060000c441a1207581404102240280907260041c1013118400b07a086050603403140641b078a83c0c02c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 446398021 1250 446396771 446396777
    0x2b0c0207090b15131a030a060e070c020f19030507081e0c0906060f0d060501110a0c0b03090a1502040f050607030806010309050319020303061201061d09071203120606 73
    0x2101e0505545602c241c3c060b11110b80150340d0f46108402202c541100380c1e50000b0001111700305400300c0000000000c510868000c04201700403500c1c2c480348910400c080d0782c2040060b05050118006084c203808400140c20020078031110080121a0b00c0da880701541c004030703202e4009840403c004c40c010000e09007008030300c607642c04a20350a03110756039980340c0105040384901610004192a51503220841e0300d0440030b270107002e07590032445c1d100703002415040c85864001424009100d4007000d0100c2c5030301e01d01d030b40b0841c004021031402030308101d560000f40c119185070048503042e00005505070740ea200911414003001d07071140d00c0d144002c1d18116283e40000d028410400003540040c0e0700030394460307000b002424005031101c0b960408928600070394101d0581c481c000014406207580000145200d020101c404244641d0080e03d9103081c1c445520034411211801d03411208074101c6140815400a400422599102d07510a041000326403c020160040344000100d001c124060303000d28130203040142 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 446399271 1250 446398021 446398031
    0x3001061a0f030a18030206040c0608010b0a05030c0c0105010816050103050c0d240603020d0e03040602070611210720030309060a0c050303100f08010e030a052b0c020709 74
    0x1040d4000d1284903000c40d6600400400036450419030f50020241481040d0980014182494080d590b140291401c0e90580012040011a188600001c905a50380c01a060342045000700054580e9003010341030300e843c51000d00020003002024420300740241608170040c40290310803900d141c142d00150300701504140c1042c0400c480d28840350100d40f01440b2400d00080c03000304400b00041d005940a00c09010365021481c0096030726416005013211075020101004219400822240c0c0c1c0d1042d407207500c0141e00045030401200b0b00501607101d0108064003980c905880300180d20b400d400e01d1241e9001405804038403001440b50b0040140019040300344071a441407080030009507680640d410092007680d000035103021180c880d54030942c1c01e035844402c60b9201d0506071030038111030920f030150092100b6036002c0007842040c140aa54280c41c41c2001444c03900071480b41c11034080c0d11814041405c84260700d05124850328620541d5110b89142c4d10001d01c03c400000000d0804c22903902c4807041c24107107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 446400521 1250 446399271 446399309
    0xc0319090224130314010b010513050f0a030606060306030b09010b0108220b09010e01150f050415080d0f030501090b030613060608070b0a03050a06060e040902300106 73
    0x8000c6907060040030910461a190040010309210300c50281520803c0103a1107001041044c08902544520400b41c02032126401000044039a4041c2d44214015121103100801442c10080506665103a0203014641c1c0c0076201c0c1c03214020743e51345502400019503108010001c0c4082e00002c03503001304101380284240340714140001c00b0b60801a0030350300800502138a1814035080140138042040d44441d15100f0381c60150a80b500034004c41c00425169401d000d120ba85040e10160740c4416204d61440c811a41814403052100038021315a0010b000c1011000100d40107800304080c8440c0309465550321211511514000c0a40b001a4040d03200c1ea0708080400c40d0540d400319455502c000340040d98603e10480703041c044080d10055004c00b84c00d0290100104003501709100070480d1082c0d40d00d003800603031104c8803800100c07640781c410303a8001118075007090031b1454650805014940010405c0d982d0f640d410440c0c0745901035070300201d055400c1e0741009a0030404203005410082c035003184c0c3c0c06109640 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 446401771 1250 446400521 446400529
    0x2090c04120b0c09030a030815010804031202030c040e040f0312020a05090d06141602070e13020402091306060903020415141201061d041a0c04060f0c0b0c03190902 72
    0x4072007001400110b4020026040710070400075200c0e0260024225045450b0700e003005410503d003915400c0018680c280f4205107035000e62492402a42c0c91758075010720351000c508030030082d0006044400c00950400000440015000506014600a5110b040d000900389000b0344014070702000c00b0a0f00d80140081c1004a401c81c0507515106010780d404006280030f0f04e40f060007000d0401050341e540d0910028499407142494298507140915004c0380d00340c584601c8001c0031308034100c0c3c0b98110740840385031040c010b00305034001d0800200c000d4021f60701c240022221000b51541034000400041d504002001036190a000e14080c00783d02442c40e841c044e05244401a14107107580e09240104c071000039110102c5400d504c1a0000d110400c4a9000c0740001c010b03408003d041540c0a841c09000c0009424031807010918a6001c1c40b00c0c1c0305900d140a1418506035041030b034000e458024010034004030fa0100300360782603447c0720b1448640e10580d203240c48403400c0d0b5020309003135a80b042d03240381038591801615 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 446402877 1106 446401771 446401799
    0x20304050f010608120f122e0e06210a050604060614010206010512010e030c0a121b060506040605031506030c12061f050a030f02090c04 60
    0x40702050103400c1e104940500d00c0c09402c0388060314030004038000103040e0540e01000c91814111a58506a4080303800c5030804458103280b40d95404103da07805040840c4c00348400c2c0044110305204840e5281e0340000c104500840400c1001341d42d064103c5070f8076101c80404c000300d88011882c5e2401c1621000c0a83c2d040394014213140d000728200c0d02000c902e0040407410707402403821b41c2c600f004101403409007089903003065585901003a0006401d000403c1c5041c505401030440580e5450a0051b0f0030312600d5030000c0000c10480d007141340e421200007000183c1c07c00c0020400751503140000c7e00074562a405280d251142842e207500c1c084d45094503c3c441d14044094418600380310050003000001c00803410f4094000400090002c88400124036121041c0640d10f10003549400c0802e04c2400b003074105803059003503480550114640300c144c0c41d900c1000781c0b03621820903142400b002c00d106 = true := by decide +kernel

theorem cover : BRFrame.Cov 446223021 446402877 := by
  have h0 := BRFrame.cov_init 446223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 446223021 ≤ n) (h2 : n < 446402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
