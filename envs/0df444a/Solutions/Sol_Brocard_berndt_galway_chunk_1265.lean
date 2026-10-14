-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1265
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:04:07.509684+00:00
-- url     : https://prove2.me/submissions/0f1f3440-dc36-490a-9c86-d9ccdc8be1bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 227338129 ≤ n < 227517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 227339379 1250 227338129 227338157
    0xc0302043008030f0405070501170a0e0106081f050603010605030c120c06070303020903060601020d0e1005070f030306031a0c0f0a020a0c0303120c030905060f04020d06060e071407050607 82
    0x107081407402010b40109004410481d042d003075035030ba05001e00d00600446492035510401100d441307601c9402c40c01d00441c244040b0f00f41c800360b5044443caa000e4680040389164907807080b503180100102801c0da580703450300c0349030050090b1792041070b0300200140e0092080508101c0032039500c1d0044004240140000301141460860502000e4451900100702c5a0b41300014240240030f9000303400f81c2440703401800f007c10302d01e40c0009840e0300251585d0701c4184942c40300d2801c100d1480503003030000c014808104a5100010701050000b01f4003446610000b0714ac2d1300b1420309508840d0f1410300b080c0b080040b0710501c201100040213031941103008628031503869400c7c04003241400050b410061807007080180220806400894101c0000c2c0b000508210f4240c0c001c40c00c03000c5d15030080c0050050307080340c1d0100741c140e03852101031365000d800a000000c0c505486e542c2d92045407001c0d0321140803020388105006005602483e81d0f1031468101f0b020f01e00380f141c10740b5000d4444101418a00a00c0703040c080c4800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 227340629 1250 227339379 227339459
    0x9080909060d06090b0402010908030c061911040f08011104080309090703060e190e16030204090309030803090d0e010c0201050a0806150a0216050103380607060f0c030204 75
    0x50b03594440d005020070071661400c144584001e40d012804242040c0010510f00400000d0b50410910a00140596250302031410f01c038030060105940d00030b4443c0380070708051001d140104014268658101c0d6964905a200b500315130084c0c1d400c940b0804104810801950004180d03800070307004030f402002ca40c40d0b02e0020b42c010401030740400d07640d044610401c070800e0040c01220203110000b1030140000e41d51801150748844012017065600e0214400c24005420a0352140310700f58402c0c00c02034829912610b8034841a08101c5400712035a0015000140c825807000700d0b08040c080038209180103101c5507002030168021841d40c0402c00c40c2c4000000d1041d171b501c1244408590303000788a255101656400251283c910000c0c2c0340d03000100e80d40000e0194031900c2144011150103204508101d503a203051280b030320780011036004025060951810580c3e515000744002c520426001400701140d0312100251165400034805043c8144803c120700180f04040142e80a00c07400e04904446411040813 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 227341879 1250 227340629 227340649
    0x60a15181503060507050705100c050f030c0d05090a1205070c0e0a09080a030e0f2d0109060c0507020906010908060109110d020c070f0806010303090b0d0b09040b190908090906 77
    0x5403940313080c83c081c01a001e4100000b411242c5c000c00c04d4404007000c9242c2c03c1c4c2a540060011400104104010040e0f140c0d9403001d0f6400a2179450502e141044422240c0c0c00d96030280e50414043c3c21015080c020803038030720f00c010321000c2e0504100742000816105e220000555103e1192030400e5035000554400caa40e0023000070643c00034007151a480d039014014020503d009000c0a58070641101e00c450080000703d1000143c20040d0785081304448281d01b2010300f0b42400034a451390740f03904008000610380c1c0941c1001c010999a00c50321003d041c010090701d184042c18141c1400001300d810f000d4008017041a90540d0041c280104405910070700100b824411803060302441480403c0104020001080c60422540025801104c507a16081c80c15140c02e0284001000315544a00070058800d00750702500804d0f0204800040510321800800c404403002c5404403400e85852080001c8504900150030500c507c44904004505503551144000c2c41046140e611070f4403803900060003035546035544 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 227343129 1250 227341879 227341883
    0x2010309020102100f1a03070503061302031c0c0b0a2c0304050a090509010c0f020d0f1b03030501050301112d090303040603020408010b090412120617060a15181503 72
    0x1001041c1000140c01c1c028070301c06d0420540103a452003156141c2c030300022644181c8400402601803501c1d0328040300c0800c200ca100407a0140140d095411003400032a140e10105881c944841d26201d0007443e10790350450004000f022418178200405442c3c003018000c5031602591103001641c8048044c503080d20f1806150712040e1b11400700303540821210762a0304a01c2c00380407500d00074408042c141a054445c02d4203500c0c04c00050380b150040c0d2640740e00c01c1140c41500c03403480c104149621101c40404401c0c402c407038010341c0466141c0e0010005c506003442211410402050b41c0c904080210304000c01304081c10603580106e00c000d407440c020007172000c001c940350540001c1c12240d4882d6a490041c010350000e104115081d4601442304116040003001d941c40b42d039200349921143c9461010540341c0c0040c840c1c20fa4400d42d41c603400441c00c0020f03114102116604d5070020116850648090815242c0031034080d14020101c0c0805c006a514400000c41110f000c1c1401141c2c115500341d588030460340c950b00c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 227344379 1250 227343129 227343131
    0xe010c0c0f0b190c03080f040204090b040501021b0c10050d02040512070f0609051c0f14160b190f020a06020307030501170a0201090519031406010806011a03040201030902010210 78
    0x3000482c91140340091507041c4a2495005040c031041d007054408015003080503010a65000002d40c694014482d1564010310007000000c1040c2107480c1c19100080c11142200c20780e41c0001d0190401030300001c5010300c00013000090030410b01040215141070f0000c401501440b07400328400104000e91b8056401400000e0300300036170349511080980da95070443c0700e540c0039045c004401007400d0b40b26802141c1a00c1c009002c09003d50301010810b0103888440754290b0341c6030b2840100320000f92940c910000f007545400002d00b01841018040242480c05900c52015040b0401c070142c84500c1c2500b000301c160405080c081d1415010740002d034201203100c840100f040d07100200700940c46030191300c414161201a41100f803c070500c407010383c3d5035040c1c414000e130114402804c10001440d02100ea00c0030000203a801712081c0740d40380d48410105002d04800c10554002c0340051224100800456004140d0815040415882d0304060662840007030400303410581c036485018256402002844420800440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 227345629 1250 227344379 227344409
    0x1507020a1d18030708040b07151a011403060a030b04021c0605071d0108370c0e092503110c0604050c0420030402120303010303020102030709060c030e010c0c 69
    0x8100d9581000b1504041e9440410b4494684118000141c60089900420341445c050608107005080d80062000700c582c0a1b020703802c00c00c0000d86000c3c0245482444407060452074900300090482c0481000750b20b40050f00340100100c40d69130b41a140b048079084040d101f510344407400400c04040c240c180b034152003003501c00d2010400801d03034846840741740f669803130701c10f1088443d960594540096840038006401c9201254030803121112400200c03400818801101d50b03400004108480e040c0215034102c2d541d07200c410074181c0c0204012071803140880b0f181d0418608a00b4889c08074110100b2040341414056190346c2c214040c4c0d02042110074a0540c894440518070783c1595900d004840403600d50081300400c008a041600034140402c0990030b0800024100300076043d040c0d000140141d0303000070703c07520290314000d041c00114081d40c069800960b6a11b01000c024200084c10f91129040011070194100400d50100340380c0740b00a0240380054420328107046c2207001c2031103600081c0c1920442d04d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 227346879 1250 227345629 227345669
    0x50706050606191e14030f07031811030d0e030d0f020a022e050c070506090301020f070c06030e03040f030807050705040513050f0304060212070f0506040303020d05151507020a 77
    0x5561a4046182508889013882c04942c00b00d8201198075112581c85c001400401d07594000c00e100ca1b54001c81f246000138914018452036509410518829030700342042d9205c010540c1024441c1800c00701c000c1c142040100102c00107e03545101c0c60b00710340c0802042202054546200340a8405203039001004100701466100130403424000c034041030001001844030502401e8040d205132421441e401d4050710009150070180801c035445200b42a6055608114141d400f1580d600030b0580d5501a403c1d0101d143e08000001c0c08030b8145c048211741952080c0006c104444090500c074040e03a80c031207101515888140b40c62032802e08185c00859119041004104500c581d99203107260590081c000c44603028501c44c001e80e1284214040e038401038000c80c40d4501c03c0c028500041254038440c4880d405240e8503529900d0801d0f200b910228000307500001c010071402924002c0d503800102100c5400385103032140000511501141092081801011410109540c2c034480240c1c000e00300f030554841400030760 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 227348129 1250 227346879 227346887
    0x5041407081e16090305012406051602040f0905070b0a02010b040204030203280c180609050910050a020403050a150e0a0c030204020d0e030a022b05070605060619 71
    0x48600c0d0000500003400280301c40a280c440d4074404105400c1002c072030f152000c5483e044050700d40707001e041c0b02a288001001031402d02c00d462640304c5000e10804a40c83c10391035084a00404d078007550402c4400c0c0a0250900c14204411440d50350440e00062079907405400f28019050162028081d402030140018000d40564010715150400d070f0700030001c0c0d920b44c404200c00c038020f900010b03405910040684078181c11803a464414088642004100100c00380e0700c090f01e0841c140c2180d08080114400d01d15843d200f4044c05014009000c414001803904a0003107503215007040e000c0710a151240007281444240b541260041c60700001030711280c446508146043d0964003c89091441c0303807807610380300c03060045034072521944d006a01a01e414610b40801c0069009040300c2c10a9554408017030994580c00c100800f00541d0341d401030940d030060000c0000c3c2c044d541e400040c0341d0a410700c0300b0540259002e0102e911456006400044a032249808078035130740a4000d11128002c200c108400706d00e608 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 227349379 1250 227348129 227348131
    0x2060106090b04030b0f13150e0d080c030f071b051f05011206090221100e010c0c170c0a0804081908120a09080d060e0a110f13050414 59
    0x66292081c40325514000c5034014855484007414458501c0c0100d0411583c01100c1b0350803109a0100c00015603154135241c0c8282c4600016461032661428010700c1003406019102c00240982040622480c140c0c6900c3c2e00c52000905090b80316070144001090301740140903042020120440010810003d850300c5075a520508a01c6c0039030491207541200c440030680140b82c143d540c1040340d081d502025035125005000a034400f21b0740080c0741400a4615000065844549142c101c0186007480042448400f15071a40c2a0080540d0404800d6500a50031000500352207604c410000700d2440352621203a154020840da60101d40188117041050000c42d40291096a030a40b05490000c0d001c101443c811604406004000800a01510742d01e04a50360300c09a0201441c440854031900c01c0e0b40c0c400a581c000c401000c00386070f9071203043c402c4811010782c00fa844003e03103200300500e0f103401c6041411401040d0200e154550005400a55492419040801403102400c1440030282c00300c800382c5e01040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 227350629 1250 227349379 227349389
    0x3120a0216080c01170a0902040507030506010e04060f1a0c07060320030f0a090218010608073207170f040e0601031a12120f04090608070f090228020601 67
    0x18a04010802c6400442c3c0a010808143c4030122070546501d00410070090040ca101b128540d00c820703090240e211402024400c076410707a000540c9143c1321002421050100080d01d001d0351030140e050098405140b0800e060b0780141c0e04034a200c02d01d204540c111480f48020300b1019003c5e03124002055138142c0c0158443e40c3c0909071000f61141d80300802c151074082120a400c01d22406404159500480e0f03006802c494006805801e2440381800c5000c1030090aa000c0c20000301d1160402c16410ba119000030402e001d2541c00e03554068088804548148904111128542e0002038200801c1a00320404d4801c1002200ca16207442c19201c0640d45031f0850f20901300c888807444c0000e00035601c0380c801c400413005a1414040c0b00700b000d50602520701d0019107110b0061017410303001c0c2300c13880c14840680800303040381044c5581c0b1030130800102c0c266411a88031580b1503011800501c005212905100e094502041c3c0c0141c5400074002c1840e442c9400a200307969a0701501d900700c840c41da002c2665810b030f034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 227351879 1250 227350629 227350663
    0x150b0306060c010906141b0a0c02060403020910060813030512090c10050a080109112208032a01050c0d0504050c060f0c0c0a0b09060f040f080a1406040b0105010e03120a02 75
    0xc1d94011f800350b409020540d506044c90000c02c0540920343c081c078106440c00c2d0000d0030181c2807a489034040380010f4401c1e111a0340aa074100000c00c8003540c0100801e07440040d20f040c0000c043d205941c042e025000710f40050351005040c0c4005410070104201c0c0c1c10f42d01c2001040720b00302142031000030780594810604040054081030010a00110a000700b808801000101c0c07403a00c6d02c0400c44014030420400c00c60301842451100141c82c0c0310800240c001c0012001007440c184051902c1c10040d0919002581d200e641044100a0301d20840c0301a11021440901c01280701c1d500c47c0303446402c109036150810360085e80070411104491105018000032003a40084608500b401420045403c015100d07a0b03007848400c1100c14068203140c006002d905400c002036a00b01a102c1c1540c00138540316401280c955032000e947d1030140030100c4c40701c40c040028007001e084241441c1d00c5000540d0014043c03141400840300100c000d944040000304a0910b56500c00750300c40024a00003512902031803841c90b100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 227353129 1250 227351879 227351881
    0x90d030f02060f0103020109060f11010e012406050405060c010e0d031d0604120c0812010602150a020a08040f020303090409060b010f050408060a150314010c0909150b0306060c01090614 81
    0x140700f50008940c1a02c0c4c058552800d024940081240d54064540000b42003120340101310044c80024040c503240340280c10004074100c4501c40b8244100c207044840e5446402e1024003c102040c0c03c0342c03c039425a04280c80c1642c4c1d580c0e00344032142c05000036801c0f12226114500c4060501c5500d54001d00d106080740304c4114464002c411401e5803401c00740c402419510003e600805940d00550381007061034420600182040350401355400346d010b09034440009600b0407030101d040034800d005115800a21602c04505110304160001c2010500910040031180ba900c55141507603820401d480c168013006005010501d5a881e011f000303844116183e03801b040328482d00131030a90040c0700340c0b01030343d070f00500031320035a80c81c1c080c1f44026246040b2004184103c1400c0400402e03030450070f080400016038008030700e18200f0380008005091541c00f000c041860004203d4000b201f02c10720034100e65042540700d40701d4071840c5c0010b010b8440c9026110300366103415000010481c4035040750a04100c600d40c40e0400f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 227354379 1250 227353129 227353141
    0x507050307050d03140402030c10032403050601080d2c0d2406080307020d02120d030615050412060504030513031b0b030606040905090a0c090506040b030106081908090d030f0206 78
    0x6085c00c1902d00941c5a0403902c0d1707c0c070321030511071500714443d0b0952401090140924421482d903409a000201d40501d14080610611404120312801800000d0042c0060b07107034420000c20440803024500c0340d1040d40201c003040f42c0350301c0d035545038a282c00030103400c13074a0014509182c15540415061500c4140451000400e40f400d01c144011a14003d004d9840e01d8403030f5080200c01500d0300d000b207903c44694030044891103000c00044d800300501e9140010b4035400c0c6900c0d0840c2004144c440c0c2c0070443c0800c42400f00144d420008001d6a03841800403540e40c445280944050040006c2e44a40884d035520010500442c810404008010880e00d9032079103440b83d03e040e59a2100315a900e4003c2001c000402420549622455208800780c0644100c44201d0b902c1010821041c5d21040b00280c0300c2082c41700b103240900c20300d4404001100200203803407402c01d02644403c40c4600c40320300d5140003101c4100b400400c10031900d200c500140600301c882507914001d0b051030b1414a00400502c210741c00114 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 227355629 1250 227354379 227354411
    0xc0c030f08130311030c01051e0604050705070312140702010c08090118230102030c0910020d080a020a030603060e070312050c031204110a060917010218010f0507050307050d03 77
    0xc0074442c0c0c00109128202c15460a44a0000c200307040ba1a5220400200c410300c0c00a129142c004e40000030116001c440f04122010302210242071030340b01d03601c3c0406020006801004907131115505052558a003042d42c058003005055543c0083c40d20001401048020741c0d0641c007021111909460f04541611080802030803143c581c91360b40100302e02c030f640d0140801c001d031207500c0400040c606108000b42e4a650f4890aa8000781d0b2001c1020401060030b001a00e441900091500442d100516120402c403c0041170300300d02400d04030704030b6800504541c60f54420f0704480c010b180c0100c000c2c0a1154580a0155960290304c400d498030324646104c0d5618a20034021151440c80da1340095090030070b01043c51007443c00c01303402140c1880c1c1241c0600030545841221000801c13503900d0b0035041d00c1c60700b8400c1c0c10f0604c0d1554400c0e001e901c100084000480001080c5900c080c0a20f41a0402e00192509036002e00c201031014009110214150741000400102103c0c04c016544d400d0103545010ba80645d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 227356879 1250 227355629 227355631
    0x60a0c2906010210150603150b04140a12150513210206010806011a1602040f0b0906101d060408060c0a0f050a1b0c0b0708072108190f0c0c030f08 64
    0x4000c5c01c0d458010811702d4400d0b0880903100303c800580c2c00c440c0c1d5a5062001d22a4032650280303222002404201c1c030986000c0c01008000c2c603440c07004204042a41e619030302251040700c4901c0c10716070f803031010542c1c0800e500e44070745a007688403842d0403100342c16014450642e10507007101c000611410b400440c5421700415940d04880b00c6032419028001440340182141d0040b03554030420079200003e0b48056600d03400340c14000c018400000400b451104144041024001d011074060015038141807110342d40010740c1403402103650000000204202c00207030151003240d001188600c212420f2003100c001c5080140010101515080c0f840300b020042501e40b03008110308400450300c0081c0040012801c0f80701c41484500c6448280205900c60640d03038440e81224a041e98184000f050754002c200c525040c10301000307a000b01c8945c1c098407800c030061600c20028904491040c0b400060083c1c4000c50304113221203201100c0500c0030007005400100841d04001c802d0300050f0400080d6044640141e03421 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 227358129 1250 227356879 227356901
    0x180501090e0403080403170103060f0b04020901050403060b041b02061501080708040605090f16051801030b06060a050c072301030510140a0e280b060a0c2906010210 72
    0x307103065407151410780e203052004200754240032002d07600e44200d94041c0c0f1070340c0c083c1d44100b2000510881c1e100c000c0048503d4034200a009520400c10704100d40e0f00f100035502100d038420408140014806c001c5400340442000703120800000c8079a040340c00f900800c002e4482d0044610001041d4840d800441e600001503031584085521360022801040d11900895849582c030f0b000c8408801e044000a0b03e004080301301c220b034901020304103001520b42050b0903c507008210198076070f99411a00c5202421a0140c52a03109250000d02d8600f0701e40a00c041d203d0007002c0c00c05036081281d88080021002018256090000290310141406580a4483e10780901104000c0b95402414034500481228411801c10381c406840e98000078888021941d02d80700c0c9450801c214900b44a080c24464046141101015424141841200d90351102d0003994540303d85413a042d003210249041034800001164115019100d40c01111390351441010321607400341c4400e038200d1f02d0411981c04c03071030b040f43e00802034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 227359379 1250 227358129 227358149
    0x10512010b370b04060215010305100b03070e0a0609050105041a1203090d05030408070609080c090703110313050c03010917130b040609050f0d02030c040509030c01090318050109 78
    0x18000c0705191449400382071814080c4064010003000e070b01031954a07200d07400a0140140001e00744041039060000208101c0c0d0f0031001d585035415a42d0301c41c1c841e25507841006440f5501c3c0c0c005d400568080011320020036030340c8400c080c1810b040100002400b010b001e0400700500340000014141014880d001e2046041100000c1c0c0300c4034a000c2200748140c02d004000d041c841400700128942e1400340c000000c0d40706034015a81c441c98000341d6420144141e211005100d4031030801c2050b40e070007040c403402001c41159122800d5031150815801800f20000c60108100080100207103101c240042103500e1b401202201c0b400b42c01c0908250036202404002030580c5400d1040070101004072024000c01c2e0340c00000121039684944d8180c0d92504990312000026211040c204400e06207000e60340b0064006903032410307a08101e50082992001040b91880c0240d07940c100217400302f40c0a005850000101c00021b2040700784e6410010704401c0c80c0007600d2aa007241c44400507941d07005201880444ea0082c0c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 227360629 1250 227359379 227359399
    0x10b01140922230109050702070803070b0a150e070e1f11030d0c02060f060a140d020d0c0801021c02040303020a020d050307050a1410051504180b0a0203010512010b 72
    0x48450051018411482c80252900d1058200c59803404400390070481455004202d58900039404e01074901c043c204d9000d5402512003480303455004811555690382103403204003039441c3c40d03401c400201520b001d01c00a0111082001c85c948080b80d100500806095403014481c503160781c01c001032542d8410030f040304002c40280b0102c505005804484c1b4195501041c1c90074425002400405e03a8807a07150305006030045020450410103144c100c58001c1415282d8201003801c00c2e20592141c1e0f44100524881c66104103207900719070b28a14140c024139400400020055a50b04085010b508810058a000079a60851440e4103140303200b83d60880c2d07019801413152226507004d01640d035250140a4506010130441c807800300d42d007001420056072050444158080c1800b1219040810076a400d803080c605240910001c2c072003051034a0b03980d19003141d0016a01c00c03603500000440e050140700400100905040002d82034407907016504031002a1003510300010301d041e07114204d4225030700c441c0d403003036075a5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 227361879 1250 227360629 227360659
    0xa0b010e0a15020a0b090d090603020903030d111e03100b0906091c06060b190f0e010e0d05010513020a060216030f0809060d090302100b0607080d0b060c010b011409 72
    0x20b401c50441e161140103480501e64561284500508101c80b1803001c1c0d400450807a1a43d03a0108850340142541e00c0d045040009170780010f600da2040a40608450341c071201170000c004411004c9503030a5582004620140d1458181c0d0201a00100d0311150010300c1ca0000003040c041110485a50400040c000c61500c081d8100300310012400540f0300f1050820302809900251031441444040c00407206900e49400340140e089081890580d040e0003048410003011004a400102d219662707042420905038a001203404140141c02d02c81001d4455030178542030010844c1d0003024220014000d80340102195101d62090740c0e40d9070403510044030780c48007920400104440342000c030324480c0b141500c185003070302e0743c000101681c202100d460b05043d500c0610310201a01048800c42030003124200740002140e020004003c3e01a4020103004110001000e2005070b84591080d005842e000702440e850303900d4403104d10300030182e44c400c50b0701180000110550501020048e541c400740002d0600c9941c0c030b42a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 227363129 1250 227361879 227361899
    0x1b0810020f0906041e21020111012304020f0409080313080f070303020909060405010b040608060a091e0c050310060e030708010c052101030201080c03040f050a0b0a0b010e0a 76
    0x8403104030503104144008040c9903100301c02800101003040c0a82e00b01c00317000c02c1c1c480b07118842e40d00060030303032000400300110078944e2801078900c0e42c1c0900b4010140404070611a000d860100044a50700e914541424810180c0e4940c0c540181d00a6a4442040c0d0850341448102c55040002500e060800d1001a544560b00340c0082ea80b513200712004e03400d20303682c6d080362a0681c11804048010a401103085030650030140340700c990140c811a03003806154502450f100036480f07180242c004211210300094003a40760144620010304a048082010031804521740714098580c0600c110030318109045511040e1140007030303d0250203101a509601303403a04c003023604c85644400c3c00c02c1d05402030180000d10302c2001c0c0f1800c403841c042922404c1ea034642071602407003820942c4040211600d241001400540d80c4405031960041411520a40c0c0351607505050a0b14592000000c00c0d07440740302c0b40b507810840740c3d10070a030103212156000d10001d1070520040d9501d051f003c000f1600305a0901d000c10806100c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 227364379 1250 227363129 227363137
    0xe0403020a051c030b0118060e0d0f080c0d02031305060912010f0c09170604030c02030a06020d020714060403230c1002040501090f0605040504230f01031b081002 71
    0x2003401110040c000c25914942814801c0400c41c0c40c08800500d50910300790180200e0300018424a030101200d1703102e0342c4591101101d40144010480c00442041c40b41d11446070310000c080e04128480003080301890b015941d50b04c000000c034418020011300040c468000015900200340050981e00e0850030704d4140411f239045680c070903501c4914448003c111440c20700c02c100c0310401907000426202440300c400762226035140c0c020784645144001e28a00b4180124010760402e81c140b1344890700c0e000d04c0c00000c0c9400c4c01c000002e07203a0340c400128500c80007030039802090b0b5036110304d00041202c2c54415007140c41e91005c80e00038011402d50581d0b56101180d00120b500c0300d0a007800c000d0304001c84440e036140780ca9203408458014950000307060140e9038115031800d00804000126003070041c10100014564003a610130750780074580b00d050960711090f4048400e1100400c10b56980c1d518603040aa064440340700313201c02e4030802c207c000301c02c00c50b40710181c6000c11b6541910041a0504826848600a600c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 227365629 1250 227364379 227364383
    0x1060b040815070c0f03080601110d1202030c21010e0109230a02040801450602090f090f10080601060c140c0d050a0b01060c11010e010309290c03060a0e04 68
    0x40e404651000034020080251700c1038004ea40ba8582d41c5000360015001015010024000754042103010055940c005070482090011610268a9440710b401c0700000380200155100825908032a07405100f285812460403034828106d40d15107a661082030104076025403801000d24495444001c1c1c0d040c81c0110803e401110b012001468a503a030342105085401042003012449500348030f280c89424411910760074055089520000070452802c524030042e142440100140d4010804002c50356030f031131449880041c090100300061511001c2030350744003c01c42d0b038904c42000b07003000401e0040c000507856060f2141c039100e00e1280103c6032100c02c200ca0700708001000314850090603070402d441c0c1c4000344408601c1750f8014074181080b441d0041c0035400503009407041081000c0342d88007140350081842c0301c44c0d4084c202000d4050f40240103d01070f10143c0c4000e03001c00e100c4241e03a4401d002442413000d1950005070721340c001d0380350b800303842e403041c03009958040d48000c00c00400e2041c50981d2103000e030064 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 227366879 1250 227365629 227365637
    0x62d0f061306080312090f0606010c060f060603240605040603022206030c080708060d060e030903010606091a1309110408150a0c0e031f09080d0b0301060b04081507 72
    0x95514085050b954181c0060400760000f188804800d198404042d81000c00c14003c1c0105032084034256680d20801400c00e41080480c0c00c0c400705100c4203920011107410003000611540d80c4503800900904100c0e003c000c00c0185503108480100b00307000c000401c3d20260740c0c0e01440c003840c10f441180603402000c1401c403102c02c0e02882503400800e00c03500760010000c9403004504406043d0b00a017808000800f01ea0038411814100714282e41d88001e010461640101e0018103030303021000140c0b0754010449541c0d0150300e44000400d201d500704021508489240824603103624103490108078500030a510b162021001c0b400600050340b058000720410381c64413500700d003055940c0384514a400b18024040c0369010303a0800384040c492641c0030f41000d00b110b034100709070314145040c0401d5540320810100c0aa6081070f54080401001c641c000799402908200d0088d291058580b4110081c040f1a5465220b5171a0000001d0115403c030140e83c01c0b923019502401d5080403ca10b40307822000024180306c100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 227368129 1250 227366879 227366899
    0x1b030102090405130303060b0a1e0306120507030c0b1309020904021303200402030702100c020f0a0812070c0201021f021209060601090537080f062d0f06 67
    0xa40b203911500f4407035081e8000e0321803e02c0c42d40c14041e08840060f080400047c5040100e000c070650491442e1442c608030614034004969002021401802c0d035400500c28504002e88a200b031040000341d1900341ca010b140040544c969407000036407a4825212119008580b881040100280e140c0c003a20281c1c0c0b0140025103032642601e02c81d07903131b064580c0080303d00c0e0510461540c0c1c2054818803000030200140c90031031440c100060003a5a07a41c240e40401200c030f4071484c0810040d4824854100b07115004e0048509488031850012403039006001c00406942e291030028001c680f0920f2440380d11601a005040e02401048010000c411608541010140c0030000c1104900031205464400c0303800344041c26050a00b1800140010507540c0003d115000040712440d04220f01c0c0c081d22035200c8204a050b10350038014041c140403010b03d50100c0910301035100f40c50104079001c1b4515100d5801c07941104080c3c1360310350030074041c2382d24042d081100b01d96500018001c1201c0300072041d04010020486425 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 227369379 1250 227368129 227368147
    0x7050603091c1d10090b0715051503100b01080106050708040509040309030b1303050f0c0c090c0a0816090b0a0c02040608010227030a030c0f080309010b0f030f1b030102 74
    0x1e02d40c001c40c2d42c0020f54030120104050f035568007007480500044800103c400064a0000c001c0006401192021a400036002d010000f10302000205500604000e00642c0380692100c2800159001c28074000d010b01080350f2034080251059050b0554140c481a00396401d041048841da004940200c58542c0208404031f1140d40707a10445100301d00c01d560700a0741c1d5055241c100034210018098203117285915410300c00107608401525250790592544980b5152114405071402c1618214150000f0064041c8081c0c07980000c010300ca0701d540ca49401129883e40002090084034404101e000076a9087c414400142c800006021950881ca800d0010f940340d50000323402c07602a5400440d6076940001d6121491105d61410040501802d00d600d681d8506000429141c0b0b80a20004040054458410003000016400b440c03d4076003040c02c1c280c40b46418640d29000300054060184a4aa20400c100c03d03454005112050300768030101030200c180e24100007403145040700c0075450f8195000e0200c108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 227370629 1250 227369379 227369413
    0xb09010507170f161215030606080313091e090b091905060402010507060603021809070b0c030711010212030a0b011e0c02040c020f010213090501090209091603020f0703020d12050105030705060309 86
    0x40f46c4109000b20031446c03552400c1c1d0101c400c2e581c401070403a00107018020400c1e1103418010125050041c2c0441c104c800d0b0000b07a080780b2035505418010030f01c0d1080d20000d005600c00c00c188156a000101c1c1c00c041183d026611038015505001801d546c011400240103500c20ba01034180a4403455000c00c44581300c3d80007074482c6111000040000524204010445201300f1454005007210300a4914207030042080d01d0f02c0e442070000207080061024500701103a44200301030102d000e0045200c50710fa044c50040c940c060240d10441c01d000584902101490b00100004d86018010a481d080c1035900d2030b0b401d1202030300340e05002c0415800764882e0300c032a03420280000c141c0800d100c4d5908500908120700c42c030485006030001d0710800c1c414040b0482c1c903118080920303003140d801442c01d0604442000f0071800b0f44a10070560801c41c5011422004054000500541036403183d00c400185803413428005084690910405a159008101c00c200c170303080000c01560000b81c04400c1d54168159181801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 227371879 1250 227370629 227370641
    0x703120209041d07050103202101150207080102090913020f100c0c0806040206030f090307050d11010b010c020307091a0301180203070e19020a05070b09010507170f1612 74
    0x3d03c082c2a03940d90a2040414020440507190900b0104110700e00c00d40c000c400800386010388266080001400c405081d00701c1040301130a07480042407541507841e410403d451800c201903000c050f2280080c0071a00501c180243c50002101414030b043c956201c445840f9042c045070b40598200c1d035a404000800e85610070900400b44c1182c80d0740d03800d0101d0740b0305200203220690109200360000c0342848016958541100c0e0015070002c039242e10390312001c224904520621704020451320540c0124103c041c2c0010b0442206003e64000f00502c4583c800150790040074610002d42c10342207400300340003a21032980862803034050268803156500307041c40464210303950160360803030424009900a0840c6010801c1502a20344100c0058803410200714440a0014481e0790000e22034003c10ba103030040d0b1040c8241c1d041c0c0c503000b212001a078100089024002c0c40301b501c40708001800860902c910320b48c0680254001e4140d0886a900b968800681d030350304c00344280750744040200c03055403d605410075000700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 227373129 1250 227371879 227371901
    0x10c0204021326010203010503060c03040201110a03121113031b0b04080102031006020f07090914011a0420181c051506010906020d0e0303040f061d0f06070312020904 73
    0x41c0c000c48151240303205550008000c42d180f07070307801000188642e4034040f5200ba04020000c0c029901d87c0c03030f01d10068a0f80c02a04900031014442d111a5805140d88908109900905040c0c1042600840c00850b021440b920010026110071410200002040c140c4104005100c96600601d5a0345400680c20705a00680c08014640c1d00807003072050000c0c12406800040080380010b2064041468606447d80581e01c91080a103660b6000030041c4410f09107a00c44020741d04001b0800007403218554003110a001c02c2250265181101d4440d40340c906a11450b900a01000e0403410801000603515003054121400b07a0040b030f0b40d4a00c1c0c244038018503035080509200320054914690307441c0c4045207002c002081d050422003007074010861540c0120f9140b00c1454a4078040040f068032001180ca18800e030b034000c8040c001036160000c3e490303a1201480402c2d82910559a48040281080299004410701a103600541c200086800a402803428102c06107644e82d006d0305042000002404a131103110360 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 227374379 1250 227373129 227373149
    0x2030a150e19051501030b01090902010917061b0a1d030307050703030804150b060901050d1b0315050607030806091003050105010f1805010b09040c031503050304151d010c02040213 79
    0x1450b4100701d010700640f00030742e0144c2c40c0c090403580b5503240c290303090318188aa138050998403840355003903920804060000d012480c1d42150b142204002c05a43e60a00f01e64041035042c0561031175601c00445403c40351100f40550701e12844001d0000800e26031912405002d9142c0f00c00c1110300000345060015000640c005d17103c800042ca400e00b4260171140284680011061800c1c4850075140c0e149410341d016400286805038a941c3c850721404018001d03066204074243c00d0515000405615401007080d1540e41c400c201e640d955203c0510003c1e00900c007004000c541c84900140a80c01c28080c01580000203100004034039030380351942c0c3d08490080c1c202a4683d041c164081c0700c2d1365111483c0115071070290b102000903614110480c42240913510641d445651a07041d00d0076840d00c01d4002c40305d0000c10706030200960350307030f4a0b2080e681d60142c890041c201c0032913036007411041e000700b800c503032034010848400c0500f00a0900440b90300c1400042240d005a0034031004881104000f210000341000002d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 227375629 1250 227374379 227374423
    0x3071502011b0809100903020309090408031501081501080405121908060117070f14030a0f0b031506091003080a030b0a080d090b0d0b0603090115050d02030a150e 71
    0x2c03440074044200580c0c68144106101800010741001600c409003045072440060600d00903d022406c510030681c50b6644007960300c0921013804002002107008035000046200d10740b004900545851400b120007070a2500003086c28459540104243c50b40180701e00309662021110705202d83e00c035004031035507561203498a400b203103ca6400000c482d820140034281104001c80307110182019501c000c00050403c1448981c0107040d41c001c10b0700c810460495100309480b4602403c102000b0b085125070655018200b10154116041c08906691425200100f41201d039642da810b22150700c0c4003401c82c0c18800d022210010100303102e5805000d482606079404561000f035942004042a4030342c11050007034000241345a074058110f4004000c451307406082684400b080002c800082039501c0c102c0d038015000100300400f1213419808013150301108100d14010b03d4071076040c08005d1a40150081d0142e2044a540000c24000781c800504c0f4800020f002c10a203040c003960034103058a5044040710994003034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 227376879 1250 227375629 227375651
    0xb16020613051c0b071d06120a1103090d27030f0210030203010602031e0702090c07030318020a170a020a06020d110d0516050a0501060e01030210091802090307150201 73
    0x101074464405040070400b01445655102c0340f80454015017a48244a501c0c1030a4403c800c502d410941800001803180351505a100507800907820f003140c506180707038601150800c105000741c055902603040c11005190300c174500b11041d030307000c03180c401500d911200c0120009020702c036800f4100c0c099485880080c03503a0860344103004401a01c4941e05040c10300503c01800202d90010694900800b40314680040070076000043c001807060300b070081c1d0448400b508010103034464400a18406102e990104040407c1600c1c05150b107804060080d4170941c201e404000d04400c20307190f940041d20400c10b540307100881c0e0340000d65003e00c0350b101ca000758010701105003c80d50071844104040030420064020409072100041051103010664079040d081e0503281c1045c45803c0110580c0305a22000800016450b00c00c400d1862109100c103c2c444d1030b0070716408081c50701c0f0703210391821108040000c40e0ba118440c41c0900c0a500300d030101e0754141c0714522000580b4946404408180700707143c0c000050116070300f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 227378129 1250 227376879 227376889
    0x60a03022a0c030f1b010e0a0306062d050105031503010c030507020d0c0b0408130f0e06040b04090203060c031320040c020a05060c130b0a0f0905030a0305040b1602061305 75
    0x1000b01520a8124100001c150180410550403207078400c0f9421140b82044401030f0344000040c1c050741c4e0041d00d10700020007080720329400042600d1481c1d402c6070400480111400302e85004001310520710841400400aa50045010719088106078074004010f11000000c01e00f106c2100c9a1940047d8849081c00305013901445107000140161400b06149003003500d03907441d04040600014600f180018424078640310803070b51540940100386008039071075600d0203406609041610707014815860400300c082c080c60f0a104040c03e195014018062503075400484641d00c0d0801801113010000c03910300f030f00018202e9940e440d203205e680d480c18594500c460007480100c5003556410803e65105994030b2011440c001400c80c6d210039594000c0e541c0303e0400340d1240405038a6440000400004646100030b01d410260414000c0705917035071203005c0c0b5650020140d1300c000c040c6024000c59801c0000f40300030443c5200400310180c015031252010140303903000ca6000d501444070020040040f0005002520300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 227379379 1250 227378129 227378143
    0x204091101120603080715021309050f0705120610090503010f02030a14040203061308070c0611060703051308160503040612062403050603010b06030109090605060307060509060a03022a 81
    0x1202d500f00b00725421945d9808a920407010007800880a42035034508090340c1d038044407941c416100110407811f0f514000780d0301900e03041e0307460303080d0044000000c2c03a07491144041d034110300c00c544684046511410244014106d200e900002000103070350340882c903900e09000e402d001128507100140e41e841c05040d5001102c180e100090008003105040c40b000d69000607850382c100012a13815100c5044500d0080360038400c035900240301019004001420541024448003001601002d44515a403216011411036404864440f140008900030340007164610026014140f050102c161781440c00b03454262964101d6030143d030000d00c0104441d14844a6401008001c0403410700c140c1d040001c3e05200c80341140000b0100041643d00c200040e60341e50309410204048038060f150958a5844481c680c02404d611035041d14000c5c24100860303014140060b070071045940aa6480c2d007032240e040100145030703020003000f00400d078007404030501c1c1000c0f58512903408007102660350381c9189141203072810305032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 227380629 1250 227379379 227379407
    0x30803040c09090b1612020414030f0c0607021903021c02040f090203120901020114010b0a0f0908030301060e0d02090403050a022a220e010204060e030102120f130b09160b1c05130204091101 83
    0x421800d000c83354a8050541d041aa8100d41400510924112024085103140d20295001c1d8100741c603180c140e65042600c0d074003180280d500b030210030741e000714001c00d485080d0802074055211400598400c0b0181c4054403050304148000300e180354110f80044071610080c1c0000002020000d518108190080e1604a1010030340c01c1260069140c0458a40c6a010511800d010f004d502b030669111580c0301c0d00042007103607000380341b00301c10700306410024119041108020007602c174900d40d0018064507049440031071800b00b00c00c1584d007503030700c4c043c0040140782405a2021550300c0005120030f201c00d005181a0b20210400141c940346001030003813041240005240c001d900c108a11000085881e801c00e9001390004401d240c0354031801e40070a1001d1040c1c1c006007450000d201071000c900c1e07001c01c0c1d02d002c41c0900e0038842445500c52000a595125054948041c0925000d00403090b180300c0d00810350250030702410000782442c0e50082801c0d41d07079214007107806a030903640d00400c66070006040b0f80c0a207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 227381879 1250 227380629 227380633
    0xc0406030c06021608250b07030f0810050d08160b04050d080a02040b16020a05040c090503070504231302090403080a0e030f040b090307030606030803040c09090b1612020414030f 78
    0xd845e000809440c1c004c81c59003400081c22007154801408010300c2c5003070082c0411244107a0713428080c01c00801281c011982034000501e280040360314102ca0452aa041d142d000b07003410740069a44c1c0d1018038590251a0ba0318042c040101000d011480c1403074100d00c0b0754020805440e144206031070091000d0030081040d94020700c140001c0c000004642c0540e03004c02c2500149245190b10b0b40006903041c4042c0d40841c1d0700c00d017400b040c8214164030420300c40032650141d003141d20f00e6440744100415100d00c4d07842444428801d02d4085643c1c0003181d1065000224242100044180354020914040c0100c0303080d4042012501881200070080c0b007280c0c458146030001d5404c0015074005504640314a02c68a20007032030114130259030383c0c0c06004407401036a005c103003007050036501d18100070030b42c00c12641999008070b01c44002810702e04902032134404030780c0702c500c0301c00c01d82c0e4100840840202e425401070412441c40d0510245900500c000c2000c0d003403502004041c614050100b40c900040c4441c55444c0b5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 227383129 1250 227381879 227381923
    0xc02070e0609040f050609010902180702060c070807080f1c0509070611011103090f0d080c0702100309050619110f07080a05220f06050315060c0c0406030c0602 70
    0x209014001207400100480d03100300b058079942000c420000299201034420f009180901006c60310550143e00c0403403007a511031031441d9002d0411951010b0454041002d43c2018000070705540d1103200400140d0720540c8114184038658440c10a580c20402d040c00c440b8000099040c1511207240301048040c4054034144602d1400d520780036150190f42c0300d840144051124a816000c40c00c1d005450012030504901e170716441e241a40c0d41d078850b4401ea1a001134010315246041a520500c2054881c49a001c010341ca8000e80d42e080c0214000200c207103a04060b980ca19040019805102070740c003802508282c020713803006404100c0c00300d800c070310034680030080200842c52044102c9016a5a080d80120032180c490b804108260b0303052098100700340d9503000302e0a14403000700c5120492070548000c0c2115880190b200d2409a542e4401910100389a102520702d42c1014038200000700840502103064030090102c1d030020506440e81342d0011036031818080b03414410a6410050009c801040740428440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 227384379 1250 227383129 227383139
    0xe06130906172d0307060e070e010f0e15010e03010f0905060105180f18060901150b070f0b1005060c10050f0708042a03150b190501030f0e030a0f030c0207 68
    0x420f041429030490f4400021220619058188192560103401210a02110385c0072000242c840890b80502200403034101c0011608030390080200c0151056084001e509031075408580b0401481800c2040c1000f102610034042600e003130107100c0f1990400e220110f00030a4911b01241443c1d0140c01c890b00841d8960465001200060b00d0a604003454484400c1944c4074010910a1140c3d0035201000e10b00c501c0e01031046141d015807084445114490000d410903446030090101c0e40704003038001d0702c2d51804030036001c0402d40b041011b5401c102c00d0200642d000b0f80d100d010410300c0e044140c03a03030480d8200401ca070403101d0090055a500100800c0308501074238213105c000d000380001030000b402a200f801c01241c881064403000000c10240c002c40c492402d03660745803400087c26021030901c6964104411540e440c2801c04100020620307001030301410700d08144c0110000e09000713411500040d210700600c03a0f8024180010a880600d941e1000044298040040c0c2640c800c1e040441c215801a002009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 227385629 1250 227384379 227384413
    0x10c02120a090302011b0501060e041a0103080d020309010b03120909011e1a0c0a0606060e0f090714040504060b0a30020901022b1103070b070e0613090617 68
    0x140d9130b09082c01b98086140031102516484103400045c069803803c0c034003007070075140311002a10039445100004665445860314086100007031100800705481800810604c0c409900a1613000854400000b50320300300d10002468100d1000a0070b4501c0340005441c441810500500342c0541030340941d00407041ca1040e010900702c00d0511400004c80c0200f85042200d800410803941601d4501c01121081c50759400d251004042d94403400c40440c1d0103801c1681e03103041c920911108850300900e43c20b540d0351000b03010ba030b40c07592008250818072001c020114060740c80703118940c01740000040715a02d901ca61800504842a450100040100409075040400609880e00001c1d155550000750b10342e0740302c02c010307464045004082d904141c0c3c10540d101c2c100442c8220000e04148990341d40300351130b08035008035841788180f5002402c43c1d00c0d0200050140c03130281c00ca25411041c050030440c54081615041e01e2210015003042515903110401082144800d0341003159502c0c2d05400303803418004c81c1000304 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 227386879 1250 227385629 227385647
    0xc131e060e1309033b0d1106091203030408030103060e160b0904090204021204030e0607080d0c05190215010614031f0b0a020f010e150f061f02010c02120a 68
    0x800c1e0b4075100c03890b9200301403003021207103281ca10101001d401111044c203100d884844401c14850107407400080798480e07103441d04140303031260b8009504450200c0e41906014241e4001011182c000c0401105104445c1e0104010761149014641c4a0344a504524061095480d1410501801d500c14510000c10324205a104021a5552000c1556594a0901250103810a01f001a510903c046402e6200007002242c2c14815403081d940d0349030104400c0100012801400b070050041d510501c29050080d01e250b00ca0300341d082d003034100300c1e042c44500121413903403840c070250000058102107400590000d00003585409052a801c1c01c40268100754584030450000800c3c0d55021141079203140c0c1010a84050403024101000805681d000b00340030180d0b59680750340245610f90310b084460321058501044049410b10134140b0421542c56425018091a0000d0300c084e91018810032454800300c0e447e046103908603078903000030603c865400700190610fa02c0c064400010441000b41d0041c480d0302107106 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 227388129 1250 227386879 227386909
    0x50d030c0203160507090c03020702030d210506040e0d1d090708041b0504020c07030b0c18010f03020d0c170a050702030a1803050f03030f010807120b0c131e060e 71
    0x450240c83c03d604040e458510940d00c0321408500c1c01c114044a6940358005008940c0280e040328001c502e4a842240c2000030051030403c4420380322040300b000005508851740105004101040444080c02c036035060619140855001c0341c9088144240303a50241619017920004480e8136149180c00c0501401d0301310018802801c3d41000321002101585540346c0001030701c0054400c42d19081720b41d00d40c40d0380b0b0007540010b031160341011b4000349507454030b00102c0e512040400c8400b41002402c0005540d0688090714107810316030288a40035405ca9617110703a1485248682e100341032489110401c560604001d010b41200034201010001c4413900081290440c0709c00d440c0c0b04035000c5e0f10000790807140c580303600000c0c2580030303007141c007020420008040d6008541c0c0500041161340c2e50000240d96118500c250a502070156a0790804030b00100c80e5954461f4807050440d2800030090b503005e205605a801460b0a0084d91000100c071804030b0010f140035000c6410110308101c40030300083d0040445900c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 227389379 1250 227388129 227388157
    0x60102060a050a0914060a0f0b0307050402030915040b060f100903110109050a0905010f08030408070504020a03020d0504030c060509030703210204080709020c0d0306030b0a05040c080a0807050d030c0203 89
    0xf080c007071600d907031103002d00d0760700300041d02c5c1c01142c0c540505440d1b42c4290f0303110707485c00d080004001070201c0d20b20407890480340090060080c20300d000103100c040d4100905046c0c0074001e00e40703607d0822022503030052103244903601d4a03a09141c180100000420103010503030045010404c0540f405410101c00e00c10741ea04190384150390800300d80101ca81d0130240c0c001c2d0342c20071031001c0d0004032146140c00c00c5040c2c581c070b40b52541300c60b503c030f003049aaa070107079110390a12076001d003008210508080e4010f00d0b500010340340141c6000050302c1e040c0c003990b9040d10100c0000748901c00c80800d00ca880d00c034654000322582c010f14a80b21a40d2002010080518200c110030528080d5496400c500d65044500402c1c1c5402950b0001d80c1e20548500203400c03000d52400329014084041c006144640305030f0065039400020303442a522038003140340c01404003c1c4200d4481d0801a0085098502002111015403007007a01c80d41c2c0d00017600e0040d0800d484d01708804185805c0c405440003103a00801078900b072a0040c50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 227390629 1250 227389379 227389381
    0x8041112011d0111070510020d0603080a02060601080a0501180218041b080c0406050d09020a05091f0e0c0301030209041a040c050301200d0207020a08071706010e060102060a05 77
    0x95503400c0a66200425610b004000c225050a0490034004001240b000300402c2820026a0013180310340c03c80104250010451440c0c02081030303014206000c203c8400141564030b942d501c9841d6400000c5031409070b480302c01088181d41c2e000070403550000b0f0800c0d041c0595403400404140120051080c008241e8011a04900806e6000880c1c00b401c40024024132080000c6100301c0498401902080005141c1e0f80c002207030a9008801ca8045410a607100c6282540045640700100103001040382d118950540000e52691440d5901c0d0117101c011461641480440c0c03004010101d080e4001e003410710300358003002641804801964112601510000300300ea403603107071010040b1303041d10007448480b12110600052001201c030403803c0d290300307500070040c84010000c0c10007501100c0000c01c1c102042003003800d0040e02560080d04c030302c900c042c0c840d00c1e03680e807508503443c10114243c1100381440c200444040403504204051030041c00f11580400d482d0414600007520b83c08000c2c01000c91540303030700c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 227391879 1250 227390629 227390663
    0x908090409050c0a0b0301170c1311090d0503040510020a0b0a1e0603050106030b090a0b161106091b01050412020609060910111e0a0b2802071b060804 66
    0x102c020503d2400007000d050340942c03202581c03220740c1c100b03028000c181010350080f00302c5048000303914819004002c100088980035401c40380c0c058448203486001c0b404080c40303072000399111a0114500a8411030207180c4903400d1006000780503282c03107005000c540c001c00f0483c0c045910240c0c020303017113000b907080454003840103444c00d403070400040d41210a1514050001080c000e065201d0400e40b8441c000828a40d21055a015239a070400c16000e008181740b00b02103150703d180000c0e201c22120840c1004112242030a150030f040c076808a80c4001160021092a840d00d62000103a0140700c0003424401c0c14207003800202040c001c0c12542c000d000e4100000c00741415038504055a0300080002e280000c42068000010214604200900c10f08d104260307001049905800080344004d80b544003c107807290301901c07410b049030784c0a040c052070b00201e105919400304840c2c0c400002940001405a9994014580b801c18038600c1c9001d204c00044054080c0f061356400000305402036000403807100005414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 227393129 1250 227391879 227391883
    0x30702130b0303190302090102070605090310200c010b0f060c031e040504051e0919032d0203070314030f07030c02010f05100f0801060302060f030901090222050604090809040905 78
    0x504000c004401c0d040e0381d03184e01241d042c2c0040c07014403030130b07400d8600e0300d43c1c2d60000340c4040c0a03446425500d07030402030303401c80490040d51040c4c2207806540703110340e10501c01041080312540319141c1d4a01c02d03519841d4640c40c50800fa1403034000401d080e00c0710740c5009001824191a805802068101e02c11084692112090418244c17006448010010400d604000100c811300340030750707030b9408803018040c0d0010340448130215801035151b203c40d02102a038036240c5c1e0202c0e5500d0f021a5607140c0d0340300303010a02c03e61900881000c0c5a5825640003150380b1506400d0141c81c10104940000314404104200b0180f05074003030006402c03072020708007c250340a01000682c0549403001090005c10301c2d02040003d0f1000310308000040300c2c82c4000c203501c1141c40b242090309a030414000a900000d003042001c40e01034003040255030042540e4000201e11a090b400248540d00c8803002c003042d803450b0f043d807040d100198404c0750340145c011241001101402d40e00c2070741c240031f03d0002a10503641c03000807800340001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 227394379 1250 227393129 227393137
    0x501080d0c0b090c0901060f0e0d02010921050102040608090f071a0304140f10200703201207060c030504050d11070801110403030305070801031a0a0b1905040509030702130b0303 78
    0x21305003170700356840342030050a81c1f0740351030340c000020070403016001141800032420911a4069480c00c960a061a181341c2070301c208810803481c0501e0052494011420a10142c000340c040c5a40ba903081d070a044e003c071860554840111a543d4000305020002c00100000100824508140c01074aa40e0340e4100f0900ca100e180d06027802c41e0042c40c640042d2444049020f0740300582099040051511046281d042e22041021000c6202020050031022034001c00039500040e5a8030107000144900ba00ca241c1851801110801d011101250301000c0150b140100c0350707a20142d1401300004e1800361511584d030766940c84240140030006500d000d01c0d00040c040000a881c510b402030001c4003410b0b0a0301400d5005110940010b0724000110302c070144a001e105040341d8100c40d094403240c10701102e00180c440302408015926035681795000da00d031035842c0b2020b2801d1b016540c18241c203141900727002c180c034001440b41c0c0250302300308501c44c016503a1052030b03904c001c481721000504803074110100e8a1442 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 227395629 1250 227394379 227394403
    0xf0f070e0d0204020c07080601080d0203180f030a050d030f0908030406270f02030d030e0d0e030114010b120708011208030a11040b1806030c040e090705090901020c010501080d0c0b09 80
    0x1300020780301603600000245e2800b100d9001c001c07038500c0c2c1e9840001c00e864000c1c64184c01c005800810410314045d0044800200c0c911000741080c450a04920010340f5040c40362200b260351360844a001484a60940319400180050b1034080c800d040260791550b8007448003c000900850340d07008500c1e070050741d4480c001400c0c990b14203403240d40d4049090032100d00820031001c91081c400c1401c0005280c0c4640608420020342c40010070001e99104801e403403000d41080c6540d019035840e921b40003040c60144000e4005d001c00709125656014010807085a036030000d2191041c0041200100510000145903d40150b00603c0ca079031a5220f550544000d08480355800d48900c00114010a0320310381c9000422480320a500c0e00c83c14581050700b84056400101c030700320342c8440140001c00410306200009a800000d030010388826030744600c00550990340580f01c0040f240c3d404901d4490151091048a003d00324400090894200783c18000303045081440d07000380455550404a641c580b801c02c440d41d2044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 227396879 1250 227395629 227395631
    0x90201090326030907082413080c06070302040503010c03151a040308031f08010b0d0303020a0509040609150909080d021b0d03020d050f060130021b060f0f070e0d0204 73
    0x42800c0d840c90b5620901d1b07004448850140d454000c2c2c88106800d1000d16800c007101d8625150354611907a51241e0410810543c1e41c54410440c51031521000c0c029503115801540380140c40b18104001d040c01c6030903504882041c1403802010248800d01c0b40102412600035200401d1740c1f40c0c6a4031180c1c0b180c060361b80020102e08000c0148070000c010b260030f22040e007421452a84042c0d5540709501d00343c4400b0360105411919060031980824841d400505510907182000e03481c244a03100460100c0e646503010b03081e0720b0742c0d42d140507500b400c2d00824500284208003052040080c40e84509000344690344050208075400214020381d84016600000031400f0f003411f449240f0003119001d0301a520120001908074a003100189444140c5107941d0300a00341039560076034040b8601c8506207132003203c50031030601d100403000c22099160301c0d000802d4002c010245c11040c0224000c10a840c3c0180602802541880f83d0308020301858245d01c020350188040c60100140d44000c004602c1454100c8000380d045 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 227398129 1250 227396879 227396881
    0x816030902031005010608090a110f0a0528080c03030412140a0c0312031a0108040c0b070f0501151802070c18150905100504090c080706080a0507020109020109032603 73
    0x881d00e240d0019041b00c000d9100c1c60429511070481c151039070000040204046100315642100d4100f540c040030400d40081c0c0621186621940010b4900342c8003012020000742080c0c040300d4070540b002c000c0000704100030060903100b1181c1c0000e5280d0080d4001c0030707944a5444041003e010061052005092100041e515041c0e41410266101c000c41d000a031015a406890320401c18484d2003525803099902000c4041594031800440799080050400d840f00d025010010a4010060000b410014818841060441540c0c908142076800340c044142100340d92400030048541c81907070035444030b00b00c0d010060b40c5e0f0b01c0d9850318668809007608071405e0302000c0504600d40000b584d0054401600e03a41169080e40d984620312801e03540f00b02d9440c2840d001044007044541002d400a40700e09100d40300005d001900c4038201441e20786140c2c4030b0000030300d0580600210f5201481250b8002006100920080400740c001a0101d0000c0c803000b00992400803210141d900702c061000c020b81c010118503075076 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 227399379 1250 227398129 227398153
    0x8062209200d1104140c030114090c030f09010603150c12060f0506030c040807060e03010b040c050d02070507030807030801063203180a050303090c04090c0b0901020f030301120b1303081603090203 86
    0x4680c1003402740c000c5c2809034164002407807034040c0f205845840012440d070b2450f80d42c001c00b11400d010192a020b040c0d0748447d2301000041c0444e1010303042d88540f50340091520041100140118080310514011070725050301400102c0c1408041d0080d1101078841c290b883d01ea5107030f0240e40c0d1040b0b034400781260041d008041141544048180c9541c203088000340b2031f0f00c0c1004108000c0382d000840ca080402e400704034684503108140c01604804d4015070560300510340c1c0c0e883d01c1649a100c880100e000590031401404150f07001072510341240342481402d81c202128092030b00915109000c00c964003840030002460074240488205000c902e07880503244455100e1178a0b036640d41064548a44074084c4a496840c00c0c00c00c3d11406180c2c50304a21050141407418154107001e070722066480e41107004141d00403080310304c00c0000710700800e4140384901080720346042001000f00084c3c00c1c2d00700095002c0c111030200c3d81c4200d81a810540002c0d104212103c9130300180c00401c040c140003501406042c0040031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 227400629 1250 227399379 227399401
    0x30609021f171e0423101b112a1906020606040b03191a161403060607141903030e0c1203070308062209200d110414 51
    0x82d24001d4400d41034069228100585404642e0b8154060102e05210005002c5501e41c010076038941141a00e001d0450002e0010b44c4c200144038402081c4103031260315800c1c1c4c0b4140c00c0304040f01090300f80380000300008404035851300d8941e50440b40c80c02d00c510080c00711228108186034244044c005005542040402c8200c0201ca88544102400340c0190030003e0802c0c202402801c0e400c45006000d000170820009100d0701d18030140000343d4440304034561789640c0c54008468540960b485484030040450840e0000b08143c5103040d04e885544002d2091000e5a250081a81e4210307601824644014005010b2545804400c0f40c1407001d00d41c100384e003101410380603800829200c03200401d6800050340c0c2c400340b1114044040104105134010044134004c28800c00c0d1240c1c001c00001c00081e002d00c90a100303510518906c034a000c0c0001da65000a000700000328480c8283d0000c2c1d000b060b4402141a40001d0229083d000003901001c1101e0200c4001d5990382c2c40461014a142e8104d0f54a040070340400c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 227401879 1250 227400629 227400647
    0xb04170a020109020307090509030406030f0e0d020709180206030112030210020f0c0708070602071a0d0c0815090405071203030207020a06080103020108010b07211701090209040f050402030601030609021f 89
    0x81d02038006c0e2040440c40300c107207000d030314850800d410040d882c1501e004411401070120030022031b1902c1e51111080510501400000d000203016402444603e040590345003c880c4014034540000b1083c404410040c0c031000f040c1c0e130455181c031220003a200901d007000d03810180085010a90b007440082e107c4051079409001e0308070320801c07508461000b501c640e0150307515012800b845015911134981000051864001c000401c2c40c0032044a0030720340c3d0a960101642e40d403038141c00114681000300501c0b8400310007003040c50b035012542d17810b450510b070b1242a01d840680c040e0081000e45010101c0c1494040d8048802c070542c00340886940c1a13a035007006000000070b0000f207000450342400012000120025034044e01e402c6003200381c130321040444100041083c0001e580901111046482507000300410481c0200030380703c000740e46d8098000800044442d110110414a4034010500000d40c50000396981500d03404000000c07411b195000244510040005204803001001e10745041d999101d100d407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 227403129 1250 227401879 227401883
    0x703020c10111b0d0807050f06010b030f060f1003020306190306091403071e020f040507030b03010b0118030b06060f04120203120405010215100f0e150906030a0b04170a020109 77
    0x3a0780c3e001c143c4042d400a5112988001c1d511054841c0301c000814410030050512610030022a50092000c091060404100742c1c4500c41c0e100010040110380c01c1d10300c11195200200311200c03402c2e803d0b9407000a501021505103042095070100000d006034032581c595502c900c6101c0780091800780d8034500b10b806040440e00072074451584042c1c0001a02c00001542e41c1c0550000c00003454200e0401000b4040e803103801c080c1d07401030180d1210212500d0381d200d2240241016600410494150000d141c20b461184108604200d5030085c00503244851104078010b480d80060703803803403d86580c00050040d0042023030440d080c500000d4000703006032203528411181c5e482941542c0d4188400400ca08144c0541d1080c240560401d03054848184120b181860307114107812801e40b0020340720120401c420308030b500001c83c0ea0b8203440a0010000354400020707101042114201594a000b1010903240d0840c408010002a8044045010045d0010041002a42d004011504c580c19800020f010300900081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 227404379 1250 227403129 227403133
    0x40207061d01050709090c0917030a08090c031e0f0d0807170f0114010216060e09010b0a1b0503040506070f02130b030d0e040b03010c09050901080601080d03020703020c1011 76
    0x80507084210600616110701c1643d110b50b04950b280541403400b0b00211540c0c4800c10141320303c0410080c4c5111190b2070382c0e0402c00e008649034483c404003d40040b0024080d0661540300ea101c030b100c40c0d600052032007104110240302106885071412440d182c103581e44001040c1e401191408045240d200a040d40b10302402e503952140188030813403524241005489581c082e2408a00510440884610124203410184120303680b00d449901040388100481d0440c034002146240300d0691071426883c12030140c890b0315510707450030705000000303007004810324008428180d0450400050003428410ba4004000c041d10050f698055807500c848000481d0304103e128501a00301000d9001c0c3c3c0d40309109016101070000d00da1204c51080684101549685942d40300303450f0300c1c4400301070310280214a016419611090001401c0900304144080141c103d6100380c0c0c00000108070036500055542180042401e00690758042801c0407824087c0140369560003040100c002e0311a0360707100c003640e6100803200301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 227405629 1250 227404379 227404421
    0x1e020d09151b0807050a0f18030809102a021f02070512010b090105090a06080a06020306040e030a0813032604050c041a04020d06050a06080f061206131104020706 71
    0xc1c003038483c0041540c5141c00100203021141e042070058440c45e441c00501d0400603c401c5001481480d64800b075042154040030102d070030301d50341c100a821008502036a05010f6481c00c4c04c406a20850103036080406000c0c0ba1024050095450f400814000324030403021a07403030b0005113180a0359412292282d5800744541c041907040303000d0184550b03191303854000c1468006908c0c08042054044000c3c0c210700780e60b030b6580340c0010341c12010815411203070710900f00540c072407428500b08004c0f642c440300e86003c260000c0014180950348024060b030300500c0b1141880d12000c407800c084841c6481c140c031350b00000802d4800c04011907000b86009100c1c074480d004135400340751208240010365812072228919034048009410700351030b0a8000d00403401940c00001200c6586a000640d1070b1403507407180020030440800d2007048010f804801d5407040d4203440e0306411080b1440c0d40d83e80c03910002e00c0e030240e10024582d45410455020400310f201040208199140c070f0040c188035008059041c007034816120190 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 227406879 1250 227405629 227405681
    0x1204120e0117150604030f0b0c131703090607110a05031606030b120102130303030e0a030801031b08160e1005031207110a1410031e020d0915 62
    0x1000c1400e240a06030b5a094003500804100c560b110409403140140000800481006844000c09400214025922146861200d090511801d04007070a84480d002c0c04001e610b101c5801104244100c0e90708908020044c1c0510188038114040d5a140301e500590008010003448000121095080b00031503942100035660030070199143e00b42c01034081581c48440e001c10141c2d000b0303480820301c0300c80a416900c540c14007110341c1c0e003280e0203e440c0452544070001d060092680c54460031501e084050000c1041051503140505944c01c140300040a1314411100d01c01f2030500200e0701c1d0020400d842c11503041c1e0386ea00c05200100c400754080e0304450109680019003081c007a0b103112084400160103070668407841c030159841c0d0384c4000004c0c3d0b88040d20f20300c1078025480d0a804840200368080030002c1107010001080310610000c60400101414104051031070241e0410495401002800050340e900481c01c000001e041400d401601d0501540307451441180766400c0103540f00515512405561901 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 227408129 1250 227406879 227406887
    0x301030809062d040905090f0c011812080a110d05031b0d05071d0a1d0c04030512040303090501030920030f030c0c0f030f0a032604030f080601021b0d0303090503120412 74
    0x1624080584d4270683c0c110f825540900d2034140441440300c1c084015a884171695403000020300c904176600800000c9507000c142d0701c90140001c0c14040c4c80030340042100b130745000b0610700020b40b070340c21a80d00a000c0d15000d624002c007204c0791012403600900903032904c1340c006443c0d2050b072234000d003899141000f4051289410340f441c000381d40681c0325820b035000105203860038003103000700885100c0c00c2c200b0000c40864002c10441c0c01d0307882c503112955607850940c540140400c2c0e46170312040c141030070300b00c2c2c40340000d240030464008084506100e0038105a5400020b240600072281039200b8003000401c1e200b0300d42e001c640503020f8241501d101c04411080341c00e041d038503520760315400102d03000020340800191188038140451124001c3d80c034101042541411800c61054608a022030801058a03110f650002d26080d0702c03e8090000d0714007a042c0546d039841e807288043d806841240102d9090781054040d61010622981040440e030f1074010500035088a20800d80e41601c001c0180380310104a9842 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 227409379 1250 227408129 227408143
    0x140d1e0f0e030706021b100605010e0a03110d03030b0d0c031b0501080705030603030d1409010608030a090b0c151807080102030402150a0c08030709030311030301030809062d04090509 80
    0x10703200039442e007261900c3d040c009400500388003d0000716442c5424641d4420010120302e50450b5000040c190703d00130015010384112042640500200c882c10400701c2d4584c0307180707003c190707068441e8940344d10503103412801401210065580302e010445c004c4140300e040710700e00017520f00c40d07200040070b140c3d5641c0c59400100144611030004802c0800982c0c00340c4501d010b1a0400c5003c0d08890030119100c500c0c6045c0c0b40450607100c8203d84203810821a05800d01aa030700400101000e145000b4001c42d0003065500c81d401141e0f44000c00040040028108010051000700038201c509000d0800c0d21500304040270081050403548210800441d0b003007070600c200c80c09103500420854040401c0c0304805c011b030b080405802d05000f140ca81c10305c04102c0c0b0b5402103110384000c3c0e548283d40d604519002d17200c500080355080c0140e2041c030061000a4282d003c4071010281224a90f072500802c04403121442090643c01c220300c01c171000d04041100600e0060001c0d108200020320590340c4019200d9982c101c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 227410629 1250 227409379 227409401
    0x180c0901060f0e041526190b0609040203070b09030709060806041403120a050a0902130f060e06090402041e15060906080f160e0405131707030906140d1e0f 68
    0x5d40c84104044204808031000e11703070410740c1a42520400642203070428000041240d0144203042040080042c400300066008108075a94041800c054020903a9030a4a001d0020b02c4480018020456542085000700400706d0750070900000e901c9018854071810f00344c3e030407280080e034200d03006a042008400c1c3d5141705601204c00d0320740c2da030f0404100d020745006031a03c82100d80e200c120001584855119400d803414065000c113018040e41280c60450301103a1080100903200002d0114680d038103503000390840d40460b03000c5065002040d004001807080c000c403421891401c15526061011075124001304c0f400307030b2584071032907555038803d8600a40884034107801180007000500072150002040c0d1810340f2511301000591500700124040720015583c80380032141082c184e408100406580080866424100030300701100c0359000340c281c4403907000307038400c1c017500a9140e0407400c00383c82a40c0d003040c6003d10900040c1d290980c1c801c0b00d914070001800040d410b0030149030b55078404c2c0c040c0d0f070b600e00c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 227411879 1250 227410629 227410661
    0x6060c060f07050c011a0f150a1b2a15020a0212010e060103110a06050301050319050c1003020301170d020607030c030b1302030403091e060302090a170d0e090609180c0901060f0e04 79
    0x35170b4070402105c0102c10745800e2240108607803807030008621519081400c45094803108000070743c032511310741c00d006010382c041c0cc211002c2400240c805030b80400e140281c1581601c090090a442900142c0541098005100750b0f101350710000081c0030035000c1801d45000b0668400c000c191722124115103030300c824014190564080c10100c80c006001001d0000d216000d2001d03903810800c840c0c00940015401d110303460000c2d0300800140701d201c000c1a012034141c020726000b0b0030b800c103100c4006901d800c0d00074131503005d2541d85e012540b100b5000c1e130020280b44100410300f15021921041c41c41c02500142c030103400041160340c010a5032443c400d420860300841d500c1030b100e220318001d0120007a50141c80c1c01c80c0c0080078000000703a403a18290018041804800140064003481c1d08020701034410304111603c1550035106015172919820300d4150401303500c1000b040c5001c00e0014440c034252403480307010b402018030400090042d5206a4445024007070b5680e071807900d04450100000c0d12404894a0504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 227413129 1250 227411879 227411887
    0x2090103140106030605010605090102010e010605030a080c10020d090506100f18020408070603020408061e0c0a0c02090a0b04240b0a020a0812070806060c060f07050c011a0f15 77
    0x31440062214001444032070010400607183d95501c020f0701c00a07400000032407008581a0006d607028043c4c0042704a00c500200440e43c64000029550740100d1409070000e000040c0c14162517105200ca00000016100150340c0c5200b00fa60348130081c00c80d440150342a0007810f01040d8502c001d1080396007200c03000308030080c8240c00c20500b401000ea140c03c6c2c51000c1e580c02c0000045c85002070201e40c00030012500c00680700e80c9403c151500301940100300d0b46034001381c0e5140d0340f80d40080301c2c20b45c2d8001d20320649054640d415214259550741c0025030203907000f8541d80c108250034803290401d00d000401900d0501410716212040e0060300c2864250700310309018a1014030180c1c00f0040a01500350141c81103806002d5680ca5400031503102c0101032240c000c0020410403c150000c0149030080303020f8940130b2a00c10444d041070740350240038000e69015498940403544d154850070566805010390402042000c0540c50081d4a68401c1440e00f402036100305960805031408000141d42041041891483c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 227414379 1250 227413129 227413133
    0x40509160303030b030304121202060c0c06011809061509110f0706090203010605060301080304060e09071707020c040e01020c1b100827060a11040b0f0906041a220302090103 76
    0x4d07003081c8480c2501440103000c0001c0580c698240c00074050300803018030605403090100241840001440c101216070308100c0c40110501c002103180c119030389194911900500d06991101030a400c56000e84400c1c100706051040b15019130540d4129410110b00700400138540d613001e6110301805103800c084580030f11000d008141c00340c01c04600741e4401800003c00355194400115960009c0c1c010611903840420705005883e040490b4000008003128072a6030ba1800741c10082c11403000c1c020b42c44205040d0b80101e65802d000700021411001c000303106100001203921005e00030740007140d6194040c0b1410b040051401418096840d250502030901840005110030a071951b003000307000e0b00c0c03008070460640c3c0e1307054058128040040c20704a01801c0d950401c0781d80c02095a0100804a0141108004c01c0102a841ca0112161411751044032170b29108a480050f14030b0140c2e0780300c444504194102c04400041c1381004114011507003d062190701800000701208810b1400008c0d0408440001840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 227415629 1250 227414379 227414381
    0x17090a0605180d1d2101020f070c05041a0d06290a05060711120c060d020a0e01020c060a1d0604060c260702120307140106051305240102030c1b04050916030303 70
    0xe40e170001c4022204051640322182203a02140e6141325002c8003007490310070008208946401040122028008668210b1007030442210180c011417290031210301c844100940c43c1c10021103c01001d8048803c0d000d0400c507040f0809800f21160b00c11516400c0c00f02c0c103458010181c4500c99040850882e40c1d00c10702080c40801810390a00b4075140c8140c4c1038003005991547c0c01000214032201025031124080305028241ca8100c0c0590340c1590080c0d401582c180d154a003c0d10716002d080e01d001c00600312141140320054100318156504160009000310340b00750404144001c3c6440381c50003800400000401808020142c40d201c62010701c1044000d01600c0c04040c4010001a1b41782a0384c03600425595244000d045266980c11694540c40c040007185003a494403d01d50380b414509200c4c0e4034128100040c100c00d0075125802601509000360b903e45d100b001610948115403040300c0700304036140c2d2a5039143c401d80320100e00c2682400c0c002501c0303030000b003401c000103585203000014041c1150b600f03070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 227416879 1250 227415629 227415649
    0x60b0c0726060114041802010804110f1c030807140906030a0204090203130b01080109020d0b0c13030602130f0308030f040201120606080f10030317090a0605180d1d 72
    0xc00c1600c601c100c0d00d5031950203001c02c2d4000e10010b04040301e000303100c00c1400141d842c0700c500c40da600b12400481c0b00143c1d0f08009095031080c1d020307400010414503c000244410031007840d06410030304000812071501d004908104041e4025110030900c1e54818104803502c00d5140c03401082c01c0400e01940410f4282640616000141d2110260805446100f4902260001c90703d154086a650010303c0511441c80c0026001d81070440c002e0003001060f1300411601c200d41e0000800380401030001660290004003a601e41e0320109607901000c80d568145040039401407102c004c06060740d40000622200c00e1070140c003c80c0d50000b00182103a44441751180008401030003a4140407000981003401551703407050b00060101350725a00a1030070a14081081144014418001c07110300340c00501c0425003104002595a0386c0b104041d000e43da82242039400c2c0800c19400405042c10001800201042c00041c280184168011a10b480b442100100c0d2540e41c5103410784000c0c040c405240f01903040c00c1ca440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 227418129 1250 227416879 227416919
    0x601080a0b0411060708071209050105160606031202060403020c01020616030218190306060b0c0c060715021206100206010e0a02090103020f131802090a0b0d1803050409060b0c07 78
    0x140f00040c104800b14805a0020740d04650034100000e04000308240a20789840c54401450301e40403244c18100064054070440310700c40030074480d100340c4104010444e040803005c0c0d42e210301c802441c0001068060356a0100b55400c9025000381d44450046510000e02c0e507200f03516441014004451200003500258840404601c44c155001194403564490941e0b29010a02040508540d10b1460400e00100c0c1e611360080390303001038100142c00c004400085c50410459007147c020340d459009d8030703200c034018050381c0e000201540003146903214510322410305131141c2d0302a61a00c2c0d0f9020511002c98440009000360a43d1361160004541400c4003640903080c51401810010314160382400c2c0744005030002c0340e0416180300c0345001403020f202c48a141080011100d40d0540c14002480000b4040c40d0107070161401d40940071507903131039401c8650481e8188001401d048210484107040003401d5600c00d010f0b08a0340d5003045400200307442c1c9181182c2c2600213120241c111103040c150110112882d01c40c60b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 227419379 1250 227418129 227418143
    0x51204110a06050d0c0201020301050d32060109140f01260f03031005010c030206040611270906010504242102030a0c0804020609150c0307230601080a0b04 68
    0x41454948461081d840500642e0f140d403078880551203031800940d510003007040d007164014001086145c48800340018401d910500c0400640001030071107804074079980c2c0d14141244c00c10301c0002180f2001c107069050f40c0d46c00e041403090540e5902040d040d007100ba11050356503a40a8010407101134504100741d400c00301745003c084001e500841541c0b5081c9a0b852540c642c0d000001404007086146401000400003030038440c4203241c0e01d407806034941000800c040e240740c0d00c440480360000320650450b403404034160b2108070501c85016260f41c1490303558600c81d000d04500c1020983c550300400039102190001880e600880914104500b0184a4000640c0038080c014594500150f550b00803412110741e040701c010f80340c0c80c0000c5407100741c8003100300071410702480c032080c000540c5070241100d041c0b40e01901c03941c04400c204445012944161090032400740800314440e010004032220184032078207020359021040d01000903003500c032031742031140c9000c95022698200004480b40c0640d80c1c07150107012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 227420629 1250 227419379 227419403
    0x5031302040f021c060e0903030109020310120807060507030b060a14070629042c0f0d020115090c1b2f10031a0d080f2a0102030601051204 61
    0x40c10b40166041400c4a00020150381d4100882c100c5610541c8020311001c0440540ea04010f0700c1c103916480107001c5c00410f00e070004006840701d6103141c00180180300000d41c8108140440c10b203020380c0d03041148101c0780c0301e0401c00030440d01c45c403034022074208450050070b271483c1c40080802543d06105006408031005810700201003c41c946104e031251000540f40b000c500c9504009040803400d60041505201d5890481400044010051403050341000c0f5030b031707110050701c4a80406151009802505015101300c05441c4050b95042d0840700b01d0a0381100c503402ca45e5190034201e0280c4400d64450000151049196072642803541c040d0001c40b801100c92440300c0c2c1b4071045c20b072054114a001c1903101150050070140500380395000d10300404580c60b041080c0002040158080074443d01800d00c5000c101c1d02d50f000303201c400c500f160480800028540d9554505014605030a1001160b9296a04c084e2492402651042c02102d10400c4140c0d030b041d20b0118000c641120341c91000d80300f0798841c181e100c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 227421879 1250 227420629 227420651
    0x9010f09090309050d0506011a13060c030210050c300708130f0f030f08090a110102120d0501080c0901030c03030c06020c01020a03050603070815130809091005010201110405010503130204 82
    0x11030001c400071b02980260155605081c203002c0007040c1d604500320718590800040b0280c000d840d2421041c0c030103501d843c0341282014207040345403036900c1c0e044000c82071520040c000ba4030200c00c02000c4682c40c3d946110491040303290ba559500e203c520450903410301c02d500141225110380e40059020324aa4480d012120711501e440c401b03613204100c115484035209004805154009074400c0c161032079032074081040c0c501408013903103d03d001c040c001c3c140004007040c101c13640c0c000c0c42040245140203000b2a111040d03c1da01002030f107030a00c209906405640321b8249582851010b1718141c0b608482c40922662440d80e04880d80c1000e110180c2e111070307080c49584c65584083c001007410480c55640814a410041c04050400000ea030016070b40e6032014440001d10034002e00c8a9621082207844000503242d90700704440746225007030700980c2c040041000c0210740741602c1886d13800e660007a40204024080c04410217440c4c0320794040c590105030140f0000b4a100206a251b0201920281010801c50519 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 227423129 1250 227421879 227421889
    0x5060c1b03070503030a060f050d0b0a0b040e060402242502060703020102130b032a04120506011502010614190503030301090603110405010506070f0c080706030c0e09010f0909030905 80
    0x242c9800c0b41c0941002040c4059100c16004401c00742005415000c61a071902c40066260316140d400203020000c16000540302c03032425401510307041000307001440800c44501345140c80380700484040744521204e81e6411401d800001c1c3d102110f044144041d490020541082c0700d815015a09641441240015010068031280b0107824654405d07000580c907070100d55035481e0007020a402400c4074180070300400c00c0303071080d00b404469184041c0d00d58030301c43c404107191000d00d440b55402c5540b00d00959030341c42e0204000020014100c501a060820003081078020490a0303c0c403a00c100c1d041e4101d0000045494680440e90954059100d00c14a18a996035004641181c100341d200000b11aa6401d042080c440c00f1520b040710480c0484040000b036042c0400a5264010408050041d80c160b2282c4030401c4422030305031000d8060807044070911540c2345c1e0014090000301e914040000d85255001c0c01601700038400b2030689414010386100c3c2c038180840341d0018280e01400750100218102c5c0000c298940d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 227424379 1250 227423129 227423137
    0x1508060d17190324060f090302061908180d261611060103020a06031116050604031b0b010315020d0609060303020c030d0905090a090209130b1305060c1b03 68
    0x20b00010740e1100507200101600f120307007100112550740707900b4295000300218024280262401400c00340070b41700030326404491004442d04000e40285000a0120130b40c92184044685024503a950310f10543d50500c003050f103241d50700784d50305081d80402c070000503840c000c4900343d01060845400c1c0440711140040d407500d03198241ca40c04118075011074118201c503401100c01d5107054600000b8a040e500d90b901084021400384901c008165541180c04481da089804582c500840782044500c2e004860600350b49030700040e40c04038041409152130940c031440207120b200809070002c826072820f0f0b181d0303200c880c034804c90b144004045550030004455040281e1041001400c0710203000100c1508610f400f03441d2642541c02148607070700c42c90940b0881a40076100009884054503440503a480f1000c5042c06041000002540000407104000c0030f1f00000003503150160140c80ca4803502e07225400b4041508800807005020758121000007020303444e03c1d41c01030100341090076442030002035403e07420703044d500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 227425629 1250 227424379 227424397
    0x41404090206190f0309030206130204020f0f0d050105180f0709050d111002070e0c0d110a0c060f1b0c050f060f07080c130303031a0405100503071508060d17 69
    0x100e681200d43c8101d40c40407000b41c0c00ca42d14101040314594a40703019668043c01401070029003d14005c10086450329010b842c0c0d0020b400c100c154403400304200403891900300e130100c160380da032900300001118a08101c0071840c0e060800f100c01c0b0140c950110031040f40100404500c18070461040004854032001c0300300c2d0340d05024040d40341c8900b603030004001481c007003858018110750142205001c8a450035132a150090401844141c1c0e501c2c2c0c400920024004c0c500c031050341e45001140340505103400c180d00307490a52140720108031441002d10648103c1e51000c00d054008803100e07103080c0803140100d50784d05820f8042d804480110780301d03600107841c0c2002210707140c00c9040a1403d1182094005000540001803008000d08007102141c0701d02100845e444040c041603142c1440404246465403c2d00480390003420901c041c1c6031002c0442101556485168064072501c040020b08001e01803203100c0080a0340d90b4444180c84090800c4944030724624140c4000000803184010b0910090040c41c40803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 227426879 1250 227425629 227425657
    0x6090c0e181504030f0f030f020f0405030f01090506061908010606030e060906060609130f090c140303032a12090615060306010210020d0f0207110f15041404090206 72
    0x801c1c040c0203410040e810111100c4a80b604080c440001e0300a402c44428140350f15218810b02038840c01180a0450304c07a640300d1403440000c80d2550072000000030016078405404844a0316844003130ba500700d82c214034010346260014000700380c02e40f0700101005110151004000d04240d1140c44441c00c484480c0d014402103030307440440c0300032203006000709540820160041c00d404c0c90420003080c484e100b6607040a215840038030340082e050b83c1c0790b44065101c1c040e5007410003010030245800714440d5414061041c6148540c0c00c1d521803031070000308880c41030510052880380d41d9100c00e10400d49005400030302429590900018a0456009000d00d200c2c1c00c0d80c00c004c2c402410100300001803801000c030b1080c0248000c00c1041000d0740c000401450000c8501c1006a49a10003503400c0c0081502200c010413241c0005031f84000c0c081d189012142d0303440d04442c113400740d40c3c2130002c001603400804407180e883d601c144400c200c0d201800c0b23088034141c0d102a2011410304200d5001030515440118842454 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 227428129 1250 227426879 227426911
    0x40f0e0a0c1211010e040905060f0a0608011107020f031207110907030507020a0209250201020403110d030210050402040924060605091809030f040605030f100e0406090c0e 75
    0x1109808203444001d040e0141028082c104a444410b09140180400c0303040c0000d8134100d003e0b940b560780c4000001900b05013a1002402c0540116038401015035496202c541001c03800704440320b041c81407810054010000301d103085842c0d03090114400302260304c1a0b04d400780421003407100d20b110000f080703d5441007051844101100d800c00c007800e0380251690041524000800c2060741d00006c02c1040150104c03504101c0e6910561442a0340c080142d48004038030151b0b0030503517103036015000380040d01d200d840c2144000c0650414000107814070308024005074004100c0c51a051950b50181d03030002e0000c1c101044004a60b01d4103c0d000c0d0500d0b22201695210072141104201c240c8031304405440b0528281d0314020484001036034010100c1e8101c190083c1b0380c00418418201042150065181d10040c0307030322a0790b41c0b9400303400c0c0d03081181c000c0c1c030b03844002c0c000400b0f15040088403000e07100690211074094a076600c6200003031284a00803140e01c4172880002c00c00d030880d03610b1a4400c60400e0001110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 227429379 1250 227428129 227428133
    0x420040317030402090a0906150b0a030b0904021c0302070503031b06070305100b130305010912090b0301080d0e0616050706030f0b060f16080a0c0b0f040302100506040f0e0a 76
    0x380c1d880d01184404100000d01c1844010f075201c010054104c1d001102c0070490184c542003000081c20344410501400c0700804001900d804148090030501ea41a1001c011091528007400006001202c000750b0001d0002a00c0c4500700d0703258926035103a80a40704407031400e42c0b603101080c91507100c500d0b00f0030102d110003151010030004000856201000b441c0500c411f04000210558012050241c1c405140f00411401c148030300e042041d00095400100070702c16080d007410030300c21040d0031403034500000e40051804102e4000c0201224101c8030800c00074148409081d008517200e40340360710615400380c020042021080c85150000d403040d4020700141200d103142c45000b070112034a40e2040e00c0c000b403c21b440f032041940c40b0030a4503030001c91101c00540d11402480144060707060348400500628003ca031121885a100100002140c440c1c00c42403401d485810104400000840d4020016804030f5240c50b42034840781c020707a40180b0003400114a104010f886201600c05030a50303203109034400d20302401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 227430629 1250 227429379 227429393
    0x305040312030e0a080904090c12051e0c09070903240c020c150a021204091a0108040809041116051015150c1104050c030702060709050f0f04200403 65
    0x51118541c14100aa006540030700f03515014082c07400341c03001d40007144c018800d07122604202c3c0b0700741d4404624642c254661598801c4001e1080d000e4070103103e0000001c40701c0d032a001002401c0b0310090014240000c02c01c1c10800c140301c004162600704400036100100286407120182090a0001c0c4907480b01c0d4044444c510440e4a140071040031035001c0c1005281c0c5882c0e803501404034400d5600c8403540e45080321010b0f40703004d20742107080407801000140000c00190a42c01940c501103411081148101d10000444030f003101941c1c09064058204200d00980c0b505034401d0110104202c0c03032074103054210120540c1002c80c500b041d28160803410141603a07500e10b21817000d015490300c0300c85546609024006042a41e4007203174a0501c05100d20110034040020340da40f6411900500c02c0c021840c1000762003500d030b041568000050b10405003c140d109014614640c19110040e220450520030501000f20343d04074000c41940060340d40040042100c000200502c0310030040d040c0550b84c0c0e00d5498520 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 227431879 1250 227430629 227430653
    0x13020c071d07110d05040909080405120d02120301030b0f0a0b12030c0f070f0e0a150603020429091c0f1103060907271d010c0306050f0d08030709030b0403050403 71
    0x400c0981140c2c1454108075044021b440c20f40e003103924009045405841c1c20b4201d0700c181d800c0703544c0c0107003201502d07030300d02c05c1c0011030f99040c2c051503094071001000c2001d0070301da90000b0f00004100da114400010240300750040f000d0381c072009018010810703500b80c5010650f405160b40100c64140c0000411464410003040803950005c07600340200703035251a050040319104068010720040c0c0b2501000718101814a40010503028280614501096552003001e0b00950040c8203503075803480c0580d00112401100c0440782000026410b1281c98625004200603441450341e211303d2202203105003050100f40e4018032401201e103e050048040500c2d00e00b01454088010500007050340041820b101e01c611340400d46500110f100c841d150348040030350b40304001e005420700070001102040c138984034944054010001c180082d0300c08021244e00c81c000e00699882408030b2a0b0031103030010040000411420081d40e20002c2031801203040c41c1c403a07a8100300100d00340c506030001000840c040c000d000c5c2d440140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 227433129 1250 227431879 227431907
    0x516170c010503010e04030503061203030a1401080d0f0e0112230108030307020a02010e130f0b01030b030c150d0912020307021504060c2307091d0c13020c071d07 71
    0x6411136152400504103084000d100a00300400400815541e0f2264890310091418800980e912490a40280001400803103030108a40035032a000140c010004600703450103604682d52a00c00c00b40c1c10300142d42c010f03016142075040003e800c1c0600c08507403132031007451403c2ea030008194601c0550500784104181060f00301c0c0095410400c10300c4100c6400041c8404250340c282041c01c404580d0200041011b0f614801420745241000345400691609038083c804080007600c4c01c00c600c03010102450399480007049610381003056070fa6603501341500c2401030402c036403c071040820010010341d556008484000c1c200d602584c40400e4070400c600e484c2c0c11220519442420048c1490300d0702900811a03140340401074900c140641040d82c540038120080300780034640b0b4003200c0469944004400041854001d0342c02d01d01c424480c0e051460728003182250901400904100f0400440390158000b903100314004822441100d800081244000e0041d80e004811881c0b0b152040c9001600030300480d114002c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 227434379 1250 227433129 227433137
    0xa02090108030a09090e0316211b06020d0b0a0305061608161d030d0926030a05030702010605031c120903120b01030f0e0c1018120516170c01 62
    0xe103c0c070703070004030343c41100c0b0070410210b000001108040d0851044503060b0a04889070f02d500000c2c4901d201e81422801c1250040d401c4102200404642031048075110315a404070345030100c2c004c17402940180800800e84240041d6082c0d0050025090801c0342e4001c86041c1c028030100414140c09942c0303001d0030860f42c2404809482c2c2141c010b0074601014609209105c56540114000040000040740502014040750b15552403031002810606142c840c000d4021031084039400181c546024403421414427100442c18183c0f0f110f0141c40c9174000501500c00c640d6103400000f0965030400590f00b1030392900080f503250440070a0001c0c50051108014082141400d405000103503200d403224040c2031050030002054005540103c002d0b0544a000361a40e40c00c000402031440404542c0704500103088600720380382c50742c0540a842145a0301040d44400e17000a8041008005414440a5452042c010394480a062400d01c840f0f500340303034114007004425140b10000c1114108001e00d010102424 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 227435629 1250 227434379 227434387
    0x60e090606010f110a02041a101107060c02061210260604020103020d090803011401170f0c1317062d0406020f04030209010801050906100b032a0c0a0209010803 70
    0x40081c0804402d041d1120804c003c0050792102c10000348050f410301d40e4000c0007030229810050141032035483c8886010701c903900995100310294041c0c4044a10011000b000c0c1c219540b4200096170a034020b201d0698004c482085003d0706152000d035058803e4050802d60703a0300508008680c252110000200745450b0130101c031000002c0030005046a00030b0b130900e00543c0e12034041d000c10014007881c1100a00c0d02030040008100b540228000107110720013a640d0178040300a4401044009000740e89200c0d9000c800b10202c2c195401c2200103049070118070440d5520290b485008184144041c00f5801403900800c1c1480f418008010550891400291880c000348402036400f0303a4086001d4801000542d000485d01e00b80b641c5c02050304c0046070024418007003036950758225800b0b8030080b6500d4405000d1600003400d100701852500381502c02098217681181e81d124010300303103110134003000342c4840b40301c100b81010a100340004204641449010f0491043da51040c010180c1d010307004625903030400c0c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 227436879 1250 227435629 227435641
    0x21030c05060f0714040608180709060611060a0506090a0e031c0903090509070e0105070614100e090307080a030504020f031e010f060b0319060f1409090706050d090c0513060e0906 78
    0x4011f64018164100c556180001405568075256155001c050300908000300091401d0b00000d01c0608040747d2070a07200c0680d036035082c0c2c0f02154003c860300c03a4800d0b00000420040749169000502d0705400d101140c3c90720008403c4004e054040b4140c00c448113890720000d00405500c040c4041c0104010755140f5094281000041c2110003140301c000e04000010504c3c0e070901c1500d40010b0102c1166103913070065420b04034040075840d04103000b01c8000d0b18032640443d80d803160000444081c3d503040201503080c140140c0084000d008094001e070b0380204003007141e440c9aa402c1c01600c01c5500d01b80e181a030149005180e1300e080d41c44c9412003070040c500e4110200066211102140d6201c0025444e491102c04481c01c11001011681c1048060305180b00700440d01100071b21414440d030740100e45030003859503103400750342d5107080380c0c080c900004d5018880b0b00240c0d08950845141e46204103064101e16440300d01048044004400c4404503a403545010080d03510098078031a0031019200c040c00c4146015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 227438129 1250 227436879 227436887
    0x1090309050118050d0c21050a0201030f020c0607030605100305060a03080a021f27021003110c030309030d05100621060803071109010b0421030c05060f07140406 71
    0xe44500d505105a580900000c00c407001c44076805000c008142da1131a41c01c0342841c0d030001c0c280d40504810181e02411104013295024804881d403503005009011040ba00d500450290480300c8040796010340a00ca010004030f0203102851084429990000d41302e4900020000403884410b662401c0c5450701050121316150031000d181601d0b041801155035510400d4224900501200c0450180183c0c514113007103d0700b04e8002d2304c140081d0400c06641340341030440301400c04124000c000e52004a148064076a540030340c02c035903400d103028032440f803e00c89410040f0382141d008403540002c1d80c0000417404400d00062103442e8201c42203000c904009030400380003614400c4408940c066a0704484c103880340340c494640001c1c0c00b80c2860800c4c1c0703403190760602c2d01814a0240c030076110310501900d400070513180400c00c02c0c7d4080b240c0c14024503240380280200b400300444400b6083d42000b0304272082c50045141000700310700480f143c00c0084d6540c0340c601d00c010900442e0201c0312100752000c00040104e981d00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 227439379 1250 227438129 227438147
    0x8030d2405090121020a0602070f0b030702060a05100503030f070b0f010305030a0309060209150703030501150c030e060d0c090801060902070809060a030b030d02010f0f09050717100501090b12010903 87
    0x515102458107001050071307104122030307840e030080d4002c0354002c010820644c04200c40049a490341c071400c152603224a20011940011110100140e000d203000410302d00e840d800c000c6d0170240802c4603001b00b68840c40401c0c2144d01c00030a846404100181c00350420802244095005400c615080c01f554115076440781c803442111403041c00c00d41c94009400c180728159040380c1c4002e800a217403441c0b0100e00c80e103380c625040040250042403400300000f80c06035411036008082d02c000c2d980c0c400c03800700e1583e041d180034920445013a008007086c0a004943d90700d174810b041d00068107803113564800b841c090402c1c1c250b84c0c4a4001c6e66559005000f0b01d000901d842007034644801084849944401819608500620705800c04592511680d4a540c0c5580d806602207102d4602c0c0c100c0500c400c1e181500582d064800340c0b50010041d0380000c4080003a40c0600d80d40300e41d035100241c142c0701c0c0c1d0701569074074009940d42038003c0c243c42070360b441c10107040d450066468041c511218009008444048c0c42c06884120 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 227440629 1250 227439379 227439389
    0xd0207170613061b0e13050405060105010c1703010f0317090105030c251112010b06030115120606030c0305090c01080a0e2103011401110a110a08030d24050901 70
    0x28590801d01c10084540c00c0943c84c241520069600341d9843c0b40d00400501e103d8100d28080e80c520389030003401c800b40c0d000300c1e480360f90032000911050b480d20b001100d040b032000e007040e2001c06169070a2140c4680c0701c0300440c001e20001c10145102415030424541c100d507043c941c4910f2180401c41181c075030340c1280a495214100601c8581c07540071000c02c14008060820b03042034041520b01d189010400c2a0345c0104076035100703686495000000d031100c6422102c00391b1034142c0c440d4080c4010004c2100320140721881902c1460450002d02c000c883c014191405a001440442d8940007540941f550500c642607028504000819102184100107011072002529072040c5d2074440c02800070540701040099140300362150781030040d0320400e007441944e4200b07010f0b040d20700c3c00c0580d050005610400707085580c09403401c090800c2078001e40e01c0a4911002d0785545030071104c98100040c0c0004140040d00350b5100100000c15003400194101e001f81008a80448180d114580c0903c686e0f19104800342c1901c5c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 227441879 1250 227440629 227440651
    0x1401050c2b0f120518010905061803040815100512030703020d030227041b050306030708010b0102100b041506110706050a020c010e0a030c030c0f0b03040305390d02071706 75
    0x80c03250181e4110384407031760311224400d6081102c40d104000e400100b0350300c2059454800c10000e5600724440341c59214501c241a100c0e80000300c050180c0141d000f0540d002040c80894825259903000400c004101c441c5030a80144c0001c60b0003820b1580603c05200124800d2608500e44140c0403030324020001c411521403050103403550f503d840b40e1200d0303011064020049110304518a0504002032540c1d0003182c00318064010240c00103180c403014001c200e0340c0b12050700a0b0910400c004110f0004041034948181d00c192914800140b82210310591409000b442c0d5a07030000b011014ac43d540303400c0c0c8a92241c020001c04008c0c020200c0e0b800304075080c54078002d00e0101c0c2e01c00c041030002821800305400107803480024413000000c0012400d1008211000100d0a80c8483d42e038030611443c50108580142c04150f00b004080c1c911100d07043d0f00499401c0c20005540040039081d040b00d01e0900d4249403000c40d82c03100190b420480d07010040c0200410004070b2006408022200742ea850f004090000035400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 227443129 1250 227441879 227441881
    0xd0b0613031203090b0109020403031805060a0503040f12030f0c0f05090d0314030a0207030206010803040b090907050d0f0605040b0306060a060503090307142a0a1401050c2b0f1205 79
    0x42d8400c1c1c200001c401e40040905401e941c40d1440c0300000d500c244011004503241c5007059040003002901d110481d480140103609000380c050303041e141c5510050084503e05014180600021503c01036842c2c42c840076900041d00e072518803e15421691542590014440e450f000d44ca0050303440007c440100e8000e0b101c099041c4010b28003603c4180b820502401c243d1400710801c56104110b50103000c80d18082e030700311800f03070b40d0714a03250f512481607020304100d04c0070410486400381864045c0d81c0e000f030068545946031106041c035100464012001e0f040c006901c3c0c000070030a51030705015944842c007084024009500b4240c0018800110314401c040c144000400007410038036052050f1204541c100c015443c00a000300011600d45029400002d8109a40b10103880004101451084640d00141a62001d40d003021003900540da0f0b00170180741045000c05c007081400200303102040d09603d614043c4003064100040c4070303411480145040c030400c2074a01c0b49002e083d034005c0d922614207043c120000b81d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 227444379 1250 227443129 227443163
    0x51b130b090a030506090c1807140a0909090c14060f120405010603120804060f090f110402040b0705060114010309020616050c0901080f010608030a021005060d0f080d0b061303 77
    0x100c0c2e505034000341ca140034503002c00c0244a40850343c0900038100301e07900e030b40d0003000291a5034401010380306000000c072490a1030141480c040014a9009150300300428070950b2540f0807415200d070f2640813076a4400c921001c020034242412034a203e4041156441c0c180391005a8488503070040e0320108506416400206c2d080c01001e5001c072019503001941028031a91500d006400c40009460480b40b2510700480d000010405100318400c0c66400300588840120030340324981e039240b0b5440e40e80da000354200300c002071288901e002041400c2c804d4015110561412101880d000c148520903410305003403401c0030300165a080201d41845c45511800c40c1642d9850401510307080318052100d4210341c104002050102c40042d03825201d918240003400340c00e40b00d1500c607480380905901580580d00000c000b040c0c03e80c2c0c5400c000d60284010700102ea01a0847d00c50313906440f041441501c1c05100010780300010107490040c8000c060003940d00d18680441c42c038031100741c04400d2101a02d44008191010700c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 227445629 1250 227444379 227444389
    0x105010e012a031d190b1b0609070e0a020a05070b0a02040302041a03011506120b0d0615060807110d03020c0c04050709051908060105040902010918051b130b09 70
    0x48824800300c0b1400c0c038030380340c900035101600722011190341c102c007015100c5281c940540766000340c02c0041084810305243c81e42c03003840c035000b20001030f0901c610080010b515950070000c0a02c101340c4003005241040c5840c0807184080d801500044000340100076180d001d9400c5422115215405401a9015a1601316800007405582c0000398054201000b00d0510000b030348459400b114100c00800c07c250038050003902108840c850b0001203036000e021120b102c3c0040d4081070700030703c0250903103110080b20354948040303a010003541042e45018400034044994403400c40703684407425080480f101c0781c040e02540d54958991a1b003004250300003400e042040c4084c0400780c00c0410182042c0007030300300203101801004142c003600d401402e1899013100f02201c000b5204044401e0b0f94046c10840e4213210900024024404042e0305016180d000020007440c904501401160320501c0050300d0f081c450b04d9190214000216a80c03003d00c240304140d4000c4524030760000315442c031f09080d0f80c0d680100c1c3c0031031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 227446879 1250 227445629 227445677
    0xc02030f0406140c100515040b030c010518060408030c0c0307081903091205070302091b12070207050d06051f03050c010c14010903030f050f07020d0804030c0606060203130e0105010e01 81
    0xa13201e0b020b000e6a1650a80703445d004603014490320040111454078100038401110132040c1050b80c075a000d4000341100307500503401800c901104041417040e507403d603000b24403d680180e0002c0a0765200281c081c0c0b44650601c05607840040c00c42c00340146d03d2400155030365940304010301c1044861841000310801d4020107030000203082c8100180030b580f41604041c0c3d2a65002d1005038004c0300701e00005a40034000d1041c80050300e40b446056801d01000415044a40e00028140800d600c0303480f0b401705281e030700d0800c0c044505200310004281803610081c18007160859000240c0381134545503003400014004280d041c020032080c640048801210704091b8441c4c42c101d80f9415155280107120400d02d071b4140c0180304c4074545840207100a855211542c1c000a8003142e208005030490b8030200e0509108203204c1d40c1043c06031801c2c402d003400720703100c80c0211406940b0000141e030002a903c401000585070030b07401042c0180909101750b01d00000a02445580002103040121038400303804d00c4007001c0f0b000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 227448129 1250 227446879 227446897
    0x6040611040e010b09100201060501050f1317250b0301140d0c0f031a090c0d050f0106060c02011106040308060d0503070b04080a1805031e0312190c02030f040614 71
    0x7010181d40d4400c04c1d064164800d44885004550360580c0752203c500501800003181e4040c4c1d03039580380080d042100c1e04160000c2102000e2650a65400942410070034400626041d85034054032404561031440b990040c40c12074840603a5030828000c01401016000352811600040709002e6501101000603000701d00790f2030010203180d103072a404a21003061500d80b009482c0704000642d60071101a00388030b0b030b00c0022590500c043c1e105000380c0d225414402d604208041c4500300310b90345070351185091804e4a03040e800013000280d08103403210640d030f030080c121044aa1108007400081c02e054a00400100e00248028041d80303250110004001c010001c48807101d07007026200840d03091610303040c04243d100d502190300144c864401a9203002e59400391600320f400050003001c4450303816800d400d0018507010003916a00090001c00a50610914050b01c1a841c0203105080c000b81544150200c030440c0d2420b408641c814021045014440e80456080d0350641c03c144100c10101c440038580380c4070305004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 227449379 1250 227448129 227448149
    0x10e0418050f010e07030c1208040f030803100603020a020703060b01020709050a0e0606060a1d060f03070e01030e0106060804171b0109030f030e0c0904020f0607110a090606020604061104 82
    0x100e5024814003088040460400c40300a01c5142145043d83e41d13661200d000151030f001e9600c504010715030001414a080c2c81c420080542400d944151084185005900a44000c0400000c110090707540e80700ea000a0002d9003021400c1c89900d0000940c1c400003030000529041e07581c00c1003860740c0c2c0204669801485242c006105615041c508100648145003808031144228004a4054601001941e0502c09180c1e1030b030100c0610106407100c552a9a90021340000f01000342c81441c900789802507220310340f15101e4455000905000404954902400700000d03407404e2028403015901c20b02864100c0c3d08003080399564040580d038900c05100302d00c00c155001d0b609100405401c0819003004480a0090321144210001a00d0560554601c2d80f0000c0c095042a0004811894070002e00340d001400076050407418180310380410b89a40c040001920140c0c1c040c10200c0603031625511a10142010000078481180f42180113075540c0c1015200400c200d440f004030b400c040707004c00152402040c0302c81e8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 227450629 1250 227449379 227449421
    0x503190b04020c0109050705030a031d0f0d240203010807030201210e0a1101021c0f02070b0c070e0114100809160b070311010614120c0402070602190914010e04 70
    0x903c034003c1c4508041110103010b0280001482e14010504103070164041c2c5408180b9050840128103900c0d89100090f40000c4101081e8a25100c2c1c020034040305201d405411040c0b0081d01c0c0d12045901d00c0141d00060320300400040c012080c001c1415400c590382800e045c034007030702000b07540d1100110810355000250b14200580038420310020340c402c0564000d002011201c0d581074012a158500131002ea5032109101c801c201d800340c40f8030441512a1110700c152010075440d030307600900543c4600d2048805510035641400003003034201545004007104e49411490a0660000c180d020841a100380d06100040000486005041c800700c00c490001c5441da0365090344841c03400c801d0340c1046006800084200b94490703811841441a035043d1009568000d079000a0541044000f034911002100b450082203002d401c261164009000f040c0c1c82100e000d43c45100400c2100798800142480710100800580d04000c4107903603003500b00d140740003840e05240c081d12800c00b1a01910880f9031200440024213 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 227451879 1250 227450629 227450647
    0x10e0d08120c070f020108061306030b1f030f081e03040f140303040b1504021b0105070f0203040e062e0e01030b03070e0c0c070e0916090603030503190b0402 69
    0x201070003000c002400ca40c540312a104803429006100d00105083d22001139a0701540c003ca0840354007031802000145450f42d0800c0d41019101d49a00440f64221444d0912480210001c4841a070200c00751045420380d1840d21003140504000001600181c000900c8051011249049510382c0d100407004980c0d070709061418a8120000072030943d02c1c0358000d150521034060100131280959001901c01c602516031400d8403c00044000c1700d9070740642d0800541c240c1207941404a110010800c000007007610348000c5c05449000c00307480032400c540040006010000c0c80d5565181c10050645903014110781540c13040440314102d50312600c48848492904c80c00700c0d8003100d0064211000c0ea000d10100d1500c02c140340d90b400107401484c00340c40a1030006074583c0346003400303000d444070f00004503801240e5945a81034080425146c1046036004030090748011801c0b4079014008054040b8100308513460741c0c500a0840c000035028070200400000e804480881a82056120081c0104119a070360100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 227453129 1250 227451879 227451893
    0x6010207050a030c0f05120604020108060103020c160812030c1b0a0204020d020901030b040c0e01143c0a05070201051303020405150301050907050306040b070315150e040c120209010e0d 81
    0x61040382c10000300d1081c0402c0c07e06060100401e58808a00109502e48940d8015500300c80003c0c0214100360382800050840d640411228240d8568515120000350410030403a0800720b5481032521031450401c24404c43c0044101128812900110025840c030500900d05080ca002c0b180e0281d4802d0000c2412068500305500230110704000340c03000c20080801000780420340f80d680e82c286000c50b81e1000c40c1c0310a5402806c20f4000322002d462400c0c40d00840c1e84034412071074651207100805201040c00101250b02011226031102d40384c07984181420101c032001821071046840c0281040008558001c0440655101e01c016650061041c032140c0f8221041d0b003d03c1031104044c0c2e20940c2004045000c01402042031403c1e40d102030701070f0605980b84c2d00d5141840c0380c041c003c803007059070320700400300844d441d84507080c0986140012011560b800d900024480b01154041c01e101c0c91030f18000c01c113a250080c6030744803c4588004007680380e450580041e1040c004588150350002403a88140c0d0030443d070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 227454379 1250 227453129 227453153
    0x504061404051501020c150405130516031811030109060e010c02190b011a0f07030c02040608010510230621071b060f0e011401090501290306010207050a03 68
    0xd8808214a0340d803000c00712a000810f00e0303140d01582080d4501011410040c0700e6a542071070080842e89403c0d80c4801051502d14200d6091441ca6551801d001e42c00d561055045094015440c1c10312103a485421004a02d03441d0304002800818559084211a1002c0d04a00d07011500480304001080320792401c14081d01e2801441c0c4014003800b10344003614940c3c2c4005540c0980c000c070240c61a80e0034490380010b49150b940c612840f0003000e1169141003856072000f44100d5200e03039620202c9034542d10501c0241c1e501a0840350003641810100b21120f60544501c204481c282c144a01e1b42c900003040011540035010011034100304002041260b900e01183c407807481c40c0184543c0201c69550032001c68480c03c0d0550030110050440304481c01144040c1c012000e414003000c000148200b40c644a03e003114440c4243c1d84260160030010042003500d881b0301ca0040c0b00762104410800b44010b9003a40f080c005101400c15414088007240e9182d01c200011b801034100601750108480c1c0360708105440c940 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 227455629 1250 227454379 227454419
    0x9120c02010221090405040602121302090618040f0206300702030f0403030f02120301180608190b040609080c0a0c060f0f030e0a0b010f050f10020d0c0c050406 70
    0x3c00c1000c000c5019444040c40300d51050011682030419a9410410001d410050401e548054007072060444030150000c41900600050340d000b4600d000c130f4814801a038000070245031040d2040043d0443c4982140100e030384c000c0c1c1c8120a440311040d130344000b0308180101294100c64100010071001040c0d08080d085030400303055080c0c00c0035941d0b1020101c1e80d904c52191480c0c111001071100b000060701035035413901d040c00c81e0300588224144140c800c00542d0000d0f442401c800c4209204008113141c144940070140c100032014100c4181c00d00380121404880e50802000311030ba50f80000d042c051340394001d40344254842c007060303510340740c140040366282020441502c01c020310b00c0c40020018081c2c40350b40003e802d0780d214a282803120100039001800031559501c128011000501c00040511461034080c202c029844c1c1c1010b82880141300c0203091040c4007038090f80c1441141c0746990b4002414154a41a9207411200140c145c90a1441c03e41d040e400240c01900348000480c0039010b4100e01c800441d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 227456879 1250 227455629 227455633
    0xa030e060103050a300302030105011b02100e15210f1005060d0b13020a0f080f040210114908091f02030a0b0109030803160309120c020102 61
    0x8604a080e11a842848020401c0e402421200d000500d641c9121a8001e441d440c104000e820740e0260000038250894800d0000b0341c000f0040c4129a00410081107222102d102e5202602c92907011070002c003140c110132018131a0f08462406684d07a100c04400140c2d020940150703c07003031028440b500e150400b15030760f00c6485030100001c4560f905074132a2841005074000c8018098904070510a00f940a007542185d02c40e103505001140351184884035150071a040001a43d0700c0d1400c1d001405085441d482004004241050104801034650300c01e8000e41c044462440d110102c0d50300740c034030b40c00c505925581e50181c0d000a410035164050f181008a06800740c685c5140383d00c0c400c441c110710001040034401806511190821440303040000e500c80b810a04482c0740c00e883c2c14441416413080380d41680541d40010410500321010b0199122044080c02c04800080c00c5990700541400300810314890700e00d00d40c910300b03c51442500104000c0d03402206000b2503c4014400824400168409034058 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 227458129 1250 227456879 227456891
    0x80601030b0c0f0f0d060302041b110708030f0c070e01060801030614010509073501091401030807060203090a140c01020105160912050c062a01150902030a060e0a020a03 74
    0x414282d4044401e40c400e480103842c40d14440c08543c01c070a8000300021400e503681c07001c012005849134401e8040002c20103c52402030705020200901c0000504114806504084400c11000e00c00000b9180d103803a00c4039095450b1410f061806203030000035488070041c0c5084230000600150000c90803410789009072401c1c0000988204682c5152100388150b40e080030882d4000340c1414810703d0078540380c03056151422081140c12041f08002c8140048014241c01454010010303903000e440f41822650480900302c01e40d41c5180c541e0802c9001e0f0b0400034000325000400500711140501c080c42c40103a204a03800c0013494141c084581c7ca420f140700f8107000d0341c41e10000c00d8030514070460520802c0c1446da14078001c03508110303450340039908001003103d2507c108a02103c13280d6030034026101c03069882a008864002d01568810311046a072580b10240c1d24294002003041c44000820b03054038003280d401f5a03240c48803040400100381d9a031080c4e2a040344141401412440b035001000050410350f424050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 227459379 1250 227458129 227458141
    0x60e01080a110a1d19060e120303070215090a0209061003020c03031302090717130201050702040c0807170103050d08090a1202030a090501080c07022403010e0103120302130b0f09030304080601030b 86
    0x5226004c175980301c00e888801020460b141c42990240d00b10440a083d058000d10408100c40c59500141c51800c003603040080301d429000c0c8062046507104403003400074940a80d01381c01080305c01da00500b20780e02821b0101c041f459140c0c060740460f050030b020b4001b1aa80d070300e40f860b402e16084400420892050012501240c1503e120300c1c0303444103c0388000d0341e8150680301ca58180e00702c01002d5000b241804001d01a080160b6994840c4c0400c04449854960a528100c0d1009145c00702e501400e2030f00184040052000c900d0003310005a0703002414040d2064507002091450b00c040c000c4014100c55044c0c09000c0c41c19804005484daa0885480e554102926500150f62048044424600e440c40c20f1014101521300201c0e8000d503448171001d11554108441100000350303000f600070030000041d86004204024400c0811069140689421801d2034500c200101080d8594441e0285441020a0a200340d20000045940c032240080031255502c2c2c0e14500036489140911080d14565111000a86 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 227460629 1250 227459379 227459389
    0x61503060307090b01030608190501061502101a03060702070e0c09031f14040614010506070305030a090212100b0310020f0f0a0c0b0703050f10060e01080a110a1d 71
    0x3019840050150445605000021000342900b071421030400d0340320100050201c80c180508090055100f05210205406082c801d080d100c49502212644150101000506501040c5034114061240021038501072003a00c44000d1840382c1c400c103500d80902014011010f030002589001c0340e420800465141d83c1d824450f0b102c0740115131405030503411958401c0c600c900e00d6400441a0022070342c000442c071074019041c0c842c895040340d080b1200703a6100d161144060075800100c0c01800120b849603d024070540e0002c00c01d00000c2c01d0850960f454006140440d03440301c40541104c100c2808480d50091082406006040d02d0a03074540680203000005052841e60f0007240c410444150020b031034505900c98040160b480307841c0c0007040141c81c00b01203000541000351580a40881d5802080c2810100414a1440b1001c0c000c0300054503003039420000960020a59404001c00b4203101c2d2403070391003806000281c4000c802c0780010020010301d03c3c00068005000c03156000325100d422500c14070500502c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 227461879 1250 227460629 227460631
    0x12030507030c0e060d020c0f0708030408010e01020a0507020607020321180a0e070f0302071a0a0b0a080c0f0105090d0b0106020709060e0f040f050a030306050f15030411010504120b061503 82
    0x80d41244d0300300300210011100e80c00400e181c0410f842200d00851440b11910b080a00c0c5410450007500001010032035807034240115a0030155000003140b80482402002e0106d200d140b800078041c072030201d4001306541e014088104031488880c401d00d1001460450002e40da40914408a00d045050480001d0360505c11500c07019219115201a51a142c00c6010703075000003020a54010542c080084000189406d01d5030b80403a4051700c600003280c1007111503c410341d0354114003e8000e5403205001c005400e000542100c00000035514415025160310040f58240300e15002941c1003503020030301d0000c00030038440301c50403140d2907800e0307a540580340c07165041643c0940c40b40c04013003d844c10124401e101815038140d04030340700d0000284680525a12242030420000051303000c00c2e55428100594288124410000305085408200306e400405190000f400b0140010381180c1c219134900e54541d001e4804c071000b40260b00090b600b00ba0007403400c042c0c0704000b129184c0c00740c1d030010607200409030034105417 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 227463129 1250 227461879 227461907
    0x30c062e031203020c0712081206060702150a03020708031311030f101e0c18050d030207030809010302070f08031905061e04110c010f0c020f030f07020d12030507030c 73
    0x2e41d90035015036908402a4009900c2c0b00254054683c00280584180d059008643d12600ca05915500d01582012080340d000748103d014540800c00b0800507903c0e403414407445080000303110b48480400400324000e0192404c0103028150000074800d022700f008111080c500c4c032400071030480500f0355082c1525408007203121921070740040e007001d01080c5650400d0001c0429416441051754800300103c082e50344055501d40031619181c201c82240e0051940351001e404251405200d5041d1a034009680d80b0040c07001030309046000c21680016031180d01103404440d045014101c80b00c04600b85035030658000c1e100300846255000204041d0743d070030b02556100d600018845011221201e10405100c0d210540503070b8083e41d40c518203000003a148006d410f40442c0131000003400006684100304a450b40906d01c001c2d035109520002d0100000800c488101c00c400114607110101072011600440003200010094100a03c00b03ca001e50b00d41e000364401c601503601800300e281d14800c143c030b4031403000c801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 227464379 1250 227463129 227463143
    0x10603110708070305090607120201050c09060d1a0307150f0c0c06080402030c04052d01030b19150324060e060103020c030912031902010c0801050f03030c062e03 71
    0x201401140b40e0101901c041d40c00f03410400d00d4808018006013642d0721052085074071001e4441007640c0140d091060b550b01102d60356196260011480005c0d0b424025130460080361511282940040d6500c3d060f41058150041c04980516844094290291201d08c50190015061212418200740324115680102c1d0300803a038032240703904007401100d0071080108241e030144145e040c181c0742074071140f003014410814400001910f40358500610442d02d44015030740001c800b01d07001880403e080f1308940790003000d071701c180744501000c0407031001c090100f200e84940e0000031800c0000910030a03078038a1070720341203280c142d18240308868860800c40f000b501803c2024284600020f08035402a80140800c0201341c0480b4205200036000641140d83c0603420303200d41d040442c0303100740c10740001d90140c0701c00d035a40001e000e541e00f425030050505405111701840340c90f000c0120840e40d2011b2084990740081c02c0161481481d0580241c0c007007012080c4032010100901f03455401c00c0c83c6210414080e0f9600000e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 227465629 1250 227464379 227464387
    0x1510030809010c0f0506150906060301050d0f050105010308031909110906010e060d06060e01050c1906020d020a1e030204030503070b22030f09120b180f01020d0b040501060311 77
    0x1030340182a000154a0340c1800004407140c400305403181e084d0f89203244603d000303003401d1401d0b4900802000d07000722410300600d1560203101d059580c49042e641540c1054a901c80c00400500703152100d805a800040c4c000e5207020300101c14040a00021031240040414400000302e80c1e5210104494007442d0142031021000e0203e281450207559498104005141401c00c498000300012801c1e40811440a4034560f038a900304416504100c4001601100f401c00741c0c11700b03d000040ca81c0b80c5040661540b00303c10703d01d4088d810861507078166000043e00c0103045444030b0345058041c041010a4286564a4000b80b91510340607100303000300e406495000b40914240b40d8282e8840c42580c10103801580c07848440d10440180c400e282c07118901c41c90080d60782030a400c0d401c1d10041c0c20040540c01100c440740003980f603a40841e000c58440341d04650117220801084802d01201c0d0300300584541c5071081d80d400004d040f1403043c4160400c010403003040320b0402c820b0b40e0764203040e8201c0340018413896450f00240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 227466879 1250 227465629 227465633
    0x11180c030a0c090521010b0103060510051c02030106030507021006060504050f030304030b040506101a0a1125031703070e0d0c03060204062c09130c030b1602151003 72
    0x1400003001c044241c03c04107607564950000134591407040070840c45a24a140340d01400f15001d01403100550002e003002c01002e801d10740440c2034040111060750501000160403031380100700d001c1e1180c003c0c015034411900c070350319068002c003d0202a50a400140b0a20611503e800818030402045441c0d44d21014a40b5107460b09000b00c0d510344c07200050707040c0814040040400c96140340f443c0b0461084029061510300200035913010074040e04140d00c1c8007840500070700c464400e80b040721400c1444d81000c4080d4400c04064034079045a481e9451680c4500c00000c450000c603083c40d8109680c0302c0e4807007a04039514004000c115020032103182c40015500d40040e20b580c146100d0507642c8500032150000815101d440784e00690703001d50721010000b8030190522040b46824000c002c0781e01170448400030103500e184001034110002404000034081402644010450b500c140800210740c008044012413504c0120001000030f000304400c0540600c80071b1580a902d21001c240c890062a4050a4668116 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 227468129 1250 227466879 227466881
    0x41508061e0117030702060c031b010b10030f0b0d0b0604110711060304020105070602040b1305040e070b030a02040513020702040b090106020604060c1b11010e030a020609061e0711180c030a 83
    0x200003e0069000821840b409030320f55000511351000c002d0000c565440c03411401c2d0302e5050041c1389090a0b40d1409101481542c3d803403008190800c05880c001c10740200302c0c0300c0600107055660406c0e80c061007425a0b4404c104e0350f00d51062140790103e90802c0f0000000b01079450611800100500070b18400766011164600400550341140c01890100d0070801c05981d10300c00c03a44150000c4104000200e1040c919032400c105150190400b81e44c02d2041b100325114442e560040c038083d50540840c040002401c448656050300c0c01030000030180c1c103010101d950020025400310710144c1c0164140301d80b00700c2178200420b40318100c0e001a4018166541d554507030700001d101d4101110100f02e100d80040d44401d0000f02c1c2680d501e0b00400410b10b0807416040003400c401000e00190780240c22100328480036a4918042c0e80980c0002d8801955a50b04140411184074198041e009800d00102d8484240038001c4403400c184401070f038002c544810111500345d289041115001d21042d000c00c0021b40180319 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 227469379 1250 227468129 227468159
    0x80c090414030403050f0c0a0311091816050a080a121409040504032c06180f03150f01050301020f0a0c0c05090702100b0603092a041508061e01 63
    0x10704900d078016032098804505680c01a4410390300c0fa0f0000c91002100341050101e041c00100440d0003240e114607590740c80720480d20140d0080d21451480b0001007980104161400e85085440700303071030b0354240e0081e81d446144a20700916014201030280403400440003d05821016000308000094004a61080324491120507030250031038818000010191141d0052038003a41c442d440300384038400444a41c070b42804215240c03039025140350104031541d490b40f0045425486201603450090300700440030481f4880142a5250540300710440001010f020300e0203180605444001e508169a0752410507080c1e00544103070900e40241006440f021a00030602e0503292403003007000c001540e5848000031502c03001120045e001d40c00a003c0741b14008103034030488080074002c0700c0780350443c2000010191388040c9061608807000c3e640700080c1c011032600384070303c000190090050085c2040802056010441403089040c079200305c401240305090980b1209600032200c3c4213001e2540e2a01c094002c0f5030f44 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 227470629 1250 227469379 227469383
    0x90406090221061e1305030c0d0504210503040b2a0d0f020a1109180a060c0905010e0f060a0e0409080403020a0b04060203120a0e030c0105060a0906080c0904 69
    0xd661000040142c4441c186040109054000c1c0703441c07100c82412407410440f0042091000703030042254510354018409503590044540b1580ca00c1e8426185046840c5118000e00c80404e0720441044414030b0350301000501c151100607402090802d40320a02c811b00d00107011005000750004c0c001444401d04c108080d0118008190300d080e02a0540031016900010b2011489e520350814848443e100c0d07000000b03092205540d10040022005036150081d41d2010b1411081c07090001201044018080280780c40141d4001d05c140c401041103440c000c0014140d0f96030704004903400807000107980d80074100d0340d0301410002d00b003040e88449202c100320a5a0001d504002070101021001813151140c1c40f03001c100034884d078541c9594606600400400618592081501801c1004103001c001d5000c81612000168a10140801c3c1c64404030070001c0e210309400510984000b00c0d000c4001c4405401c51401140c05a0b102c24a031a11020204155680ca00604840d41d0040c02e0000590500302e080e40c0c1d0040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 227471879 1250 227470629 227470631
    0x1605010e1309050c09150a05040509070515120a0506030a230a030309110306070518010201090b040b040606170a0807050102040e0415050106020a1a1b0301060f1b030806090406 77
    0x1442002141d040300c2a451050783c042c0d10580c1265081e0800040294001d40e640070038200308100b400001d21060f074240599030145407154003041040c1c5080203800003410000300709070442217000c0010b40310360300030003034402242c04180c011514109043c0b20715801904064090a44900c0d56102c102c078201c0c074404190801c2914a1a200f0001c20030300200d0403e910079900401c454545003460308039040540607243c820b80000c000d2146140e0884125010281000c040d032030383c0541180183c2c014007603500c0280441000804110802130141c3c026845a4841c2c0381c1002800c0d103038001010108140310ac81f40c03860303010400c81030110380c49070098090341e8412000940380c01c0c0c481a111441c440d050b0340445030b0b4111202451020f14403801824090b010701d20061501500c19141c0038641c40c2c011204007081040700700481c0490803a8002d244030f041c3d040e880b440d940e5a442100416003d00e910740340000070004806281c0114405800403140d64150340d81e00e030f0645404007006074025000c4e100301d4000e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 227473129 1250 227471879 227471899
    0xd0212030c070609080114040f0609020a060509040c03150b071401060b04180b0616080c061518040209040b1008010e07050108130c1403030c01051f081605010e 70
    0x108608100070204209030001400c001071500c880504140d403560003044450341001100c00100e0b4092002c194030079001203410300b03004a68185600181200e00700650045000c0d20085140c2d50884000d110b0040240c03002c0101001d40030b000ca08a9424200c1c400108071000d0080002001c00009400650b0059000400005c0c1618105007103880c250b0025030b002401283c10004102c0095134482002501c40d42031281e40084c4000904900c1070082560a004007c2070110501c005030050391911468001245d025080c24a0418500254002d200c1d100345903082d1518a106030b040d415602503a80600100b005443d1a91841c2c50072000400e9224040303111710300020140800d004000e18110b21401504c0f88c14102000140303a0316008104c0d1036403007441042800040c0014803100c0031a014860001e0946c0c001000080c1180314480c00c5500d0b0798207100a00440400e9075144441e9004501072010760f1903a1941016181c1d4220016100d458034a218208000d500426040c2d0782400000d10300966 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 227474379 1250 227473129 227473159
    0x1d100e0a0e060108060402150a0c030516080703030f1104080c10020a0b0109060602151e09070906080610061b1209090504060507120b0f0402130e04030809010b06070f020d02 76
    0xb500000340d10a004641c00300007800154109100011807020a44940602d8092030920140c00810003110060030444002003080200c0002075010000c9680328000d04da45400a05000f809044080307044019503140403940e58042c01c01e1801c8900310b412410280691841c61010000c5140e020300030f0704294081c240a103000101d0351100b0314040d1102d0000060020304181d002442c1454003024540f60344902002d2140b1403110304035000c2c1c000d084804081c5155183d0355201d013064840d512011810b410114007141c04000482c41f18458180c0c020041c051581c3c0303510440d2031640050050b00107103503074020340c07011400c2480c140c103103e6000c4c1030555180c1c2d07440306030034212801110140e440c07643e281c080c01895a13100c402c02c0d820301100002841011180e500040001c14a150b040b88590390004d424614004504a400024264040208014540ba080c068070102d0b0031a0222295464150040c0040c41e000007501d240641041e02c1c010404a25802c0c801e105a90007020380e4040b00c901c10300a8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 227475629 1250 227474379 227474383
    0x5041a121c0f080105010801050a05120f010c0f0e040603020a0e040809150a080702060106050a051602030d030603020a0905040b0c070311010c030c02072c04021f03061d100e0a0e 78
    0x205020241e611140c4032020030070002c00f40308060704031030304200c00800100b02075178408600c007003501c00c11901d480c40c46810128080c9404803803030107510345500740440f403451540c01000302c0702026429150000c03503c04240c1000121401400000e40c08403000b1428090307054500e800550280c8a01405480c0090740c00018140961200e03076440c01d200b0001e4070403500da92100ba543d42003001400108115410201e000e009030161600c1031080207804074545540490703912262a5894024041c1c5c1c495041da50380041c007034045d5000c264080e0440c10300001e20f40c5206e1144610994010318140c4140d110550700c10308951004409604105100884604801080c40755407451032103034800044140c030402010303080880650020880d01800014901998002c070001c102800720496030924541d190720005504102c0c28840c2148241d40c912042c4c1c80d0340d0142d1141701514031000c0490f0b84c0902e1900024048801110345d440ca02918003800c02c10f000020341c480e600100c0241c000701d6070b041c00b200e00314 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 227476879 1250 227475629 227475673
    0x1b0618051002031b071a07020712080d110406020307020105090a17010504020a060507030c110604031205030603071212120b04020f070209090705030607054005041a12 73
    0x707101e079400401d1140781004502080390070700a09000c50304141540c0c94281541400300a543d204101080004d45128424407407440136000c0080301031100c403804e041c44500c64008400341400e0718904140700e130a4819803c161000c4501c641d004518150380d650044607540c000030300131900404403100200d20210904410038404024100020b058a003c0c0100410702c401d035407018052141c1040b8120100c2d41c03091041140e01d07013123038402054480000100b4070910071a4805070480c2070000d25404940e80c8a00114050781084080750301058650060314203160610100404102d41900300202140c02420740c01c011102900c0300065070301104001c1001c3e0780c0318a103464184e160024040046203444849103800401d03000003040498201000710365140b0020f0601e03014000301140b03e0070b40c85d0100c640701201204e402d40d80c0034032949800e01e807040c00c40030701e01e00420410a8100495182000d200b40018a0300c0d070811840d040002d8814800c01a441d030912051600600b50081c0d40d1146d039010b01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 227478129 1250 227476879 227476903
    0x140408040618050409030c05060609150409050f0a08070c140a090c02100218030709051005061b0d030626060714070f11120c01020c0603191103161b061805 68
    0x5610f07c03120300d040c03030400200610035841040014180305400498200a2821500c02d4a0000f1840841e08281d89010074074a01545103100b010300400c02c00c40d01c0009002a6072041d2060b10300316454224181003d007200a0742a04144101401c1090030260381000303941c202c0034010341d0712000705081040240e9001c41d4250000d4200340d41c500754107003020040c00c0d008080700f030000c10881c100701e184e00c8000300c5c580c45181d00c01c2e9008903a00300040a901841da40380c1d42103e0864486014622005d0043d1a0b10310a0900d005103c20300001212402d802c6d000d074442e03102c0058405075680d0202603419505a43e290307170500c4024001080003c52141c0c044100a002d403004151502508082040d008ac00c0c100c187d00e9900108143c1d41a0b98001404406181003111066140e6840800f9406a01d9894100e00c11150420030354407c1c1c280f00c48011070203860100009a6101d10954041d0b0b001060740d1318080d07000d401010b1100105869a0020206041020301039132203400c248c0f10a0314003003203401c0d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 227479379 1250 227478129 227478137
    0x6110307020405042402130605040819081b0a110303090102060604230411040509190303091401020a030b011d0306040f0503070c09050a180f0308040204020409090305090414040804061805040903 85
    0x7401580701030251f01c16000f040240f40c0f0900d000c6c14081203640700c66174804424020700c403003650303a020449140c082ea07543d1440600d440340108141d1052940c1e40c0c080041c00c0e240400c0d06542000c00b81000f00c100d40c03244030181c00406281c0c441409100040c841c0f40c50890405102d6070900c1540381c407518125004074090020702d454000007800700021900302400c4006154070814542d0020700d8421400d182c15501424009140c01c2e56081154031520400c254140c95440000c220940316010303032110861030800e0342c0c0c031a640300c2e01443c4861081742c00d0882c15410b90150300013a0002c0c2d260781c040000d407441801640e0031301e902d41e5500c41568078640c1104584d1910b9004001080442e803041e20728441c8840141c440900300c0b5155403009020b411006401c00603020700140070344d101c07a01160001d1000322400c008040b00c47c140200590440380d07034248910708042e844076071069011540e0303004941103440307a450039142117400da0b070071855841410b0710400f100d400000c0d50341d2144510550180240c50b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 227480629 1250 227479379 227479387
    0x30f06121207140d020a06020903011e1a0f06040311040207020904050d12061508040507030507140a0b070b1603140f0702010c0f050f0d06120809090106110307020405042402 76
    0x5895480f1a840044082403075100e40004d11000c0d50008140034440d410031001680c070684540403901602408260f80e102c8000601c184580400d594084141c0d0320540029400d4468035000708145520100d080c660b0103c000d001c2400031943c402503c0440880c020801454040a980400c03114007080710290f41c1c940000c0f009145994200105401c02c010301141009140d0801c22510b011041d2002d42e001000115000902081410042c0e000a150820100c0780156510203100340b00c002450b0342d10f80111404080007501550030001e4540c0301e6403240581d00c1d40c0da107102a012400103120708040806440d004180340c1c1c03851410006009071855814201180340060707001c4d007901c000d800910100b0a12504040840d0392080566a0400d90f4107c015951303400a51440e000c0c10300c82d001020079070344a08045003000041d100500081100369180780041e039071440151208503441c00c81402e02e8104110040051905521040c3c3c850701c00e014581c160085c010000e0f03021718182a5203038030390b58009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 227481879 1250 227480629 227480633
    0x90c1512010b130b03190c120501080303071107180b0d12030603061a0a060503100906080606190e04080f1605010f0506040905070909110d06061505070206030f06121207 74
    0x40c243c030000d0550a00c040d8914200149028106000c10392600f000580d06c20304034405500c1400844c1450001080501c038a58440c01c0b82500d0b07600581d00000807910034103a0049000c80030a41c4011110b00206400000c000c180031180501400341f41c0e0356020b21189409800030382c4a460703015105d00305075400181581107280c1081240c00a0141c0301482a83d040c03d00d02c15500d00f42c00800342c415030314105440b616131036400d4a003540329400c0f191003181000e0010403415800921240300c3c003000c450b50794008104900f603c003408401e00542d15820400c40014002c6440c2070000c2c000385401130901c2d0b180c038840250140740888404022203103651146800203415406000c0c054000320100c0c0c04004044d240c1e03980c40d80d80c401d10301c2800344680d10341810f00b05000e17080b842100d41e40409001c902d42c0312050328001c0010002802100306110018030350ba4074a9204230141d480d440d03406031080c1e00d182c8817030b81d65a406940c02850203501c000d581c91700d06410b101c14441e45001d410500c0300103484011078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 227483129 1250 227481879 227481907
    0xa1808040e1005031020070b060f01030212130c0b0c0a03080108010e031e041203090e0c0310270609090605060609210a0503031003030314090c1512010b 67
    0xb529990810940e28018403550f54049821013107001e2908001520800c110450481d402440c1e50f11122540b01180350418000c0c0d549949101c4e400444420300503603502c0005408078007071350342034544004400340000c00c08808030070398040150042920740c420720f984002025961b40300c1d40d40d545c0c0700c1d0050300300e241c101074000c40c07114090806030000b0700c40c4240354201c00d6074a014007550740131415002c003410400072070f4544c1141d025107840d01d8140441c07241400c01a082c000b90f80300b45031103640e580d00040c00ca421618162805800303002c4480c40034520304040341e40340d054014501400300464650f10f1000108501c0398030001e00c9603410105148603541088803c9440044c00c081c000d03082007002e25010390301c6198000d02480c001ca400404d5140c540089c43c902125404007c06d14440082800103540b40740b0101340889109560501c44250007180400890200b921b0200300e036404181c080e003043c60491044010380c00014100c0381841c801d01c80f060100c0300300383d002200038440060002040c500f1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 227484379 1250 227483129 227483131
    0x80601020c01021b041409010606020d020c011b0201020f010e0616030207170c030c1f0c03092102120706021207020d050301050f15030403020d0216030201170a1808040e 74
    0x2400a07040c5490380c10300103502e803050382c8034240c40c42040d100c0c812160398039a0310500709002c0c0c0000c006401c1c60001c020b80e008010602a600251150380700800c00c040c4000781c420301c00401039645000d0080c40c00f010610311641150101c3c107600400550803070404091140d8010003031410f005104509110b00380f5980c87c030901284908150042050304081a49041d00003160ba180740d1a240d82d8800c010341044c114000c54410809074090082a8102522034100240f00030303043c0c6008025040c2402c0080e4115055150002d008240017104403140350710324010b034409020030b40191000405e100703100301150340c850f402c100e4200d40c5c0410b002e0201424034650a80c805650300040807080c6c44002c000d440c03400140714484c81031142015040392502c03410700142e502c028201d003498581c1014035000c0e4030b441680420b5001885440041300101c0f050b41510011240c043e1100002901031506821013074400802008010717488030450182150501d03041402ea5006d01c940d81c1d02c2c1d9080038506082598 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 227485629 1250 227484379 227484391
    0x15070e01050a08063c040b0904020f0f01021c050d050f070c1203022106090a0c0e060d0e16030303060f18090f170d0f0c092306040303090608 62
    0x1034103200118840ea0082011a007101c000c40b605d46101d000068240440c0300c0026048030b00c00c06110014042c00040e100010710150120380611030980b8640612610303060458004e940900480c401584909002044c0c0c944042d040c419901c81d4038071300d48401500d513200780d02c200004500040d43c4218620a1240c2d9410011001d03c000303407421300c150000d101e25900d803c0501890086134160a50f68000d07030403036000542c6e2034400106030031039030301d1081c1018080750300b640030b030070914002241c440243c804d12103240c1c0c440d04c4015a040350041402095040494a440125501e03166582514000c10107114405803904101d4034590a40c07500030123981d0941d00001000745910400e01c070f440c1460800062a98200310001801440380c1407030003000300ea03100d02078056940862800650740349400101340c244040c0b90140328034045819a14100c440c400595400100542028800c0c4514042580b1203400c1c1c103050010700503103201c0040c00c294070591080700410150602004080d13000140c440d4004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 227486879 1250 227485629 227485637
    0x110f0601080705090901061508010312030902150903070b030a1508070e0105221e0b0613030b0c0c060709030209091501030b0901020409020d090302061b0f070609020315070e01 77
    0x15142907115907541800d4000c85102c3c401c0900012076401c0c0943c880c800516a90f10030f907106076102003010f440350740203020960b40c440c0f51070a138640032806401000d070f645901908407c00f03c40031b0041078145030040382400e54103008100000560714100b202541c09841014000a5a00701c04515040003059036400304005800080e0200706200c0c1c0760b843e55045800c11340d490080401248040031110654542051200b45030151400c00c580030030b140b01b0341a40180314200a4051000b08010f400e000d09400c080ca5150113181c00c0c400640742c2c940180d004440503015a0400410518081c148007003103e0301d000140b8032401c20402e501d884900746404c10b45030030250954265011890a041d541400084d00c240b10381c0c40810030041c2e0950464000b083c030a1011511202d0b6030490401800d000c1d0401e900510a2101141500c122600600403d0007801c024610307080011400642540084c81c0a0f40c03242d6031242e142c00941c900707002036210b410f44040451f0355441c20540c040c10310400303105594104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 227488129 1250 227486879 227486881
    0x705151f090c11060712090f0b130209280c090f06030207020f01030605010509010f020c0a0305030705210a0e040902040912021c0e0123070302060f0114090109020d1506110f06 77
    0xc203406c40f150198202e120342011803010b91030709200d54580c410b01340081403001140104200f840410001e100c949200b16810f40141e1502428010030010302c00190301d0003c40d03007003206100000c0c1e900006d884441c0d81890b44145580d080c003015262129030001000ca030700043c9003000c40c40c2200c2c404244400900301007000d00d04240000f050350080d955424103000c1a0207584194a000300100c10303a5100007041e68035103917143e00d886612504900d4046685201d02c644100d050803440c403001c02c40e001c1488a007401c18140240854280740e42042031604503948801c1d0f0405a1102d004840c900380c000c80c01b019542c1034000e4000e00d02414a586020384010300c241d00d200e40c50303200301682e081d20024170f480500c0d0f82d5000300c008880203051501c0c4044071000a046410540c0101e46a8840c1c1122511000302e03a0381d91210303a1101c0c50022101d540044581700520050466901911840b0701c00b03600010381c0e00c100500c1d008100308a80010010441a014151702d10341c04020589440c1c0d0414007401071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 227489379 1250 227488129 227488141
    0xc1b06040e0a09020315090c030f0f0303131103030a050903060a05060a091e02030406090c0e010302030a060c0e130509071208030103020d03050d0f06030b0c0705151f090c1106 77
    0x220a002c0d10040c001a2180f1001c815580d0801000c43c0d048400c5070a020182080200700f5505e445440f061402070113160b030a400088004142d01d40b0082e1690050740c0795560380d002c01c003241010500e04440090040501400c01c0e20100061b041414198844540d5040380c0c2c400c251811000514145c051414802085001c1e00e80c1041315007141d141031004526800d00c0c64003c3c0070000c1705c8100e11411071000c0100306c1403006036003101790700c0da0003110740004403070300c80c0104455030f1402d01001e07405074040008240000c03030a03401110580210b241c180b6410610400241a402090301e0340c2e038803661070300e082c008068014000c940042107520288400d0504558503210340b408144004be2088107400001d105041c0a1030480303005c00a80002080602c06060b14034000f1b001c3ca0000361051003034400002c10540c4540f08545001e6041801440211456110700c40461300060022041444441c01c0d5009401a65080c00250542c0c800105403030001600042c9000e0040d07a03408055400703c003e0040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 227490629 1250 227489379 227489399
    0x61e010e0f0f15090406080a0302150411030a1a0117100b0d021815010e0d060e100c09080d1419030b09042102030903150901110c1b0604 60
    0x4034010040d100001c101c400c000000e00203200d41c0b00b0300341c1c0003e40c0300101c1070440040c4005084985003268200301503030700c51282d2541c41a51140041c05a44508244107000c00c4030800c17958481e1040071040c00b410540c80110b814001c01c4481101d0f15030701c076948a441829807640b400e025140103980e60840b8166121403503070b070351030107401624a80d94461008a80c0c0d1521a440318100d5009000384019080060fa50328403031008450718500340040a4200d1520741c403032900c2180402000700005c0748070718540c5612000302000070032036145110340984450070782030074015180022882e0711007140c52031034856121b003451070a004000400ca13202d000e82e9050b01c0403200313468590913458001301004c3c440140c00d4005100280c0c4803a031114030101000100008040f040c040d250395210012502221040c1c00e0340d580c01510342d8254107400001c089a4144024080c095000210600110782c40401640c0707156940c1c0142d0307045c100d0742c00070728901e00709100b01c0c0b4201d466101c0503501c00d07282518044805c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 227491879 1250 227490629 227490647
    0xb0a0305010b1002011a1e03120a0e010201021606361b050303040b130306090c0303022a0f0d120323040309062d020303071b02090c0a09030b0c03061e01 67
    0x40c81806904800700c01f82c1e512281902030242c0150440d05031050800f08c22200d500410b030102d00180720042070725603651042c001c0c1c035144400d0343c540150814981c2d41d00310140c035041001c0000fa03411000f0302032140c8011003103401000080c0d40c10041c0000c0d5800c10b50700380c92850408041c1c042050500300007580300001100d085581d010b02ca1030300c0e0030310581c841c42c031503100d80d00143c459402c0c240c00e10107120200800208030f9100b9001c850086d10748000825491074500c11015172030000601c00409400c0421801d0071941004002020089a6588440510350b4030252400060ba8036200c55581100b1504014500005c1100a1545180c5503030028100f4900d4003420303003004070184c01c2051181d10845041108840000143c00d805920440250380e600100c444000054a502c204040c40d12a000e09000243c1c01800402e03d681c1c0f0a200d0326402d0344440305400402c10914400000301c0c0200d000307140920744014146540e401c0020801c00140c0c41d0a2156050040900c907050650382c00003021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 227493129 1250 227491879 227491931
    0x3010302090f09070317120a0e0a06020d0605061b0c01021c0c020a15080613022706160602030115080609040b0414030a0309140303010612020309010b0a0305010b100201 74
    0xc2c16665401d001c49003818643d9000038a40100b08081c4092040c102d8041c0c00341d0501a44810480c3e510080e201c020354540110355107603500100b84900110301c50f90020300c00b021507800089a0140d880000c00d09941c448458141101c40d144c10a07080b03540c0610580000d160248010034200721180d5291900317151170040e520500c405900c143c0215140c0004c2c410080c00380031061103d0805580000e007511804a40140c41540074010740f0410180510035a80a5600400311a413054841203002c00301d50315400c441070340040f05200e50981c1440941352241c50b144074100168881d45060311140ca00c0042640c45014481160304015030b5840c0c2440b081d6220381c000100c810180c5440c00c08404568001d5200015400005240030b40345805400900707500388070b4880150091584007030540c0340d0200b800341030001440c080903298490350301d40195401c246107500004883d405400010b00b41d0030142d00898190b511689907010f00c2ca000700c45140b2908080c002408110340742e42d8903501c14841007101d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 227494379 1250 227493129 227493151
    0x6200307030921060207031101060509190513120908150c030f150603090a03021203043813110f0616030c06050702031c1401181b050c070b0301030209 66
    0x40d000c481903d08030550940e5410410443d40c0380b0703103428000c00c90306c81104040d400c2d6080080c00035890805900042c40381e003100e0520580a0100802900504170240c04880d10240f5001d194002c90f46022003400c0505c0603499802c003461a01140c1401c2059a2a05c582c02100c0034080240800c241011280d02410030700303a03185903a0b02c80480d032304a41202018160081e030048104044900005610b00c404d50094088039103810314000710441740c0c401102d004218403000e1440d1842c1000000218010149a008035000300c4845814a11038035021120300c80c4481c000f02a810034440d04220400051030b058a0013140212404042101c5114281360246010a40120079040c980b1504003580e036030381e10100034081030034000ca00035500d03080587d504e28403803490109a40c001055126041d001c540c16070300d50a1980c81c0020001410058007011403603541c8506800804145026142183c0c003d10f49030b540e2610700869649181c0f0602c1e40100e10031200c00c2005202503a01d103045260b0125004c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 227495629 1250 227494379 227494409
    0xd17070302070614090c030105040510090c030501090309090b0105120415021c0504030e1c02150c0f010914010e150a11040b0c0c01031116050c0a062003070309 70
    0x124024800c2050141020f89070013000c103942070002c08003d0194007100112885885d0303450406088400070745009003a6440030548903007420203500031200c264000c41820300b01c03a9580d1a402d00355a002d0305c086000502004c01404a01514441d1014043c402e1a01031f0808144803c044000100030704040c1c0460100b03040c0e880784140b0340d01126450401501c503a03403a004001c600d08081c203002d5038210040341c2d40c0350401606042c0394031281d0780c014074050349100301c0380300f90240240311802101555000104002000e044001000034800600c079400c000101ca03080760400c4101d006c00410b0818440e41440251004c0840002d42c84801100c0d01d54800b481da15401c503040002e11a0240000c0c1d07000002c103000031140d07045405080b141346180142c943d181c41400045089039128110100100e90510600760401c1c00303002d401190358443c0085510008a60000071000d901035400000040d011446070051766035085500400165007100440c2000100c0da00138109810034056500c012071000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 227496879 1250 227495629 227495641
    0xd090f060f200106120c050405071106070e0d0f120806030106061202210f070809010b010f030911031608010e01020c0a030c0804050d151505010807030e0c100201020c0f0d17 76
    0xd8031110007030039425403000c02020b00c0d28001202d00c1c1b580c41080e1080b85410300140d0f031a8002c490112842c0001f501404a55441c4c510944e0134400840d402604480b01060040c0018140c0000c050002e0007030303242005080480c007006020180c0117011038060b9041040400600f5040004403019503100f0401586900d048000e401d0404441c0e0f1100b00140300c950244240781c00e45601c0c172409420559a114515941c240c1030701e09941c500e002c0c080c0003c505004a0030014481d80c03002c260684100d02c0052209183da001915100040480d07032508034841c4c900f00b00005092042d40b95004e201e000a5007051500c20015031640380e00d1030060305004107003598004100080003264040c004c001c1030713a01440d00ca81800004130342c020440c448681d24040004110f00c481c40040c0302221016900c4002c6696604011400390000c02c1c000081da110b111982013003551008080021001d19a000588030300340502c1003880e04418034550680c03600015001102160f010114400303180e08803c00400c50303100c80e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 227498129 1250 227496879 227496881
    0x303091012020406271401050d090210121a0a0e0408040815070306090213091d010504050312010f14010305100b13061d0f0d020406080d090f060f2001 66
    0x105804001d910b01c005801300f840758105190350320340071050301981480c00710400400e0300d40d04280226207402d41c1d9803a008600d50f200713800404078000c038440c02180415103a0301088020300140c103110007042012086580301e074030900c07440c044c02d140c85072960440b507140404075049501d5401031040780403c4900240520045208507402007011070200d6011000882e05219104800d80c1c201c130010b0304146001656019a0003a01c000505101038400722a01e4868032900500284441a008075805000c10540c02428410944503074081c6c000766a4942e080c003880b0201c004140c0004200c02981c14040c0041a580c1400100c109001e0900284941314100107001d020380560011f0600f4a002500812042c45007060004540c100d440d110030201e04004110001e44901144030b8000b03805a000900a02d410794400506500190001a4403515140800d08241d000110075012500b15042044001034054070f010042109260040003402341410040040c00d480060001460108942011070402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 227499379 1250 227498129 227498147
    0x1b1a070c0b1317030414060a230405010b030a030302090405060603010f060503131709010201110301080a030e040f230124081e100602060f0c070312020409060e150d0203030910 77
    0x1082c83c1e500d81340d01d010316107820344140c40d0324040356502401c00405c14075040380c040e10014021402a4070b1214005004000319800018010b030f94964880c041c60300d2645042c8400d140082c001c0e540507a4134021102404196030000c2e000030b00644041004101c0007030341400398401d880c1d0602c0c2030781c1c1d60b0300e43c0a20300d04004400c0001400d0344001d800c4030002e031900380c4018034021500303030024803150742882d07103e02583c0404d101d0031007582c204501020019105482c0c5252003000108002020005004400112051034070019181d02849410020010303000107041e0040040c13807040007a201c5800100301511484406440502801c14082010b55111428008900720034130364062003840d0606042540c400300d80f1a00c405409180d002c42c4e415540040f80d136106094030032060349402c0056038101c601842140c0b035407160751b50900012459441c0e80c090100100001c0001202c241403084a41010015411095105542a115100c0107032004002d48a6052040314034460610300042e060303e82c001c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 227500629 1250 227499379 227499413
    0x9020a080c040312050f1c02073c0212030c0307020117040510090f051b040c02010e0d0c0503041e0302011e0e040203060105070b0a090c06091206020a1b1a070c0b13 72
    0x682104d0b40f0003000c5041d230141c030030b0350b0068040540c42010010012110700e100101e80812071040c2292a5075004000c0c0440c5945101500044964803849006804d5400009880440780c100050000c203540c0d0040b00060010180025038000741407130b41d41e959a5510915500c0c040300d40307440358001402012001c150038182c00605503213601700c50701c401040401e400c484281c8101c2c40c00c0b61403c0f80030301c1441109060354956000b8007151144000982d600ea0b240d1600312081d120812000c9901400c484142c10f012002c0c0c54000303601401c40c80050800c60000132a03140584a04850b1a503503584003078131802d000000c1c0c60040c4d981d00d134074004813203c1c85001c00160180c0d10140034040312007020791018460700e026032400c10903591108c508481c1e003449445040ba01d2420100940c001c24065070007020710035a542007256003105d103403007290554003907188190b400240c01c40c000030016403006502d9034080c08a2500080c3c2d940560351f040aa20f00280c0b148000300080048041040410300940044038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 227501879 1250 227500629 227500657
    0x19080c091902070b01032f04021b0703110a061403060f030106080a0312180201082e120c080304051c0503070206040803031e040f030f0e0a09020a080c040312050f 71
    0x1aa030f60918920303c52081c4811682c61205141d0409600c000c00c0c20102c48068141d80140641d440740b0420000c0e4110a20001c0c40079041050a0141d4204020000040d407080b0500d1420500702020000021a160b101000f800118454201c6400d1f00c03101b120350100d400c031000450121020f011a0052109400900451040d00d01c140203050b040401160766a02e11031041c0203103042c0081d204001949144000c1c049880030010550071050074401d02c56400040790031340d01880415003203030700020003584019440984c44130b4080030301c1541158000580100402145014984400f0a00d22803c17050720148100c0c2582c904000c1001c1401220005d680040a00d510356444d40300440d2260700a441d05c108030b81c100000c42c002c0e240369100c128030540d0003800882c51480c25403000c0d1801c454200d0004200b20303400421034050303511411541e024016002005885808420700038080c100c001c1c000c030280c0302e4180400c20010394461040510b8030300d1854940d0300c900c0c2c60404080e060207515050380c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 227503129 1250 227501879 227501887
    0x709060807030f0606050403060b0a060206061c02061207030b09010308090d08041a040e07030501033c05010606030e06040b150316060503060405010501030207051002090d0c0f0519080c091902 84
    0x5d41d502001400c140d034000e050810034295040d040000345500707446508096000200001c1a5181c20480855108650441c42400e2141a40016215840300341c142c40580074100130f01019990501c5041c07000320096411030195411500c0703886150040418441c480c40d00540d040d0304101c07640040d100203044c1000112000703601d50302401c4494005005a1550b0544c80000585171403090182e50704a9030003a0b4a40080c0c3e0400d51030b540c3c0380032610303604501c01390650b640d009d1000032540c072078203454054000040ca2500b4420000c0545104948800d0154007070320a00c00403c6459083d03075000180000c80c900140c11000109080442000c20380b00011070200340010040d401070300640c41900102d40c2002260303200c2005608a002c0c0b40e102800300d5100c2481e20411040300d500414420000410312198001581d403402d0168049400030981002d0a075020483c07801c05062804940504025108a641c02c101604d075039403410340c1c9403910510419010944a48200314510f181c4982c54100f075540f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 227504379 1250 227503129 227503139
    0x1206090613023a05071d0f06210f010b091309020102010e031908060a0305030915251a0c03040605071404080105160e010f0309140706090e06090709060807030f06 71
    0x6003c504a1a20716441c10b02c1c0014540b02c0c440c054540b5400c415003503038a80c503c40d00c8107004500c882c0c09515034005804022803103404960000d90034035800e800001c203142d864060031001040b0410780c0030022401050004070f90658803d40e0b01e2015100e50080052488900d000413409051b00c0b001e10f4103035000c0010240c403040a80c401281c0500000d0f19640c0058507a6020b00080a1080c0f0015046400070b00540490345801d222010003180710540303e90410341200c01c800141030050000c1c071801791001e80c0100403c2102078014005a034282c0c1110b81a1034501c21443c52440b004100030982d50f5607500145426000b501c00106400201c190b444d212500c44483d18000d01094900c0c2e000203440d800e0004110303200388014541f6a0040e0b46d072072541c035082e000030341c09404680421100001030300450b00c007072401040b4806c0185542d5a64030911880e00b41120507a140281010340159110000c00105a4000b6609022039109181091447d41c4880c070860040180703403001c04481e824400b00041c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 227505629 1250 227504379 227504467
    0x907090623010206070804080d0b03010f09110a06050f0307020102071b0905090601230f040c0216121106091903240e12070503040f0b120609061302 65
    0xe005400700d0381092040c000d24005a9403035070212624000205910300150002e408540034008886103502e01140d1101200000f82c01d55a180c406c1c07440f9680e90b0a03001c01440100d48404600100c02d4640c0c902150801100070a030748034481c0d80f0007034503000001150b2810700c03d5048401c01c5401c10075046901031a80c18135010003420b441400ba0b190b051001042e15800081080d82c12100c40e108840b00c5014000000c1e0703501c130034903041c1c00d900c40b9800c0e100d040640c64a02881d031054203540e001c0c0c80e45d444038040250b00d001090708410360b4002801031f81e000007110034900200c2440120b94403a00c80b028040010042c2031000e40043c04407200c500700000f04420800050070f030751440d9414500490085000004498160202080c1da501c1900c403940d9040c1c0703510040400c00d01410540740383c01d85481d100310603007440783e00512000c4400505808030190511130203030003c0301160700840c2420010300103005080d1a0b55003e454503800204468520340041c412540005440c804811001c59400f03555 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 227506879 1250 227505629 227505659
    0x2030f040605090f040b180702011d0607031401180902040b0d050a022803171e0c0606040204060e040c1806021f06050306040f050a06050c0a03060b0405030d030509070906 75
    0xe8000c13019414601854a40390003804210900070308107030103400d202c1b074012a002d00003801442c00c0d5541c4549801c40404170300c03c10704800f1a120000d2089003040d00004013207941904d03040d02d09402c510014403101c0c0d406121109900810803011075400c0c01400000c0051401d6402282c0c8450321050360010400d004c2140600b440c0216a000c0561038058100e402d0861007101c10406000244010b10002c0d001e0b44e191284010014400c50424150800100b802642c103506480d0000010403001c901d0f0f0010800c003548000c00341e9056090070f10f0300324007401280ca01e200052146891300c44003181c0a1140c490b1031045105000d001c61115551040a034a4000094080d00c000626000c1c0560401d01c0b40a00400c0b504040d006001e650741d0f41e01e504801d00da059002719440d005016a005c04500d0a002c0d6600410071006401d55400c5140c0f0080d040ba5841d5200c105040c4080c442000103540109800310b8803250f0f8140032400d0b6480450807030030110315401c100007503898040080343e20642c2020f04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 227508129 1250 227506879 227506897
    0x905040c050607033b0405100909150501050d02010f051c0f0e060f04020d030c0501020c0d0e030c0a08031b01020c060c0a1701050a1202180108062d0c0a02030f040605 73
    0x1003d4100c1400c1001c404580501715400b41008101420201e410f065001d41d030301400890403001000d440f10540710a46520b088142c441d003841c010780142201c4e440c0704150051404480c1c500000703007264000f81081000720041c205220300800c1050001c070300307203160340e6845040e150700f08683c0f400510b00000a040c400c00e050024801c0800180c0e211039000ca10500031070300100601d16035605594110307040f17030560a045405c0d54080c84010503001c81003100e080702155030340313a86000c00c030990185840c0581c0f4140042c410380c0341440130401c0d0b030804821a4820409036034201e0a0180031000c0c0750192080c1c410805082c0310b454104040c8440103c060040318501e55501d07201003940c0004046060000c0c0240c42d170140d03188504001c0c0104441100c03070325510103002c0d80c19450002c440d942c5402826400700321660415020000b49401c40700107260701181c04503030482405041c00c00b145502000404141c45108001b90040d4424020010f9600407103280028554983e241c074401401c40d08001c0301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 227509379 1250 227508129 227508167
    0x7061202070213181406160f09092f1206010c031205060a0b12091029120304150306090902010815040204090c0201020315011106010905040c05060703 66
    0x10201001025000312000640c005000c91808190b0080d16002026004800d012081840003038400059680d4401c05511448102504080c6010205c45030300c4440500d5000801c03480600007848a90000203140a5a02d001d40015141580c400040303014580c250302e044c10038040c0c0c1a902640c4131803c00524481c101c3c0700c080041d40d1600801907410208414004003c254110788070801042d03076900c4203502582c000c0a10055aa407181c60040310b80c0300c0c440c0700381940035100070001c090b0010000100800b0038001c0802c4070042c46501c0c1c2801810700c1340f1000c6607004450420090341c0d036150342090042803100650f952a40d0f5298130004220210728048042030900000140d46981489001026034047e12840b07010790307e84010400310420300c503921342e00a90030701c000302d80c042c00341c821030200c22403030380005070b4a00f410000d4003542c04e15460080c0c10040d01000084400c500420b5440c1100d24508000c80c403500c1c0c0385001001e0301d6040e040260003510100d403005c107066204030214145024100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 227510629 1250 227509379 227509397
    0xf1209010b0d050a06050705070204061403070e0126030c06090a051207030e13090605160e03070510080403020a020d030f11070803181f0503040212011e0e010912020706 74
    0x340610500c4002e4080e01e250411420781c0d001c00c649800495004100c1d18241d4500b03142503000034100ca890b90410b401130110300906414500b801c1001c44081c0c11801c0d40d980329589001c0b00146000030314266401d001c8200d81c22038100500400c180d0380d0000ea15015505c2c40c0c40c24125603a03448a00f03040940e0365210b40c111500140408804481130141c06541d20307150458403900f401400b0303001d040300d408240d503941c007100c01082d128841c1c01d000f050065501c1950950888000340740c5a11558400e22940040e0020801680c503190300350010842400c0450f1a60307280e040682c02c007041c003803029405c00040c40400041650100307030410340320402d440b603500c5426403c148036a60b03041c0340101c3c449940704000c7d5002d2181407100c044030031403004004500000c0c00c40c1c048988809047d60b46400308001105000440c03030504181e0710005c442a00810542645008941311460848007001c6906d03035a007003421600d0421f400c074500d910b0b004010488462034100f4000d581e04c00341c7c800c0c0000150004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 227511879 1250 227510629 227510651
    0x2010f05120f040302030705150603011a100f050d0504050a1a090a080c010608070807081c09030303110c0303070c022704060f1416020106050628050f120901 69
    0x501520091007070501030070815070701c21281c42400301c800351003901540300500445001840c10402060341061640c00340c51107040c42c13000c5c98252404c0c04081d8203a12106040380819448079042d8180709492450001d0810400160940321032203a42041402641813604000034000d00068039441c0500c902e0385401000780310140d0310b01101003a6101290351300401c1034030020801d1440a050030760f8080000140082d07944102c9445c11410b58000c03181d94002035801c210000062020b120b15250041022810100d84000203041c844103020013024903640e5800183d0140d00c030000d407030084502108032580c0341070240d8080c24840541c01e0481c0320f05000c412901080030380600b2800e400342c1210707140701c50340c441d0742d901d4014028582d818414941c4d40e00d100d004000321101c0c5c1c40c0c000d40c41410b038150319552039030000303003581c01c5a04181c0c068041000304814544007a960a011908040901114110560400c5985104450044415070030110700640c00004828009008070203140003080240521 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 227513129 1250 227511879 227511887
    0x70e011d0f040f061803200102070b0f0702070b1614011e020c0c0414040501050121110111030310080114090303040305030a1103010b030a0f0603080405040207020f040f0902010f 78
    0x80750200103000e007520201e800281d800700c007078010a10810020a200d4041d03d850010703c04907503c00c1c0c0006503103080062400164a00c90f03800f1101134030095180540940381d64040800c00341c810300d201e0003200d000444a52092000001070f081381c106095427144d06110000c80c0c01a140d0701541d0441000c041489004d005121b084080f503c1c055504044c1c11145040c10029001040400d14130b0040c1d140c804801c1d43c81748a80d03a94030030403016604140c20a03081c510708565050300702000343e11248030105c124005070355003010401d502c04440840a609000101c40d82d0b41c90840791441848003006010700c5031443d81034072003030740c0c071440c02040010001061404400f0050303603031320503d8008102140c00300340728000640d030041c0d1003100840d00c50318001c444009944242c1c0f040d0407e520110138040c906050303000e0702c2c7e02d40c01d0210051044509645071100c1c50b2086110315403241c1c2d400a0748104545800300150018417005004108040039400743c80064000308a04a0005009103046101d540c09 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 227514379 1250 227513129 227513131
    0x50a0f030905010f090f180204030c080616050c0a08090402130f060f1817160e0a0e06070e010f120204080703020a15090909170711030705010906080a0b0a0305070e011d 74
    0x2424444e803411910b03040c04070407c1211108403410580d0201300100c08614541000c000411103200101214500035450030300c0c40750b41c2c8005804201041011400c52040007a12036686d5801120441e900d00e01100000c0c001d101b020f0703041907640c00010001407901240301c0400c085840700e4440e05200d441060003151000c00070011880001d80e103440901015950500e030303894044000003110380b251041d01039030300820b900364004c1105a840ca02085158915070107410480c0c0c1c00304005003540c0c00c20b0300c805030101d01c01c04001410008600b640000a9100d05c050040c00d50100b1021503884c2d07140e440094640d4182c4c00160b001c1c11141000240d404048074400620000300c1c1d0703c1000540c18240582d0142c0744403101921840e420703411204450310f01000a2019074880c2c9461518500c06405050811510b03501042c14008111000c006268000b4000b541c4030000a1000544024001c002040418a038001400c00d105240c404194680d9501209058503100c1c003941542d102c0a40007c8040c01c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 227515629 1250 227514379 227514389
    0x601060306240905090a0515060304050c12031312060501061119050c06030a1b03060b0912071a0a0201050a02040b04180906050a06030b0112050613050a0f030905010f09 74
    0x104003515040d520030252081c2c008030039a20700b1640140e40c1300300141c40d0510a90b0f092104a81c1c4e4400e1054034112004d000c5002d5106946413402d40c40c040c0c503220f4543c0d80b1600e03851f009510741c200d0b4403840903052080300c4015034a20440c01038581c5415465080b841e1066007192014075000000c140036000344444861000700b04010250b5020000d00718601100e8107004030b0782031140e00407500b4503698440c095440392200940c00a03858502c0b066000307622480100d040245880d0200a0081d51090011140044030030b54204112a0408804500c0c000c2c0d01d611504001203000c03424032a00448000501c003990a40e0b0090226403100c0c21444124401e40c422420b600b94100000c01c00c403c17000385a6140d00804403c009030440d5261100c2c0203654048410300d288a545102c14800c02204048060260600d20242400c040896550310740d100400760900e03c2c0394816492200801c502007010b07121465000c5d40040c401041454040d102c900d25010305808150302d010410b0040d1712680084040340c2c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 227516879 1250 227515629 227515649
    0xc0f0201050609010e22152906030c0f1e0a081008030301031202032a0d0c0209040605131203020706050c0901090b0c0c03070312020d050c060621010e0a050601060306 73
    0x501e03511b40c00f0a00500e40c01d1078504421702c0400d020003088288007103d002540c1d0101c0030841c0300c080710300164468442907c2d0785c00090012000301150329075009407a03009000a03072541da00c0b000040551550b003d0040040c01070240b0304401c080510f404005400079140b82e8480308855200c3c0b203050744190003640a807181542c0140010000715019164420a03002c2a00640385450303502070003802621040780b0040801d820300c0f0300c004038004003080a561101d140b80b9090041250960008245802c040c0c005080942c0300d00110340d84142400003596050f0741702616280301482c110300500a5000200103466452401c0c000943d14852001120f02540d41650781243c203d0034020b02e03041c1c0703030840c00420140348140340300061182c50400085002d9401586604030403080507400a2070304400365010410442c007031050440740000010f42e144c00040c1240d030003a4401c01007511482c4101c2c6000c2c140003e60922400421400380030a030361610a005074191030782c507030701c0d54001c2d0160344403442042d01c11 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 227517985 1106 227516879 227516881
    0xa03020708060702030c030d090201020f070f08060601170a0c09120609060b0609130b240901030b0906030c040b030f01050c04060207050a0b180409060c0f0201050609010e 75
    0x100343c40c07004520b00076030138803039540b00d0040d0410040c89a84665a510840e070090141940c4424110100e41c1c020355138940880364103110303110311300003801541c0106049512a500845040000b200c0c050707030a880700540d81e0010300c10480d014041240c2041c001c00c60314400c082010155000359408a1402000d0502208031a4544200da109020070072445020b82c81d081d042206400003d031000510504010100700903221441012980300d1800b4884c0c0c5540e030f1210091f1094034401c0c1c1e4204055800a0140000e41c40d00b41c40e00d80e416405074032711501d54a0643c00500d0350450250035198144200f0b55480c0c01d4a00a0350030300980d880224051001580c1008050014603040320300c04152032801c442c0e00c1d4030784181014040045012038a540160b12103400600c07510740c2c0244100704c09900290002d20500c0c01d40c0501005508050100b042e038a01212980e041c0e8201c14035420507 = true := by decide +kernel

theorem cover : BRFrame.Cov 227338129 227517985 := by
  have h0 := BRFrame.cov_init 227338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 227338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 227338129 ≤ n) (h2 : n < 227517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
