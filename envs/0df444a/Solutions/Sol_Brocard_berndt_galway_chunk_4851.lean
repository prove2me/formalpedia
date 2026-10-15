-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4851
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:56:19.262402+00:00
-- url     : https://prove2.me/submissions/a9a39c8e-990f-445d-9ad8-dbd951dbdc84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 872302158 ≤ n < 872482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 872303408 1250 872302158 872302177
    0x51f090506100801181e11070b1003080a0309081207081e06030309010c0f080318071d040b0402010309021c03090509061c0f02040f022503020706230a030e12 69
    0x4070340b4101c1080300c000c1005070366a90940c04079090b003241c0c2e44254040c1c7c07032001c07501c0c0f00050744850a0341080400300d403025011051701204400b0400020340610141c50741212142400100554a41080e0503d40724940f0b02d07003901c000310340821560325041071010f40101c400741c03035400ca02130b158900035101d410240c1d8016031640c4140001151076100310384050300a4030464803412229299034610f00c03141c1064901c8281c1a03001500049220700c1001884010729000103000e1403e4006070900c00b603808051b001400660b100300000e004c0d0b9000307400001202c1c0c0c0c00b601503082c22440701d0221030340543c412011070004020f8140010b15181c008507141c003a580040c0004a241064011007084075000481100d0411012207041c015994621a00e1030030801c0c00405692007804e445100c109504007558001c0b2a50300960b0b070001719a0014400080d5141030078040505090943c540013107114070140c4180d58000002c51060859168000001c0c00501000b00d48440b00380351500c4040c3c0c020280e11 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 872304658 1250 872303408 872303429
    0x606060818330a0204031a0705180f030f030c0f061630020d0c02060f01090f0e010e010603051e03030a110412050a03090902120406051f090506100801 66
    0x2844030010342002800d1a4401003030208841400d510003074902a20110f4480d01495800305003002030003c0d0040301d40401e006a110340f20365142c00300b009442809070511b103040391300b852405080710762160703042410a0038001b011290103094401e200c42e5254855000a0514040e038010300141c004001380032402510100d601002e0458088011110001820720380044080c400055442031001c24001220a14411102594a0f400110700c502612130130b101c0c075011036000300100001d0031651180d0382d0546404000c0031401042d070300d00c008050241400440c0710f5510700500030084210541c0010100d920680c291001c05e00c1d584c00820134401807011035043c98004000041a5401691204e42c0400c010400f11b400e158036010400355454a0600890b1f45c0e603c00c486060915412881a00c01454115020b44c0781c1031203448041241e000c003400040c185a15000403401d02c50b14070303800f020015032201c0010155a5201c0c15000030708003d4451901030b8480c2034003030340e2441c4210403407411780d40700c0301c2e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 872305908 1250 872304658 872304673
    0x30f09050705090a0605091906320f1806030c060a0507140a0f14060609130201140d05040b010e0604112203080c1b180c030c0409090606060818 63
    0x14441d00d10f1000785030083e010381c0c0e86408501c80da00c058039280100e4006c000405072100c0754141c1402c40704030303030080c00504000d101c038440c6001e0503140080000c41840300300408001c44034080396041c800070840030307849440070324640f00e201c0705040e4161003100220b086907851002802400880e100d1110703c44000b070020000c5034003185940080e00c102506410484405008940303ca801090b0300364030844140384e202003203c8000c54200308042d0420421510912a41000c11000080720580040281031101601c1c1018010440100780e0340080c4000105002500d0705281046009909001e661070084506000c103015003231a20400000003014100c04c3e2421150f401465a02500074a40108400b905000400044e000601511201d140c1d140108440c4100b0002c1040085541c40781502a00010840811031030280b40b045400c10056403605070f4a484100c0038101e207100d20b800c5080400d0515403240100046075115030200c0c0c1c8c3c60b0b60340c2c4a0b192913110808030b17500e03203071000b002140c1c0c8200c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 872307158 1250 872305908 872305919
    0x30f0204030803071b061e0c0311092701060908070806010b120402030f0d0305071d0d060506010c080408100f02031b180909060108210f0904020403051c030f090507 72
    0x71011103a05c60040703507078050b080b0340e955054180c403002c5607010800460500c445007903007910700644112000a003418400c0030100c041e540e006014000704c46115800c1c06020020406800b0b442c6d10720020741071100010356849020103460507055208624091254070030002d134a07000460302078180c4600101803464450001884645501c014000341e0b03242c0035810660301011001c00c000300099145031000710f8076240100c1d02514454443c000d56035031102c2d00e008019a82e881103d03048516030b000d40000f90b2a141c5400484000c402900020110300000802044460000843e010702d884480750600640005480b0031040e80810b4900d24110a041b0301074481104032030024001d5401e0244a55189003000d00014100c15400d580220b903d400480050111120a0001080c81400c0c00c4c10110362805444141e0710707521407000b0350044002d01180720742c0240c1d01c5404580085400004542406404c6007a11002c0030003110a140824940001205090349031301a848a481e008030160600071f1400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 872308408 1250 872307158 872307167
    0xf020306011502330a0e070909020f061b0609010203041203020403080a03200d0509011802100e19030b0f0907050607060203040f1b0320091305120a050a030f020403080307 75
    0x20301074030071503149802c000e4140100b2002a03600c05d0403000400300d03601505542c2241001c1c183d40011080c282444003440241e1104260880b800b041500c0722660b491042c0d40682c601d60201c00560302ca40510400e0003a07420054011714082c03802510300c0701200901c500150220f1040c0c1c8001008800309000d40a0100e00a0f44603240515255000c1d001d0101c040c000c05586501150041041d02d59030000c0c0100c9030002d00c102c45000d4000d20380e0800d4100303550001002c00da008400c181c20400d8040010b5000d07250400180710702100c018481c1c1c0300540b00e1a160b500d60f00102c900032442420383c0b00151703240c0c8000a0002c1101c0340a80208d15240d45a11070001a6000400550b508038080a2090000340c505c0c40e40c0c1c0010482548460704a070941c9405500c450200e101d03032a40d20020442e00d007481d5683c0300229004240c4000c0b580218800e807401e41d090240070402030b8142d007000300706045160b80100040c08044400c3c0d174200042110f20721020101d0140d400081e26484003800002d481c030703000c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 872309658 1250 872308408 872308453
    0x9070608040201080c0717030a0603060b1507080304050c0301050403081e160516080408160e01142b050c0111060103150504051920040e0a03031e05040f020306011502 73
    0x1d41e1030315603500350447d0317480031a500c1500c122130b481e43e0740c0c6420070500c85103200b103211001d411244000310840c010321310307440e42c0201c06000d071015070000046020000108810910000f0181c000e00c8103140504000d050144200c4421140c40307074550129130081c240d82505032103030101c04030309000440c1d00386c001c488540000003104985176840c10103801248200c030140008054980003803034201881342c076503440030b11181d20965840d406ea13001800840011010004446410386c2d00180d4000c9901d808002e0200151030304c45d1420b503048612003449000704510000c03040a0b04c454a13001180b4105a07070b5a542440045c5c14068210f5400500c44010740042d50054050422541c1c46e801d8044071210106400e4802c03140039aa82c50940e802e200c00d85840c86140380704840c00c1100c10700104682c0c0d01c807840200300a0806699038480008103130070820079082840c02000c01c0205103010716210051100c0031b00d040e4841d20135070000098410b03440e44102017070807096000d040d185022440358000e0060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 872310908 1250 872309658 872309663
    0x70503070201090b100f0b03150402070c240305060d020d17040e0f07090603092a090e0303040b0a05011a03060103061809060b01020313060c080403020307060809070608040201080c07 80
    0x101d500c0400c1c0031807070722000c00e800b40d0450301d0345c540c0c041e01c0c3c524a03004d40740f443e901c2000e00c80c0060040144c002c00c103504a2a0f900d2045d240961350f806540740441c020b14485d00101c90754081000c69503115582100744008140c09500d00b08007a4480c40308000c54440400c1d0000c0d44007204a910b507000864000e050002e540c907071030040c2d0620362500745800d00c00d2012039500c0001c82d00c080402c0314280e40840780c14010812400e08100d81c600c030f82c803213200c60f800e00000d242401c0d03105940300310354522000e211002030038462401c10480c141744c001c040d140e81c02582c2c1070b200c078441200425071601d19481040d0481300e05110a448400c40408039083c243c1000381182c0c141584c641c000107541a0358001c409841e450030000007094101c40c5000c600b121240d02003a0f04651052000303208141c0a000070701c041c6c0d68241007014410311b0350314120382c4901c22600000d4150058400c0001d40c40d40001c8034901900e507038401c0d10303001ca0b183e0301c00b02d86101c801c03030780640051161404221903101c4071004201c0c80d030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 872312158 1250 872310908 872310911
    0x80906220204060b0a0c030315060807050912070b1218190302030702040504300914061c0225110d15050c0a0201060605093a061b020c09070503070201 66
    0x682e541c24441564000c03605985c08a00000c1d00c050400d80e052003100315004684880c400b03842d05208004020b200010115018030500150001651780c41c40e1400c50076210701021500056241c42402e40c00b070b0800d448502c0301480381c1c030101c2c88444080162005519101c0010240146c002c40d4911152448090079805e6010406c0b410000da103560240700d206134041d1000702c00390b11000024a404110304401e0003620140b8202a149981e8843c0700001110030082d0f006d05103d0400d000940b1900c1942c881042e1400d16124000c1c140809401078000f4101c0304111400903036604070440c80e007100f460002000e402e06002402c0c0a0300c2d1004059008a02400e107040c14200042c075018112001079450031000708010070000306a83e0709014800c05002e03c1e01e4054100951900031540205000c05040000360400240130852415400f11030054254030580740e07010002818503600400d82c3c01d07101850031701d00355140f41c00d203400020070b1182040054203034646941d90074401c41d15600041e10600465 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 872313408 1250 872312158 872312171
    0x1111005100308160c15080f0709080a11040b0d080405091909140d020c1f0302070c06090602010f02030705220b1c1d03040303142503080906220204 65
    0x7000c840213070020031801c103015940070905040c010300c040407992107240c441c1c03141d007014031050354010001500000c0c01014100c090b102c118050300c000005410070403480c13040c40360110a000305103285458501042d102000502400d1701403010b08580041d000d06045030400c010496420036048440d482040c40f94900440c90002c600d0009459840380103880703a107255a50910301e0041808510305002d5079000a080d605015408504908103580e12282d100d00e0703141d40140114040e80445208603885064210000c4d200c00004d400503c1074000d101c0190b180c030000d0000800148216400b6140c5138035101d050940303080c030000f00401200c407250361034101e42100051150740b90740506003c3e03814489980300d00d400c2d0003064044583c400012440c240d030700c80f084000139030301004aa041ea60140390040a07007040300924642c5100307192121014001c50751060000b0b10030040001d903410701c41d944201058907011a1565207520645845502020310400c203401c0c2241a0741f0500454070203480410784 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 872314658 1250 872313408 872313413
    0x306011202040810060906210f0807031d04090b0f06010c05060c07060e0106030f12030603211e051b0c06131d040f0204020a0c1704080705011110051003 67
    0x1a40c0080c0d10942d0141d20102042c2e50207501d5020306000b03424441d20407c203003441c2518440c4001c0d41c00c1003030006c205000040760240910308010700303002c0f500618103580c0c6103040e24000b001400046074148000e802e080e000ea94034030780380c000c44070300a82100280020b512007004850710b500001d070400d811721481c100d003034002450500c010b51103040c0000b401c035201c6003241403000036904101a41c0b42d890b403405205000050030f095007031040c0d80d04001046803a00c02401c040c0d0042c1416007000d042000c05940c591302c4c10380c0c0e6044884403940d0b540d840401e0a0030006840100810341d669040118005010a0b118202c48111070200c2c42d00c0e240c100c4601015000101d00298001b40f403c0f03620062004052000c44109107091007102d4031610705540b58038064403a014046002400240f05980000d81d1811891242003c4808141c0103840350005903003524443c0380b268014440d0310034500601030002110340c002c507000500c12000b0006441e01850f0302982034010b24004041e102042c0060030301102 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 872315908 1250 872314658 872314661
    0x907061815021e1b010201060b0a030b0a120506070f020c0f060a0c081206190605070303050406020d050702010e0c1203030609220501020904051003030509120f0a0b060f09060303040b03060112 84
    0x3000f4020401a0030750002d600d019604c00d404101515066a04150080180c182c400c003c41e4000601c503e00000c4031000040002c0c03002400f0fa0110105d107020417041e006001021488901680342078442d1071014a800c0c0080c1d855002d40c40740d0683c404900346010b451802c0c00002041000a0303868181d03c0c41195564000d115040030340400c4a1b407000200300801424900c10001c201e98100c80c4c800c10840c03910300010554841e1610080c10151140c0100b000c0000e641c040d9590780070205c200b40100d1500c440001e00a000842e00d4401c680300d1046035000728201400b1801e018050071020310315641daa0f109102da02d11018080c006c1c680c084c64450416400c03a11032001500c3c2c4103c0c00507035a03403084800c020130340b0402307090240f00c0d4032290000c00019070000100d91000800751444010007403134144603070400c5076200a1001f240a00544041000300001c0c0c038a1207803c00302d034801c003551202020b004440d04111245501035008020034030006403490041d5511000501d41001c080d458904c0680 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 872317158 1250 872315908 872315953
    0x50a0f0207140705060c03030a020a020c1e01030b04050610030506030c040c0c060f020324150a03020714030702090c2b02120a090809040b0a1a03090706181502 70
    0x11801400040d05140c0400c0034007103c00105003c803603050078440c48200311601e900c00600130003020b550000c0e48520390b9000f4001140640802000010380100c4011b244105440314803013140041c1c50041519043e10b050300c02c8074010a00500b1000804d00b0f19807040d0003e140c0036098a91505c5854049605603441d03000302d42510040f650340c030b2000d1129203000340c142c9070300c58040002c450040c400c100804074400c0040c050800446d480aa070440c1c1940450000249910904e02820000844070807090305070700284805882600aa088510302e4400e507616400307048002544614800c0c003081a10740d445014054528400d070006d40daa1700004040350104660387c1480310f40580100704205102c401c0500554401c50209003884444090396881c00c4510458800c40d20907951440300c00465120324a03060050500e6080003a100c0c001d01c510342ca590b03082211551010708c10380c800892841c0c07040a0303888034444601d012904080c20b0083c032058803507101d040101180b180c122400c2d0080c001c0003841 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 872318408 1250 872317158 872317163
    0xa03110406031b08090c0d0311060f1006021c11070b030f0f06040912050c0106080a08041712040312051903050106020c180a200c0d020c1206040303050a0f0207 70
    0x8044240344421011943d040000b142440303e82020001842c0020400081c045802c440c81d148000041c40c003a9007880300b18007504440c0c815003040004240702400b1160180180b004c00001c00c6a4442081380c1e54041110011505404400498105c60003840d24008144000782610007540e10744141c0000d0390030441d2414030031107000c1f0520541d4030028954540144099800344441c0d0110b071504800510a840d01e80304200c400a090405c81e502940810003800c038680a50702c801401d410010010340041c05004d004a1a10070f07510052480050403410402104805a00302407072f607100c590180d0141900300003409010880341d8040313003a403130f1b681041c0c0c642c1c1d8400080c42d50401ca0003c0c6820f00042c103960044038901c01401c4400b910042d055407003224940c010664841c500125100718600a45040b05c110010594400ba91030100b40840c1c070701711070390032600030500303c2c1300708480740044d00030503945a0070140129021038825000035500955217540032840d4401d40301144100da2110006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 872319658 1250 872318408 872318411
    0x9070504030210020a0b0a0204061706031c0c17090102060a0e10050a0e010f0c0c0204180c06050703082410022a030c0609061204030905130501380a0311040603 70
    0x4007000705861b05990840b01240741182004c1c10000050f0601808055402e80c5000103400949240d07020009482502d1a50051042d4140300c00c501800c1c40388800f6080721141c0170100c0b01034941d1422000c0e03444c28003050b0f009000d01e859502c0c41100a022100d840401c0c1d00841c10814900300341801141d0141c1d00011002903084030362944142102c40c3c004a04d020142003961790040c8a6100b03e501a8450b01103d000480700d20070240c0e0000e0344913002000385115007030720001440c00d400c8805000110b000e40c50705040366030390780b44840300b0300443e01943c1c14035a503400710f444881c00c150828419140710342c01101c100070b042c07040c802088004606000081c034516001000e581c00c0030312009000b6401603a010741015144d400149050245043d0400300011040009052511a0040f20024003002c0e00c454074004c42041c7d12000303400c003401481d1003000c07842000d00c455104030404c084050f4400030082c0b8284511600d00e05941d005840580803d40ca5950340b0320000c41c1c02c4010001081d85880 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 872320908 1250 872319658 872319673
    0x31b0c03120e04150e010b0f09030a230610090207080c070f080f0a0b01120804090f1a0f030a0605060103020f04240c0c03021c06290a140907050403021002 68
    0x100f10607074a00240d014045044c0207010040303801d10080d82819100e144107640d0301c1f4030800c2c0d100c0e103540c000c4885031541403142120500502002c10980190520380c0764040720340c4000c2101c070729540c100689004540f102c9501082049400660180c40c0380e230300c11042c01d441e001002090918010450b041a404885681810414000e0402002813188090f00240410019a8580003034100052242041410641000c1c0c010802c42000f100c000d031400c03c200f0080f1803120200c4400403c0d6000826240f050004290441850000700030300340440002e004102000080da01c003400f400000c0d007100c1c10301d5000d1006820400d10100a44094030943c407014483e03484441050b100020a80344040500c0104100f030070204485030541c0058940580c0c0d911a00c01115515449041046402926442c134080e85c903e029525206900c00303289490002161400300441001500240b0b403141c0c0540c084400003001e001c0c141100c2c0b10b039000c1e403181000b5041c44d5698003c9141092020f03400c0005030007451 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 872322158 1250 872320908 872320937
    0x1305041a09090106230d081206090a0203252f12250c0902041e0905161b0204020c0304210f060f2c0c030604031b0c0312 53
    0x1041c09034052a42c00091185034a880d80006080d08004411559000741d01407558031a10354810b0260015802021159034620590078910140e0090791180e2003000c2070801b2880d03051190090301e000d9003d09001100d40c0700212030210041d06031844403010b000e51403a50b070f0240e54018242c4c88031030140e00d0f01c0c0141c0140c203000d6181840341144640b820000140590b40c0c0500052a454080340d80c4400403043d0340f5414180444134200980c0100e034054000140422144003020290210011048075503956680310419001038401c201c0d584e480340d0300b001c1c0c60039400724030030701c001004903100c0d409241003d0f1342c90300440d003a40c0c01004d03000c20390b5200080c1089400c0c803001040b081460200c0840d000159280e94442d40314108200190050b07465a0380078a1040d480da2081c03003400c401c8040d1601000d483d46026100006041c4103040ca409408c0d030700301c1c69050200751030b0700c641e03896a00c0f081034919000c0000e00802c80c0070030941c1c3e5981031710008000a2040d107a00f5444100070f868480b08804501c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 872323408 1250 872322158 872322169
    0x108060405040c1205030f04150f03060b0d1806051e090c0102060a05090c130605010e15030a05131b030213090308070e0d08040e042f01051305041a 65
    0x1404050049240070100700c0490600c600700c40644000460140d500c180c2424501d00d9405000c210089421b000500010382044250710341ca20100181c881801069141c1400d500b250500e21422083c1007080041d503440207419449120001904661200e138511070761216001c56400300d544601c949021101d0901030400036030f01d00c0d40403060074014000c000503000000d444d40750290003203a4098642001c984003041c203200e81e0a40210145c0481c00030070413503200f038028000c1c2e4460309010405076292000740d81401401c13102500c1020101502e1500c03922064001001e00a1000540c3c00c2c043c10403100044454250880d60b102d0711605400c0182107004025040b030f0303600ca0580d91189070200d10b5001030341080c0240c2d40100d01d03041024503c91148082400485002001420034000007404142002945845405a805000005c0001c41208411000d010030b07441100c494003103449240e03515610171030013060044c0403005034042481d42c41000c81c050783e45d880d51402e00d4001040d45036a560920 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 872324658 1250 872323408 872323411
    0x301030515040f030f090509040308071101091e0302160320010f0210050606210a230c070309120818041a060c01020408060c0d0e06060108011701090c0b090108 70
    0x601d200380005040c00d50300d0034000d5541100c002c0c00d0100c00d4103442050b07030081104600505026190320024a041d02d402407402c041100c5c0388007c40c41500483c901c0407014440c641d00c066118003010582c9a01c009140410208114101d0840c440d0341d4140303070180e0340c05c40c01100a41c1f05143c40032001c0c0301c6d81e030105848980c0354501c44c100481c11420f011540e600080194080d914001700140301e4803051f0108819105001c0c4820620700c2158440250344404d980061117484a9a42004003000c641c0e0301c0c1d0414002a1420f0f0110345520022a146a02d0f240040a8035032080c00c00d52011552200c040181039003e00040d50044004200c1c0c040b2134800016444002d10102c03000c20816000d20005181c0d0008071a18034002e40700443c190800e040c4c25411103029160510031500240703840356490b9526841003008e002c1c414180441c3c1e1002c844005041806000140c40380803041e030074041042214040942c42c0e071169902e07801e401c000705010f03121000c00b8219401c4150354400000e800134088040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 872325908 1250 872324658 872324683
    0x2a150708060603010b1b01021308070f030b0c0a020c1e040f060e0c0a14130812030c090409080d0c1d0f0d0204021303141e1b01051b070b03010305 64
    0x4020051940c0d0742c20100c03410b494204211076107520919005c6251000b103a168800298400203c4a20324a00c03401c010080355404811a20001c1e20f60003680126a40c51100401c1110183e01040300c004404018215100040c4120b45c41421090001303005640101803528900d0050340c0401c0c01820702e80515004e044148500340300d030314a092000012103a001303048400c10701010500ea1540b61003103100341d401050084406440b0b8001d50ba000c19120014801c1e0710952041078400754402e068641a64800c9503680c42550400381c2d50781c01e0001401c2c0d131440031955108200280b4000f28414428542e00c5c1a165582454405051030503c4010048641c2070780304142841411540f5502d9036413200c6d600da81a900541c8a0076260b008009501030f0750001404050102e08040e918100011844020125030580e05035544040e04035a89490364400c107010040c0403e20101010b50140c001071880d803d5006440410305502100d550078515150043c07100e80a0000042003802005c101c40c1c070715090b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 872327158 1250 872325908 872325917
    0x10170303060a0509090a0b0103080d0e06040b04121b060c12140408090d0510050a14090a0b0402062209061e0303180902040915080105011203052a1507 66
    0x2401c030001400e0024600c80c0c0340c45500c0540001e461007100b88500e00382e0300e0340041c60004550b12844c2030f40b0950400c0200003d80f41ca00319200e6802840010380718050b07a00600c0c4101151181d072161450b10404003901c8040c40320105207070101d40c50350000080c519004600004100b03128440013406801c80c000d001d8080da04140201004115500c44203421039032008074155103104440204001c02c03600c1e5001b41403406450140c07046182c43e50090f910419681004016001c110503607059161000e40700e4110700d07030140320040c00180c2140003040c0c01c04d000800884c00d184080958001c21900f08490030f02c400c3c00e0480801840f8001d00440e806003800649000d0350f04920b10200749090034903c005401c01c60202001d115108030f030005503020305150807041d5034481d03c0385895030150402034850045540380a2000030400c2040c4541c40c140e032405000c0990243e100c0e2001c03a403a0300400ca56998018840600000060240c0c0640720f4039030300d90b0050f01c0c2d65401c85818a01c40d0100502180030300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 872328408 1250 872327158 872327161
    0x50a05010e16030e10060608011a030c18010e04150e01120503090d03210c1e0f03090206040806010303230315130b0a0608061003020f090d051510170303 67
    0x740000321081c03400c40940780006001c0d480304c0d01503180c03008441d584810075117030138004240141d005d00301da8141d61107040514000341503041146960701c021130301140e21074818050000f8110045100caa401041407400c1c2074021030200014048440f8082c0d8251301031300311081000702e0040d0010090045c005890000c4503a0440d45445840c0c0c4a16406648219210224001014000c0c00e842e03400000300101c1c88440759424854030b0050403002500003f02d4821415081c0e49071400442007442041a960844c2a04880c00243c02400088400300d90250042c040482d0b507840030840180294001c1d907507804145202a40c099052907070801940140c40c041041001c40c0700401c0d003003030f4052815120003141c5551044d07018001d040b0192865401108590005281603100300018000c0000700d566554010020600790708a109681b00b441010b44140400d207041d00c1c10520f1424400c0c001c03025110340d1850f443c20500030313070f601721014016140e007080140300e040dc080c5903025190b042300000703500c1c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 872329658 1250 872328408 872328421
    0x7060e190b27030622140304360f0608030d02030a0c050a090e182a030a0203210705030408010c0e0906331b1b0d0f051f050a05010e 58
    0xb640300080003007080b89101141c0601040007101e44070317940d0b90400280981141141103880e120750080c480c0c101c0b00c00c0607a9050919080c800340d02616020301c081c0400380350751040c41c560040d00e142004550819921400000e480e503050004101c3c0c150714110069681c0740500082040b2088440601c04000c0207111104001d03030040d107108261000750a0250f6241d9a98030f100080c41403140e04c804c0d250140a0759281c8100c4852101c80400c4011081027624000d03400a150f03540015010103503259022a0141c10002d2a140010200200c030000c03161610500740c581070329660080c1e0103900607079511000d0480340c1d64004200000703120104d4528100d4145840020800c03070340001e80415198071080e05010040076020300380007444103510060703200d4512550003103031082e060411144a025a103041c0344600b11010814601c56030041c540780704020300c2c1e05c4149820b54114411a4203114503141c00707110407019495001030030003900c40858545445180007050b9201030744016042c0c000002400032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 872330908 1250 872329658 872329663
    0x2190801050a0603050912040e07020c031b060705030706060807031104060b030c0903210a080919031803020405010f0503010c0207050609040e07030c030302011415010207060e190b2703 81
    0x1220f00383d150105442e00c80305150f80c01d05407081c000540480002600103030b040c105403d464464840c0340c00344c0701e0b02c010190034140c86007820020503c00802180000b4018508080078102c50b82c024001c50341401146d5407401c003210866002040c155000c0700040042115801c0808884074043e41c080c02260300d0400e4050940c00702621034503050340301103890000c0d03450402c4000c2007a8003401355240441c000880341c452303990000c544400003c44140004100940c000340b02e03c0130480d004c0910b030281704162401c0703c8000e00c0f444030141070800000c002015945d0350040c00e018210103201d4903030092a00080500f142d41070300c50b020654100342003c02250380c0b001b094520100c006e441c0454a41d030700c2d12815062845980005204060000d008424542c0c154040003904111a40a00203a1654428440035200200d00c084c0181e20590b014802140304070340030039101c0c001500c8102c1084101c2540300010740150090031001d2004039146a22000c0c904803e41c00c1002130400254840b10b10700400d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 872332158 1250 872330908 872330929
    0x3110306010b091c0f0f120f02030306100f1101020d29030714040603020d062f16140607170c090d0602030907080303151011030304060509120703030219080105 70
    0x2256203083c04a1130007408002241c40b000c8079840300c41072480c41c0041c50040341800030060014000b5281c8420f00c801c80f4000001c0300d005240c0104a80c071841802d100403141403451303500e00030810030000d8500174040000d001074640300030407880c00300d40c4828480f0740e074403010455110503800e880614042c49298402041c03e030700740da00215a090701200c008020401510640d07100075003101c0d000d520310b02441400d174851210035104103170040d8203800500035038600c940c103000e14043d450000c001c10b102c0c3e601c4110450b189944240801005c0d800d00149090402c2d400329080c001003000201c1030040c0481d02a50f40d0b80c40f02850660724100501880404d04010700ea00c80240501c1d80040415511071b000c0010000410031030b01129a68540b544048001c8841c076030001c0c3c000c2011100004041c0e01450f4000e817160401320041d419551181c4401c4042e00000e080b500d801d005000c00301c00110644001800078a0103910003595403482ca07019000f08581003d419010480c0250041c469542c0701441c81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 872333408 1250 872332158 872332189
    0x406030e2a100201180305090f0a0b0f07060f060b030405011103100b07021507080d0e0a031b0614270a030215190f0504051504030906110709050103110306010b09 71
    0x582c9042c0d0800090780188401c1c503c5568280b00c10400c04c0c20150701100810a20310f050f185103560088880071b10120503c6406400c041000511407a2141c00b808070143c90601e02824001c602c241814110404842d42a00b100340c00080010401041c40400d0041c20001c83d00302408618614240e44000c00c03241040c040c00c0700300c4000050310001d6646410816030225000c0780e01541c1c40a1610f00307000d4030b038860034030036017124241641428840c0000c1032504803150540c44000700d1000214440700c0d44482d04400715510755071286038403000300c4024007580c410a40c0c60492814001c03520400100035440329261201039100030303507040c0000d60100758200c0c0402c8080e1032a040b51030345d449408800541c0300000c01424600101059901e040d030f0000c0c0d015600800580d20480310001207000106001c9401a011881d00c0004001c0c0c1881a11021036842c898030660315130300d861321040c0041d17078070aa04c103a500b1052440581554901404403600404400c1a0a480c1618040205d8a03c071324201d446c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 872334658 1250 872333408 872333419
    0x1106040b01140d0b0109020408190203030d0f140403020627120a021015050406080a1a0a090510090501050c032e051c0b0601110606041107080406030e2a 67
    0x20401e0b81d119441050012980001e440026686480102000b50054400c204407481038621086e400c0c8104c00c1e03880c08094026000d5850314270a0f02c80e0303801038030300c001c01041410340d145440c404a01d44481c000b801030703101e64082c09907410080000d000d08001d40c0d1180c010740d4600c41106158200020b01044030070607041c149501c0b400030789005c1e4245080c8104042e42c0b641806100c4654070310606a0300300340d507003c9400700002600d600c0040c1e039132070001038010001d0381d5602584000014a8294941c0924001004a01c4d290169036090400120395080e09245403961b48020400c60280656584480b5000c0540d065103041000c048103410710800d10200503080d071124062581025910720040c100103001c4400ca0304480258054612021105444001181021403180d40c03060107049549042d40001701020303243c820400000703150307a041d1544521070402c401d50000d00c540010700000c02031620300040031813103004581e00f001c003045001d400c98460815240010311176841600c2128209a45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 872335908 1250 872334658 872334689
    0x72306011715190e0f030a090603020405010813110301060b0706060603110714070b041203111b090a02120c07050601090516030c23130f05011e05070f0b06011106040b01 74
    0x3c20001060712001c00c812034051100d00c690440e0001005008189056a4920010340e5074601101207000d00e000d46400156102c2c0444c0612841d4001c4020460240403007001603040403000901310b071401da01001200030003140701070a100f15403003144005e0525050902c802201d84409460303e2241d80e000078071803000c00500e20358100003013145201a1160f0014595240e0311501422a0441c4400045001440c283e84031542d2500100f102010041c103420400900401c2404100900d1401813180003465803d01540c660305e000b0b52035950151140210311595003016060003410900e0580041481e9402c3c00240b00c8034041d0009440070017442e91034002044150420101c13005031100b84002454918411009a244601401004100700300c824400d02c007552031920401c8100035110300c1d804956418000030350020510741a07000b4403100d19010b880c20b9a00d0351031820140a0700010b40d10300240104112003540c01c903e01820141d06600101600e10307196031080d803100014090300c0280700a240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 872337158 1250 872335908 872335951
    0x7080c0312040305031611073309080d03090c0e070e030d08060f150703180f15090e1003112b0308060907090b072306011715 55
    0x269095001a481d44a41c5402c0c2401d00404a4005641d8201107041000c88016401d00403406426165140d40c00340c4092031409084102c03800c0807800d00c42d982d403035400d0f010051703030210369002c807400301c2507100d4000c1070b81000a82490080701e0309090050618024050001c50082210801128030f1162140e0310344d503580f0001c54001802c0c00301d254051142c1c401c1610340c0e03500b0040062113581d091301c17015001c4240408002c410100d02c41c00b1140781c402080081c0101e80705402c82c1c1001c104002c413418100740d880c0c00900000c009548400940000030490b08011607210920400034080d1041d820704508001018194544640c800200845a4444448100c1d16582c0082c80940340c4014604403e03540345007a80504c4480d00c0d0100c0004264800144152516011a5001d80941d50f1400841070404031092000e0b4000003066450301c01c0e50302c0c1302130b10350001c02140484906090207081030754503110f40c3e000c508040f00c4d0307880c4058204819030a40140e1220841da80244c40720340c0d0450000d00e98 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 872338408 1250 872337158 872337163
    0x1009020a03021903020301110a0e060c010912050403050d1e1805060d060504050c030f2a03040501200405010f030b0604030c0312123c15091107030507080c 68
    0x1607200079006a0144242d10b00c0c003e603000050201c0b80264000e10003004040b0391500a84079450850f008500c246108107040e08001e4081c0101100c02400029080c100d40c50fa02c0a00300c0b03030b0f20300070001000020240204442803001500070307622400c14620003007401026642400036182840104505288866441403014580f0750051401800065585a656110801900302801005e000b5402d113004684070452450445c0e100300307110039400c0490344812029159260041100141c10387d0022103044070100c84030300850042e03100d48000108041d0b10001c404030b400da2628400c03103108041c0001c001d9a60400c4440345034071868903002880070700305000a59580240c3e00084c0c00c1400003400802080740e03020310300741c0074602c580314514021411002c1400351216007001d141a05040710701d14542c00c81113150b04001c0303d04131000003143c01d007200070181145d10402519883c01c05410741040800301501c81c400503407000b02210341c074040058901a0407441104002080398a00040003404039105 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 872339658 1250 872338408 872338429
    0x3150e07031d031b0307020f0d11090c09030c0306010608071220070b0a2a03330801050c0a111c0305070917070b0a020c3f100902 57
    0x62810b40e208603a4900e1142d03680c0d044034042c000c00e00c075614510080c007440007080d500302070340c004c1a280302c02103104140503071250f0310788084440802c00703d49820180d8415400c54855282091040d4540001c5d00415182580f22580b0740d0103a04003000500490768032102499000380b01c4c0c20a4480350740b550200300001d111044108040200410311422140440e030300824903d400355280c14042d0301c0300d4030b002003103807035102e5020120b54a582c0b01c043c0c1c5050002c00e0040040180c10001407241c94203015248a110f00c4454400300045c618840409c51006012600a0040c035002085580b403d12028400e51050024860922106010030600e05074100000d10380c42c0481500c0310240220301102401400e4203803881404503910000100d44030f0502c1c5000b00c0424490300044c60000e11303050010036141d022000c41411030061403401d84943e01c62015607200700070442e000e000041d030002281d2036910040200300e4201401c4601144050400050803800303041518400600c0002c180b00280700d910b00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 872340908 1250 872339658 872339681
    0x100f0e190302120d080c03100303080a0f14090d030227120304030303020408060a0c0203030601180902070f05010f020702150a17010b270a060e18010b0705010c03150e0703 75
    0x34250b8401e040c0103000c41c5600300440180c6516484d40c4a0081c6e441d0705000484070030320700321501c202c00c1010910668015420203811100000c190340000d03c5c000030ba5011741e01130350913048440188440b4a004108006017040e50f0b14045051010b111440c00307440b580840002c8801581c1c00240042d5903501c0020002c00c41c0c00e00032a9500c1d036a070700d0064040c0d0400d100f01030007406420009600c080c81ea0042780501050b903030145244d6901d4200540307540e201041050152801050040341601e031a10007007900b03500802c407031290704c00245055803e50390078490004100b03005000440050b100c080070007550702c0c0d450743c4864aa03080c1c01c004a48980300083c008091502c1d0100004170210810011301c1245421801c094228000c40b408a002c1e55041c1d006603045050a1030406c4058402c0c10128203048000380129410780042071103030f56403c1c003a0001c00c1140360015609040000c00d01c00c0c0f1240f02818182448064001031102c51045014490b140c100030301c0c10005000540301340e1260a1050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 872342158 1250 872340908 872340919
    0x6030309060a021005070819020c070b0d06140d051905010902030a0c06020c12070b070201050910020303071107060206011421160f3503040b09100f0e190302 69
    0x158010080d607030009038020000c0d131031034070002c540070300d1045041610070800c401036024068903030301521001354050492514503004851002c1003e40124004241c54030b07242d040441c1c040e0820100f041044080c002c003070300c00e045801825000450204005002074452004101240d400e401d04902520080314029172501170701242c0d004204d801d0b0210000c0d1401c5508a406035141c00c000e0014000300305644407150783c441601002581c0b60140203040162040c074040b820700a8001c00b007404414004070034400360f08040700f0003c8107603014148804064400f402045038928002d40070751907074010701540b120805274070035141080c2c803800a070051204441e00940719580c140301229444016001d4041c225600610001884140d02c021303010940b24040203951803d1404200135001ca941358442104403603924207003854003001400680010940d411881e03660720450410042d400300846002001d01c000c03000100f0009030f1000c0000d0342d940c0140c2e01c441c0340c0080d80070300e0307445040305600c000c0d88003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 872343408 1250 872342158 872342167
    0x140d0203070306022b0905100b0d051204050f0a0b04180e060412030c09030314030405010908181c1101120e19060c08191a04110c07060302041d0603030906 68
    0x2c00861500d5841040f00317050724400103d84010f12090b980804005483c541c0003104031500007020380c0c001a030307402c002032121380220350076541c460421068209d221a0400c1c0410104040d040a09000c841c624040760350108079410301c05051054004c1d0b010b851044a220100344d40e5a0220746d11100b050100301c001c680c1d039883c0c245891084080b14800c01c1c8002400e00099500843c01401c1260589038181c44c0c1c0100d08071391004820640d00001c2068071690340700c240407000704215038024904800189421903c0c800d2100500c13000c0005a051032841d40720150541010501800c0a0000c0305000d10340004803d00500112010f0180201441e13418001c030050b94000b480c501d0140c4508030302c02c560504c140211404d094901c11811180160305c203121121900c2403880561201d116504001088044c0070f02c2400450111110710340034001c0c3c80320001d505c546814040007014000c04131481c05620b0582131a0080d03041030b42a40420a1241020300840c00c907a60500c19101002070291400340c48 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 872344658 1250 872343408 872343427
    0x30213020703030f0e1513060e0706020c090f060111070905010807030201080a0b0d0206160c03030917060106022508030f03101406030c0c0f06090d18140d020307030602 74
    0x7540400c0c8200d0200f8904502d0030403042042c0114820b8020f10f10107041e81c103400c0865500c0000008003107204540b80c1e91850300026440d4420400c1458042d002040e0b003604201c0c0203440c044640c0d101911540c03401082040c2d0b070b4040310109610440c00e180802c803802450201500d0028203822054140b03007840004100c8210005912080324001da841d410b071a00d8040140085500681d001394100486010400160401c44001c00b203a0f0b0740d00071038046050071600c2e5801c503c0301a400460000f810210100400250040400402ca400b000900321a5140501c0039544400c00348003a10301da0b1403c074038000708050300d01c1224020100310f000e40b0340d0703004801c9220303646920450340600c56910445011a03004e0310300d003001001300300c0500340b9031450326a000403980c00c1d040440c0c043d50034498811051415002809402d0250170550010880789480d058054250400108a1801250031313000c100400b0280381400010060160764040e074803480c600105c1d08010b01c542001c5d1070180006a200b50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 872345908 1250 872344658 872344661
    0xc050c060711010b040e0307020d020109080d02212703030705031b010c0216090f0b040906090b15150a090e0112020a0b0a0c1202010f0c03060e090703022404030213 72
    0x914180e0714000f00091180c0740f04000031100c0302c00003d84031f5030040c0007000040c101404002000350050416841c1582d032860365030b1070021040c40d07042c0140c1205035080c0c60141c02d1281064440243c1401905001d40c0580041c210104000b05040f00250072003841810380b824011166102c0e008000d590355001041c6094044140c0c1c1c0c0c2c14200c2d19071801074080409403020800044490004160260451a018050020b0540c00403c0140c0035a071721000301140d544d61280c0c404c020300c60b1801042c0d030035540c200740c28449401044189190a03500814850303664026851481c0c440e840c0f00d041e00c4400d81541143c4101c120340010003880c102400108054103c020244142413007100c0020503107480c0d194030b00c2039000d121481d5011520041ca4800020a084914070700c2181920000400f808900750000545811095030001301c2d566000600c641040381c0b0b50a40d2102603580145412440c640c04640d03170402c0410706283c0400f02c0c103030100780c0700750001c2190b0017103800901c106d80c2c07446c0002e000340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 872347158 1250 872345908 872345927
    0x110618010c0213021813054605250903080706060302120715030615120b04180c0801110901050703020a020a0e190501140f0d0c0b070c1e06030c050c0607 67
    0xa1003240d015100c8103030075085e4001c0c24131406080019254880c4081c8d161095802d030710b0003171820315140c46094011410084181525038055800c08a114200301c3c0c42c903075400000c4076290914078014482c0c0481560882e0300e20080b00e520400e11603481c010344c1400e10003002240c10003175202101c41c4030481c000c030001440b41c0545e0341000d1807250355000250b098040b1280740c0f15003050141918040c0241c1c90160100342c0f9902030004010414480d000001000c984903110343c6a49200c00035030b0807080c008d00c808020003424000000304014018032070541c01b03900901240714100640010f003081018401d02c880c0408030750241000c00920f07100c03142c140c2c0c034410848030302c664888400c0700034030450360724007501e4101c805400c0e071100d543c01484140041054034000c015004000c1007049000243c2e45903140c1c0041003414852501c405840c54081d1801910354000d0314203014404d80150390300082145042155054200004c0c14200322109030b9845c090a0304035051030203001c1c10041ca175600440d400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 872348408 1250 872347158 872347207
    0x1f140f09040e01060515041a090619030510080102030f130212011a12060423071e030b07050a090905130b160e180c0c0106080316110618010c021302 65
    0x300c00b20b006c464240c41034080c501c0352014840000c0300303110000d80a48010b118251001d44511702e40284070b5500b400c3c05143c0034206c0c00207580c90081201e400d43d511100b00260003900c0081d0b1944c1400c90801e03003500d1019008042000f240407040c0110b5685509590a149512009000d095070020850103400161030809001d0709048059640b0828086500d078801c940c020444e000d10442d02c4032a0302031150440840d1003501c510a80440e51702c3d03220f070b0500c004d03d101c0d042d0340701d41a0940c50000c0c510500070b8244024001d060001b000700706c5d0444c1c00038040c2d41d003220700000c00d555110514100c2c81d1901502a00d040111424402800c40c00745c0e084421001da074a502c0c0c0540e04000c28040d00c4101c0a480c1110018004041840d1040d000002c0c004110b40308008609185c6905000d4196070081d00340101480c0189107800070002031b2000455000c804442e094104071040100307104a080c007140380340c10481c01c01c1a0030219983d18440706e60761101041c0440d04e5001600030b03082d40070500b034420f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 872349658 1250 872348408 872348419
    0xa0c0905060a08180c0d080403200913060f020a05120f061008060301060f060801171f020304020112020f0d05060915010c1e080301051f140f09040e010605 68
    0x304140c1400c00032a800c8078001e50302c0c108155910100954119801080b0701e400e4000c810344182c3c10f80e0751004079141e40b405000520b5599195141402c041e60b0881d6043e40c40f044040004221588c0e03115100f54130a40100399488d04840740d15103103006003846140c0729042440810101003a90788800680303c0040c400500c5015500c402c41c4555100400300d6510740c1c04030001465404091242601c1600036901030008a007403034441d42c50201d0b43d1400e41003400003803981801002071b09100d10f200d0368654a20000381c407020302c2c80310041c518454039154024149400101040459208501000401021000464691214410b0400541d110400590744075051501150341c0386030094415000d4801c00ca04160709031001d8005561038514060150342d8007034810700d55002c404503010a0300540f07120b2400a40c2d2503041c80f042011581c0c07590441c5a1030100b5405441c209900200555100007030850340b00d4803941c1c103551019a920484031100c0d085400c19078207481c3c0090541284094400860740c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 872350908 1250 872349658 872349677
    0x315152304060e0a0908040314060907171e0c030d030e150f0f0403090b07080703030c020f070e0a23060a05010c08090609040f09050a0b06010c050c040e0c090a0c 71
    0x400c07054902e6805000d40344140c020101d48540641d40c84104254401e1040c41c0c105a540e03140d0310110810200e165940707800c11010002581414020040641410a011900d03400400c61150b55608001711845e0454103041060321942001c01c9100c141260041c00c4410000510034004d0180c40018030681140c03084c4803000915041f200c5003e071160450300011803055817100c1808211031030180042d010b102604c031021400500c40001882000d000d02e082541d1103400d031130000d0495015040c20710441d00070240100c2e40071804107502e01100c0c80c05a03141001e866003a00600100380c82500054501d094110410800845010003446800b003258035548580d51100199090b2406800c01007108108000c1d01040c2d28204000d441300c840003030300c000303801050030101e0401c0342c502c410240c41d03d5002c0f40c41241001700c00c9003400d41c010b10078a440314003040240d48403030b960200207408074407882d00c0c1e030003560b281c48007003000c030590240c0204500d07500e0420410040003485d825107610005a034114 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 872352158 1250 872350908 872350979
    0x2010509030c0a02060a050705030406080105150712080702010b1c0c09020a0909052703070b0c090a030303410a02070305030403030f0e0f07050108090109050601031515 74
    0x1080c1c8801d45010340192410503c25800c0080350b6024140c00d4081c0181800303035001185d0204090030142815450b0743c0410f5041801b00f11040407010902034220710304114100005580c01540341305480d01c1d091a01e0107452b600016405003030080b0440390005104c1200f66021010b405100c80c5150190154911554a170501e40c0c041c0d1007440d003510b0105034841c030708108400f1503038000c991004208111508034900c54100c840e100391992819201d0340d0001c5110810300000100341340e04008507950300c0b8030345840000418004c40c0382d84806000d0544d5428442c140c00700c84031101e0300446180101400321200c00040f610744203000c20b69203100c0706e04980080c00240e018800c40340f8564260300c5e0b19065544980d4100c000e8a0001e40c0081c00f1512920003132160390302013003a6118007607030402070a90181404001099503030014441d510381d80c100100d03040441d0300800c100341075981018540a045e001810070501401003039170500c1c414030018100203a1401c48010391044104130780c415040320200c95 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 872353408 1250 872352158 872352163
    0x6090509060403180510030f0506010c02090a23090a030809191709130c1403100e0c120a09293112080609010807260d090602010509 58
    0x31202800c080e4054070118020070b015503411804e6040030080007280303031344800101c0c1c00f5068020758900400d8460b103401d44509428010750b94808001e181104201c003036134001403810755011345070309002c82c1c9c1c400700c20b40d0440e064146c1c40085000703145403c071f8901b89000000d6880301004019000244001d02042044001045020300c40219800c1011020501c2e15580d41320f0501840707041d0b0007203042222a84a88444070b44417040f45450034001512002c601000d00400781050000c0001c00c0d04004200600b00e0030b5504000f0349480ca580b500b0541c0c1d540d0032011852060150610307400f440403041220006954102401c003600c510045002e66504107103c042d58892590320200c0c009c801400103810020b8212a02255000300e4400c01591441c010981b11880c0084400d8075054170b64498014030741e80050046410980a8074128541c0d850a40c0d659250031803401401c2034040592000707843c1a1a11039603003a10507001083d2680d00d010008081c0c5909024851000907501340740009143c200701 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 872354658 1250 872353408 872353411
    0xf090601080d1803121206151211070b0414070b030906150118081e0a03021c0302040b0c0c03101a060c03040f060206090708061b1812010b04060905 65
    0x46400820302e250791144155080d5840c0d038040f0010341c3c03203d440000420680c1d90400b60100c10f82e210351130f0300f280c0b008400e4161102c1c1d40103001e00c0030341400030312502684000c58400042110f0710004002030307000da03001c03a9442044005080304c843c047c01e000c00c3c000d000003881003045903102141c4d01e59960f103991a0f11400103c0e60400300e038100900240400d044005c04d54200700c03051400c041030051088c3c0f440107250081c0c0141140c0e0f4440c0c94000c11200c41c0300b0415401e003000c00c0c0108041c40065500035920800f01c2c00361954003058040e59800680240c040d00e01501e4015091621031050901c981d540b602c1194a0600c00e1040c6a50020366505e288603180c0d0310003050810494040000d402e000f8254450301800400313100030000007640758400351112014001c01d0340a4402c5040640c01c0515141e0660880c0419070096414094402100300d4403003040340c5454100740d1689000c8402100c03642074501e0183e000645c1c1c00290509920643c07040d803224000710340c1000350715181c601444c200c400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 872355908 1250 872354658 872354669
    0x14120a111b040b0310020c010e06130c06111c030b09060904020a120807080406020606010f020d0509040b0f03060415141009180615030320101d07030b0f090601 70
    0x46038008081c41d81495001030706208409401c071481000000126001c07a84184070004160f55201603506000f141440038907000781000060420300e07412502c0f0b1a914405030300c201e409000103404140c00c0c40f0701c280100c20743c03c007240d500c400c2403c0400c00060050600c288001d481580305000107410351070a4110a0300454010b0210001c0d64103000003e00090f403000c80c1660b0b4400306010b40301c0001c01d040f0040c0060550350340a446281000c40c00900200d03c00c501c07090654021003600110036130712406403400402d0444001c980b05075404081400c500c040304419400d4007480c1c0400c400c0c000c5a1490304004842440104824203051240d0148440140c91000f40100b080e00308105801454201070102c5407080c09110f24928181d69903c100c80c100c2548000503100b5040800a2503000b800f200210035010002110301d0f0718441125840c0c012a1400a810561318049045110310940304103000120350000c40d181103032030b8202210344c1e1a08951900d2403003c01c5000030400c002c0400c01904860 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 872357158 1250 872355908 872355943
    0x31f08190b2d0601020a080403120905030604030e1c02100207150c0203060109050601030e0d080106030b010302040e16230705011512030302180904030c050705191214120a11 76
    0x1d00d180c012154580b000380009045101d41c0d001100402c105000500c0190310990705000310f00401000600050035691001c3d120380c0007202000007003034000507880600134040758179500746410b105d10b050301c42402d103502035000318041e0270204035250002100c0c000c4da0b01540e01140c8034407c0d9441168808139803040250035801c10070042100b024960003580d000841410080342e038003240c1269610f40310480c040b110020b4400001001025094880d650400d0310a1030258942414070788032100912014140c00c4401a03c40b40811300c042c82402c0c103980517000701011100c0b01d500c1c44110300454102100c06d07234a40d40f030100040c550400c103980800440d60300d40d0b89500f110656031010780c001e400c00a02101500c1d6502080c11250740e0314082d0034411482900d6020820626081c40c0d407500c882c0350011400b8110400c5501080004ea04800088440c00c001d00d00200341c2034503015001c09c040c0b00c400e1045100e04001400301c0d0202d4000b078071450140e075654428611003c08010b41c0e0300d110818081e00d24 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 872358408 1250 872357158 872357221
    0x306080c060711030106170304030c0e011202060304060908031003150501140105160c0608011701050f01140111070b07141f0906090c03060509070602030906031f08190b 74
    0x582c218411508043c009000143d4150f41e0941d207515054a00021170b21900005418130407c48e10f20380c1c04d0044c1150401c40011076041c869035004071a61080081d2191078007100107010000d540e0040440c1c0c55011181a849007444005004d464119000c226252140002c6200f0ba0704420701c64039040b514440c001801555000c001541c140c0d0100603541e40e002e0702080420040785607032900000a10060755030700c800f98907000302004074240b044c1d00c030f07007559050000b80400c5080d400607207415505840c0801c94000d01c03120050b500c1340001c050105640c0176054000807032045400240115500030080c01c40c1d030704a968501a00d904c52a9238041c0401280f16423103102d491700c0d52110302e000e40300f01c00004501c0e66544414407046425442140c0c820386910401040072414040c980090285000450400c6410400900903020003413642100200c408031100507521800c183c00000d080c1181030307814196031219912000383e840030701950700085200100e01710300501d0092400ca40040b146c0c0305401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 872359658 1250 872358408 872358413
    0xa24111201140111011b030605010201020711091e0c030115081311120f0c1504060909050c2526030a0507050405150909060402070807110411190306080c0607 69
    0x800455649904103c1103130100030026401340320300040c101304000b800040c0c01040c803004040d1030303860f000641164014000c40002803084801c628030314034211002c09030355070350354208020421101108038102c0074102c140000000b10100442c1031b40c0082044810703144400364103850444040c0c417501a0041c170344401602007000c13110740b01e441e10300081c0182c880d91501d109007840c0c002030f5001c2417256000302d0035202040c5031400d0803c940d1001d0b600d01c54201858058058a002c15a1052410003519070740001e560100d148100c1c2d220900300d00e1801d02c1e0b802203290f00c685243d00d849044444280c203001c40300a43d06440c0d581e1212018a200c40c0e803550307990508030009130102502501c14007006100c046400d9881e400c00c800654161895140c880740e0b10020805030300d0020b01024002c52041001c10b021920440c01c64030b00c3c94014103183d22407000c0c54086401401c02040c085025100401c401c07024403a5050614001840f40c1c2c1c090181a4407407a00d07903100e034001861141d2041e0304000c0d4000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 872360908 1250 872359658 872359679
    0x150d02030901090812070e100f0302030603070e01030b0a0e1f090309090507020f1005090303070f110318040b0306160e0a330f1b050a24111201 63
    0x20711a4038540041191034241e41d8150480d0444141c0345805001203040180c01c07580801003500040048030041c04052182c40b01402240420320759104050f000000140ca07520108045002810642490b844a60b0b481c02c104403a008181c1d400340e0792508195591022240003d000001a5200c010701c0f180003011a5051004100c4039601700c05010b12100b00141d90a264803449201d810907401a102034100514890700300804404000761040c54003047c814500713400800d1343e0348a0240d0400c044583c0e10600706651008082c42c01138610722001410000b1129117068660040605031307414800d1035403276010035485180841d07404454110703407620b4694042c4610310b03065410002034806c188880d02c0e01107410380654034940d05010710a0b0f80c02010000c00c030f02d078003840207118035203006e4000f00342c00c075070040c41d1a1200411841440b421100441400780a004285100e640035282c1049110b040da0f0f21070070316888461880ac61883c2a5805c0204100042251074121544070074480582c03d0000105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 872362158 1250 872360908 872360911
    0x180f240e0613060914010203390903030d0c0914010804120305060609060f03040b010f120b0703060e090c19050d0b100503060a0f05181b06160c05030c150d0203 70
    0x7982644ca030041071021030141401e80f8100c3e0361450016035245421080c803550030111000840c0c0102c0303400b82e039a17085407440c1c590950302c80555201035520079000d0b00080c6940100c21041009526141c4101311040d08007680400f01c03120080d00c101c50700307861401941c0f2618121400380c012070301d50200b10441442944407940c0400c00a2200381810104170114034160010480d40d0300803800042408140400084100e00600c005d010000740d0301c1c01d02c041c0501c14081d0a00041160b151000890300030b41c001e81280003c0c140425160341140381100203d55213101040c0c07820300030316481b40b80c0c024100c000c0411609492000c0c100d40d801ea00301d0ba4919a83c49001805a442d1300c542210205031a507041c80355a0085a801d034000c02c03a1101505c0c180219076024125501c207290040c803420000d400032410f81d80d01d2004c828800c01c030544041c080342c076900c198000d101580415025000030400081c5c44181075610a07812075a503440808103000c0041c5c4400f18403207d17020113000000c13609034541c0045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 872363408 1250 872362158 872362163
    0x100e0102060f0f13080f0a0306050a08190803060d120e090f070e0f03010f0c0c060605011b02120a0203100606080c03010b1606060f0b0306040b0411030604180f240e0613 74
    0x40c504a41a901d5000b140c07c6080c400f40043d888130030410851411049600140c00518040d02042c1c20b002d15161100ea071407000140700302008000500a80e07140070f00c000c2000e400105085002d480d9940c000d0002c0c4400d00010711401e00b040228042e56042d04c146445480c2c1d0340c0341d41540e100034008003c90441ca031134003582d04d50340391501d48020403581d01550060740c546455002c220100c1d4580070741902c000d504900d04024442c41040c0c046015860b0801c1001d40540d181000e01000040381420f0860013400690148a00501469002440c0e03100c88216030907542e50386207645441450544c140300038880d0748000300040c0b000c20544800d00d159101150310401000604030703520316190646403240d0f0320042a01c4030210410849041901518514500c200da04200e0364a2000b003801c603e0102034000d40c000c555606c0316101203484941000b0a507500314aa1031540700007031800c0002c91036046081c2d01c0070040400d2010b8005485e025440316007200e0006007802e80c1d01d40c03509004608004d5001d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 872364658 1250 872363408 872363423
    0x1005040c14040e0706081e0408030705031306060828050a0228080718201614010c0f0504030c031709120f0c0105040b120411100e0102060f0f13 63
    0x2400002c3c1010044034006016589818480d0324002d1991030110400a5400319825038041c1044000707400d900880394061020f05086840b6181c0041c4a41c603e40c0c034010080c90706140100c081050000000c00ea0504200455092001e0717200c056841e00e42d50340c80c1c8000340540d020081c081c00515001100313844402036041086035659080062102e8402158040081a0810242840321b80c00c646040c02210540810900c41046810381c0e402880c0b00c0580e0b104140d510100d20505a0519010b010700f80d940c101411601d2000c0440c40b050003802d40b64645004a2403182040d6421401102501c08980e00300e076409480034959114016044080c80d11900031400800416602d50f961002500e100490360300204501c802803240b451500c1d003264040d505003c401d00c41004050344110880e024860700e03601940150725a80703060914100750b400c0f0075501500010710085090b078422000f41c0a0f41c000d90807507005440f00500303507200d1107082d1650a2000b0800c030001c5c0160701d100080000c081e200c0c0c042c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 872365908 1250 872364658 872364671
    0x50618060c151006021c0206150a0909080d05010503070602030a030f060f030f0507050a05061c0908120f0105060310090c1101060803040501021b09160918020c1005040c1404 76
    0x2680d016202e8212210034890744404424040c1aa04006141107440055540e0b28440e560f15400307961050000c05045400201842c03e80043e100c505210004040c61441446490014036007003c0c0c51b0059104408254540380c00082c1d83c0c900054a001150210740141d442c00c0b1240900700c002d0400042907a0186895203400204442503000040003140114159242400c66280030b034144202075000301e218402608040c0076a540d0310080320816210456502c500007624100400540503518024118001c00b00700a2070303c0c00c0d14040580300384542030f8103031101d03030f20341c3c0410815000640d2524000b518900c01448906445e90045055030017500f008518140f1110409003914880c1d040002c950b00301090801155804016400326103d245400e4400403a000010800c0b10f00300801c3c04220001882c1f1405203a806042d1400c00351030002c141c50482d05034034410102952000449460600c5100c0680d44407032050302c1140c2c0110307841103283c2e860b01d107041c2407500c40c0c4c12800e0055601a60313591 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 872367158 1250 872365908 872365933
    0xa03021207051c03020d021c0c060b09040302010c09150909091119050a05010207032604170304061b0f030e060904020304050d02070506310302030a1b050618060c 71
    0xc03c1c840028020b20101148142132500030b08204c0480c007200103541c001c1000c2901c6401500d8816298071a900d000e89420b0340c141460b0015100da0388000b03030040c060038184414990b040d0042020704074030f0303143ca803803442d5610370326503c4450000080300050b000c0e1710140700d400c100b5080f4900c00c501030300c881210102000c00181300c0e600d003800e00a4100c1c04a80007003100e802c0004051009000074009860240d107035071120020110801280c60250169585500311501c8100940d0050988058030040c0700d10208a070559a501c10f00400020031081080c507414040c038404010107042d0b00c10340440d0207400b507036001e44480d10303a8120213034000303014404400b968490f0701c040c1d44100c0c041c900606010070500000b90800c1c520f030308414050b0b00c0c05c1010042c84400da21407845041c0289480c8152030030f9403884500c000b10590002981400b0340e540d15010300840c03406680c24140303014621440d9555410410400e88100103c0010191300b130803c4050700c1c80c000020b40180d8405c00140d600d00c3ca40d08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 872368408 1250 872367158 872367169
    0xf03070c1403180a1203082e08060703180224090411040f060305160f050409050a0f0606050903102f0c010e0105100e190f0902150304020a0302120705 66
    0x10303c98070105100301c4003201820702e08498010000c16500c03d80d0380f010009920000c1015a0041031001d039a084480340d42c00c0100c64051500d40542c4250140e4692501d580469842c0c3c40195003910010703007000340007010003074081c1c825001107a00400d1b504000b20f0407010071801400c40030084410740344c140702c0c03070801d5202da000700405850800400f075551030401005001000c2c1e5500b103481090b03e48000c10103a007101c214803d5a01c1442d08004441402c409001c884910440d0000158542000c091012350030480e04100c0d038115582e4010b203ea540c60700f400300c9190254401003540b5522840d2035076200c140c2d642c8140441604004410a80f50010220700210010903803140c441007400200401740b41020b102e910103800a4000038803480c00c00404040c07401d001e502400980071486404110307031240031900c010700c0034601c040a20900d2092010000100340460050780103283c85107900740010003c004891080c0e43c02009804410b045400b402045e05007942c290a15101c2e1130070101d15640c1e003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 872369658 1250 872368408 872368417
    0x1e0115021e03040e0906040b06060f07060c0f0314090d0e030a02150a02240c0c150403021f060806010b03061306090506040f05060a030b0c070b0c090405010b0f03070c1403 75
    0x340000316038a904d042044101080014050b1205400420034040060b40c40d0754800c6d04541d0403a21151106608032a20f00c3e0f602c2201c000500740740c6014200b0f100341e0740182920b0302041c140d031410001c40005d045040405801211307524500c1e004101c05480d4940588185c6559800103001c8403401540c641c086080062a80351003001e1380e00c049900208143d042001a00c400c4601c09882e0281700c403510840d280c1039015024055030200400c251b071030740c00204504640214411646221410a410065200d012185569010007100d005406034a0030500030041120700b032030006c0101d60710340074032810140c1000c1d022950015246207940220602c0327000e02d402902100c0c2001940e41000410001124080c150405900342404204100b5940d801120011a60004070001d580c1e03031220b000121a1141c400c000b48002046002d201c0a85d0101000c3c0000701002d540804c80c998840c822074401d4041c40c036120988090800018560701d00c03030110340000c07600c14030030941c000d1030950708103045410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 872370908 1250 872369658 872369713
    0x114030d2f01150605070c150c080d0c020105070216030f050c0303120603010605120604150f0908030108060907120f05071502010b03010b010f0c0303020f0d051e1e011502 75
    0x4407a5a140081d504003000c4000500150814170f2405026544504109600d8403821104100d81e0f01ca88e00024011030507544415800704840d666883d001d403010300200444200e40006610300000601d50600000700408604044001c40c0704a62540c0c1d034180d221903200c80200d07200d010340c2d403164110f500c0803c003800202e0601c0128030241d01d0140300341400c4a60300ea010764403c802c410091031049c2c0d23001c20b000b500250040b08907940a82102005001390003c406600c1c12986442903000501110802039410795041c1d00c19241c0320f0b00d0315080c29a40c1d0810340151112400e1f03050740180000ca100d031005044a1140c816101060303599110f541041d0a0644e4000150351145004000c0745002c1c45010442002401e12129440801400030002c1d119514001c06140d80022402400000700003501c5400713544903024001441c00b00c1d20140b642600f0b420850055a495006c600860104400d14900820030030001040380c5c03804031a080000181d0007060305501450030601080030380e10180c44e28425 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 872372158 1250 872370908 872370911
    0xb09041805060912192304150201050a02090609220203010e0403021e0316060b10020c0109090c0507062316141e0708120109090b0114030d2f01 63
    0x5082c0d1000c9044c40014512014414010070019500b02d055015041404d00300e45000d0a007400c1e407140b915040c040b0140346514003800030500007001c0a000015201821150740244001d4464001510070380c0600e400c0117600c05004c0c0407203001400d142e200400c494460504001c14a13034414440d20881c0c0c400c0c1c01c0304480d00c540d10108003d060b010010000a112082e4509101e640000303030603601ca019400106080d4002d0030782c40b038203110b0b032038110f080303104401030602d8074003107146401035074800c4034005840c0406e800d02c00c006402c14861044059103551500e0b44ca140081a940b480014100741482c01013900501d040420403c0007a40401d01c0f6a0550315070585030801008080c1140a2605580c1040902001200e5110888103030b41da140d054510038158807501e80303291580c0d19015000b40e412a04004400000c3c031113a05410804000340140e1040c2402c1e41ca80fa0b00601c1c0319444a0301d0790305544801c40c07408089204080d1a207031400d1320210800e120f00c5a555440d900f042c0444001a103a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 872373408 1250 872372158 872372161
    0xa170307110d090306052a0901081803090d020a031a01030314090a0e0408190201020d1802031b19030807050708060f010626010b0d05011e0b0904180506 67
    0x140c0040c0440018481c0d5001031444124501c00180700001d0303400020030407134075507022550040322420624442c1c0340c0001076104000c0c103041d826030590028071031240041c83d03101c08079447d0420441e07445400105100a185404008000e115586901d084100e800c005d0444000000c40c9201c2c0e5880e8507070b440c1600c40d003030551550400411682040000c0041c0c07101c01c1001c170300681d50b1008002c044035112089800c02c1c0d40c6a0400260310700600f051942c3d80300d03001d00304000407a030641c01005140048101001480070b00c0045101000d1407000003901640108040c100c1801e03290a03c0c0044d800c014140c01944640d1204110106a6548103c40217500417440c00c04011050141c3e00c06050508000c101d603103000311080540c014103105100078071020502024460034501095980340380c00015440465039134000a504981c42000e0000700c00d0b203442d00225644901c2840002000300c140e110412050070a2400f9449501103c01f5039805560341e101034107001a203807040f2081900810240445 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 872374658 1250 872373408 872373421
    0x301030f03050a2129061b0c0306070207080f150a0213170c0f10020d0c032a2a171c0917010216060b011b0b010f08030301080d0509030a1703 62
    0x21080060b140c0b40303807801317401d07821003240c560605596805000307000ba04040900001d2407170900000c3c00e41d954040c000d6108001d50187c00148420407144054112014002002655a128001c000c900141e900050003c61101c075040e802525924200c90038091840c0d540d03018010030540e01c040b400386580c214440d1306c4010b284c0346482d105488410b0b201c0c044c805000d6038000391100d101048200c18080c1c843c503a00141841341a203080c680c20004d40050b100303041081d10303220b91092b10404540c825001000d0f94181490150080300054144803922451810700700380010008101000c0401031003501481c8151407007400b04044001d55944411300300030300704286d2200c0000010b00c0c0b010142e0041200e4450000420010300b030b41c0c6d40008001540c0012280103e50340031071382e0014854132064040282c140480420114103c5d504501d48500c00790365989001d499001c04d02c58014950452030055440c1409074008080c0c041c0700070181c03000c0040710340da16091525900c2c0d05041810020080140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 872375908 1250 872374658 872374691
    0x809040c03200408030403060513060f0b100e09060f180a0203090c03150a1503020301020d0b0f010201060605030105040f0b03030f0a141c0905010221040204110301030f03050a21 78
    0x41d4001030b88289191600b8004050394a00c6140b00040030700795100d00080301000b2407924440b4807603001c1000d222503d0800b1500b0301800c0285a01ca102e01f510410f8a4051400341d0500c11030400042e05143c03442d030318042004915041d0b042d00b1a000000742d40782403103030f0140040c024880d80c40148010f80b0390406480c1c80e480e01107224a402e020b80e00c02040760310403601e030500c01e552000804d000801c107071440348905c441c1500b080d80025007640c00401d500010031803903002640209010380c0c0080403100360500490036611240320b100b01240c0200010301042c1060780103072010203030000b80403c4444003900441d103107500088461250b111f01091070180a50b01490b02030010280880305c1e4140a80e012000206100402102044a555511980c10010203405542008803555503824684901c864a045142811937040b407050b071074414814281000030341500d0503690000d220580181c1c0c241d50540d9568040d407411428440d101106198090202859101c04c41a59401188192444541a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 872377158 1250 872375908 872375951
    0x12020d051b0408060a0b01050f190806031605040203040503040314060108010501060f0801120c05090106090504110a020a0b22080d1503051f140c07020a090b0a0504090809040c03 78
    0x20807100c08000c100500c00f80000e01d20303004030803c0380c00912040d00b0340040e1424812102d0502c1240000718031340b068801e503807040c95006a00c9407a8010685e03980f1007096200e04058440c2500060070210030301c41ea04041e0301a651291050b811646421f40f03984840282d06004030108080ba4003960060240103028058075004040c0b41c2880100900c1401010700303032880500400e40b1410007401101d0a205000c140303440101800b504034141c1d1f50315007200901600c5a4040c05015a0034004d1001920007548108c5a0b40c5249a01a001c8448075030f807800c075070150207041e82000b207141a071000c01405051103102e01d0b051054100e2541d8803069039045058901158984244503030a040801c00b0400c082104070350a5506640568644001303801003000f080ca0000c12010f40c101502002000112103004240e014000ca480c43c0b040c645c1e6450b034038283c94036003203401c3d004003007a101040340b4101a00140d40380d510412a071130402409101003011540028080000244c0f00d070458621103c9c0e100b50311 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 872378408 1250 872377158 872377201
    0x110705010231120213330e040809092a030f06030c280e04050106050118060518010302070f05010501030308010611071e0b07202e12020d05 61
    0x5507440380c90122201a50801100e002e4015094980340640703c03686580710641e19403c0c4924045800d458000c2d070300780b020541c408080070400c2c4200109416220311501f0340305543c03081046103000d90600520079901c00107000c1b10400e1046000382082400b01d01c12006501d084101007940782d02d0305190b20901d841d8064000c0303009412501001e091601c070401150050000c40c000461074800c4110f850300d034880070740d22151012510409100800406420107021a40c1c2640c9042d2110000d40d071240522001d44100d9000c03036010010140302035041c00d030a4480c1c0030141001030404d11140caa058400070086405c8685965030001841099000030301603003d08060301d40b69084502084100b9500c484500070f0960040400512110111807035034054040e04400002586910440c0350003610046603404004030280301408403070359401d114001500d094440300020f541043c202d0303507002e240008a9100c800300300c6460006442211540011b0400410348500083c0c1c515000320710005001282104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 872379658 1250 872378408 872378497
    0x7051314401b081f0b0306130b011d0301060504020a2f120c0a020a031214031005131d1b060901200312010f290d1107050102 55
    0x44480d01da50342c0030581d401d1021400d00303041a8a600f042600b42031003034040598081120280030442411075030103180200416918401c0400c0540170283c2a82c503042d40c840c5c00140f00e007507503041d007034000c8030300c41400080980009503013912540450181e0b4045011600400c001140b00800076010100c03030540d03080e8140c41c44140440c0702a000307480b12003c08405041d0750000c00da410410038103004003035036580e0040c411070b41a503503840c1c080301552301850780401150707040d546094500700c5002240c0c460b0220340000a21a8101800c000d50414040440c800c40c503074480101c4001800c60301c102080aaa1800411002038031004290087c0c08107a00c40d402510144031300540c90340c206a050a06005018500601640c01414103207540680b81980350900a0300c400000c014014030400030070ba6058405024280b402468086065131b200074a003498148100607641e940300710355020200304552945404d140c18aa919010709a8100c0e001c96018620504040003800c083c0d641c050042492040b40d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 872380908 1250 872379658 872379671
    0x106080403110604021c0c150f170f0a0c050d0507030618021303080a02030f070305250b0412110a050102090423060409020d08030a05010303080705131440 68
    0x4640c04000c413049030f0001c03c0d03100d10314804108030b00510001808071b00b00708442c100f9154000900070405000108040307410000c41d074460412b84c01d4910b1040801403a00b1580c1e881d40b6800b070000700440c041310f03001c00105004020006005004040c0942466680469102d0601e0400c96205250007441240e0754030400944030900e41c1d4104c1602200c1e042084961a03600110303050341140f00303802100510300f80008895041641110241042d0700c46100145003045845001d0102140e501501801c0faa0070301c400640040c1460800f01e01c8100349180494100c100c0588151074003405446c00c0f155039401207101026810030b41705804403542504000c42c40d80d241505a600941e02c043d006074001d072f48641c4030106644403464400ca115a00c00182ca540b45803540540001300781c00e0000314005000e00f000700d841144a40305841c0d0b514800031a448506140c604100c4483c074440030001c0d002901c800340f648001070f8030b80c036180180190500d0070740c2714030303800359400c0e4219400f9101607202c030714040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 872382158 1250 872380908 872380913
    0x806090705042411070f030b01050607020607060c18062001020a1b0f1401090b0906060303040603050402120f0f07091404031b0506310308040201050d11030106080403110604 76
    0x10700300c1e28501c0d65124818048031400704031080001c00b521342e01c042c0300c2c1c81d40018090700310144050480b80242407103245039032110b0401405104280c40658040d00c14050040032030f0703040c1e0124110000a050441910304401c0202c5540c03001540702801040403403411a4481e0031000d10034450000c0c50008500d481c0411030017402244400300c0c101c0c10100302c40e0040081200c0c1e0304105c1d28030341c0c000b201c5914000c84500e015010f8103040b24225029200c100c00310b0010803002031168082c0400030069401c05003007903003c178000d01c4002c3c4166407040028040f13600b00e04040c4002d0203851011000390400706818a8410b2070f020743da81c0201d80c0f261400070700083e0701e00c09101d829007203071f414a00500e06040711000603118260000d00030305940120b0007440241e00c40642001856084103a114610013211860360001ca408540060301240d01c240c00100150311840051211805441c2d001070080b040300c00740c495a42090f08040d000c50f42c21001d01050507004040040e03c0140e42d0010f14491425a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 872383408 1250 872382158 872382179
    0x1090f0608070f230c150c03060d05030426190b1b19030c0f030902030304051215010608060a1e0b0306040e151e04080a210507080609070504 62
    0x303107103100b000181d0440c0b10390503118204060024401d00352961a04400091114080e405001039416910411002c9081b45002c0c2c02180d2141188504080c150f94540081c000000c103081c01c00c0ba46800204030203d12140c8103040d00c0200c0d207505240b0b168001c50072540031714105000c02018030004d00210342d000011144442035501c008100d0034149103607040d415183c414000c4d500004003000000011300c60075981544001186800c6544210481d00015403d03000c03a032541c900a50150800c000a0066080034004400041320a2080f00d1441c1e440b07040c200c0c003407482030704040009243c840502c5000c8c60409100c001401c02c2c0d103d04600c01d042c0130704950110f80399100310a0103840102c0081c02a40c0d880e03020f8050070303080e0f8065400441131500040b2030b803c0100c4603400009142450400c001180d014494484c0745d124403028900b1041c04030980d650001c108120020403440d1200003c0d600d4117000c0c0300d000d070500d0b445801440c01d2484c00c101155200030194000c00206204c00c100c2c1c1c4003078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 872384658 1250 872383408 872383411
    0x50a0201030209041b0c03021c09090b060f03130b160c17090315101202100315050a030f032a0b040c1d0106110c01200c120c01090f0608 60
    0x2400d006907a43c03000c0002c10013501c1d03260481300019001e01000d03032442e07400000303002c45288680d007a180c2401648001f603800040208000002400144040c01402e20f540d0128000f074070300409050a000b001109015154000c944910080701d0796041d40e0100034000f1002608a000300c0580c00a42d1081d01004004004403c800303054000380f444171110000c0c8180132158100c13000740c1502e000300c400c005801106c2d50142c0b491251921081b40c0001e40c06550041a140641d00038001281c85100b00e2048020309401c078021034140880da40f000900c1d65410b2180d40003103100d01041a444226402c0140095003030312040c020303500d00310581d04411380c08001d03080e804540c04148820342c0d0301c0d00d08210025518640003001c022403400c0412106074500e0080c03030b04880180d0b17900040e468840136070356140c400c1c4c041c5440c0841c490715000182a12803243c801d0782115010102e940c04c26280c000280c40150741104110b4030b4024a8503000c6659009000801a00d55180400c9106250200c0208000c80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 872385908 1250 872384658 872384663
    0x12050c040c141308010510141005070320011b1d0616030e10200706080f041a0a02031f050a0302010c02061b0c1806130c0e0a14030f0a050a 61
    0x2d03d000200841555200a009590000c1240d4500010000740440c020300a89842d0321100e0a034003810715100079a81c81c070240a0b40c5042c101007142c1d030240c50700303408100d040005104881c498025584244600010f400c4a100d282046500044014040280c4031800880f80b401061141241c1c1e158141140c03400031100c1010444204142002c88441c4081d0681540c0203023011800360345694031030140d511190950740d40105810140c202d5507961103c070310518001c912480000344251000c1c00100754481c0c058010040030302e0491090083c030b5507080b1440c100c429408002c1c418600c0d10905406030512880002c150094100301c005082c00103144030007410450044180001c546660081c1c0708036062a40c6072501c40450505110f03202d202e90035400d0f018101007540909044902d81005000d0000940bd2000f40c15103003c2000c0a040501105410b0280c05622203549484881c0e08030b0040211452058003e05000e040500b40a040b21410a0940c004003080300440c0c800714440a4070396 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 872387158 1250 872385908 872385947
    0x90307060e0301090206040801090b06060a0206062403040605010e01080f07050904170403050c0f01050723070b3403020d08100b07080a11070f031b0e0112050c040c 72
    0xa241c0400a8050a180d040c006c2d00f00d03501040c0002c0500f8150050b04106201720200c40035547c44405000e018012051810010fa0094022a1003401c03c0240c080200c08925841c0c45074000c0100c2505950b48251403c072015651000100000010b940100d809043c5400103032000e080816411580c031151401050b205201038000b04041013040804140e0b0701001b82c0e28640c945a0b281031590303d501d03060b0301490144c1066110044a0340c031402c1150340f42030744964040e07000400340003c1125407094a140301858480c008010a800c038001014001a2035130f4440c80bc49030248a100d00c00e50003041060b51a00800c0a41880010f0b40104145a0490940c80d0840c40d80c0c1c0c0e410501c0703500034000e601c1103101072000200f0b1070901c9840c00081424014540f51450b4212003117080031f9440e2642d1140112156004200388000f40e034098403601c901c41101c00001e40a42c0b51a80d4441440003a401128210128803004040050600c1320762410350003103408000305581d0040c0a00b90b001003141010940 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 872388408 1250 872387158 872387177
    0x31603081302030d0f02060a0b0d0807020f03030d0915020705120a0302160812150f060703050c120903060a200c0f0a0623010317070309080f0304180209030706 70
    0xa180c11100a103846400404580e80101e00c4400617012904c4480224014022a00020202c1c0c5041c056880030341005840841c00c586c01c0d40340d81100f5007103030004030381c000c0e102c0c0300d40300003030b80c041016040b400b20044002034002c1c0309182010b4504540001130040c0c43c0140081c0c400304d4004144e1580005442d10503603516088400128020b104001603101c80720511145241032001c0440034200010703048644c815103859402ca210004071100360507a83c07021004014100c2420224040c088292280c10024100703d0112040c46c01c00c2e00f800034403021010702140c40851031904000c8107400205200c0700304005100103041d012042200440c0c0c03d411540013890741050075040000e011003840d94016a802a901c1c1d1829101070000d101901c203134400d2462a1010400c08000418101d030361242603895010383d444060080c5402c0908103a0a01080420003d04204240b0107450356003001c0028503600c2e811b04c0c3c03603050704910740180540900c2c4107109400e810f8070b0006105090300c01d00d0401da03294 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 872389658 1250 872388408 872388421
    0x402130b0d0f26070b0c0d06050a1202041506080f0622050a060617010512071d04060c0804021c050c03031305040c05070b040602030c041511010e03160308 68
    0x4803512114010a14250403190009020000c0d0300c081843c18000300c3d00740440a030398140003e030700400d24003402d404601d00104980308071b01401011302c620742c1070340400c03c2941d410014080c05030540c0080d1114200c2e20070341c8114a051b00c900c4025030300100f52000041c0c00c05100600400e0020305040b04002d000380030400c03603914106c082e030143d03400401101d4201d4806100c0b002410003900c0401295007084408103542d4041c1050016401c5407903001c0605138641820084c03140c0581804240703d018104d4042494030b10008443c9050307400841d00105801d00307190140403145060072502c20001c050091100517a40c0080786051f6080c0c5515050b0107419900700a4100049204090751520001544001082c0c010003400300700c80003220100900d146005050301c8500c00c3c6900201204228000200050080d07805550800700c400030050401743c850f0010303241201450b02c5200490340040c4c80c0078201d20300740110010b000c2c1d00c1c1c001d035007030880e4801002a070600301d201c028144018500003d40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 872390908 1250 872389658 872389669
    0x2070c060f0e04051e090102030705301e01050402090d03030b03070906060c0506181c020a0c0303080f16211506080f160e120c120619050402130b 64
    0x40c2c040c80284200194188544030b040350100520594904101140c00520500300c18802c0d203105405540b00d69140c0138034540300c400841c2c405240710942410800003108914108201d0602c5000c011402030a201540c41c80030584900c140e202c0d500c00c500411070103031680c41c2e12102c2106154541000f140721071072400002d00f4080e40d0340100c1c035a5854078000060943c0e0218042c0c000f1030244c401e4618075103a681d203014800260322944d40e01c030340c0425281e40c081000340c00d80341840c030280d2043d42e4a0050643d6003c681340d0191f0700c1030b0005040202400949001c00c224240c0003100e42c42c0c00c4868109985029141c0d581310a0310820102140048003401700c002e4200c00e25440d031400290841e0360f141c940152507920f0548001d400380560310006511060041100f041b00c46060311458203001340b2004009221803280300c03103030740f50140e0342644102c2c0d19003443c0d008011010302c019004919100c900d190101800301186080103040005005c05a12100c0c050115135081030710100d00b607000000481c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 872392158 1250 872390908 872390927
    0x150308091c0c090b06090904120c05030406020105180d020c060d090614150307081f06050907020f0f0d0e0f04090215070209160f031a0303040f030501050a02070c060f 73
    0x40c0c80701d40c00200d80040007030402c5804142c84101c1010040c69030460144412800303106c4a8641103015000460049582810b43d104410118900002610b0741503a800d811a0403a602000250b0744a905114805d0181c44085211010143c0140740e80d00c18814000e40d640603000320386001703200009400011035850340100c403110b508140306110b0301c400d0a5103020010b200b00d400500f40481c103503820a491901180110031582000001c2c03046031a4203d91411030900b07002115800c0d551448005525103c402070350384564056000b511030b205641c1c5100e818a422081068074a8220f1444802001d801c40f2410750000c0095485154101d204e1001c20018101e451010750300030013040f210a411828040146803251003030300d105507162906c1c84990110f007000e445060101e8021050358012510a80c448001c0c051112807440f803900205020030f0540c1d1142c2c10403240f89032a074100b8428018240646600580e09040851808a6a8441c2000d094190090404004020441228452141c0c0105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 872393408 1250 872392158 872392189
    0x1d010b0f090d210e0a080706080109050a0b040903080417030606041701022a010b180604091b09061a03010f1206060302041409011a0319020d06050f100915030809 71
    0x10303010411003010213448002c15282480c41140b10340030100384000c0c0412484125481c82d280d0403007507403d002c071100c00381c10001e103000c0d400d0369102c21f107508550742d07401050174080c000c0d210391b103c60030b01b030034000110402c400d0754071481c2808100f4403415842c3e24085a04460114446148107402e0142c02e138003900c9048a400d14944502103c03030440c5a844d108e4403403425160008115221820342800550240f69141c0c490071541500000c005007041d03040b25041d40e00c16070700c80b0f000702d1013401c3c60903510802d50401c401003580d4001c180000c0d044900454001108170011908540c505034100340300c44500d0050041d07e4012a01c0078040000903048400030310350003002800080c401e01c0800310080d100f1034401089600b0500035002809a10380c080102045c050060500080c0145c0803035120780c0141000c0f078200b440720880c0c40128149115540c0aa010024030701800d0402c10034074250401140c0004810a20303001c096421000383e0142c48040340c0e40040d68585620090001980140005801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 872394658 1250 872393408 872393453
    0x60308091801150c0611130513062102061c0e0c010306030209060111120703020d09061b0b0603150a06081c0507060c05070f0c081e070308030406090c1d010b0f090d 72
    0x7522456010903c9070350a035082520324000110703004000c10169112b40c03041c4000004000304006503504600d0400d540103001410b40e500d41100900700268200420b000c40312100d558103030101c5c0303214050120003a0701a0034030341800810b0035a00080c1c03402202a00079414004c100340100d00d10402844800a14640e241d81e031501c1d101039040c060b448034039208110000540400e030200358213005514000309604d184003c004403200d13564408102e19009801244c0c503120b544d0705801d410410016803031181803502004680a0b20f01813120385440c5001c1c26110040040c0d84010550903480750a80b5072481c2c0041000c26000c0c40c0800983c4c2c64130601078007900082c03100880b10103010f50740640c5000c8401820846084050500320072070340b41068102c2c071669800007081080407441440145400074015007001070a40c00f0755440545c4150b6030f5005401160380040140d42d043c0c13150b80958014070300c0f044a00d103041c0b03081d426420280f141043d450320034614101c00d00140501e84000c00b8030314a40602 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 872395908 1250 872394658 872394667
    0x616030e15070201060b040b030a0b010210090809090901020906190c021206101a181302070b090c0613030219090606030e0714101d0301060308091801150c0611 70
    0x1c206100c1802c44500c805507090900010b601c10319081220200c40c0c00c0c0368018115203404030340d10064151500d24604522409a00341d200c80c0d41071240e4203019101c0c840e07e80d900d200f80d0f014041240002000807149910501204220351526001c6407010b0002251040100d00124410b0305c0100303400c0b1000c1e40211080000002c001400611580203c4030702c03031400e03e400d948841380c02801003681a00303a030a03001485419103200300040c08400e40d0000034441c98100b58906d241c10100d0f005000252000c0d00d021051004807082400320801c040002c2c0d5986103001ca100742020110343c45840000e00460b408482c003001101c0d07035050840903107274141d0140015642c0310700003800340c50411601440e90003018000a5000c034030f03000d591004100500000d20b416411141a11074441c82c450840d1107400202881c5c40d030b950280f082c840610300c00c1440d41c0c5c40b54124003c0c040701c420115203012480c4684e40050281104035084017490302054a000301c42441300d4a0540042c020009010301415004034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 872397158 1250 872395908 872395933
    0x807140d0302121605160c0b070f1707030c02061b0d02030d0b0108010305060c0c070902070305120f0402031234032715050912150a0902030616030e 65
    0xb0010031808403089903440d6661106188200e0f00741c180e0034040702240080015011160403890005403090007040300d8001c41740d41707507550714141e8003650084a00c02c1e5526400c100304911400ba0b0341d038100c40c004c6064105032041c0e50142c031111030307034202a00c904008600e4072003031010400604800101d4006482c1d40300030b007600c00b955039001082400d030740f01d042c6a02144194820b00304c03a03040b01d80207402040503896162000820368011190140309000f007520116410301c103030004011082c407940da15944c40751070070180c0c032440344040d1103080700702c110600707002c0581e0340026102050420000050396500001c0c8550003682800c9050340055801652407a081c5001152260f80941c0a61544000e448880c468400181c4040c03110403840c002902051000c6408190060f8034508641025482c000c4454000b5031440181010508654001c040250a10340c50b104600e412021601c800d00810313800d54002526894001e000c0701d1484141d00e400c503555482904500d110550200547e4404160315 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 872398408 1250 872397158 872397161
    0x13081b0402070f081204140d12050405070b0a2105010303051e0d060b0306041b021506030705060c0d030e0c01090315021e0a1707081524130f0509040807140d03 70
    0x2120300b80e40d80170047c1c618100c07030040840d2415034240b4070798034003200c915085880c0d002818060010b454601c61000c000ca0031141044c01492032100b281c5460010030745801400030500041c0000501290901e07004000280d0171509442c140d41e03c083da002c2600e842d54803060403a000790036030725a0741810450300181c0180d603a0015070003900309880600611002c80f840704801c642001c06800103911812210000d80c40c03c0305000d800c010000d06586200d0f60310300010380395400480e9001090740281500c1d800f8250503114400a40d00401c010b00300305484100040c0a6080c03500c00a00800d5806010402c40009a81207507159084980d0354114414400c03d15401500325980050114444070161140080c000f200544922101c3c0c4c4d401c08941c2d127040454441102c0112596002204a42e09032012030b080d130445407884012000c295141c0034441c40c247c2140c40785521041958421000070f01058403507101aa60168001d0b44859660700c2b2440c14402c10104031002928600400e80f829009070b606 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 872399658 1250 872398408 872398411
    0x51203010f060809010225030309051e010b010207051f021e010606020d030203090a14011401060e0a05040509061611030403030306090b060307020c1207050a0b13081b0402070f0812 79
    0x1580d84801290b031310948041d08030f100764942c2c0403501c4407543d024507003201c41c0381080100c54464500401d014900380c6d1506d1420a00d0503400c00e501109845510920030b0034890110700c0e4009100a0076450700d09404520b85080100c80c10210441c1c0351081c501c0b46000304500900c0b0b1150900307056150403d008094001c2003d8020701005000740008072510b10700c2402524010100200540034a000c244d6640105050520081205548a021070655600d86181841c000c0085032559600c00b00d0304000c121003002260081445a4545814400148400150980d208003c1c0e0140703044007030440300c290b5030070b9aa5100280300c1d06c03001401004043d8160450320403100440002d2085808840c00c000f401c0c003044600c0001680401c80d207000c2031412041800314171402d48199a4402e440382c000c02c021842c00c0e0003030180c01c840094026515004c5040c408010030558018295250100441d01c0e140240306a009100300d40200c1c3d118207000d4050034000aa90340041c8242e9110601145081007040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 872400908 1250 872399658 872399669
    0x18060b0a03080c0f06060a2103090b0705060603010e0d0804020d0309030507060e01021b010507060c18170c04020310061107090c0e0102070506030c070f0c1205031201081f09051203010f 81
    0x1740304007040c0d0700d04290007180e00360f4030302c290043c007014503c0c04100101a00100d058041102c0048000b9036154a1402881154000c0d000b038840e520b8408107050964a01c0000480c040e8080c2c12203d040560001602e5000740c1d044a40b80300d4030119042c200d5011030f45810142960081e03040c00101d49400080642240303c0c281c0a48070415003420070140e40d819201503450101c0c40411164000030240d41c026514814a0b080240149080007151030a0743c1068104440c50104420141304110007080085c4400408540551071031400d03032050920400a48507850900c51480d8000e10000400d1185d9005402d0307101041200f101040c1d0300411150742002214094007a02d480440c00d0b04020b402c80b407080a07c40909480c00c2005c0c0d1301c907202088052415207042c0202d802c0883e2070a40146012401c50003a801940c0b501c0c0c011800c480c1c052011391201d0076560064070200c1034008110720f0001003100c9481c0c005009070850420f9070030b2551001004440130400030000c0303940c007031a03e003103030581c2c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 872402158 1250 872400908 872400913
    0x30906010609061713120c17090609100c0f060615020604260405030a0c0611030702031e031b0f011508030306041805160509070318060b0a03080c0f 65
    0x903600c041c15140c08400e070052500282c0c03592024840044841d4107507820030b0000d10018540c00868844007072100811040d0340c0003403070b441c2c945403e0188070510800408402e01c180740c6480403090004105210b84804c80d4003404020040300310300ca02400e9203008207900200796084540c440d00c0e00b84010220ba018800e4079417524180c24210b20b01c0001c00e9407007203520904d4500490346480b003543c0307069500c0d089072a038801c0400000c200c945050010540040c0b0440c074810140e4145a006404241c100200c024240d1091065002581e00003909039040e0701080a000c4a90702d00e00c070740764218801c1a440d240d18520404d03003581484000140c030302180e0b030380d1002080740c03040030240000026014868003549034818000300d80e051420b603104803c100c00b80f250b400d03402030060b072f03038641001c5480c401400d0f0024a24010012420042065688020a8a000c1191000b4580342220401c0c0e03941e00a414940e84207000042c584400c00140d01554001d0030071501d542c92207191350354030304d0204c01448950 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 872403408 1250 872402158 872402161
    0x24040303060e060108070e0a0305010e030a020f0a1101080408090915040b01170415020c071206230403080406230405010c1b060c0210050a2a120e030d020f030906 71
    0x880581500540050b520717180a916022021200107094000c01c55105640180c004000340e400d11981c3c1e032512041d0051900d51a040c0c2d400f038241408015075000d103410074825480010f0032550344040440090038105015110703800c14540c1c4e0302480e0300450300320ba214000c3c0070240001190b801103a900c2160144140c0c0e01e108011107000d52100b81c516500140c00000c43d00143e80076040d03140001c00302d0030050034040a6504035161000755803218440311045103051007848254002d015003800e82420920f22622040001c420519008101400700018000803c0800020380c0101c20700c00c0002c040c00103034007a656824541e0150a490488071036103801020500113000781e4000f82200c00380b90f0203031540c10b09a158400945640c1103250114041c1c2410b82030115101d2103a94000d000040000524101c104450100710410780c0780007003029a9101e12120280d0b00805a490801d030b410030201d0010840326045244d03008a50b40c1c210101c0c004151001e82840100266101d81c00303140440c1d415 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 872404658 1250 872403408 872403419
    0x70c300306080a0b06120a14070608010605031f0305070b040509090f033403050910110c0f0f0603280b03150405240106031524022404030306 62
    0x101d40292007826201d8111081c00d00105841e91821540404060416030001d4542c51449041408921086480c441d205102c1c5592180401c8000301800382d41c28580300a504294000d40030703000042001d1541c1059004001c03101c20550350b09402075070302404861985032503122114954100e40101030080d0250000603034685000920314180f15103d0000d54904440e0300d411042412800c0041c6688c0001c110802c020705010749a00444a4040d59585032181400c00c20002440810708400c2d00700503d44640d00315401d400f28105421070400c031a104540007240c0081002c0c44010002d10754000d1003c410001900307520003200002800000c42c8081001001207070004488001c01e142d40c0580c8250300324200c0a40c04640f5a4206010340c0841340c4510221080342d000c00040c400142c0d45030310300401045440d4040c010400f0108138040070b9496039003800d807154882d02d15008045080d500752500011460300074092510300020100740768526010b08100060710030810b54003100000c4c0ba0a50000381c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 872405908 1250 872404658 872404661
    0xe0109020a2603030405150c191101140c0409060b0301030b0c030402210d090f1a03070e1002010b090a0209060d0e01020f0705060a06050111030f03070c3003 69
    0x59990040540d0701ca607003001c10b50740340001d190303a400048010005541000a804001840c880c0344540010030304001402080d001010001e0030715140c41c01705102d01c451000e840f211805441042d80391600b80745441c840100c1c05810040140b9141c0c800d1082405202d0003910000d2040c2d071a121000c0c810135075a00000040c9200c00d10000c1c0c258810b41c0c0100703900c44060002503400900042a0a40c1d81c1040d00c03081040007130f500000c4c0c80c164024448002841e402c03125001c020141c1400d03085000707152400030740310a580b500c1075405803180000041d80e0680105900400500301400d0303d41002c2c1d5000e0041c3c02800d031041c4040c480d94540740010889500e0b4000c0f154055009400301d130403d0202000340c1c0c05041c0c6d00588900b00d540034404d00129082043c080c00a4a0280004001ea4105012404120395403500080c2c1040214030104480e40070020444001554240780c05503640c1c1c9510044a214980303403001400582841000f45d070392120303d507820109041c92a0b00041d40042c60000341c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 872407158 1250 872405908 872405921
    0x6020609030f031e1501030608030c0a030309020301020c01050915010801050c0702100c1b0306050f0105030303044115010510030c030b09100617070504140f0405040809040e01 77
    0x800c00d900c1044a910600d0004000d190809600f00384030f00d0b0001aa502e60039040340c1142c1c22024400c0d40040c5042c15a13160042d24001c04a81016510b00010050f0300c0d52549070041015052586031901c5008548007507041361610050074000700b01d241080e030600d944440c407064000c076402034075100200c0e8100701841194002d0188070315041c07074030240342d003440800030304031300080d05002c3c251088502180da400110008000340740c0c44541d8030381c01c40c0703896000c40340090a00b121b9508102e00500c02900c00008694104c1c1d008605407401d0010f40315000400c209509214405042554501410001c40000843c000142070265017000c22410320b101c40d40b075400d119a41e446076030751504591481c0694452000416146400f08a02c810b04005c03400845099591010480c21041c0030000300758002c40e0003004d8020004540c07020709040d50b000705980200d000c0c0c03000c9001e1400640030301d41d5580446001d400e801030b200f84503c4c03800e400c2c260500d4003d5103040c1d0246040481c4412404818850079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 872408408 1250 872407158 872407171
    0xb040819090e070819110307020f1902010e12070306050f0f2e08060412091a090618040509010e19170a23071703011511100606020610060206 62
    0x8030b0142c0d03106201280d6621020b000d0485410a410141c0d607105054060054042226402641e44e404c102c58000c0c50050900084141c070303000401c11074000007100e14a0582c60745c091801c03052402002d00024100440000d55074058415080000b0801406400c0309100740c18002046189030740307041c1119803a080c12240c0c01c05010401d203070341850884075210440f041040d1034520300f0007500c0d2941d82d131901c1010344043d03442900016142d801c0f1039000f80000c0240031022440e8030b04d80301d508290802802810500352080034003080e100e486200d1118a0074000c00c005001b40440e05003080c0c140c0c02003942c0180500180942c240d001c080e00c001d520030756101a8031890070702c003034600140703411f04a40280301a0010810003941d89100d806902080281152080704030319035a400a140083d482d4001e401c0003110300000340010031a0060358448450b000440741042c0e0b2200030816400c42c1484017a0904003101494618081595980010b9040c81004200050070b49140c80384c0080e42d42d1001203603c2c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 872409658 1250 872408408 872408429
    0x11a030f0714030c03240a1a09041412030115020d140d1514040e030301050121110a110c0f010f030b0a03060608070825150207030606061106070e010212090a030b04081909 75
    0x1640e45400d25105680e400750003501c3d007500120140c0141c90a00d24103180961402c00ccc084014058038607110f18003850b001c0c480c001000d03691a8010080e0070a01e04a88451460001040360708030321307400360820048a843c2110a0103219102c3d180b1030440303400180300078081c5180c81e22441c0e01c0e810000c204c90584405848900c01c00049903c200b02c5503c84040010060780ca64040400640020000e082119042d8035500361498107501410324028043c48114800d69102d110088680d8100d014828001c1a0f031a010504030305c44400700d5840c2c880350780b004220b24a807000014070604081086010f8800302c01c2529041241c1c83c89128660000c1842c11008141002e0b040202d4801c800f20110300307007842d006541c00c45079030391100740465000741d2085020410440104d44191000e00c0754643c80701150901501b010841c800003942c1f41c001418080384220000b41300102c5a4903401e81e18011680700d100078520303107064030703040781d10b5005101e1061049100c204034030410707800340910106541c0e81030705 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 872410908 1250 872409658 872409701
    0x929011106060d061b020d08160512041a010b0405040e0106030206040b09130f0c03182103022203020901061d060a030f02030702011a030f0714030c03240a 68
    0x4100300500c00e42c8046031328036558603030604256034121642140058580182c49440766031400a0b103204402020300491000084071003640503040401d50300c048101820302c20890b03071540ba2400f854800848850340340110346d0b0000034400c103d10010030540e14256018803865981303490b501c0c00c3c1c9101d4003000f584280c0c140400d100d4214210043c20207024004c1000b00b665044c0341d0b583c3c1c100c4522200b58905681c60300e8011494540600851051745000c0c640041e440a80341c6411502541520044114201503299810350764460b4040d200c1610000f110310407001205040c0715110040c0e0301c82280200103e000025110340103108614606400300040782d40c0109003410461941d001e071270b081041c03668400d40b0f4182d5024901c0134602c505034a8000180b007400784003240006403040043c0501c04d0380b00039241100080080ba24800726031a152090900c06c030321200007410208450700c521303018480c0300640c441d1a22880459003400c584003010800e6905c600d00da440030348461a0020340c52800811 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 872412158 1250 872410908 872410921
    0x70605030a0b04020405090708010504110c0a110111031315230a090e04080711062a0a060e10050a02040302090601050703090e0108010b130b03071e0929011106 70
    0x80128000002c010070042c80e15440e1000a20000e1080c0c0b0244000794407480140710364141841a028130002107202c03141420701e81c8840341d599006080004210300014010000079900525240c0c052030340c4113041d80d07240c0742e42840780012507906102d0110f881003c1e0300111085401034198a00a48024082041c036850702c502030442d560203480345da002c001c80100d000039008102c0151a02841c8101ea0342691070b1558140b00100401c4414182e10a034020023811785041100c11910003c940c0580400c071814103a14503c5081c682c0703802000e880982401c48c00c1c009040c02089003840396182220400c240d07218811100200d0007207010003074000010802140241d8040e0740500b9600f0320910b4200c50030f6480701c20840440c1401c1e409036a0746d0b915982000424a032902e260980422965410003203d540d5100080d65070669210701c503180300e803410450118611052038030003d828640402d00c115421442586c013241482020880241092020a00c7c3d944c0300f8510203038140f1203071004094985400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 872413408 1250 872412158 872412161
    0x301060f0216050315100b04090b040e011104140109050301150e0112021e19031b0e040506010306020927180114070e06161217071b14150414070605030a 67
    0x86d02c01015034500c980700117844121040248050070241e0380119110b10050709101c180c0700b04840b416016410174230b0071480c42d1141800e517803c4a06001064030340c001644016210301686030002505542007038104107066019908181c22161402d1765601316a98408511903511001c00d0020750213480c0d1a0780c050402c20001c3c2c55401190010401c10300c2165914080d1003106407a4400c0b20b4003da608a092050801020480014072800e011055a0b141a946641e1517000502004140f258081001509070302c03401a016285041c40e00d090072030742c9682d4800c1700016012600081c801c3c0f2501e42c4c410080340f045c01207a49240203070700520071685031104242c56450300110110f13000041807080d10005054401d440003418051140740d00041c0009100900c024910f00da51480031461000f80035496a10110403052001e1049003850b2030505860201d100c204420120f61040c4141e00d0107a205080c2d05a101e07000c3c40c415002580b50244020780c1540b42d080b1403151a010404c07d00005010031f410303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 872414658 1250 872413408 872413411
    0xc0609030905030f010e0d18091a0a1e060311070b0c0f04230109030305030112170d0e0f07050d0b06060c010e06090d0314130212030301060f0216050315 67
    0xe400c00612103a02d40707001c28036001003071118034401d80d15504a5031030281e05026030f000004036442c1c56140d0025820000f104070b40d0921421803010781e01c080c000616030410000e4007601c1c1005110f0100756545015070701190210030002c13040316110010006a5601038420004501d20721901700d400c1400e03589070184091001482c0c3c3d05550f500300410800b0361032110040020300382d8482d6400c0469041c000714400d225412500c070341441601c5d08180003107034204080e64115090300c00c4080c5001d41519000c070794000b50152041d0307501d20108071509040410380010080b81c4200049801600030382d0a034035502c403c079200c3c041c0c0046035104e03041d020420b52550300ba807019000e01000e103481c41d6503081c14215030341c41e42422141d0b000350003070082500d4240503814130000c0394039051001180c01d80c03e20707441c07003c080c1c0707001c0c07201c4200b03840c171411501c522034403206840c920010749449681d2410091700b68503800615000602400c2c41e03161044544d00201402d4800143c000e10200d2480c0c01c40d10b005810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 872415908 1250 872414658 872414663
    0x6070c09180f06150305240f01060203030f0a020f0403060632060d1803030b13090803070c06150e1902180f1f120f02030609161407081201060c030c0609 67
    0x88460b4040f0100e4010801141c0b0b110703070f410f8840883e58047c06e5002c0c01401c003070580090120000c004001041d07002087d070741c120300b0160746440e041c0c031104045e80080c46500d02254101c10007250000510032260300c220112203c04845021840301c90f407000b081507005105449070710854016078215810034001a1480c02ca030314a002401800c0b0540c0d0100500e8550401c074002a11415846c516080c07070400e07640740080b1036030f0912011030703540d850720b40600000f0011000c002801445500b40724aa0b004980142e640c0a00604166120300c40e0f0410301c00222489810a02140c1c0850303004603441c030866140840c469240c020000c0740c4000c010205038a25000d9921409400361940141e08001d0807155100450300c034108400920440101a10003000f00561024414000c20000e03455034020305030b01103082a0000602540c1c02401e40f4070040401d10741440d180c0105074241080803000080c400c0c0000e419505062360383c1d8060466603242d060710001c000403088510310380000c01ca900a05249403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 872417158 1250 872415908 872415941
    0x160924053a0c0f02030d0c050f03150108010b0a0203070803060d080409020904142e180b031e100905100c0c02011d060405060c03040506070c09180f06 66
    0x9a68100841200069200070281d00103040e03440d80001c0307500d104440d0a500d6a040990840410040294072402003403040d45c2159100c04078159624802c0003211070801071190107a840c0d051903650b007880220001c1c203541c081100c420001c1a90f03c08031090380d00d510820341c025845d00c036499440e0152a04080e140e960480140444400000c81510250010f490350b21001031315a451141004280e4072100c00c88034400c12400c0600952090583d00440003a402d040007454141c4101c1800b2641c11895004480300040000c6c55810503905d60040c10303034020214200c40d500e100e415501401801032401500c903551250303a000b215040d29420855001e40601d01341c9640b545404001030588201c190800006a0281d54200841d0b030020707000040c1a51070742d00c00c0310f421a0b040c04640248500d002d2184258004a07a8104800041044070080c1c4800b030b0a1580b41c1d4a58901301c0651511030041c600c0c070604052000c0f51030781c25598001e55460b002489049000c005480d031000600f0402032454038103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 872418408 1250 872417158 872417197
    0x21306090b1b21030403080a0603020d080313021306032901060f050403201807020c13240315020a080703020d02091011010b06070807020f010207030b16092405 70
    0x143c1401100c0903207a5104200c507901c1c94145001001c0e102c0061101d0a039600e0500c0a00140c3c6400708507902d29607103c210307581d07240c854a1102c103440c015a14000e510000303040c0100b1a40100340c200d81b0840303118407480c01050191803482c00a00303840d00b000b03c494160301401003140724414210100300d000e80781080d0f0714061716a15015aa00d0b1700c0640400500c44840d0361408a0178211850300381e210b0030342ca20514900700300c40000d40326284940040c1c491080d07102000f40c0302003150b100502940c0d5011040c842e0300704818082c501042c1c20300c005e5a106840003902d50400c04180201c5841d80200e40d42d03a03010344e40320340302980290002c829200d102c0703a0038032210034591500342820b8010821516981d00030500c2c92521400d40303141050890090105019940024000d002500e030280c1c3d04445903203407182c800d00103d00c1d00340d140e0f00c050100e0b29004180900c250004603020305540d02640c8810f2500e0700d4140d114940c00300100e98148041e540d080007a003ea100b10301504200040045201c1e50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 872419658 1250 872418408 872418433
    0x230901211104210b06040c05040f030609050f0601030b0705030a110c011a06130b09060f030a0e150405100e0f070906050a05010306030c0e1e0901021306090b1b 70
    0x40794203020104468840c0040c0601442002c4803441814440d41e00314003140c1601d994818a4011014080600581d101c2c00320340d44042c010360a0390b000e019120701d81c2c1142681d03030411030301400b01c402c81038481740940508081010400300d90b1034183d80d04800500c45a4451042c120740c81c4d40000d0a81506540d102a10a10a4031303040007020740e948202c0000c5480f43d100783c0d22000404841640c0f500c2644200034491507840d01400c0340044449810180e900d60400e5400f082d903503c50700f110300c040040004100060f003e125802600c0c00b050f02422140306561010181d00b0078031060314003420f554414081c208544405030050400ca60310340301650141c0720030a8242e0700c0c2146581284000b20b4444006105c80c0c201032250384018402440c0c01e011aa1a588644055548a0042c558016222800241401d174842400401803c40d4400405c843c034203505802c0c001e40100502c0303c40c0031040207002484900c6090303000107480010000314604440358000d40358888100f4101032040c002c000c043c2e803d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 872420908 1250 872419658 872419661
    0xa090602030906150a35010c020d0905060319020a0c241a09041712010b07050c030109030e040b120d050301031a070e15090a090c23090121 61
    0x2d5007410008000c00e0070042c0383c41000045090740c40e40945001c2c9004c110000c107034209040440c031440101d403015080d072915041c0241540749052019800c12090109039640020490310b1030300f0b5552500d11164544040180f184000c1c2ca83e0078105d241d8465182020340168002d10051440d0b003003d60f09442c081ea00c0034465560450401210555030000d00d020440500070b02848854a00035090001404800540707004000341014183c0701e8403e03000036403032402c40200d520409802a5400107503a440310788080c1e90703004110445480c016100100940e00f03050117a901842d5040e1200e0070088604c40500c0010314404402c10303801110701c0c3c0012800c58060000340581c24090f95a90366941c1542071001420064600301d01c9214a810b0801c003100e5801210213500300e40454500d05520b07112003c8000d0f0f40030328003c00d580942001070020381c40c801c41e808102c10f1181500e46100001c0c26840d900054520110780c040f04007410040346031320358450050400c40000c01c2041c0030b02d08203812003510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 872422158 1250 872420908 872420911
    0x606010f1b080406030e061e07020a0c0b032211130b090405100b0d050309090411041509050907031a130b040804410f10170601030209180a09060203 65
    0x1190004005000d010245d4140140421003c1072801003c560410403000581c80d01c12034061100140420040380181d8801d010011a030f40e0843d01d880d0700a526041c0000340d5074000c1d1486518009043c007083c0041c06546c030307a009259000200c4000c031100040502081c0e4101d00322040a49560300c515444580c1c0c1c031800f2030b000794010401000c4281050400c00e08488283c1c154501c02d02040201d0703c00501d00008a8040e4070080e41c110515440c3c1d840d245901954840d0150b03800b0f428000e1305d2046901e0b409514088681c0800d0030700c06034440c0401140c48503070600000c2d1020030211030829000c6040e2034250f4003c048080e142d60f8101158940c20a440404d8034100d405841c00101002031140214840185c041c0079000c288500d4580380094441c82c240884000d0300c18510080d07600c0694603224038101400d4041c190000354a40303500001d2680d42014024910000158049909035129200341c84001c40e014002407140c490440b40c1040a14004080300407003a2101300c2c00780090303000d0000c0c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 872423408 1250 872422158 872422163
    0x11011b02150a020405090103061a0d03081f120f080c0105190f2702030c0a062a030207170304031a180f06060409050f01020325030c020606010f1b 64
    0x1000c005007007007803440c2030110140c0007100890050109004c155108110281100c2d401400000c44040c41c0c3c43c140700c80f100e006407565101d8001c042400505810007a030f1031150142c00518110082c0c0c4d559500c2d0701e0715960090100484064202d4800034010202c140000c80c092901541040315070a4000e0a488084444040c5a41248079183c0b1848082c0103085d01e25207a00f5007070100307011055119420b410407000c1500369220010a210540d2820f000e03135030b010800a40b81c0641162202c4014100d45c02001c40c00c2144540844903402515440800801403545036002d404100d10304081002014028074501c0324074001080000002860042024003c205c3c03402c410800b49050060300000702032072041d29141e900b1110f4491400d81000c28860741c8030000f143c00080072003180c1040b0b4605102441201c2141d8400810303c103191080d418024883c6019201d18250f042c00410700701c041d03548010740b40c40503a04c00c401040d0b0360760042641c3c00340401c040c60300703806003480e442c801d005510100c0c005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 872424658 1250 872423408 872423413
    0x1020d06080d110105150405060d060f05060102070909050312040c080a0606051806280509310b0703050601140724020721030b03060a0507082511011b02 67
    0x7246809078100fa5500c0c254081c3c50300810561811201000a00034140c2d00f4510840d60342001512643d00c60340c0b4446000d130040800c0281b50001c243c40c13030043c4410f50301d9601510801000088080c064050540c0e116401800b0314100b40c100c3c82d51610424010340200c41880f00ca00010a25101c00c204452905000d140301142d0213240c0424048001d00c0b0182000402c2900000c100d11a05d49012800b1144056521a02010079000103642c1070011a040706d0341c440c0c3d92030306000b41c80a15041c4401d4403054030345500300c0300c1e00b510030307010403c001160024005141080062340d2035019500241d804101810710281a0302c1b503500d16525a4012103003250490070031000c40b04c03a0344a0003140180422030b030804518080711915600354109a050044a40348170940310081070030320030b801c00c0302c40744000790480da0b103420070103141d2001c1e21003101c1c0017000131a024001502031805c41d1103001e21050742c55518a410078640e104982410116603110402e640700c0d044514002c00c1040d208107003660a602 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 872425908 1250 872424658 872424673
    0x307030f17090d050a3e0a0b1c050a020403023d02060702011104120b100e040507061112040501030911031213050d211202040b1207080f1801020d0608 66
    0x148081e20400c881076140801c0442c00e140c101c04010b421003196221001000c10366000c4400c2c6c001021400380350000140c2000100340c1c500c8005106030001d4014116580c1413185964105218049020345d10003e0351007145032006084107201c08140fa00703100343c207150240c45c002110102e41c101d1200702030800e0069000d141042851a82841525004d041c1c0c0c00c00c1798030301407820b4108807082440c40005404130b40440d000c60307000c402da65400002402d43c40d03600107041c500741c1004c40e107078100b6214800100b511a1a581542440070804000d80304c0c0301c200c581d05140c00e060045004180c51102201e4401d05200d83d076160390380400007a8001e004041c805540c82c0010701085070045e90075031040c0d0150700c107000e00300c001589000300c3c00c41c81102426a040c4030010008100d60406604220482280c40087c003c921032010310010440043c03480b20040540d1242c1c0b108659403881200c034103000d003104002041370002c0b182d014001a405a0b0009170410303823354447d0301240d041d648280c440f94403c24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 872427158 1250 872425908 872425913
    0x501020409050c07121806260903041802041211030a05160f08060c030106080916030510140f07050f070213052d0f0a06151701050307030f17090d050a 66
    0x5c0902d045c1681c14a03100400081d0012850b0128040d80203440c01d126841051100b1820054003070034103020b0402c0c50041034245101202d0301c988c4603004030400180708418200e21a0154000c031003c441c0000660490ac00705030301c440640f072440b0b14100e0b60501948600002040b0200318440c9101c04000510241d80d01c1d10795011081d070520fa000035825040007042088150500c2c1c2940d0468500c0d003003805842c0d0321a071240f4141900c0f14402c00c5800050303034022040c0701000410044004101000f04500b605666201010a1085505140768050390300003614040c4208003415141145030001428403809d94002000618205c4a1841043e61881001441c0042d521042600b44802c0301c001c00e404c1c521080e0401441c002050101d403124041c0100d6440810f43e80524018200390050384102550420010f05081030300c1500400034800000100d651f01c3d012503020200ca40c40050303d02e02c464266190101d8014010300201d0f03e500a00c50800310391183e0300c03081078a82c030401c0549002145131 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 872428408 1250 872427158 872427173
    0x1e0a150c1b0902030a2913020a140f040305060a062301031112090c12060406150f03061514010203040614071e06050903130b090a030c141503040309030f0501020409050c07 75
    0x2283c208109880c0c1000c080a8684007d8207000b4560600d000daa1000c0341c050644000c0c80441856444220000f03040040c406240d0180041c0c0e84104107855003901e800c804007043c0e810038084c00320748545035203021540c2c800d01500e410ba0160181030206500c420641c0036080740c0c2060f41d074100500801c40030002105001c0c006645040011039004000e018001c20546e87c8010040000309030035926100c031000c80c800c6450010003001d2460b85144042d8903441d0180140c00020541700000300c41c007402140e490350800c0745124505042c0e0003103042c14a00f4030100c6190040c3c0c5142c641c209410410500403c80f01c44019125502d042c0305d084170100d061415400b1150700902920b07080e007044c402c40d0022143c014010044944d9982d04544038000100040d40e00002984010035501612500060f02d0082641210034000c003151884e0b00036400260585a920048034000c0025059010910015540d01010200c2c42c1c000c0703000508190700c6002080c100c41c4107460400c00c428006c034100013000001c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 872429658 1250 872428408 872428451
    0xf0a0909060f14030712150b19091401030503190908030705010507170903070b07110a05010c091208041a0c030f030109060b0a091a07021e0a150c1b0902030a 69
    0x15402814070514002c038224007182d107024000d0110141f08058030882d421a000100100e500614413541281c0516a004c2c8890451050a403e1403c1c00d00465200803610b01d050b04980e0020081c52401400c4028601000c14a031001400d100380d000010030305810400140c108984620000206810300030380c003800d070031186018810201410020420300300804016902d15a5002c40701e00720544480c00241c81325603034044a20141d2280011403000d016054000c415071814544a0a00603038450100c070101140c121300151500c00c2c1004104403003049402c2c05c00406020420081c100000000c4c458215404010340800c0c0d50004001882000901d10900300207180170003c1d103151011310600602499814407a41c0b0016400c100c020000e28580e10403182e01e19401400590903008000050b0b4420f180f070344550740910b6200390081095814103078540c05034000340d00c9848002606035510712880403903a11143c9401e40c00100010041c9460010314080c1c00d40750303001300da0700034000c100c0500c4141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 872430908 1250 872429658 872429699
    0x5070f03050d2118060b120613030c050d0203031909112404081e070620030d0c030c0e100c02010509060712020609010e01110f0a0909060f 61
    0x15060080001400c0001d140c0000021800d056490403541d0019000b82c1c0c03038410f0103c02d980e090400a0702e01d520304051000c0203511504041003240041414025204071203041054103501c46c0001c0344130302c3c442e0204001214400c0c074101c45c081c1301d15981c0c241010b402005400241e84007105000980d0741081240701d0100546000b045014030720b88494010025030310404d4040d0341d5a040e101059016200751204542500500c140e640b560b0b0740c186952075030101801c01500900540da080f01100c08244502250000d0340c0c0c0c40c00c40c98800b49890003190105a001081e48070801c00820030401034000d089018102d6240040c941c07000b00e02c00360030a1905078003d0700c107281941e4884005508a41124986502844c129440710080c201244007846581070142903043c2119454040b180c0c00100c49103d0359008000b4003965040c1c01c3e2582c06ea070148041014450030a100f4900b2850075840035158100003460550401d0ba034941c401000c0f502181c00c04543d100c40c416061103807107400b80d0520302c0c441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 872432158 1250 872430908 872430929
    0x1e05072f12041415030a15081204260604290a050106080a1506030905030d090b1b09220f0c020c190b0708070503070b0a1a030102031303050313080d06030507 69
    0x4404a00614003840001d0661140b01e47d0707412204040d680740e030600f0024041304012940e01120103500215550002c3c801c4440040b5079024243c2c0080e50603848080340001e400c02003540d0380300c40e03484c080201d10b0034082502001c00c20500c0c5500040754100703203005560110380015607504190005007000c000502030054a801c08c6180c0000500303507003000c1c0803103616240c0010010a103142440c02c520600085411036400e0031000790510101941e2240244140854040c0c50b880d4200c510446015074104240d0150200d01d03c41502080f40c4d0a41484001082e800600d013001c41403004103d8210002007401648180d10b26455410700c40404600c840c650b0742502d0400e0f1500380952941d106d00c07440108072a002060203c00c001781002500c0c0c00c941d00260201c5907180c98403003c802000075285000500307051489001946c1810300c01c4030b025a80c11501448c04a01a85060b03801c1d0707001034116800c0c0f400c84e002c608041040c880281c540300c003000c08041085d83c034500740349180210700e81002002c41e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 872433408 1250 872432158 872432179
    0x80301030c0b1306230c030a091706040803100b0a11100207050616020102040323011505012007090603050f061005130c140d1e05072f120414 62
    0x1c143c84004102151400d2030b08102265a040a4640c1c80e5201c5c4505481c107900440e201c1c0607880040b019161282260359000c0c00b0903658445c00d19403c5076907046200710b8000c1c4000c2030200d03031144004d5034000c12601085121542d100c01c0c91007030340e00c04d20000780010207a8814144034181803180517190120b501c0d00303600b000c0c80c540f550398542d08040e08900d119250811004100740c001c0d01998002c6401189105443d54240c58604c17102c001c40d00401199440e01080128009654601d00245c0b0b07010703529081c441c0003145035140c000100c07100c4000181700703081c0001441d07509802904040d500c100c01410010411070111886e00402070101c1c4424280110240302036151352a090101c00441c00000ca21114582c10907500300c6203080040303240010002c2c0c0b400600c1c0c025000541051a102d80c034265800100c1a400202c0700c00381d5030705000460469041d140f00d400c0084018030141500ca2070420000c1102c002e034030304aa6a41540c2600202060800c0191030902e212a40c85000303841d02c1048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 872434658 1250 872433408 872433427
    0x10080406060e0613232a0315060d060f0f03020405060a29160308040b1b03010b0922200a17130c0602010f0f0905031222080301030c0b 59
    0x4100d041300c0c90340d099640b07550031500d1401e50a214281c1841d102059205400c12965080c0c105851417000f5215900302c0c45010150f02542044078400c40f41e070841655031801c20340800c800395100b012000280c503150300c80400c0024070880c5070001480007c4c0444400e5207984144025500c0045c44984500202d00d4100003142045038001030084211030403820310701403452452918020b00c1210180c02d106070030711904064000202c0c60280303000d0095424a9690030350a140c0030844003070020b00003241030004200001104000c1c00780310000400c055170708a80c6940719a806941c141c2c2d8141c25030348452200031280803882500c2c40c0c5601d210421841e0102c416009001d100d12120310300036261004c00001e8440d05c1d01c034449402030303078450000c030103103a9982002400381804880314001c0d64a0701021fa041380070310307200b020b494a5104001d1410821404444076000100078906d0091404050580c0751a80002100d41155441614881e85030350440c1007888a40c1e8441c2c0146044940801403680d6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 872435908 1250 872434658 872434669
    0x14040b03070b0a111507120513021002101e0b030304150c0f051c0e0a0612050907050312070302060105040b0d02040915020a05040905091504030f0e10080406060e06 72
    0x40e95004072903503039245502c00003251113040c2c07075070050001d00440500360158403080c0d131210300a40c403da60700c0560900d21075941007203403410f072141ca48102c3c00c80d22075801410b0030fa01152142005005451125001c1d000e00d000342e502d03003100e08401d0300e03941c0a100303030000c194442c001503241c080d40110b0500d400c00e0070340f410382c0190819000c184038500604200b00700c9404200004c499105042c0c0c0d03003464501080204610404211802241a004159080f420b00b0036244044031540d0b51417100c0c00148905590003084050061a001e0090060210342c40e00c0c04c01007200c4907000030442c9943e406650500170f09203001a0132061195092101c104420399440201000341c6404039000143c070496484c04590020b11b003900c480c0c00600200b607083d50701d900310020340100c400040083c09943d6980050648031041900c00c070402c4003030040842d010a1040c103001c3d21019041c1015103050300c1b000005200c501c0c6150401d030016899100f00020884140a880c0081400c010440541c0c24000001807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 872437158 1250 872435908 872435923
    0x3160f0528091a060c0c090604020903030d05090a2a0e070909180c090e12070215180306010312021005061f090b0f12011d280c0914040b03 61
    0x30202501d594000519440b0b409200f207000c0001424150f0310448803419a485200b0520401d202e020050700007007050501d03000700c40380e01000401840c90302407143c4880d801020701030490405c43c030422003c44005002c9099040c184001801c0640d2000000610000c1e400820b401c40c00d560001c01c0d040c441c1c266042900402600c0d01d030b110225201c2d21800350100e040c07a401c9006002c4107a40c3c0c0c80090340e0860741c0d008200300c0c42c0504c2561401000000021010721400e10000e4014140f110642641c81c01280035020300c248100750422810110b1000038500f1400303802c00e680c1d001c081c100302260705d501009040c400d40c40b03c14040c042c0d440d024002900361030ba05490781d045040010618030b101071184d16a01d000e088441280d50710341d011007441c10390b03507082080c00301c4c4120340c08c00c004501100300311445d1600345542c0108802550741d14001050000703107100c259100c24010000946140043e0203215030300000ca03603803401010b140c6294080e040c0c03806200d250040d490301034044550780b404900310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 872438408 1250 872437158 872437169
    0x702091521031201091505010c0f0204090f0c0b250f02060c0102040513090c0e40111e0d081602130c0906092303160f0528 54
    0xd8111525510748608610402452000c48480c000c004210140c07079521140c022205200d011540c0c54843c0010340c1e6807a00d02d203000c0d149410f0074581c01d0051138507410403081e0078402c1c0011030259031517a503000303c1c01c0c03002d401c85014040040303180c1d00d1103103105c2c0582c40c0203081010000402034594603244a002014100030340035441c00120b889144409404031002854007a00b25100e6240c001c2c9200300805089200b00c0b842d000162001580280d2140503501420381c0240c24a010900c0000d0300c131401d02800b09000070a80c84222043c00d6501c1c210104d030070540900101c2c580c0001c140f040112005040c1281c02108004d075001a80d83e8407041d020034180c0d0740c41600181e03604030034408003180d021541c0000354491805071040d084c60205804c03002e1803491a448495646450702d20549141003603010380c03507846010030000c2c51800110900d59180000c040c1c244c43c1c0e0118105070414110740e80f5004035540383d99140b010450b50405000080d19409049803a0304540f18182111003010820300c070700d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 872439658 1250 872438408 872438449
    0x114040903030209150c120a08070302071509110a050a1a13030b090d080109020301050607080d060308040f1703030606040608150d060f0c031a010309030507050a03020307020915 78
    0x80c108040c0a07030304451100310300a1071151309140301410205554803c50381c04140e40a000d02d00d4184441c03440a64425079499203d0000d03a941e040b400720001c0d005280d059480107140301600e800610315104840005005102c0342c4405801501071142d15020390f44101c0c012901c0c00001c20036524030582e00500b02c458004096035900b01c0f00d0036044000c0964201a10401360001801041100054014251401d07030f10b4581f0240e0744c1c9c0300c800d0220300003440342582020080007894000b03009400185501000b07014000f80c01501d03a1a0003103075800079001490810b04c280e1040c08040c400382c1c64221101d903040015803031841e2000100300b0900980c4126018003d0001c08142c1c0001042c400807030414029050f08070050b014105880035040d0b1040c2c86001070300e400c55100446100340035010700244000c01a840f0300309150b0046004005100041d0200300b0300f0700c8041c00062041c044944a21b0199004503140d038440d0040101c8207170302821104e03080072081034848840c2c1311001000c059240481c81e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 872440908 1250 872439658 872439671
    0x50601050f0d050615011106010501120e011d073602090d150b0909060601140f0c12182407020f060a090e0109020a0503150a030203060903031e011404 66
    0x20804100c0d40b804014540d0060000300010740400c00d902c14001c4000341e071401610840d4041d41902c48800b0700a03580000c8000030215104a030a17000b07201d040000740000102140150308082803007200c51081056500140b1041088a0f510b211503c20f64135500181c261b10f50b412030100c0704800c0480e81040159401250860083d90744032541d19980da080b0034404140101d00c98003000800b51041d48902c035803d84004903c0300c0c40001021445010180c589461042e150841ca041640085603101e0010b0f0342080802034405d4180b12130031000e080400032a44520600440d4025009104002030080c0410320300380031054009064010485003154003107554100c24000705445a0200caa0190060700009003c180682d1100b070b004100c4003608460707101640c032902000705034032036200d012001030014400308401025011002c1c42107a001000020b40741e0380c8ad404039042035002ca88511054002000f040070984410100786518000c0e11006000c5e9818012250b8014524030a214096556040b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 872442158 1250 872440908 872440939
    0x518031c0603080d0e120301060206070c1e06060f1a0708181e04050903090307051912120908030703090603021b0303090307061104053d030e0c0108010305060105 71
    0x740160051600900144c0d5201e85030700703600d005820140e2265005200300140c206007044842c0c1030383e05892081d40584425181c1071002c884068504006881065020599545049544a500284a1140d00d0104d04207240c4580d51600b4095070344510400315031401001500035412044488032503004200d2034a40e04085108091300c1c04c0c18083e0781d0096260001091ba801060083c40c0818038121418081c59480c4920382c2c2d102c1c021690001d400d40c0c0090020f22451074400a0001c1c2003400c0c40e59007041907074480c40410950f80c100c03010f0343c0c3c1d80500925a000715034001000006080b02c030b001589031001d144d5008107102c0b5184501001c242d40410714181d410b101001d117641d092149005c80340c0740c1c140140c0720b035103035400003a04071802841c10480001100d01c240c25182180c000420300d042c40540e40020b074108049002c540000a0b01440440c06001d111090313003001c1b60243d036400a602c04007607014038034002c0c0d007804030345c1846040340c01000050800211a4191001524011165050070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 872443408 1250 872442158 872442161
    0x10519020f1207020301050601030915180605100317030103030909050a020720011d090a09050f1603020108090f1f0b0a12110a0e0106030b0f100e040518031c 69
    0x20789407203003074064a100c03000c80780191000783c500300d40210000c0010361903040064084a509010041901d0210303145404250781c80d900c40100000c40c2411100102c0003075658108546003120449144552a1424003d0118600c142400000302c2c4405a155506545006d8200070b030134807540d01c0b5952154006181c007603003601500e609a9014a0b135049052082080c2c0310015400c816030b60000d00d010a113503000708295000041000c7d0041c01400c6640c036003600d44400307401d0b0b850069034240f02e120700820445400b0080000074400d4840074410701030440c40010505a4050410316450b4806028100c0420307010580e140f0034030321022a04480c40b208101c1c0ea0141c011505444e42c00505054001a0040d100510300e25582c030455000e44d8102420040103044800341c0142e152072340d6528010701c8140c0c040d502400705410011302c0014040c05e22800215404c0007005e03001e0026506260b8511203081c80d010b115005130b25494040c0a2120b00c00d00c4640d41d00440455411030304e410300d080c40408240703 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 872444658 1250 872443408 872443423
    0x60312030f060f10030e010c050a090e09032101082122090614041b020d141e07050d0807020d1404030c060903051b0612180303150a1401051902 63
    0xe8010940f6001c20039018008003e1160301b44855402d00b030800c2c070014842c004407560210340da11040c034239500345100318644100091007a100d5100810000349a80e0141001c1944010029060051581045003290170103c1000d18401400c2001400c00d6905000c2000c0c0c03014501c00c0403580d8401505080c886801c040d0540c400c040d010310f85840454240340482041001100075141808030b00090082040400c01c483e1070ba130010303005810000d80444c85034020541d41084100350509242c400e440d00041881d2411094401071800601c0d03104001c030501c088640f80c0c1032410320b0b003e98500024041d465100072040401041242e03449007546806440030344014580010318102c900c6c1c5c0364680a0544045130100f6910780c401c0d048500c0e6206148011602c6450006e884181042034917206104030440c081d0088413034150103410418140c10810143d8412201e0700600e1014481802c148002c00d4002e400080182d80c001d0601a20350760031004440204074000613034810307800c04d401c0c103d00745101e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 872445908 1250 872444658 872444689
    0x20708030f092a330a020109080415030f0e031e070b310c06030b010c02090c220b0724090507090c0e010e0f040f02070f050105060312030f06 62
    0x1d011018240c00c005030303d110140d406042e9004204034160312945905514001c0c0401c4407400e41d5407045804c601030a014140124990001158096a940d07074010300f0380240d000324146c46003080700300b0340143d410b020b112841c05070404100440c00c0044002500ca104808500c403403070720882035105c0070944500c2107411240c1c1189181040e030074003004290103280c07440b10000c006100155a04007d501c507104680c94958020b014080036440c1c1a4164058003403002c0341c905024000303d403203000d62101c03002c031031080d070503200b58590341c151400e204a1881c0a050300c40e252604440303000d200711444402210350403034009000100a0681c0c860440c1542c900990b080d8680c0c0c1006000300401ca0005048410740e205203e091080c004800800ca030049018100180003031100a003404560a1150070441e00d440c0161020070b0f444c1c149914002680d01142d0110b605080540c2030300b007808402e21178190000d0341100904402c4849040036011808041c020610310341d421030124003245e80304c0d045258003c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 872447158 1250 872445908 872445943
    0x13050108070210152402250b07060e010501060906090504050c0c0f010501051e240c0d0207080c01030b10030b030307150203060f0405090a200a0b04031203020708030f09 74
    0x44e0840d95100d84541441007422260340f055450102c5e90311803c6100255807603600a21070401e03040d80c08601e491208480d042410206c3d140403c2080d4020000d10a55001e2400030030002400c12429086401c16030020b002c00031100c27014080d0a42c801020412a102290003144645603c2c024094510814036222800e11408005040307000c1c040d08524100e49040fa20000f80541c1c0d4068a60f210342202c0c141b950180d1010700607440d036008568441d0000f0704c07040d0b02c0346c204507140e004240340001c0050480c015a200010030458000104610349a0aa080ca0300380700c2642c10307102154440c010300c4424014141c550a0460a45d20104141c40031a600010350b496001c40c145541c2000b5842a150103005003041c4c0b0f000181030a250151a026901d6600107103488035264507803004c000a8000b0f0103c50f607031001030b820460340c2e4291230b000c042d01a41c2c24050303a951039442d04010b4600c9000c4000d00b818014407800c004503101c00c0035a6071080c0090329080040d5034a0400d00d09107680107403071001e441e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 872448408 1250 872447158 872447171
    0xb0a020703081c02191404030f03051605100923210909042f0a060e04090b011d01081b10020a0501050a051f050303162112050c13050108070210 63
    0x20314281c018010942d10940b06c03c070902c032120038001440d120b00e00001c0d10011704c5002042c0024031450040100740c0c0c001c800d55840006030340e03449081c0894030000c690426217548146080c0404014510a12481e01c3c0303080e02200aa603800342e4540102d0741a04034880040d50030b4030070586568045401c4407000615401d0709140a00d050b10381c140150110802001350014080c40204420850000d0850003d022046141c40d0420132900b0b4011000d00a030490340300c0013400005240018114060400c2c1d0051842e12580c041c80c0580a01050748038007407952115103503407510b00c2c01c07401c1e5100009081d110780303403462007441042e40f42c0b1003070480052541d8070308020483d0400490380098010f08800d0b0020a00c0418500d64a05e50034039800b40c2c0c3c0d4950010004c0c0ca060100828072800d050f803241c00354100c01c0c0307544a05006040ca040c405e000115900b1302003407000494601c500c590001c82600214285400c0e070b00170351103644039401554144540f48020401140c004c02050106480141060051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 872449658 1250 872448408 872448427
    0x100b0402073521160206011a1b030c0f071d0622060f080708030d0e0c0303190f1e14040906030c0305010f050c0d0507140a02160b0a020703081c02 64
    0x80107903010b00d81c040c91650f140400c00f0301100500c0c40000c984c1c0d0754014203440e401e0070300042503e00649004075030034000700148203003c0310440c0003400d60001c4074040c5840381a0800480d080c04505400041c0d9038001c441c1c01e1103490420703c000030035000764101c10490365031054041494014180c0104240c00005040c5141c5441e85403c020281e4011246440d011995412003540e500700750301940d0220f0b081031010f010320b40f41540c0901551514074044500030f00700382010900b541c2c45481a204688940e03054000700c984c10119200e4456920700d401d240c0b68801e04030003010f41e890b0701fa9813010410000c0c00c2c102c03002c0c500410b0360050202101c0801403079070340f86449020001c0b20f120886017135090010244207090240b280d24800c0070510407062806024512080007000000c1c8962309020844080c04c080040c050054a20401a500184500b41d043c202040d1050100d41c0100d0b1410001c0125400455020803402c081f0399111010585491240329504282c4d0001c0100202c0284046049c075070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 872450908 1250 872449658 872449687
    0x2070804080c0f09160c06090804060f03050c071a04030207080d180e0105060403020d06020d020301091d07030203033705040f090c02031206040209040e100b04020735 73
    0x200074208032000c5000c0c41003d4148190703000c00b00c800e24540403510600040a070f004d4102ca019591003580300151600c1ca6907038280c21600b00350030200016070443c4050701441e4052103803a4002070113681850421400781e0b6800a005900009030420f0880031001c9030030140204a40341c06019550107646540345d203031100400340c404134034080c0c80c03c84c0c1398900080e420380c8405007070341620400740034149804d00b180c00340a003d180010702145d05036400c2280f40340100c1d03548040c6020303150448010401250304908c1c04900704403005807411a410070b20080005940000c1212a202401d18044041c05903029008081006a0703850b4484409407240704201a17900000410036541c5d0216180c1c06030f5142c1c41c403281100d0040510002590042040c0d40e40790b4082d01c00913900941c010000752414900c0070100d815140c2c84a42042d20350b0004049082c080c03654000d903091503005441c114144030054542d2030720500c520100c039948001d00491811460342d005803d5108055500341c280c0e8034600d00001b901d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 872452158 1250 872450908 872450923
    0x201051b0303060f09010e3907030e0414060108100302030319090e07050904110d090f020306060d1e0606120f03140a080720010e0102031906050d0311010207080408 72
    0x10312030131660151400c02c3c6840760302c0906a0b18040900c003003940d41d503404400c488484c9510001c461040000300e0a04030042e0309281000501001c3d0551030304842d1901a08459a00079041d10880c14650107030380180c01030300e096074011400d1070244404c0e200c1c8040d09000e061103802c044e4040c007001031074401c00740b0380f088000b03c4218566286a0210759801d01420140170a03160007000580c00c0014114501d450303048400060752400a9a14108041900e1421906d8a0208440e40104940d440040d0b00d414046203500040941300310303c50101564480181340021200c0403010b0034445504c82c00e1022550289002d44548400300e90001c1aa040809004080240442c0000d030400b050705207110692045d22840101a1118401c6464002d0266514402140b040107042d44041c000e0069a0702400f4001c4814481d000069890030415215000c0d4080c40c00507104a03410218100300a40b0b0341000c1400e040c2e05480d180d00c04601103040240a4840c014000e04690700200d40400d0b010004141c1ba03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 872453408 1250 872452158 872452171
    0x90e160f08030706020d020d1407030c020303070219050f1e1603020f040c14040b1209060106020a081303020a03060c021009021c030c020409060506010206100f060c0201051b0303 78
    0x9028003603844480c49080031403400303001d64076001400342600013000e9030058421001e0807400581094a003d140c2d10483d85d004180c8000c2607001c80901c03107550b07014030801c1e14000d060300c06940741d8036140c0c1c000395854460440715a4901d01c00d4066005011041c020b41001400d0b903001e03504068010070b5041800481100184d00764010802c140c12400d04c8100b03841300b2030b58060299480303a0100b00c2040020705030b918401042c00f03004000700404c00c000c800180f0103011601522070b19482c1c03e018010a103c4000c103540070640c8044018440c40e41c00103920400c095200c40c1ca15950040012011005a03259100035000303024010080b00304076a51b080300e031a10a65900310340e112100043c9040980d00401c0c03019420210a0a1098030342e5041030012201d94002d003448500c0d0b100c9a400310303040398451101942c01079510740c00e1002070369052042503045147c481039200c40d241032914004580c0f655120f00414402880c20060459002d0010f40d144405c2207943c03018183d1a14818030384a42c0100ca14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 872454658 1250 872453408 872453443
    0x907050f0120030a20010e060c0d0e06091f1a10021203091c0e150307030b33040e1f09091b0621020a0512010303020f0d0903050c090709090e 62
    0x4c8880c5c200140b007200105d0320304600404d09500d50404218580e48550f290490660700d481d4001000c260400149004000c0d21008091140c1003610f1306c4043c0c1d9110852808441c1000c44042d650440c0f1009090b00600445104180d4020082c007a0310f0007491800c03030402d520001c41007102058011560100144014030403611026101030102e5281c1d17003c40039994040c0481414144015a5502031503200e0130303c1c100024000300041c00905a61101031041e0380300740d245111132a00f01c05e01403c2c591482c3c00a00c0080c02c281c00d048140020410050020041000c0d4844600441001841c542c0081440702d03c100305c18055400c0c079480c0c2c0c0c448903032503240c101c10308a1b00042003403045005001d443c440c4030000e00650b50700c00c1c80034041e6000d4554502040010300c40318000c0304020a2441c02507100380c0080c80c0901c403e603501800c02c20000b800b5400d10048100400c00702300082000c1c100d00c10102c500c0c1d003035a95030389030030784200c0032a4104400ca940b400c20781c2e00844500103031081600414024 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 872455908 1250 872454658 872454707
    0x1208070c0603020c190303061223150f0403140d051b040b1b070f0b120c0f040e071701060905120706050f0d0f091a0907050f0120030a 59
    0x74241c00b41c0c450f03e1000001a07000041032290309150030001a0710500c030381b8020900e5592040d08001078051800140d6980386030646510884001c0030110301ca40d03220782c01400f00144408a8035000a400420704406402014002800c0500c80c485080300651000301a9494101c0c02c04988014142100c0d640c200c120740300e41410b4840c6070f544c242c50498107802801480c100f2104a4148498800c1420351030501c5841d00102d64628100d400d180607040b007518507a220941d40d2007011201d075000d1304000041000300b00c601b088103060011035064450000044c0b0790f60301c503040125001d05c00c2e010b030709003a010740e480049411b6501103403c90407074000300c80840b040e81c80c24911035140c40843c441c0310042001081195601210080641300300ca60180c0c00240d0041c803510742030140c0d4200035085512451012070789908900380e420040c2c2100702c0030010401e03541000c2c041051241214161410b000711450240f07500a484410300240c80d00d0314003520380f1903054501c06001e2075a03030f5034101d800590508 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 872457158 1250 872455908 872455919
    0x90803040f121d061b061312030603031d06072301060f05130c12140105090a051006030e0c03071203020607020607050f03071704030c020a05060a020c0f01091208070c 73
    0x74400c90070103800381d20660f14120780c01d0400145074010729011050081e071034204955107005001c01445102003507629120f136441803404000d00404d415442052600d004800e0021030b81c00000080c04590a407014040041d1000001f10180501d8038020301e070a1450b19103201405030030a6a4554081c520700078894592501ca42090f40000c50081c01e40003041c00060901c80191500024414200da00b4070080d0307014410390724420358804410350600d1035081c030b00410a0341017003500305034480481c1d038080010b42449407004500050520601c400c250320307000058610312052004100d07100b8003c0171100c0c82e6503a280d041c6480d041a83c0c0036001750090b000011502c0b400401d0350b0f0700c50314295130703400d16020403d000c034102500050507890800c0a1104050200051038500750300441c0684c840c030055030b210f80f040000408290304120f00070041401110341698000818203800d120490381c02d0790030082e950040780c4801a9600c042454075007540c00409003d80e49004120581c01042540719241e04c55 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 872458408 1250 872457158 872457167
    0x1a2a0601140d080d1b03140a06080c01030b062a06010603020c0607080405030409050c1902030c07180b0918014a030a0906090512060c0d090803040f12 66
    0x10020a402042e58034421001926070801008002d0000400003402c200341178100b041018181d0350350000c0790340c0c0c1005404500a20006c65440804100c052146900348030340b1544590302481e401c2d040c144c0b141c04081c4196034080c26601140080380c0784c1c1c0b40d0711203110004020f40186000e400c07414041c0780d0000c1190b0344280201c6000118060081c116611940c00880d40c840f0b0042080e90580000c0c000407030f40311802c1c007603140152080c103160f603220480c41444504c203203104034001040d580100488070030502c011a05000f06c0b10715140d4040e0290100c01d01902500000e524140c5c0700442000700081c25107041e29004c100d400c104020044096030118428230030702080c02d41e0001c8003100317404260103070024801c0c000526021642400c040705e851101d074034541001040e40c2c00305625000c140301c0907521a10b52001801c040710807243d0f121102201c1c949942015040c5144010006482e0000c0e0042d81c00c24080a81d1050041d6601d01e05420f180d881d09010030811103400c2448001d203c80e06108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 872459658 1250 872458408 872458439
    0xd0909090f08031005040f020306032e0209030c030f0102130e010e06040c0c0f030906170f0a02090616050304030b06040c0207060807021509070509100b041a2a0601 72
    0xc19214008000c882e2241d6809030030042000300703091803d0901291940b150701030800f0006501d80701680360f04000080609290b4060100d81c01c00804880d1000c624a0202c0303114010300c0d014a0061741e03001864040b0b0708002c002c0340055054480d1030030600341248150f00a11612400110880b1001d496200c8809210401c1c0b250300b0103a100b1801240e114a07241d48005503651311030a01d259a103d0a60311800224201e01040d0045100c1c0c1000f0070015400442d14000034210240c411401c0ca001a0f0044070f520020b0310314111158041203e80894941104403545e1440e0920300d207000070020301c0c1240d580d07841801f01b1203250300100003003212424680034203200201c864020700240f40c100501110841802014002103110f015641180e105401591500400034500a000c03124145400d01222b45805003130108030117400d0804120b030b29001010740703058801905a0390300f040310f03030100b0003ca4001c0c42260400100d81c140c00042c0c804009001040010690b001e45240c0da0b611003100c00350008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 872460908 1250 872459658 872459663
    0x90501091a0f0706091401050105030a0305030f06010516060501060906031a1504180614100c0b040c03061a011202031003030e180702100624180e07020d090909 70
    0x780d01c0c80348003625508001504156048040c0603051248a807034520070b8506201301078422017403030502d0903003204d0700380503907800340405038010010911181e03401010381c44000e1440b240c00c420100883c01c1d40c2c1c40f940c120340704d00b01040d490350554001da0620500401081c4210404945083c00010300d45009001d00d002941e0400440012001201c05000c20200740c11404040e107030f0100700220310382c2d0450040d100144114040090010b0a120141c0d12001c4d0900a81e0303c20078600b0030b40312075030350b11008071441c19500c21071803103081d01c552404204218960b00700414546c01d1400f00c80c0722240c4c2c99a400d5010170243d84030402c01c20b205605204a10003510b549014618100050020900909211032a482c000d40b49100c52a400e800d15090040c007500c143c40140c1102c0940c030040c2e08240504005812041c0400b03180400c2203945c0e810f481040f0070340c0c4042c00003242071303520038103181401071005207a500c004030814900844001d4943c41951015800b1440e140001b0039503001c0d6100300401c0e01e6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 872462158 1250 872460908 872460929
    0xb042c100603150605030c090d1e030305130f02120a0609031d1e0f010509040203040c05190e0a1817190801050303030c07140d05070c270c0309020909030a09050109 72
    0x100c03410001f8803154030146c91150400418500b640000d41004030091110040c10748084441035186002401d031440a429490a8903103000c9140c046000030003401090b6504030703a41c034440110f100c811414206685400703084989002410414150001c03c680e02c0c40d40318181c056000a0707400104201280a03c1c41440c0050402043d0001c0c0e05042c4203e18210505044c85418003442c41d000a060340d000300c6084442c214036100400003420b0040d801c8241c80c00d40d22420b501e0f60700b07050b21003049a400038000c200c40c3d80c076060501d11041c5404070a00c00150400c0003030309640c107141d00319640342e4043c521900c880c00421140350f110500c11521300d4161040280510300c2d6495424070007005400c404c0b01694890820456a80d21150800c0841c0011105032101d54a840c2039003410703040102d845e4032000c0c200e480a95148009003140d4890410300b071800c200003401e4501c1610860003400500b10094002000d00c050210f24880000940074400140c2e981d14015516034004441500c010300c109d00c40740 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 872463408 1250 872462158 872462161
    0x60e070f06210b18011719030503070305070c050613140307110904022b03021216030309080903030720030a0803010b0a0201020913090209010e010b042c10060315060503 74
    0x10b1025001242d10610081c401c0140c03000c03e5001080c483d00a80c081e1144003000b04200889840900c1003012074034030072211101211494801038101d10000b402d003810990380d1400550264042e4555034240d903000812a020b9140c1803000601003800f00c581501da44007828034403c00140000202d465117a4804001151142e40005121400c80094070407640301040482801d2602c041c58120221035180301c904112450140c10040c3c1400012a0f40d0381040c1e8003044a100302480d001040102658149400105c01113541000e0304540150340900d036040c00001014800d001601c0203d920010140c1ca0030315a098a8404041e51080d00d0100280442c00c2400104001c1407450042d0150990500000d40390501c8100041c44030b1546168488009a40745481419410500101380c09464000c0c400149035050850141141c0114031039085d5200c030200c0c840044c00c0f110070710466041c03005c0c0c8611081d400c1450750020101000d0003003000091400c40043e000b0b8101c04544400c8429985522789075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 872464658 1250 872463408 872463467
    0x60a1a150903010e1b030601031e030207050319060501080105070c03050705030403020a030b07170601051c02040504151d040210030f0e101b03090c060f020a060e070f06 74
    0x9030510384032400000032051202000c80c1c0c40030b024903240e800c000c01c040d129210a40e01800403014107401d04c0790103030740040010700001d41c09400161007161038034401c022000580c9000ca01c0c02c001030300000c1d014041d800c1401c1c0911002001c144c0340910420050140340e0b22280c0d50b0342280c070102d502900290341c40c200c1c000428091300050007214041d1066926064403600810009000741d8401c5846090481c00c2011566100310040d111020307145110b16142031a100003005402006208605039003900060817001d0901d5040310020030000c1d00506c0640042d40d410500341031f291040420381c080940d01e03040700180e01c00e40944941c0c0d00070034841607540104005c40040c80c02000046940d075540d06042c0c0a40300c02c00c00c0564400d120780000c9881d40d5412002d4840100d41c80e940401d045c1000d0314200000c90115042c0c040d14040d180540c000d0606070401c038601030345480003508080c0b42041840340b05601260000c140e95201640039030082c0d585d03030103d503007032005140611480340d5000368595 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 872465908 1250 872464658 872464669
    0x1b010c1116030b100911120703051005011202040e01080c03010b01021c030b0a090f0c09080c0102030f54090f0601031e02040e070f020d0e04180311060a1a 68
    0x10409180e0007480540790b2168017140480f840440716a140700b0707021407451495060f602c00c00d94002c0d00c2d07203024406400d05010b0303491400d013a401a24103002e41c41428400b441c0c280d6050700c1c0105081402d00e0990f580d120402034031110204071140c0030303500300207170803055500005039110321006c55850750f1190444207004070020003440d10100c3e030210002100190300e200328051400c0040c2400c1000940e0100010080c200d40b030250b002a00640025695401903a00481641c6041101c220a1035641c8002245011170340d03001d12124400d48d0b4000d006602c244c0003c3c5041524003890148000c0e0080303c0340b1440141d90f11000032685c0203d44400044041b142400280e40000060401050085289034035035a4035013092a90142c4030b90104e42005403a4191200b41e400c030b500c6061448440e0708041c0025164140c001005041c07024401d030350543e6486540c01a007202c1c005180e81c49100e83c691500501c3e0760114502184d241c4680408135142e08181d119054101c0403c0d600e40d138131000481e040c0700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 872467158 1250 872465908 872465911
    0xf1c0e0301140702010213051504030605040c030f031205090610030f11090c120606030601050a08090f0a0303020a020c0910142803021305070f141b010c1116030b 71
    0x280c141d501c500080350305044640c0120300502c420f400260302c0342c802541c0d049042c616640007520031424040c2d60101240000308407800e4035003110002c1219a900c7c14210900409070340010a8070740c9080f045000e1640c45600c010241031180020303c07047e260306082c19550350b82682c04220180c0000e204000182d4110300305400300f4444c2c21850b502150941c00a80c161004403003003401c1000008008079260890640e059201c1c208561003400c508007200020300030f01440b0f084405010300b503404a10414030800141103030400a100321001c00c25203242c0100a90410041c2d4000b600c038030010051145050030f20b10303108038110a04011103502c4d020ba43c0c1500f0498000f00780d00545a0781605000c00401d0704184107140380003c3c181c05051851040c06001030311035686201c0e141c940300900c003405502c07400a030001c407124130309210308900b65a00200d49208003803d0042c040c0f100ca07109081150190018a0001d41c940c072110800e45100400513110781904003402400b001c4208140001100d035131546 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 872468408 1250 872467158 872467187
    0x130201030e010c120f110d0203060d0f030f0e09040336031b05060708090d0809030f0705040e030703120f061e14040b060306092203110f1c 61
    0x4100180003a4001d4211160390610070005a584600145510301900440d480e068003550704002c00080c40000108900510307500c008a2134000011503a103541e4a080440c03a6500a091880101d21a142c003900340050745800d04041280c1107c180f141d864058582e138030840d05519240030700c107038551400c0020600720501d107554048000101c40c0038080d04034110061481081c0e550b07880e04014040c400584015030110b44607103010090a00091000c03019110310135030a0b24003098008103464101a00c1c0101081c490300740c0b14410910440800002c0c0702c4045400a4030104240c2c3d49108480c0e1703c0e44141071001d00850048041904100040c0e88a03103240c0071010300002d059a04c412140040c032154000c031248042407040144011884e2000c2088151001c0b10200094400c88000c141c1c03034040144100d20600d03160000840041910a00400800c040c03400d1031401141840d0241403520341c801c1581a0384903000d42060242d1002846041d03640130107210a0744007002c07070380841d0a8104030100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 872469658 1250 872468408 872468411
    0x4030c11062502090a0501121106190c172704091208040c150c02090a060e090d080a05040201020715052215030c05030a0b010504050a0e06030607080f13020103 70
    0x10440c5810784456048407458078940b0800429030140100604820054684c0f40b00c80c0c0b500c001000039020058005640c150312100d1440b0b40e25102c00002c815000e100685083c000550052481669100d03c116484d2803003000302c9504800641c2141d540c49c000d05c14600c444440603241c2d001d0100301e80401c1918440001c00100e803003240c030754840c03100b60750680390b050101c1c00c1c1d18140810081803540200140ca0981e17002c00742c080422034000c1590340b1010010340215203240100d52047e040e50855005040070190003501400c15180180d030341e07101030024000149030f031320200c0d405030401d004160003140c059000300039150400c96108401c5815027650000c0c001e0410031810704802040c0010fa00540b503da640001e1792415580040403074010030408101481e1881001c4980c1d08602035039080340094500140ba845100010b030b465209a030445030b03003c0100040000e00c44800c24035184504400c3e0b09480381900c0d455010f8840c2c02c010345040107542c99502c0002c407030400c452a280d03e002d005140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 872470908 1250 872469658 872469667
    0xc06020d020f090111010504080405010c050c0405040809040b0906061b0a050d02010614030f060a11040b2212080d09230109020a080f06060d0f080a030b0f0904030c1106 74
    0x1503600480e44000c0d001c04140c1c001103100b007259a002403411008240c4d000003406140b13041e581b898411320803802040c1c148140a01e000c000c1c002e04015a501105020304100301504042c14402400c1c1c000075100c80c4542c0c201100c1c0c02080c00e00003c900c2c050301018220f1130800c200c081c5101c0700e0090005009000b846000c40001c081801040400c4c0c904065400004103541419001d0143e007181201e103a0180c0d000d0000400004800100294040c420100c0010442262400e440151140368041210b0707071408242e0b80e00c10720741104003c01c10350b031440c0102c0d003442e90354180c10320754015614040e020703400c24051260a001c007904608822881003c0701c288040c0e0092160b0840d458100602d41c1d01c0c2c0d074400540003142010001e50001c1c20168006000440e0440c0c25203a80d46001040240075210f000c0064040100001c0400241948034400c40d8540c83c040000030010004130300c0ca58032401c08081088120b003000c0c29030502640d007590b100390f000540e685a9255100c5220001d5070010030411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 872472158 1250 872470908 872470927
    0x5150906160305030907091413031803080c0c01021f0203070507020d0f170921033001050a030809040207030e04110706150f1203113a050405010c0602 66
    0x611040c0000d102c2e8407010384074101400d40502d000840c1c0c000140c59490010a511405040e20307070241c3c462145a2207042c1c405c003524040b04c0e040c1c9000c2445150300c01550001c130400100d940a0905602c01404440d04960724038012652200c0300442d19503d441c181f1280c01c3c030141650020f65020303071103090403860b10085901140b200e500850007a42c4085110305640300b040007001001a68519068810303003804012400580700141081080c1141122050726440c40745043c800c1d00d00313141d1070202130405043c8840d881c249840700744200d42c1031000d0f05000032034685031180080c02a6a0007003891810015101706100080d4066601070302844481c1103a05800da527070303000d00090140510328142e01e0307190900d0041c040c1c070522511154560065a020703c03100418240450031100c41c0d4001003059140c5040c183c074204500007900c0001e0241400558550740070498100c004210110300c01c0c29000c1c07640706009103120300204280010020441045030b50f1042c60107103d914010300c40103140c40c0450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 872473408 1250 872472158 872472187
    0x100e07081b03100e0f10050d0c03060e030306011e0203070308130f030e011b020303031513020a02060f012c06031213060e10090b0a11250f05150906 65
    0x803620f6840480940703d050141e04071202901d508006025158411800c200704032009540150096501848404020400380400301d90468001d50300a40100000c03030000380c5d81a01c83d48100c0f03200c3d0104050003101204100741345914084892954003543c200142990100e48021001d40825004062452100e0120f007466144004480c429110700140c09085030026000c3c5008540c04003003005000c00b2040562404011070390b121500c010b06d05501081a4006030b108694540e170350300060300c0440e210b0030729a0000394a501550101c2d400c0406c40e1b80c2c40400180005a00b040500b209034141081030303c18101c1d0a046400580040503185464403440c90850140c100100c025000e001c180b008100f5150000e034180316402d015034003040c0450708184043c01e203068500c83e03507a910320b000031100520b901c112038071483c506007001540d404116a415010308465401380e22081c0c3d5500e0040018a03204c0e40984404507000540384000b94001280304000e0b0340c1000704500e40100040200507468082e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 872474658 1250 872473408 872473411
    0x409020d0b090d03060b040506040504090602160605040b060409110904050f0f011b09050306160306050a12050105160912020310020f1e07111e0307170105100e07081b03 74
    0x44003c0c8201107100d803005044d1200365100c1d2121a000300424081038072036008840035104150780124142c4010300c5e20000901c9000000f662941003c05001c00300303e540d0b0030081c0507c6c01409400f42d50f8540ea0200700841d10603001c0101140c254500b00038560418010300d80e8000d00a006442c08074604195007810f164980940c5805659507030106410b103600c1c6046051042d0080c5010540c04d420980440e0351000054600000d04101ca444c2845080c030030f40090f03002c4d01000e0008a00076a842030700c1e4041c1d2400c070340115065403c000000d5030f400c828607804818910760307940d00b280701d6260640004205a01d81c1c4160303014001c0200076a89001c2c00e00007003000f03c80e04d81010b581c03030503840d00740c0c4186020149400000c1c078007048100702103141e244801140902c104c40088c06215a038403040c454178103005031140c15001c0c0071340024909400f480e016400d1240440240101e80c1c1d480015203a661090103040d01420103000840d03100392181c5030300c0364000c0b5900c1480c2c1000300004400f000e550070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 872475908 1250 872474658 872474671
    0x1c060f0615111504021005030c0705010212011503050f0712150806070f030603080306041805070e15030304180915050127020901020a171323010f0c020409020d0b 71
    0x7070407242614003002c00c10180d04400803c400052540c00c16a0004041d0052541000100400030020480101c85c234402c4814040d4408021550780c006031900d0a80c0e041e00f442102d0038100050824120240a0301603140304410000c0d04000341d9640f0320040c1e52040035030880d0070000340d82d50800c0742c1c1850000034200240440e80003d00f036a10b0f000030000c0046019901403000c042c1003540030000140c0107000c0e03076044001110041401d40c5600d003800101c2006c000050094440c04400003099071600e19014040e484000244400d803001000341035481c480d07441400c520440d900c0541c00030245541c01307821000d120b0400211140101c3e0041c40c1600c50a82281308520313139103503045641a080050007082041c40381000e5003000141e00000c1d41311000d0501c0500068149405081c4400207817089403405c1d400d03208507885141d102c4d0401c24810070180c188100084607a07942901d558040c0c40c0c1031556417525550544a030800781d003480050f0004c1ea900320f81241c0141e43d100001044501810310800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 872477158 1250 872475908 872475917
    0x3270b0f0705121204020904110402030f0a150311040f110a09081905151f0b03010504110405030d0309020607060c031e061a1e03010305030a0206061c060f0615 70
    0x8003906015040c80c00c4002c004400d40f101300007a144e0101422500c5a001c0d0301180c051490795964108083ca0408044a90380c0c018400400c004c0b1030130003454054050509000308120b01c10b06440701c4010701d0a039010260042c1000c540c03555803850705030010b40100d1582e80340450344918080038900140c2240300d400001c1044410140451401000801c5038101d5a1807940c1441425869441d1580c480055468103e031290f80012103440350004003200f080f110f4044060400e5807035401e490190420302400e031085040070450203419607036070180c80641d00024050015411152800c1e4020a541d2900300d0b0031544c140a0380300840c5031485400004a083c0d200410801030380d07031044010b0342280d1041e81826150240500000c0e50b9000f003c80102c1e114290160744d0f010348040701c42e0585034804869840c0f0030000005c400c00c04040301a004070142e503000c54140781c0b0b819081147c0b000d01c00031210308150304840c059000c5126030f04208203c41c0a45000501c160310303440c159000000c0d41c002e44d030105 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 872478408 1250 872477158 872477167
    0x10605121b010e091909140a0309054906050f0f010b0a0f0c02030604031107140102031e091e1e030a0311070e0a090303061203270b0f 59
    0x1220600e015079941e102481c00082e4a107558001078003001d8060301071645450041d9814900c800700d40e101b05442a0010840d08100301500788495445000d00710071000100002d00018050400303080080daa90724076444010008500c800c4d16615100c41c4a041628590312020f031294100518101200daa028150129031441e0085608146910161425100a2603040104039100810b03040e220306a88a140c00e420342084503008031645a59008043c0d0326004880a2000b090b4000080c8924100f491003036456040da40d207c0880030b1820440200e0250b0810442c8000c90042402d110a0703100084c10024108400c0c407003c03d0340d50150303100c0520009107800c0d044c660392500064884240802d1050140075914120101c0e441da461401d00030284400440d1002034541c09220f010301402c440702d0032110524204000c40c002e0b08103800c0a0300400d190070340100d02e43c203088610140064040c0c9503007048000c0b081c0ca00b100d038101e400803019000007503540841c0900300400185000c0494540980e203c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 872479658 1250 872478408 872478433
    0xb070903120519020a0b06010f05123c01050d0305210a0e21030411060c01050402010801151710050607030504080c01020a021309031412100608130602030901060512 72
    0x16042c0401d00c3c010365004000e41c0000402881c0f0181d400740c400c2c40d0a8001e10b646520079141406426145084000002c0420807503e42d110040c0c0b0611b0036514103d0413251050340740b0494010587e070200320b04c0352840018071503824288002002203200303261044c9071048001104200c541c0002c00b094030749024000740f0210600a02600c0814944000601403210341040401d1050076110880960024003000050034801c1010f01203214040141140355202c003035038044d90003000c0444007240424403c1d000070039212020042d10041c1c1c81d003a00ca41c411078152620184018800400c28060480760303400200d200c2d2250b2020302039442c42504d949071114103004849040c850303a06c1d000b40c1154094120071f000740c0d0b03840840d60346111194030300164805807820308aa030b01c4100d82c81004510400030b41514a0001c0104840c842e040c00c0f4000e40c000b54440200b05c6e40140180c40001c1500080d904000105159500864000b280c0c0e20000500598840c0032030b62030f03011003c8403410354115580380c104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 872480908 1250 872479658 872479687
    0xf09060a020f0a11210a08151c05010f06180609140103030507110301061202040e06091023090109031119080708090d060e12070503070b0709031205 65
    0x300405186415810840701024a0040d070003100d20b02c81c01c110341008200b84e01001071181d880101c1c00c1004400319000d03414100601540000003903000660100d00042c103400302d541d00319490040c014001b0144820150901608032000c03d005e841d9556074094250964400d407150000900d1900c02442c685180000c1d480f04076610b9038800c9001c0f03400c0c41c040c01200a5040e0055044d2645030800d1a1142002d04001c80581800c155440d0135600c1c00c50045400081e83d02d014030381358400c81d814448011a056110b4a0f03071815240304901e5405016040b29800c2185c01880307038000007248d0340001a40b44605500001010740303802c2d9040e55150b480809055000000525214083e00108403540c1134a1542e0302c09a100c01001c1c00d1680046154010800d01e50200c6140e4000100402140305450070440d0051810440031190b40c880e40c4148003042c1c03061020f80c0c44150300440691b080402d10b466002812500500400402c484882c020000903070750305242c1315038401790380d43c9521500c00407203002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 872482014 1106 872480908 872480911
    0x41a030c190906080106091d060103140c03031c06060c1a18030a20010614150415022109130c030204050a090e011a061219050f0906 58
    0x40c608134150811003d8511418041101c054550141060200784032803818854025000404c0801d01441002c090302c2c003003206442042d07400c040024255400340070344484c4080d06030400c001c201198411200500401d003441c102d409590b445400361011910f114030350403078903180041c20400100584446880444040740e84584e94501c3c00b500394100d548400760020300b5000d030117041d00014003031a411910064406024034201105001140d144084101e804060070000000e00700790300c0c40c015810359050b41c05444622420080010140d0000041241001c1d05008207012560307491520b1504500c010030000c2e0505071030a0a4000e80615030042d640004d85040010700440719400611185650300020010040c1c69000444154143c0c1e00058218509226070500d803042e00c1d40d00e940104d03c1c40c000400c0018001581001d03140b045178510100b1a0034000d05c94110400c01559 = true := by decide +kernel

theorem cover : BRFrame.Cov 872302158 872482014 := by
  have h0 := BRFrame.cov_init 872302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 872302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 872302158 ≤ n) (h2 : n < 872482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
