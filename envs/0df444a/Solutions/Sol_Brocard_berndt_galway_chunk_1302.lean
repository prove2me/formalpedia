-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1302
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:15:57.238727+00:00
-- url     : https://prove2.me/submissions/a8fe7ed8-df83-4747-bdd0-6e3ff678e2c7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 233992805 ≤ n < 234172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 233994055 1250 233992805 233992817
    0x30506011505162a081b030c030727020309031905090d0b010620100b1f090510020303070e0130060e010e0c0904020706060b070506040c06020313090c 66
    0x40118200010040d1038078080d40311060502c04c43e450943d40b0703480e280f21185180d0207500041c04400000f00c0d002000c0d01710610079070620608000804d00b0203903d20712103941b602600d080000e034040a4200d1401c0d00d0348a20420030400103e40c125030481c0810784006015900601212140c110b5143c028401c001c4541000c5003811040000500040d042c0c180031190403105c1c1004000340c0b600b010f6400c031380005a206c041041001c4043c103582e20404040805070590312100714485586541e6101e12506404401056160220380000340804000d07204440c014100401103041c1d0724404415640079485039600d50700b8500c10b8100444810181c012034141000a071014000850f20071544d012144c008e000f40422111b10302051031114003c16440030400c1d02c500d80400803460701000486800b040202c1b0016162005c0d03007030081c01003089810060309200d001805d00c1c00d000d00000c4c4607111707611440b60070441d20b4480344202d03280d000d2a20004518841100f050142c820f29800900342429a8640a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 233995305 1250 233994055 233994067
    0xf07090503010504050a03080703060503190f0c0801060302030c0a0605030a0518030414040c0201060b03070809011805100605060f04090f0f0518060108120307111c1116030506011505 80
    0x642101d030140c070100c50942c8006d584404042d00002065440081b80c00d04011041c50640440d40311041e520712104103155203e4200c04100c41007014041e96034114030074400d0b907074840701c025008054500007030340700780304041d0740701c00304e1609840c07800c191591a650107003540ca030280b2000c041c000141c481c100c601c50f18040c100f0030b0082000a4001856905261a400061441408125940b88400404590402805000b04450001220780101041c60846a141d0720010780a0050040021040c1c1001500b03910500384080001c0c4180346a101d85003c0100a94544c2005014032500d0740303402c54050244410030080d4481e90045420000d6404d002c502c000c0c2450600040344c00c100e40080418440107c14280810108109805064640010000c4076810808000607000c0142074004011081c591758041c1503050001d00386541c16644079014606110300c0c00b822a000d200000001482007950541200400354001c000b126001409401e060342072244682110350320004c4807060040c10000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 233996555 1250 233995305 233995309
    0x61206032405060a030807030f050702041401090e21090a180509070b0f2a0601150f08040f020603070203040b0708030105130c17060a030c031202070b0f030f070905 72
    0x100789601104a4941580a0314001c109821540d010700740340d010798100f040602c0022000801c6425003909401c0013000b2000d035040c00c0b190b9200c0c0840094011b0b050500e140362103803071030b140c0c075050b00d428a0090145030310a42220756114001c00c2d86030ba80b0744040d60400d02824141006106c0f5040c064003010300c10b92a088000e108221030100110040d03500c0e41007002e02901404080c028143c5190001c0c030785414010b4242150040448400390001103090800404016046041035200caa42c191005582d4443c82004500c2c0c0020503d004140304800c1d0920781441107048611440d4881e9a030000303003101e074080c0482038000900718030a501c4200004200e50035484041d0140901c03130f026040d41d941c100800c2c0400345413075541c1203040508120341a04043c1d00701456060045121080641d250744090004044038026030000c0c0008a0b000d9000c030911140700310701082c038402a0206c803041ca6440d00043c00394864180b60302c48402080c80400e090440d82854550400c4c102c2c60201903580d21600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 233997805 1250 233996555 233996573
    0x601050c0613060b0108040f0b0c1204060c091e09020a03020906031009060504022b3210050a1503110c030309010b0f030c06070609061518090c06120603 67
    0x107100b40707407208464414003c00c100e074018544602828600081c141c01c3c141d0760140c02d4004003038020043c400c020006102100940300343c5400c0d0000060529981c10310b07080200c010400081b42c400042d0030f446010036810300c4007100034000c0031107104400c051b03803030051030400941005208001701034081003004120b688000166005551401002c41614903100c140b0303044460315071247e40500c0c010f10a03c140300b070858014104403031291203000c00800e10509400010480100e048502d25107805400702c590fa0106035405d04000c04152030003158075601202100080e1911409601070f9186070140030b002d180140d80e024580c61410003058445041d4103810554111000c030395115070011042022400c001d0045540c900c03010344800d2644010000030a444514116929001d1500041e16904002955001c0d4080030b410250400002001d0001404041168032541c6039411059120300d000825500c074180902d90302c40404441185480e40c00d592001d004144203034801d0b56141300001041c6a00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 233999055 1250 233997805 233997811
    0x50405060d05060c0c0106080606010914031507051b0f1903031512030e0a141905040e15090f100504021c0501150602011b050f07060608030714010b010f080601050c06 73
    0x1241c4c4607110000c0e88042400c440241d40800c906500003414003100f81d800415000c1074800001c90f40646c1072510010924040e2510710408061032103e0400c0000e95004016203a0030f070703641108858001c209410b15503100101d84002d00da40c0c00005c401000103084940110b002ca20904000c54410082c0031648501000f0341d00040740e031f01100341800b00f010350041524410039004c4403080000781c1048001ca00c90590098014041c110131440c04082860120310746004103002401800b0580c00360701c81540740c03881881c0700c0702d60034501e00c04192404e8020a50070000c0c600080140745a600c242c8000024000240c170030382c0c001410004a042804020b101c030045540a0000460609a0008000c00c201c0c050f42c031100859241001a204111041c0d4101114800c1450314640741d07441105203009901c208130008068901d000700000d60054007001814419000786404e103e02041100980d00b0303142c0a81410b4000380c141c0d0209280c281c06529004d401081c185001c0e4240219150041e203020b00076 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 234000305 1250 233999055 233999071
    0x207021906170a1404140c150403060c05030c091504080f010606020d0504050109090e1207050109050606041e0e0f0a05010510080d0807120207080403030c020f040204050604050405060d0506 83
    0x3908514050701d058250740c001c0c0300700d9410000410544c40201c1c0300c100107031008200307804005449603000300405c9440b010720310013028821110032000c080211544580300444009007010b0000d10349030302600170741b48a146040001c501c3c1160b00c00412000030041c80c4d180d0983e1105200100c4c81c40401c00148094000650000916504040019240131110700152041200c204800d11480c1da008104004a9605950114081c480b000b9040e04102c0f942c98221820303840400d641003486415088040024000d42c00e4841a481e001c0510080d04c1c0c000c42d1940254542d00f118000203000d41e40040341e1005040140d5002c820114503103414103012100550300e03a0f4651091018a000c2d07a480c12005243c02c6004044400d08284003500f418070082c000c1040c8503001c803104020200d160100c510195009954507130303440d204c2c40c01410604c070700e103000c0e40942500e4102c1501c9041504c200d4046e02c00c000d10080c1070a1802d0200006050002c216a4110034004038860008604005890080f848 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 234001555 1250 234000305 234000317
    0x7080a08040605150f0103050406060b070309090f110702010e030114150906100f200304230409050c0f0607020613080d09061d01170705090109060e0307090207021906 73
    0x81810300a00b42c0708090a514403851128081346810307662411003824001d030a0801068590359420101c004000c0baa104d00c45480000031101b00b0194094451010b55100110401055484043c0c04c0221000d00d080c80401c10001c02c010405580900095040600300800100b08004c0301020707110b40040907100340d0440d02070400d07014010700d40010b24961241c42520001c030810b445500040c031a110484101c024803d081141e0384c0d06004143c0c01000301d006403000c030380e95150340fa5018190b220000521607a9010703083c0160075546880e001e16296203401c20020b286070b000da00700700704102a09400c03082d44613800304150001a1580790141000c1c5024949000c2c04a14010b515820583c210700c41d2000c21106650620a040e00088402d400e030b007603130074150640607080c40142c40344801290420304c011150003c00040e11b90002c020460a2001c0ea601c000780d07561040e00344c519124107860b581d41074204850a20a40c0c903194007078007050340020065120799000b40300c4100511070355000390001440c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 234002805 1250 234001555 234001561
    0x210a051b011701050d0503370804050a081317030a02010c08093003090a020120070e0a15080a060b092710060e061203030105090a0e010207080a08 64
    0x40000c5000c0100c64080c00d00701021001166401c00c224014001e40d8862081c0c00d4020060110030000d562410318040386401d4032040031661817084502d0b80302505035080070001950085071203641001e0089074040014052202e841d0b5030412103800c400307540f201101c10300000203030810402e8130700c504a540800180d651041300c804004c2c02d50f0341c030061039414030011b1800e2025400000800310a28000740c0150b010008015015403610020114a0002c140f00402030154a140100c0c0c403501c0303c1d100341c844400d40b038404081100368451500c920030701908501c40c10042e940c91100700c19440100c2d0240000c0c02903811030b95008d450b4080d048481198000300d2071504000007407207517180200046590585901e000ba807031038582c0c0303841c0078240fa040302c10240c54800202c1c200004210015510818030400e0348403010320800a0045414a1044d8030450402a20000c080200c0c0c0c180d03500500880c515a031001c4d06040500805407100303486660801610300412030905c054103000d08541c0d00e4a082d41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 234004055 1250 234002805 234002833
    0x1030b2404030c170712080706111b0111120903090d080301090e0318100908010c0e010e040501050d1713091d010b090a0e120d0c18080705210a05 64
    0x3c40c40e500403003401d2103000480414031100164140496078064690300110005280802c81d80c002d4810041103030f824511501501e000700c0d0080c01001420782582c961401c1c80310901d5081e02c02101003030000c1502000b50719000c60324008100e174080451402c880c58180f4100115035160490780040d540340c0c03004801848003004034007518031444810300086051549072000308244145640d00c06101d06c0c1084031001015008011000c010607002000700840803041d80040c200f00030054076140020b40c45100348026141500c2154181d0f4030280071028094600e50f120b11360010030008007682c9a1041c0701c4043c40100300d12041001e40034654001c81c58032040080180e40d007a1000d40cc0341c031079050401c5101603846c2c0c220f009500c020005008680b0900083d62603007004a80f001c5010011070003d10030020013643d8102e0000b13001c042d075030961461811080803600d440d41c0d018030b0302190403200c0200680d00d0f020120708215844220300054100e6071186903840c2841001c01220140c21000c0046205 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 234005305 1250 234004055 234004073
    0x70b0406051e0f0a020a030f0f0e011503110d03171317030f060907090909230d170a060806070806120309060f13050303040b0903072301030b240403 65
    0x10ba00240030344412030070f0109240600c1a0700605401c8529408981101e40c039210340c1100385101080348080042e110030b818801e004d03024541d01c2c060351f5801c18005848050510054000300d0f40c12104e522900d128440800c07101d5094100103408114002c0c48490322101c91550540c05071032000105403100100703160001140ca04014440e150520905c10000f0134074008a01a44c0100c0848540600f655020000e03184c4d40d4094001c880d801f49494080400c100d1412100d81e80c00a802c40c4000c1a01e818801c07a0790764000b0500c60300c002a605500394019a1000f000454014684400115186840b41f44082c86d041c1c00b2520800081ea411007405001d0600c031490b00d40751803140014501c5c1c0714604c0007042c02407142c00701d540c40c41580001c6055200064002c4400906002015251f94580e5100048007a410450025100340609100001c0c40007030010423a0b06000240c0039440d1b18002c0c0b80056004100c2c5407a02c0341c001e1070300f190445420803020701068100c0c8621512540f0749046041140c41c13 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 234006555 1250 234005305 234005341
    0x31b0604022b02040b060c030a030b130b010c1502040e19051609051903050d1d01020106050a030b061807020a03020f0c090f04030e03060106050406020f07060e1005070b040605 77
    0xc4248002c1c05400e00000d0001c60074402d6016100410b1002c0102d021400d00d218481d00d100c2980400708482c00269819000b240c1c840703c08a0743e10948090383d04105080301c66044200e800b08000c04110350001d032030f0440342d580b08140d0309001820f1603516507407401510b4040707508107000074000d5400148042907200307a680000302a1280d400312030070044081d188400e64001c3c5807041c50840c603000007509007564404003665114050b189030244a02c00501802c2886011003d00121a0040c04aa52052244c6000c503100140124110380c507549841d4107800300504102d4103c0141506000036460100105010394515401802e004040d0f040080c28079040110703180f02a0408443d100c0036541d500741154004041500d00100d07510346143c2918403a00310f40085805010f801c0c00011459081005441100c000d41c00f602d4810420a2815458103881e0180d0808038011100d8103403541071014051850b003606043c040d1400300340d038446c480114421141220380c103032507004110510400c0da104040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 234007805 1250 234006555 234006589
    0x6012303011508060f10050d1b0f03020109081b06030403051204030509040b0603060607020105030603030c01090f030906021504230a2003060112060506040b060d0f06060c08040e09031b060402 84
    0x2c2c01d4100703220081a000303414405d441c82140c90022368804d0000700c240c54500074810300106048145d88109000e8002100d05c002d0303012035041d0700700058802d000b0600050400800300c120034084454820000300303402c00351050b001c01900703004c0c1c44410310180f5940380c010307402500c41c42c2c5c803003031440300700801d07501d03e44600e6000c0c200920501c80207407070f101c0944e00c2d250340c242070040d10707a503c4401003850f5010f60805500151f08050002003400345c003801940c07129010344d496541581d100c84080ea903441044032000d02148072000014080b59417a107405036002040b2a070040300f103010728ae04504d45030140c0025241d079200c1d05a80310b84038941803290382070050b00350041c107815850485902107900f4407075805031040e5118400205559100e903c40010814020049030f22402ca0607244c00040c440012410025881c00ca00410000c4c011205000d140d60301004c420318003403c008290301c0c055006006901148020f00c482c1801e4000c840191284240d8a03005148500d003e0041000c05005105211 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 234009055 1250 234007805 234007831
    0x9070e070e040903020f160806040b181605010e0d0f1103030f04090204171504060f0207060219031d0709020705120406020d1202090d080a110f0c0a080f0601230301150806 75
    0xc04400480c2d400e9010750002c1c004bd0450b80ca005030300456050710140d5120b54051243d4580c0146d503078883e6041540c0d001e980300d2034011400c400384980e0841c554005841c041030a6070000020b2120180c0894403440a025a03080c01c0c6001383c0210b498020381c01c0750b101c258000c035040c0080c2c80440c80c80308440034084020140006211195411907001030700140006403541409031410007240c0440c5c407250b86c404c408540c0e403c240710092489000c0c8202e180c00080c1070548200003486e42c40988100c81c100d0038007600f03000340303848101c0e0000c3d40451011286800341d4903520b0b41c02c0a05401420040c035484c0c002e07050380021140014507191700b0b103922010f2107205003d008080c2d10b13111800c5110950000303151361313a5810208169103418641c440c0062601c22a11070795114040854140c2c088482514610041c0341c039415080e8655510000c07502c1070b40d010308010441452440004011103046000380154611203401203800e696001105480c034844540c02002220000c0203001d40c001c1c0010010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 234010305 1250 234009055 234009059
    0x61c0e070302131a09100f0f0512010c0f050a110a0302030903060f070c031407060515100206010b0901050318030a050307140c0a1511070606050111030309070e070e040903020f16 78
    0x100c0940140c503c0b040e40100e022000041c00061262500c00103404e4900c18000780623920824402c00f0866401000d005035982c10b1800c0e01604140203148101500d81c0f0b5070709510f051032104a5168000510302e50401041c030ba20f0700c00300e11043c071545508a01941c0030350f0351281c1c00d83c203041c902000030b0102c842140307214041088055001440b140c02582c1443c0050441110f60780d40c000c280101400680b15520740018014401d040380454420f03a003041c0c0d248400344001120607178032081c007489010840c1c0000c21140510350f1281c0001c540c0010004034900001140700c00192540d0084d41000b00420000002c0c801e0490700f104081c403203d030444509518005440311413580382c0c1c4c50605d00914a480b000c0c1000e02088076038004002916049140c070340ca808503410108042d01c00c078420325001c80d9483d00a200200d00100843c0e00c6400e540000b0040203150802d02403030f44000a002100b004044000d8041c5a51940200207185000394020405010400c2006003008030402089200103c0310b101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 234011555 1250 234010305 234010331
    0xd060b030f0a0c060807050d1802010905010318110301110301082404030c06110c0f07050411032413020d02030412020d09090e07030203070e090d0c08030105061c0e07030213 76
    0x60202510003e03c5c10418170303240e59409075100c0c01800541034066003407c84074000c03c826100b20142c400c6c000d980c1d00e800d803540d82005400f2220301079511050045c1d04800301c0d0205200048403880e5680c0500002103d031804170460aa1350020b0f00621025040355084c481e1025922000101d030700301011a018150401d550b01910f0417000300704c0280101d84510b119002d29126505603220070043c0c005803a92043c0d0130900c0d03603d0302c599015140c41189400902c050059907102683e1280d43e00841c0d06002c2da40e01180c80e11810401d03424a0b80c480385101c80102801c4003070024040f44c480c0c00c4009a103d01707240c038043c91840d440005007003c652100400103015648070060700200c40d9207400004012103022482420300d01c1c19000a50180b00d0901c00080c1b0744404640140300d182c02e0b4040d5402d007042801e041b01c103450710711780c0031301000da0038801845a451300d0b100170b004221514421445c281401d803040d40c141e640c095074017802074002c00b5080096041c806c2d41d0700e00f0b208104030200980402201 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 234012805 1250 234011555 234011573
    0x60301050909010f061502070e060d031209080403080304110301052203020a02090c03010315020a051c1e0204090b04020304021008070c050a080a260a0f020403020d060b030f0a 77
    0x10030507104081d00c070081184010700b940281130942c000a024004c05840c0d040c1c0c81410003415814000611800c5070005000300e031000c80e503006071401071509000c0b0307400f600c08484103080c214503030080c603a945540c2c1002600c0c40006000640c400d1069984919080c1032030404105580b00880c0603034180010403605c040c0306000c644119400000d16961079001d070904034500300c1c540d00005c0d005001002842200b00040c4080e40c12a4495540c1c0c961405c500340110050b0b0066003240307008980217000314100c00c0c540385100700382c21414010020312401018040d424200c400d031031048420350f00007018001251180540740a040095a0a41c95402c00f03501054902c0c0f0b00400c87c404001144020030b000d076201e40030601c0c07131541050407145445014240b1005944c441494080031401400340304000038000c441064a8203000d030100c1102e90b4400d034810010382107194400604035400c010110040c0e03292641800700c0b82c001c00c0c2c00907000b0b41c0c5005151030a211408040e844c0d0744810048000104002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 234014055 1250 234012805 234012809
    0xa0312090c051507020a0311030106060f1707050f0304230712020d030509030d050316080103020607030f14040e010f0e090d050a020a020d120f140d05190c021614060301 74
    0x20350305044000d03a032500f800b2a030191000c020350142071048000f060010131260100c1e44d0408030009c20009940b800103845908503565100b0210701400c0e0150040a00c00140340e0f408502400c00398a06003603083c0001c1d1a40c0211000c4984214045200740c803d05401c91900c859199500186013060814101c15543c03407100e00000d11540386400e1840415100f01c065070480c001c0503084652048015130b0103800c54104a82518900c11110b1610f42e03440e208140050480341c01810680c50700c615618104c441c134400059400502c00640d000b02c01607042c90008100401d070180c4124029410096954501f83c0903500074040c44204200b80b00520304003080c12041741105040c108e0766080c1001086e0f0500c41850b0001e54480a411a11000e001d09001d010341c3c459038036034400ca1a960a600140e9180d121078807c0401e40e04240034044010f107013036028a4020300d00380b400c0703070a0341e40380c200c082c0948040a002c10010380010034096914162048040301400715000d003840303542860340203e0f503d2b000c14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 234015305 1250 234014055 234014059
    0x60c080702040b0d0b24010e0108040c030b0a0603050c030604050d0c1a0c03040b07020a11121c051c0603120e0103020d06060e130905060f0c040906080a0312090c05 72
    0x403540215074481d809020340c100e011346808011030035824824105a81100c94001824402c0400700c0c0c1d000901c01425170201c1c05845844840d003440380110b580c481d00030011114440300c1c01002c80810441c10550340301c0c00c07480d540414258110f281013410080c48d01d9035230b40a540140103100005501203644a070030742d42480c040300021f0782c5003810320310200c0034054100150410360500c162945e07030310b0042d8441c5010f091806182e4890340b00403130703030303040403c00240070040c6100142c240ea107031031310114911541c0e1174201c4c3e40c510740c003128010600c022680c00388085000003e5208950100300c0d1800d408100d21002000b040d80385840350680c942100810b40708110b22220f8004003a8001e0b070680d000c10f218039204104560f02c485020b00003144140000d803207205460003a111b00c100c20302074840d00703c1c0e00001614480d22513000c0e0640c00040a8011442c1d544213110200d0203084d42e00c103e0f0010b184a4005000240c02c40c1000750146070800e01030741c081400d00d1844001300f001c0d00d040404613401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 234016555 1250 234015305 234015307
    0x3011d06180f070b210703060f05090f36030a0e090c0315010318110103051302060702040b0d050d0201060e011505030601081008030c0102030406150305060109020f0702040e030d15060c08 82
    0x10240d1090700802c00c5d5030700c44180da00c04e405003c021035141d40b011064a04120010810507200d008002c1042000c881c03c480103031078640001e084202040c04908604a100341080c0c0c3d4010f184021f044107200d0111001c0310b60701c00310f0f07040398162744181100c07281d69050b1610300d058100060b01c41128480140880c004942032a840c04280e40310790f1000400d40200030400c5050b220502d401c48808a41046c01f03800641044042010900185444030720036a005204510308a00342e801e003c003901414031076035030149404007031401040c000d028015100a240e0300000340b860030b020800301880380603040101000205540c840000350003404a0f0740000090800907a1540e80c80d1079030000702c01940203240742e4000868491035004054000c0c0d40070300c2c42010180b10b544028840d014408000b444041c1443d403100c001009170984981c01420b80340812070f58140740c1000390700840d040c0c0e409044036050903031000030300c412000d5075071043e03281406420440f480828a482e00007801ca00c5170100141c030701c5e00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 234017805 1250 234016555 234016567
    0x11030f03060109180c11010204060e0409020d0602040e0115140301060e030a050f010e07081204050910120804030b070c0c0b0c07030c060f090920030603011d06180f070b 74
    0x801034480b0300c020071400f282d601c220011302204002401e00000380401040f8030341c803000707540e1078103000740c4041d120281d484162014445007008080c0c40081002e9030400401000c1c138002c9901c42c0002e10141c10b51070040380d05549426940c481481804880c0d02c108503a01d00380c0b91002e0004412681150802c0c035040d60781c00c050f8800a400c0190f80c140c01001071150140c400300c0d43c1410b4000e240c10000100030b81319044c4e505e4400c0c41c1c85403607d110050401e14104014809480c1102d08960010b2042007103400c00c50b100c41104a040403006416100800081410400c00c28040081a800100c07407900c00ca05800a5903241030050250280c00076001001c01d01c0001e08404000b01001150800c2d4080b0707070f45e656204064a00700c02d40d07880c0740000c1e610070404211010640141a005a04010156107041000342e41e45026000688480d81c10354803050142c1d5050780e1100000407441140c00505044c1c144118240c00c14400001e80c000300e40c010204071604d0800120b10081203510424a87d0f40c0c2e49 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 234019055 1250 234017805 234017807
    0xd090f0e010b0d0227010207050a080d1b051609051f0501050d020f0d050103020108010b030420011202120709120b0c030411090705030702160b07110a08070905090d11030f030601 78
    0x8000d001c201d1740413011807841450f9458104a00b0040d440080c0c095034081c41d105d100b80240034181c2e0080d49142c3d840014041c0b160ad00c200d8070340d40038280490f9074507801c04040c0e480174101100400403100000c1856803d101c40704440c421a60440c1001d9180890f010000e514428680d10900c07659040c4180810080d00d100c01c0f42e0100d0b00f10304554001203941707090340d181d0b4600512007800240c0c000307007140307002050740401001200d004a81008400c05903010300b001d20302030300e214041c65504100088503504485503050001e00402003040f2120800b500e05046d00510399100b42c0c3c4801c00e0245a4204000032800022041d908114241c0d000350b41c0380d0712410031032012000f40c1e40c041e40001c1d100c020015500d900001070340c051901682039440f15007410f0b9031400c060303440f07020320364010200704541c01c0012400248900c012901428018005544220320390601d16668441141c1c15260030420070300007800d0150b140369032541e00300b620f0188101030300140e1300d00030000041c020481c00404a1101d03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 234020305 1250 234019055 234019057
    0x20a0f030b0d421a0112090c0909201017180f0f060a02040617040203010603051617070311011101060305100c080a050f070309030908030c0d090f0e010b0d02 69
    0x341d4441840743d41c0c810318502e00d0340c5042c1d02010705044041e01e04644800c103c242100310b00c034040030503590680e07410241d4204500074026510304035500344c00c10800285400f810b00421012a0150074004500c1041c800701010f03150540001500c07032400c100090403102e4203d03c8072400e1240341c0034101c4643d56010b00780040314902400003401c130f1080107051207070b40d100010310190120b10300060725010746901840d44140d010b10b00820b00891114980741200c442201c07492680180000c00206076039a41e46c691031704003859107580c50f04200c00f0b101e080c032a6035181a00411800504401400c0703c80c590785455494250310380000d4100030780440f032940303403170380c250071040146404c0019100700c4042c000801c1c006200804400000c80c034540c0004402204030310944d031141105002181a80e43c0b4101c0403401081401001c0b007c1c070002d07030f10100b41948204060451441c40c00d008250559840601410085095000b015820381c0d885040c01981c0003403100a0458555002198a40d060204c1032070107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 234021555 1250 234020305 234020363
    0xb150301140a09021902070b070503030606090105070f0c1401050c070605030618070216050f0a06050f130b090108091b04090309030f030306050a051e060703110709020a0f030b0d 78
    0x80344c0080b4103c056078800354001000100349030205d5a409035106a40c1e21a8000c40fa009402a042440000c80504100c0000c11145d401450711524150896494040420741e00200b80c1d80e001035502d0500c00e0010201500d80540001d00306a0b08001c244250700303039601c00394081c2c20104000032010864a403103c0c0b8002448003030019030103c4078604000c0003551101a06481e4409030ba00d1540041d150a00d010506080640502038070f075110304001d800d950b0303503103c0c3d0002c41080b6010841500a03007400c00062000d0b001c5020b11542d80c00e2201c00050075003034003404180443d0810003a8919019000ca81c0c9000800c080d5030100311401c140c00c0070398440b21140d201030800c0140a041108040e85a480603060fa041181d45001c41600c0d08140031070294441c000340404990601e1103526440c004010300f01d000e02c01d150900d0039645003241e19003050825400902400e80109003044019000340045242d6001841c1c01c200700306d2880d00040c455036400c000941030f072849000c01c022650704d605603a01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 234022805 1250 234021555 234021569
    0x50112050307062f130b0c19110d03030b09091c0c0807200102010c0e0f3d02060601020109030c03080a0f18060506061620040f0b040b150301140a 64
    0x19412003a40c50006259004800342c01840d10101790218050034500c2c150389a00b0a400700405001c0318000705610b0f040041d140a039144100c11094a40030399403403500e80c1c100c41c425900414013240700803d0016065000d8078840e05500a4140e203074446c1d0504601001001840c40c104521410307a00f00a005481038030302c0a4230586036210b45900300107445808801d401001c1c0d0080007441c460040c11a45c0030700c150f4400f030340100021500803003441c00d41c064104004002c801c4e029100e0a070b40314950b140e228442c5060180c40300c602d02d80c1000381c051081e241c0c400c9003800244400c1c1210790f001081000701c494010244001e120105030070910300e40c030110001000130001c0000140300c4040011048007540708440702c43c00d01c00058a5410300c40280d0300c495004401c9981461032980c1d0701203403070700c500c41c000d03207100324212081c025a6030f0741c050040010820701307001541210220a12013901d1301c00441d0b83c01a03000e400c406500c2d03d000d004a030b044440b2100005680c240f51030001d0b540441c40c0e40485 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 234024055 1250 234022805 234022871
    0x4150f0606030e15041e030306080105072c0d0b040f0c0e01050a0f051f3006060201090b0c0918010308040f06090609050f060706150905011205030706 66
    0x21460700d802d9485a030fa1903545904803440d2050704000402c1c400301c01c80300249100303520341801c1006540a030310490980e00c24100454043c4c1c41d01441d60840740101e4003400000c04030345120300004001403d50f808095414a503120050441c0b020a51081104800070b282d520b84100007800d000c2d4042d40c640c41c1d660b000c0c0c5904205039442c10300880c1d241085c0506c51250441100c0000c1c0340c40024a4001110380c003070001204401002c8012405988001d5040140190107180c0d0045404481c2c441183c1200b040041c00001500c8528400b201d009403c81d070207581c9030500d103001180c0c009d00b009501519842c640b40c0c0d1111608040b554402e0048450070440c46220000302c20003002c50054000e8500c60240c0b580420f0352034601719214040c42c401c03a00030488142c01070000c1e090081200d12510000307005140740000c1340d9160780c101d41c0d598190511032600c00c64280100070705401014014450614085800e108a80351651203106080000b0900c555582214842c255a003c414a20b0050300c1406 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 234025305 1250 234024055 234024059
    0x71a061903030807170f0a0b0303120105060706061a071109010e1b0d0903080f060102010b241315020607090501090b090a09090f0309050901030f03030203090a05030a0315090506030604150f06 84
    0x11b600c2104150748400794141002e40483c194180007040e105018250542c42017682d21b41070030301c420341e070040c0001c2e40c007540c0f544c4000c903005415400c0d10b1403411885c0741c0b1a544d05e0341810f09d400c2c0181c2603800e0520801c108801000f04110300b010080d003100c0305000c0110108903080c008551407117410f034915071a600b410341480a140d0030030030380d52064100000160b52a500c10004908860074424020382c8141c1c001c04000c0001150041503071406032004120b0b1900041c1c22035400540e10f5a80105c10b02083c01200e015200e50501c0501d030848120b0814001590038680081c0004490740a43c03000043e011071080c84558810070710724000d10320301c1001c100344c3d64282001510004081070640c04110701c0000080c0c0c0d800c0007921a41201c1d01f11111841c440d1459600710084d45c000f500d951680c0c4500b008841c041001800101950501c1ea2400680090350b40e01c41e802900a650008200500d445d007000b050381c81c086502980310f035208204101c3c400302e6111104c000c00c5400811108240342c0a80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 234026555 1250 234025305 234025321
    0xe0109140a03260708070207080114070f0305010e0a0b0f0a0b220b03041e050f160e060622030b0f0105010305060402180103051b071a06190303080717 66
    0x20300075042d0081c0c1da0078014041d151a11014000380701c0495003000d60700c40000f00039510502e10030f50400400d1041d00e130b5440d9500c2c0c200d82520641c06685820383d0b251801d0044032900f00d280410307103d400e0305040c400743d071504034618031070f40008251044003a16074401400503a02e10400322010000140845001901c1e030822a01c1d68101149080303c0e55411201a40d0303a50403920040d007210803401039940740d43d030f941d81d5110110840485011608041500d80d00001d003052201200d0a09120010081c0700e000c84980c9403130112075401188140ca04000b44101134035030a00b20ba004071b0070304114412020641c1c800b0340344581c0b59030020b442030200c2c07024441038913200c00d43c060403141e090342c1c04d00c15511581c003000301303d00c101800d05041e40f40c007001400040d40a5081190701c0301d5100114408182c030800ca045082c2c2c040c1c4001c03964270345088440c42140c01d44001c8103070410030940d0446110030140000c000c801c5580e001c098180404000019005072189501d881180c0140085010354148881c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 234027805 1250 234026555 234026563
    0x4110c0102040812070c0b0702060f0c010b04060f030c0b071a150a06050901080f15030a1103070e01060906050c0319230306101103090405040f1704060801090e010914 73
    0x3c1c010141c064080c030340c9070490501040c1c03000caa4100000192003880d246484c10141d1203418120303081034040c0040c80c11501c024000e4280c582001c00080f51882c3e40204100486105800c0701c0041d810343d200070710110700f40d020144191181440705956503042d034100780302950041c040c810105000002040403008003c245001c10b440107030b0b580140d02d9102c510681c0d950061403001c9000608800008014181c946865070f04202043c3e9090f00740303003900c80800c0c01c00c110200e068500b200c032816180c02030b0500f00905c1c2c000784213105207003004e035040c104004c240007028481c4008006001c20f081485080900c2160240450449001e46610203404007400c81c990b00194020b10510f40445200c049510500b128401c0100130b107900c0204400241c01c1e24070200200201d03205d84002d00c40c01c16103446521a05004502503144620103a1030b0303140040b208014003008846842092104012013504200c0a0341592904000410f0b402a140c030014010721141c10098480c8240740b12048440c00042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 234029055 1250 234027805 234027809
    0x10b031207061b0806010f0c05010203131712162714030622080403061109032104030f02061207030c0e190501030c09080709020a08060906010905010e04110c010204 72
    0x1110078892803010250181c01001c4031407500000c1183e04c1c000030500d6104485440146965041003501040c840d186c16089800480d5080d424040e5a06c25500380440c2c0c00149003110000d09a05262400c1603164a40c5101c001e0b00080c140070300040d08810490003909040740c4106d8400c082d0b04030310141412004400c45900c07038100300c0429900401c44606000c00c0203072064045004855410200c4140d000491004400c01d0314018800c1c0404030009511b8044c0780314907400341540350340faa5410000c26003000a20010323103240d4030302e070303064180c000300351106540441c0e40002480c0c0e0300c95058000f1540700c0c446ea00196450444003010801c0d40c980507401891804000e50703691101c04940414880d903401c96002010024120610421540d80710b500060385000040c80d00c501400d64945543d40f8008240e08040070454001c2032040d522507111002d5075002c94116515101d505003400043c0c980040f5009081c104280c4018003034598449030041c803603c0c0a075800f41c0d44e0701c071042c4440768000d401074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 234030305 1250 234029055 234029063
    0x6230d050102030a29010804030f02030409050901020c0106060c0b040f0204061d0406060f030521070f060c080708061c050f0a0605040506090d0203030106180b2703010612020d05010b031207 83
    0x4480d80301c80d01c0242500c10545d01c081a145c0311f026880710b0300d0944071219440c8401046200401c80861441401d0092a01a00e0346400158480b450410000e00355466034101500b004400b2200740c2c003054508907015081600103400c1641803026002160150103140c0080c8030140c411034050b40000c44054099200700d0048404110035512800754000130407591101030413503401543c5051440041c5c0f6a12101c5141021003d858240b00381d0761504081c00202081c1e6409944a07000105d8607000481c840d4413640310b152610b980c6c6070090000d0849940c0b6401c4600604286031402c082107400c02c2081d0300c0140c8881140c1c1c20004901d0711501800084508541600400000c1294003000007008004031900f0380207582140e0030100203c50b0f41c030031544408043c00420070000f5030802036034018001104107581e502100d49204012401084049007243d000341e01d8280c0400c0340140c440f9206560560450755050300c0681410240c3c05011003603600c0d945409040ca1150f141011000189291031203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 234031555 1250 234030305 234030341
    0x1101140f120709080d120e2401090b0a060809121305031209061210030b0c09040507020d05041503020705030c0109030f0206040201200102071a10050406230d050102030a 74
    0x82c1c040c1140c0e0b002c0340b0712403041c50b41d03c424484a80305008100000c000325602500040302ca0f00c5141061500c4000c104060301280d00e014182c1c84541c445000a0252514a00521022150a0100780d10352058031a07034080041d8003000c1050603800f440b20502c08000d80b030115840e1821015003003052001441a244030348102c60000d4010140a41655864030000348200c4c1801400b4003c228041c000608040100c03007864404400200300407580c40c064801880d116032a0001d0f001400b0031503070040c02004c01d5501070b40801b00100e0340141194143c6503100c003409000003031514240c010340202c0310f0003851404082880c100c0a14150702400002d8026541c0718020031000c002680ca807207090390042d000900c4441c101d004c503840c81c81034042d030880c10800180b81060513154520300b60580c54a2544591426080c0000e0300856030242000d8042190b0800110317103018150300e80d1107050303103150802000015203c1000d5842115420403250044002d543c1e92908240210040c10080313403405d9000c4d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 234032805 1250 234031555 234031561
    0x611010b060702040e1c12050c190f030e031209070e0f0109050c0c01090f020a1703090f030708060c0d050a050f06040b0a09090b06210304031101140f12 67
    0x4140284040180d02a06051800000380c0074880a01104c0201c84024410001d070000c10070b0704060640f00380786003942d030300511803950300c420810b441000d80f01d82501c04051105504040082d02815607070a040d081c1021f00c8c1400d41401d070080c04c1c00c0200c2e14420f0001103450a0140291103d09121b0070120302528a216204d00f401c0c01d42580a8400440751241c1c003005100703020b2140d220f550031040c103a5416003011504d0050382d00359443c0c4801101d00c074603460507860842c24030035211000381c403c0cd035410400445142016940f400b90046030303032154104000c1c00382c090304c0c180044000b41401e03400f6603603a8070b04414034a89951200803008019450a40002c0c081880ca10805010b0708540d10150a55110381e010000941003000c0c050354443c0e4459000600d17504035120b0002c40c2c80c422000108545880810000b0110000f0681c25101c00c0405000d103403a4400b004072070039241d003c880014404a4000105c62543c0c1c8542c1554002c03400150b01500031103a200640320700c245410090f03003656 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 234034055 1250 234032805 234032837
    0x4051e15070f0f05070c030c080c090105040209032505210609190b06040b041e111315050d0203130210030c020712020d08030a090b0a0e030a050c011b0906 68
    0xa0644040b440001e4400200b01121489100101069030040300d00a04407510394035200c20010043d442030b107884c0d1020202072821f0915010075401001c048030214202054000469160000c5039208070030070149401f5080d03240d24007850f07180070b00005401100d207028813050303460510b01d0f0b81d103aa9081c0d00c40c41c00000e00742400040c03101c096865000322210440c0c81c0d42d45803078039080060b003101d92041d102d099404a61b02c41d48160180c400302c007030900e424220a01a44000c84440072002c14507032001300441000800e003000c82e60300311500c4142e00300011401c10300840b12030144040b0182e44600001c1400303d801c9001d6034100042d80220b0384440d00500d40c03401901110741e4100240301581001030300700250280252880d185030b001601d0107040c10b0190b5624441a8021243c008001d030391500700030144400483c40a501c550300c000100070851846074140d9580c022075809000308100007808404400082d084041006102c682c40d200743c00310402c4c0034155038828003440c1c0000d000407601c100b0754 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 234035305 1250 234034055 234034067
    0x40212070302070327350102090a170601030209061503040501140f25022401090e03041a1305220e0114040210050c0304171b030d030504051e1507 64
    0x226142089402505103010030003d11803c0709030010b0b40c440410258074480401e082010389550019800041e038270a60f1404000458005070020840541c1070005043ca0500c0044c0343d40c1903c1d0119044001a0f0381c8a00180240c2c84400001c2c45481c400300a1004010054105402c0d00307196003d460f2480c0e8607415800c100368801c44000e58900c644140f01d401300a1031040b1402c000100380305a54007075a04015800c1901c0360801200401d594000041001c00a1482148608400381000e940741c6491700c402d415412407203242407400c4a00c002180620040030b0001c10004000c00b41c0940815001800820355810f0325981c1d540e0680d00345605170b4909a4180b14004940c200030603041126101c540900c00b094441e002c564003445800c0054005100040020304004c1102e00d05110b41300d50362a031007a0a0600318200219180104820035801e07a40c041081d009240c01c0f46030024581e83e40d820110318140c1c0d0503480207002e14000644014048000c10041c40500b008800c1c24501d0f241d0704000c03100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 234036555 1250 234035305 234035357
    0xc02010f03090c0801060611070803091005030c0d0903020307060b0a12112704031e05120402040902060a05070201020601080d050f0310091802100311090f0402120703020703 76
    0x80d020560100c21540280d11801c6140e0180703c200300a00d44071007965084941e0750b0011408103a003456104020300c000c01c00d44000d0f006820207107042185120100c5c41105201d50030380b00340600800064031140111054503484816841c040c8402030741d40c100a034403640001000d071a914104107079103a083c1000a5440c04946000c1d100d2008203015484550080c44100507499100e00c1078080c40034080c15599060700354030000c0110040d54207107454081c6c51070403940c810100c8403001040b0036941c1ca400c0340079036100b217100c0007041040c0c0e07a652002800a1248140081d4050008208a601154800007800d0203034401e0302214042d98842804d42d944802030942d072400150b08100c03058001041d20702135174001d03501d21020b0000f940c03145218016180c080101c00c0f40750920599510552030b01c9008068030405c01e080c200451b4420320040c40161140448050061410a40d40c00b02612070390304941c4442088107028140703061991005000e0351140070217600141c1003411085102400c8003074494 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 234037805 1250 234036555 234036557
    0x90d0309020609010f0203090301062c0903030c03130b04061508030906030703020906040806010b1e0307020d030e071a0405030105010e0c0315040e0d0207090c03150e2e05040c0c0201 80
    0x8200883c0100440e20041c4c8002c03400210700060103107c045071024010348010303000c0d91601e4105203102d000c418201c04051880260303003001407000c0c07020809022003166046040300e040d5070b035643da9000170501c21041c10200103040d01104020030041c008a0f074400784907480400303170081400d42c0c0c81d1403540d524065110f103580e10845c1000440c0c070a5000754010241d04074003510050801d682c42440a0a04c07200740d00903591880d0003d000c3d46c854078103220101400d01c02d02c2000d400c508043d14000d43c0d45113040408424156503413803000368104100000303001440040c0340e203941a9100d00f9410055001803180314020740c2003200205250783c0701d0076407900c2242c51090540c10b41c0d0301c0340d03c00130300d041a40074003a81003030f030341c1d6040400760304148100e10f000f81d016001043d10900c4c01c0d0b050310845510140d800d00301454904100c0d08003441c12a40d100322020a5458a03c0e03480c4e02c000381c0e041c480191850035001a6070000d079545a41b030380f03217500d04446007102d08004410108500351002e0002540081c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 234039055 1250 234037805 234037807
    0x50901050405150904030e01021c1707050f040b090f03210d090c031109060f0a050d1a07170a09030c08130306020d090c150203120a091a090d03090206 66
    0x40041d0410350b02c41503001c0c8115a078180a0048200452442c190541d0182d001400364a5406501e5804004655081c0d45403607884c0031200700b180004103213611400d42481c03600003c42c00b1031001d61080c003e464503196040a4141d50f29501c610721005540000305142c000c13a030b4007003045824038000c514094100c03c035207140c414250400e60aa41a5030000c00c1d040c40343c6903102d1090000c51032441428000d5440350311590540880d00007000382100700184500d05c140c41d44440f58500303071a032141030002c0fa203040d201c020181c1814030700000002100824601ba01e0540b07020004140c3d44692842e2401804500d103103001d881c0d640b805c00596100c00b201038046511180480b0000700311500519032083e03034650302c05400c0e03120f6072100140d90010751580460391703c55030200c06101c0e03070380c0c011401029500e202c28141c121041c0042e44034007812850b4400301c46c10710005220100240c115070704640d803101c08070425206070225071181c050300383c80c0c54010b485500b45480e0214024860404845d400800407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 234040305 1250 234039055 234039059
    0x601090c080f0408121005010e0306250e042d0e030415030f060620071206180506040b070306050607111002010b04060315050915010501180518060108090106050901 72
    0x21034188014100304d50b02c1c40108940340d507090f44914020302482400034503080c4540f400f40010210030150306150b203e40c00920a00062006494010701092101403a400d91494824400e481080781e1481054000e4100b904100300482070401004880206248102105102d804450102c4501d04080e84103544104030a010100c6202c1000740e542c1d0271403401150007500d01c1025809c1c0c1c2c500e0707402072005c503d2126031140790110604516490941034001007043e2403030000c008143c2001500c016061a6590f000000000110107122004a403c90211030480c1014034000c0d104100c100c0d64040000e18041000c201e51810f18100d41d143e41c1c0061a40c0d03038000c008810020340c124580b500380199036842441d2241e60301c860203030800440c002c00510703401c50504006a41510002000340038250040c3e08400004103490a10034150350080c0b0300503a190140c061241070b03ca0b082d40042c0d604c14150400328148003017545000344a124280d8510702d4544130410301c14203881041c021164403002001c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 234041555 1250 234040305 234040321
    0xb0c150f09060408030a1b09030c1e051e03030a0e0102010b0f0102031b0f0f0102041a090d0f03172e06020307060b03030403080f0301140a121e06050106110601090c08 73
    0x9150000d07041c1e6000140c1c0c0510398505287c0c205081e0b4a038000c20142c2a040040c0500d1110210040580030061001e40b0203004407000c0300c00850041078491624407241c0c0c80030b422a00c88204050001908995450040310310243c489048085518019802c00400603420700308040e0ba05803011041c2c0065040c803400055035840c19030019aa0300d01880741d11f800401e900303000c110628410380c1207000140e440b070500b0310342c809103c1d1154483c0d1295204101c00f41141c0c86074030b200390354140c00201e0b01000a1042c5401c0711a282110010001e01d00c469081c40360307000c0300000c030030703106070262003801021041c40d079051001100038458030700036800038008000411035940107a2501c0000400752894591250f6504140d900400703804c065001c000301c014003950300c0041c44048032400c1190420780c064a8085060200b004a0400800704080d6002e04c90f82d150a21000207901c60307218800340700070b45c0c4a910080c60026000d405215132300c82c6000010350a00544159000800300d41d80d406219616003034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 234042805 1250 234041555 234041557
    0x6030b07030b0d06060b0702040f051303050d02090a03081b01060810020a140d050702070e061f1b060e010b06030c03070e010908030a05120a150302010e0103060b0c150f09060408 78
    0xc07007250003801e050f5202c0001421407052002070090891950384070b0115005100440700041c0180c5020b40c603000610503501482550200a20352600d0440c6d80c0f2040c023841d10707012740203011800c0d801070240400030040201101c043c022602e00d01040d000c1d05001181d0850070382d8040e110307904058003d10520b408404030f540042c0b004850034142000071008102c1214416448002400001680e90b02400152541806501c000309000711801d16a4100440015514400d459544416104d032108544195001300c0c1c40c0d900c22494644000322400682c2420b9002d8410900c1c4100103501c1d20441200900e000c2042d0b074040c032410103829040d907179040c40544140140002d0306040c410386c00301c00266460100002c0022141035a50a074444803010442c100e000d20142c0903c220700e0920f00716040217450b80c90b134030381120340900c0c06014001c800001a001011682c210052200000030740302e00b121030004100291600e0403e81700d045079181c0116039074940c0262807039100c1c1e400000116022a00e00c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 234044055 1250 234042805 234042821
    0xf0601030e0316020411090a081b15040915150f03060815040209042f0418031205180a0b04050c0f100503070203121e160e1c020303130f050406030b0703 67
    0x8901078a0f00170711f84005030190049a102200301da1000740c1650b21500000803c13900c0b004299001180d801c2d1010084100740100d000c1e21000564500b0940b0010039500b035040020121072040e280d000600365801003880001400000c046414100c002440d010300081505032281c20f12280c121584446c2d0030448030220250096403140b00804030700d1160040e042c0c80c0c0035442071008803802e40c8241c82c07081c0000e990103e24041407400510760304d480886d4010080403ca003801210000b0f00da42c034800e4104442100e020034071014883da41c525000c0201c00740c41c4a01550041e0b04a0b000c074240c1301c0c00c10205501c42201650000c460b450400301c3c841c000c001035a0045010300550b0b04150216620108255085910f40c8030700151112040840d0035040c5516000854144000108102c426018140706103d002c0d0781e000b5070000d101d42d0100e0448c4030a915074503500609030b0795550200340280b000c0600381e020380852114807400c00140d900d810301c602400c480d0f1140c4038031400e0b5500402540140003203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 234045305 1250 234044055 234044081
    0xc040b0d150b07050c01021506040504030903050303070302070501060e04031704050111210702010b011b080702030703060605010f03020415030c2d020f1501030b060112050f0601030e03160204 84
    0x110814003101e092405450042c114081289466500390706015140951030028541550000c03140c1080d030607007880841d6030051040e00e01041ca80c54614040f90484851b0303001a0070382c0004424048040d5150f001410050b015400034422f080d00c4012801343c408090b06c0040c0400c0003054003084d00400b001c40301d50301c58010f40000401080b175003034451443e0711403441c4080b07607100491800030301440600e402d500000e1610007045940828030020381410003980101411501f031401810411803414121040e5940c09001c1d19005640d0381351610142400d0300640e800705460346210031081e44a03100b03903011505445409010303521203400640080004d40a18000c004403500518544100f44a9281e4480c0409011800c3d148620100070700b010151006ca66040c0c0100300d00a0302580072003100d44c1529001041d0302c600d5160300006980b070f08440800014101e00301810400108c01070003000b44555000e0701c0c1802000f24044e00d9940740d1050100c01c0f9200e0b001c041c0440c0140c01e0944c42204a0091 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 234046555 1250 234045305 234045311
    0x151119030c2102030403290f1519030501050f0c0706020d020706020c07030209010b0403050a080306030f070816050409050319050f12060f040c091401021507110607080c040b0d 77
    0x303010042c1480b01c000c0306510160340b00080c01c10801008102e0781801d06641c2900d80c083e0550b15840411900300a404200a04014008903850140c1403a01103800c80c00107200b600888100302014a0711074940c40142c0c0c407940380c500050600131170303907105e54400e10460710680e190030b026a841c40029040303e6248103419900f8000600003505520007000c071503209030014030480e4038510400c600c010050704062240352080c00100002180000c90418480e0b0013800d45440350380e16800b280c501200c02105040034841e240d000542e14102040504110052440d10201c60f9210402d010a403000d07464018100e80c81005600c00c0c2c45044004094803281a1030514a0120004035030401d68015210041c4040070343c00034010585441c1c1c1400d0340072001038405000e0102f007050043d105030140e00c294400c0070390700c0d280942540c1c0709000c600b2002c1a9000e140c039480c240120000d201d030b01c0e010701d50b002c10b104a5020580bd1400740c0c84240c45000705440692420b4204aa4a055a00801200740d90543c0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 234047805 1250 234046555 234046583
    0xf1207031d031e0f07020402030c090d1506080c09070e0a080f0c040608010902060301030209040f05010504230a051b040f02160c0e010e0403030e03070507151119030c 73
    0x4281d03000030700c480c003214011500e5003503105405524004410f03103083c0b10a010044000030701d00c2d24003070355030382501118016100e94a1b2082c4268070302c100180e05521100410300c107010400440c0746905a03208040c02040140d4940403041d540d90403404e29940d000b40c100700000e80e0140b2450b070035601c546002e010340035501c0d61881040e203018420601188035400032118210107040903c1100001c3c50344500070300c160141600441c04a00c8103000c040c1c0078400d014000303801c0c001e2095a400381d4580c010000c011500d01400c0c000c2c9070580e0500074071110250082000b80000700050507100154000340a804000600c046118231482c603a01c4179904203840d6581c000600d0784501c05040340701c1e01084419010881c0d46030408504400da0403000c180f83d074032001403003248074100f80c260740590302d0b041c00a200390755002610300d5401a43c000034103510a0b928003080041807c1c1e04035a120b15581c503885600005611030607203c00e0381006001d80203c0c1d1160f110082841462540400360084100320000d00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 234049055 1250 234047805 234047831
    0x60a0306020d09121211070b340512010b0702090a05060d1505070e0a030c050103151e032003030d110909150a0b03010e0403031a030d03060f06050f120703 68
    0x75003402d140c4022032081204004801c00c1c5e03028001003130f8102c400c440d1038222580c1c0d0700c50004c000130307242d01a9400030f9441c0c0c0b440540c900c10600300d042040101003004080c06400103015904c240d07d007007001d081410000544500900a0b1000035a0040800e0810b5a0b0300c0002c2c0002e0000501c020f5000e60b41405101c08501c001120360060103a0300f00105071031801c40d002401440b200c000b01806140342d58000c00108543c0c192450950380c00f460045800741ca4000d82540402c100e812045215591000d2694010040e4051f40202c038131900c00b01404504003c0280d2400850804d140d0705074104004042c0500007a44c882c44008180e41119402c110038000400c01c580c50484168580d921043d86d00d6007640340c0f00255a00400484840c140740d076060103110000c280c4060720040616494a214981100c1c010f55403442402001c0c08a82c140c10b40404020080c00280c410720008000b9000d0201c0c000b40f04200300c7d4090841c2d000001d1070050f13885044580c541006018030105036484481491030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 234050305 1250 234049055 234049073
    0x3150b06040342020306090114130b01120c030209030f010c09031e0b180610030320120d0605040b040c081801060305072402060412050a0203040b03070908100203060a0306020d09 78
    0xe241003e4010303100d1030000d0178040c0321481a08450748401c00c049443c000390769240c00d01c41d030200201c0b4003c500b00909400580d40c001d814400000e4450409418000040c1d00d07074041c0c0000c041c04c90403104401721b601845822074403011844400a009202e09201091214a40e54a000c414405000e884c28882d1505d908680c0140d0f5810004071113800610392051007007011b5900152006208411245141c3d0701822210794060307141078213a00104004d09486080c8503840ca8654103028107680ca5440b14402c1c03006201601890380300301e00d0103600e0602170078180320b107658805d00c039118010207480c3c0300c002d00001d02c09000c460000e5901c90001100080d01404070070001c010051088a514038102c4040580c2c808005401045500c86070402c404079241005010b980e01039810419030743c82c100781c0c00b01c1c1144030320340101c0507843c1c1c00010b0005843d0321444010444801009440316003901c0083c41d801d921065403600d1b40000780602c1400820480d900a0030904080c81000844102030356403c2d4503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 234051555 1250 234050305 234050423
    0x1107060e0a170f0d030b10080402040b040c02010b03240705160503070f020a0806060901060509030a0209040f0c06050c061501050c15060a06090605070807110a03150b060403 76
    0x91074100d06842040d0711020420320301c4e54680e90900b030000c04420380200d001000b05001e82c0342001808004541591502e91085200140217030060019080030b9402a0103011410f5100d400f074803803082c0c000e85c0c07034401e0207400805c404105450300540d2104581110a03801552201c90381c003103004a21720001d0801c10081600510072502c080b00280301d40108150040554800d41c12038016208109041d541e00880c2c07810b4a600381807103038488180b50003003850000b00d848002d400c2076162083c00305102c03140b500380c1e80c83ca2280aa0303280440c0c482e04c0454541c00744440104040c1c2c00107010510106a00000f540942c0c4185411810202140c05051030150398190010005001c402030100170b00b084c00d4410003502c880e04243c80c401e031808400911511070180042c0044a02040d00c8007040391640c03072407015174401407180d45650b0b16400c00c02003071408540a058118a450b202d0060742c00c01000307690441c0d81045030541421000c00d01c0c03141c9112015200c1020401c440e005003104428070001540d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 234052805 1250 234051555 234051599
    0x6010905180f060109060f030b0f07050c0106060302091207081506132d110d05041707050d1107060504120c05091e0105031b0d140303040f03030c1107060e0a 69
    0x10310307500d05a1760000b226001c0d0402000b41c1284071081c80032030804107029401440e03000f80d032512569994801c98444c002c080318003219508280300020241e5043c0c010300040c13030048982d0180710b444452503541c0c44489215070341407a0407904000b0100718014504903407203003019214410b85041c0c03180f240200c400390b40035400c500940041e560310170442c60a800c11050000602080141e0041072860220300903d03402c00071050300c43c8001410403800d900203c0344005091b85650320751440e441c15680362044000180001010812404001500050302c4001c031180e07900d80300e1034607041440e10304403106101c1003902c11050801c2c000619442d0050f1080c450a86411250314030b00000c00d841550f031006074002c520a52110304100b44551416a01c00c140c0d54048500f02800710007441c0c580302e190700190207a0090b000101c1040144501d48081c1168288241e808112049a0f148240c41c000c62440c00c181050b40b007000e06000703481c090702480700c1d83d5100904030310715190b441c0080e5880b403010100187c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 234054055 1250 234052805 234052813
    0x1270b09040c14010c0c050607080c0601090506150304020a060806041508061602060919020a1a1b0a120e0d02190602160b0f0a1407050f07060c0506010905180f 70
    0x3003e03c2242c1c20707501c20f4040900c0c103a0703031000039a200d85440c103046010301440b4920000f0a42c1c100000300d41110031051140c81568042e69480f141d40004190482d0701c00c1c041c00003c9504201842a0300843c1d102e02c1d4020803121109081180440304010002c0c1602e800070398400054401109007480c06008014840083c030b91392501e0007009042565000c58082550704c03000500250000c04103401c0d88a0350325454012800907180000f0717135907040b03d0344003808043c00b000c3c140d101511150020044e49241c0c01301151050510604203596040500c40030b82101340b02064000c40d00c2c0b0400c0c04200f1000c00400b2005007191980002d0340c900102c0b11007004d140740c03020b0200041d507014032022405640c081da403004107516107031307d6804034030684010044070540015580c03002da00801611060811900419440700c03414a01160743c2e480411821480d071090410005103103104035880b5200c00d5103c0301905c11646080000c03006050b0142400e9003011036182c0c1060142c004000c030204032034000c2c00030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 234055305 1250 234054055 234054059
    0x30605042c280204141f0501080402030604061119050c01150e01031401020f0313030305060a0b040b16120f1d060f0a0c020411070b0a0501270b09040c 66
    0x70303000030034900601011a0400602103180c0404031291198442507640340359200295440014010310030098440d041800e0394080c00f03000b5046c03c078204070f5418048010480716480f6030044d80c03002e50864000394543c2c00f86001800107546900154541e101d00c210141c200700d803000215040d000d1310a0b6040010f4404181034000e04070034042d541c4444900c6e8038050307845040c040740003011241408082c043d1004140700714101d02d001d5044801c0d01c12454410b44c0c8074201849032031030200c50454150002410172002c41c055141070190b400c01c84801241e40d500d0146040251a09500008003001e0300040032003440c0081094000c0150301c4070900d81d80d030400e2111583d0050700c0382140d0105081070782580c07085071010352994001c803035170b0300800030f40e80f034540c403000c4811a000c0110800003500241400d500c2c10040105d04003070002107110380c0d80c10f2260317901c056031b0104032202445005071b001003d0b01c26042900c290300340b072001c0c4134140202261004c2c4103404030784205c82c260340c200c5a01c0c95160741 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 234056555 1250 234055305 234055361
    0xb0c0a022b120603050a0b0403120c090905070e091501020304050d060b090a0e031804150e070306080111180a0b07050604020a0605120105010305130501050f06010801050303071707020103060504 85
    0x3082d4079416244200f0001d00381551191650740355180401800005100c0228042c0360280201d4800c4058010051060015400f0000d002007214400c0d20031a508080100f480300b40622140c04110b0005850900d05503501840c183c50040701100b42415400100004140c6032260007400f030140c0d001e00c0700480c446859406000300c0c4c0400030800b22005252170111115600c1c048112511a03aa81a902441c0b090000000e0001c20340340003402e500110040c0000703410300901528a2042d4a0b40e00c040212035580da10b10340c00d0b101e071500c03c81000d113004c018240c950001e4400b07203000681d018100c5180c154032001e00600951200005503042d61241c0e041000314541218148060805842d1003800d0009080050b41c00b000180550b40c145600c500020b460402845c1c041c1c00020303080b0307000b44945c1c20b102d0f030980b6104206840582c0014880000030550f820000205c400c0700e0362008000e090104e024039400c0081e00b190000b02e0402d5114400003d943d03580d801341911805502821080010002d21 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 234057805 1250 234056555 234056567
    0x20d060302030712030e061b1b03010e0a020906060304170c010e12090607060905010209031006081c120c0e130b04050a1503080304050a06050403020d090803070b0c0a022b 75
    0x80844d10000e111030f500ca0010b0307403007510300b41145030a43e402621040c42c003058214039140d00e00128880c0c441c01d88034a0742907a0260300400b00101c2500200804d40c1c00c80202c50301c3d586060400b9401c0b100c108003068007428803e001b10b03070290090340032000c1803072842030f00c607074a5000100006444c0e4468504052904003802050003500d02104650716000002d8040780c0359005151014142d5552914450305029003034040314145000242a02e03a1407068010304002860103020340006803148000380101d00e9a050000790004d400c644901c880281d40203d40d4010348440e18070302c1c0c02c000c0da0800c0d44600380ca500d19600446020200081005a00e0b203040c402299801000d071602c0e41e00f003518000c028064504003401b5690000481507170381e42c0340c1c10031919122520034014922860038081005059021582901c0c039842d950742c15120325170b5602003503581c0c0a1818060b01c0c01c4070000120f19400f24100003030822924030f0042d185000c00000d6003000c82d000ea21803900c1e11554050381c000216078002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 234059055 1250 234057805 234057809
    0x1080a1505070807030f0f0f0f061202010816020a080f04060e0405041527050d090915091d120406020f0106080303070302090a0b0a09091817030c0d020d0603020307 72
    0x40100820301c1c10980c014001e6101070405000e1540d1101900c0240311103801c40f1400d25420f007c117101d81d00b401030324a402010710b5030b45006414540040460000340000c00c1001243d016502d010142c1c4807880c1c03002c0040d400b500c2000641c81551880341c00100c181000c0c1011b15807460f1a0b5844038034050f40501001c1403a9495842a40350404000010f01c1080d02e45442100e5500d001600300aaa00001c02110580c1d00c109000f080c40c1444500308440050b1208010a250365035858683c0d6884030030381602c45640003012000e078140c0f018422a22241d0006d03c0d89508441c854000602c041001d038204001114620001e880018040c000e5540420800144802003002089110300d802c3d541c41d164040070340b1450400d03400042500d81c85d512003900d0f40180400117843d80e5241825000070b00603c0861181c3c0d039060f800d0000604400180191a402e82600424448a00c0742104043c0300c1a0344001e018580c280d400340035130103080c3c155201a000d019250500010001d0443c010940351005503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 234060305 1250 234059055 234059093
    0x9020a030f0b0102100c0504080f03071b0b0301051005040b1c051509041104020c030a0305010e13050a020f010210091103060109200a0912050303180706090b0c030405030601080a 78
    0x541d01d42e0559a001542c42d89038810150002280c11000c80225034611403940100f03202e2180707114100c003012000c4010304c1443c0c070442e001030581128450415806004e03200f6100010010b000410907424140702d135903403a11440c0b9000740b82030344800d20700040e07402040907c1c0d0341c0081d032820085031889600c92990403001d03031081180d910b40c10900080c0b09813801000104140030651482000341c941d6010f0f41c004520620680b9122012514020001c000074851078411035001008540314540341b50a040d03003941c004c4080e0110720741c55000c1c020085024103440341144500000d64075406140d1060440140c411031810440d591032000701450a03406030807817142c481c0340070034001400d501d030081c1460881961700e020352a480201020b40e1444039641c02480c50000c807820ba0300800c5004402540301d5602c03001412115004202d02d00c2e55280c440c000c15011450765801030080d0482c0c080a820b03250806001c072403405468002181c100700080c4d11041c8036a0040e42c1000c10094211400f2500441c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 234061555 1250 234060305 234060311
    0x301090f050901200c0c09130c0b07031b03020c13020403050c030f0c0d050a0203010903090612060e010506070c0f08031c18112d0319020d02060c1609020a030f 70
    0x8620048018601e4402040f840c0510009105c55078a005008411440f0380092000c2e4240c0f03410600e502d0b00d1840301004070b540410040000c41d200c080001559085609a900c0b00d06541044500f01c3e20154040b10503401e503c5a8078040750b49544412403201c10003228400962070b40d1071490501d103841c00490003184242c000348000238003048009410166564101e0b656107051099041c1603007011a40600a5099400e00450300c0c145600900643e0841d041641d601809e490050051001c44401d401030741c3c280609a4010000352410304068050507008000e050720542e5108807220310083c0940c041d01c016080440c1e4081039130301d070328169a40d04120040a07c102200070710030381c103d6000701500800c45001d040b41c02c011500c0340884c401c0312426041e031227250188459036150303200450030225482441090300400c070200c951091000510b42c060f110303021020b4a5401c016060304642c003500c00c81e200300300e01d80c03140c1c413200c180c01e00060880c400c006030354401c200c4008003035030000401c0c95810340c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 234062805 1250 234061555 234061571
    0x5040809040f02041d1306020a0f08070807081603150305011a0111030910171003050d0207060e100225031104050f240d05071514070602090f060301090f050901 70
    0xe80403178000201555094645541c4107000070100e8140c850015281610110390862034640146607044ca203400c03a1101001039a44c43c40031140590100c40c41303800280740e0004501c07807400700c40c0307000303004400e6050100d85114828070100d5100c040783d00684150b03441c0d1402080c11a100303400c94680100a290808000c440880030b65079910600c0802030281790302e0850280124410a0615450901441c00c1c0904e42040c150f580410405804151494002d40e04e5488a480c0001003200498009840d072009002d584070402001c8102d0301c280070154042c81c3e00c401c1c1c008c1f80e403946c042080c0026600803446a404c40c2022061240c200301b01d180128501800d000707850300031003690307944050007900c891000240c14807203c2441120b10010780c2c1005080319408200000842d900059070030000c800303040e00604541c111441c098255202e094403104000c8080030a1090300184030450f405010b544940c426080443d00b01d5000b64440700c1240c1d0f070f400c410400d480c07444c0510394006204400a000c002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 234064055 1250 234062805 234062819
    0x603040206180402040b0d0509010b030f070603051905040308010602060907061b06090606080708102003070302071709010f09230d0203010204080a0201090f031e1505040809040f0204 80
    0xc415405100640c0440c0c000710605039603940c04440c00303800304544860321039a407440007d015000c00d40c2d040115508180050407030781000141c10781c2c1c0301e1348a4000d00e4594503200d000c0e4000d16019000c00808018568a119465400d02441c1c2c000e92003035551014543c035240d4000c0c2402c0000c0c1c0103010760340000c1c03c204081980030303420b1842607252182c041140f60842c1f40010090152030300c001c180034140080000d00030400300c2d10340304580d1107205551543c00703006060411100510341140041100c0c80c2c1c00400e034152080510351108040c1001443d01070503480361380711105051070882011000003000d5466583c81034540d048900789040c402d01090a126222403101320284601070b40607158240c1c0c0045640b41d01c0744054140e005070085550303a4031003421a490303010446040c3d001c601c408200049040860340450120303a081034003030640d00c00d011901800004000c209607249030003030506a0024030544115402544a980320315514031001c0d040c04190b8641010100c29503105001c108012 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 234065305 1250 234064055 234064057
    0xc0b03010605040b0d1b030b100311070303020c120310060e1e040c1206140406050603010e010306022a061b0a090506160c030f1509050307030e031c020304140603040206 74
    0x2844c414103400c0c0d110400550403a00804c082148213130a540d55080b64818640c06601108007a08140c6403407168140050080d010382d482680d11070880f620801004002c039110784d000d04030088180c42580c0460070000c00c025466003003960040e220140c10001004050340102e01003140040070b4036030b0350141145561b0aa603184168540c540119103981031040340521a81c0d0300c0765114003600c4200201600d81c0780000c040b45034190b100c2d000b140fa1040200d010b00d441000d5030304850b40c90214121aa0071650f4240194000b00900341e00381c1d0701c040035007540314200346080052003c601c006100c43d14251050700c540003030b141031400080c0c0040041d418141c2d0301003800702c00e503241510342c0c540c1d42d0702c045009949500c640324050440d0030126400300811061540e6140c02c035001d100e120750a50f07000803d1208031040010020410b9000708520400280141e40000c05070000806861012820340c11004030709030003104440068000242c14001e03c079000b600105410340a4840b207081d85082d602250003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 234066555 1250 234065305 234065309
    0x1501080405060402091b0403030206010f061809150302060307050306010e041a0105070203120c0d03060e0f072303010815011e050909030405041505120c060f16050a0f0c0b0301060504 80
    0x143c81c001001840a0000c003800406c022150110f250703503540d89042c000c0d12940207000384080c4055010300022918410300582201c503c0e1204185507040c544031484004054803102c400702d0b28454800000583c0c0c40f038000d58800c1c807807900c81c50759911303019000504d1001c1442d4510f105a191240c0f20000b046048140d1101c260b0030b080251f074940f100e00000b854030045168519440710009101c40ea0f80c1000700750035016001c65102441200e480e0301401039500012140f2003040140f0b803000846440c802c0ca00b41e02095483c07100d0740c070303904400444d48060364400d8211880d2a07010302006514400c0c0c40c49a20b005201481403545d5000e45070b480c602c6c50168038403074030384211440e001042915800f17004803002803e00030810001c0010200316803801102c0b904c5100c0c4280d5901c485403040480c0411070508009008052500d00fa08141c818142600540760208009001251081c0002e00410407803002c41d010b040080d41e441a1413038415954800344e0008681e5080c2400104003031134020b41030b901 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 234067805 1250 234066555 234066559
    0x1b050606060f0c010903020106030209240904020f150306010e0d020618130e15010e0f0408130801061d060d031d040e0a06060e0108033408070b1501080405060402 71
    0x6514051000d1615860041c0341000c60303c0c4d40307004201030400d601503111804903803003518400b40c1c0c0d0380e5101c0c68442d070744107000003400b0b40c5039010784850151a141c000a17501c6880104040e80c1c0e00d0340d1a001c201303001d00c00344882d007039080c002080c404190b030000e4400c2c0e0f0900044440d404002d8095020030068000c001e030180d89010465503039030343c55136054a801d04110303082e1002c108034010722000300e41d50b10007800d0040b241c0800000218400050b410000e00c540c080e5180d40802c2d440782d070303150002584240f1103c41500c481c0c817130200c0c21480a00900d4020014851030980c11510550300c0d101000024004511581d444005040044e40140c2c10b00321900c884071640c1c042400030000b0501411034000034820b24000d01e000d080410601c0d0380301500703a6501c60040c40301c80e81c07640e01480e920310aa002c0e85000d0480e62000c15540c2c80500002d20003070121240c202c480715011b0f030722590150040d840454408040c4020822039000a52042c401d0600928049c40c0340c0c181a22055140c0c01c000c2c2001c0c1c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 234069055 1250 234067805 234067807
    0x6041a0a030b13050f011a01030c020a12110d090807090203072709060603020a0305060907090506072d120c0c030807020d050f010212090601271b030b011b05060606 72
    0xf03005400300b040d03603000d00c980040a440b00002c004480a001705010940303402c40e5408001c030700c04194403a104042c2844e50f01d070001c03c43c024054842121031400074a181041080c054101c02206409000c403488407034480e100d8090701401d00030340a051440940040004910600800007400da000110a5160402c0001d800d442c600940480d000603c071a00200c0b8501e080640c0050204d500d90300030b11228031665000c200940310b180030840750410036560070002608800d002d000d50700e40207004080403486404100c2a80044440019040038031210030300c00007084044c43e0050085004c17141881c0c08251815003152141680e50001a61450201804605012402a0464441c542d850007282e407c04101e402c1001c2140e00f1034041c1d403000c0640304a500a981c0030580340c0400044032410b8070311001814150328145103044e10150f40f0821202d904d00d4035480b070340003542a500d0403c4045142944c0220380804043e001600340f40340e1681004105040d44030400c0030035030100b5013580015080b2207407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 234070305 1250 234069055 234069061
    0x30316020a02030616170622020910020d0207060203030c0f070f3509060a08060312031003060b01210213090509030414090c0d110705010e0606041a0a030b 68
    0xca18020741110000d405214003000e01885490304110448404600d5842c0e600001c684d40c0d010500032015904d1540118541001ca07030300a144020051901007208801400c180c801000941c483d001d910100d0091307000402c02c10342c2940d0600401000d00302d240011032544c00c04d40030a69143c0b05860402c0392103240414031104000700340400d0020f540e000034561201a41007280d650500b4600e001c0480c804c003e980c1c180c1d00c081003100a45150040081a050400c005c0c2017050b1030b203000090004d64940911107410070390000002c003442c0071b5070040c07040c01d11040c21131801004803400c0700038250500c0300410100f501156128984000c0014034030004d07807240655082101c0e103400c10381101000750b0618040101d1004000b02500440c0c6c0030740c0c807414004006006000010300c0a80c1c2241c01914108002c0c0031000d2950005440c0440c2500c60528010060700d840342150100c0100e4002038003e8003e00c00c152415011746174240940390100700c1c0040307076040001c0905007280f000410707a500d00000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 234071555 1250 234070305 234070307
    0x50c07030c0816060e0f010605031209120304050d050c040b09010b07031805060a03020711010302122a3702100f0b18011508010e1909020a08070e18030316 68
    0xc0750b0f4815903c01c0c0d0074040e4585440303246403035200d011580f007800d40c84c250740000d40345800a10350107101034016030175240003c1c070341c18080146410340b140b031340a1104010028443d168911601c0a240c012005001c2c2c2030301c144204800d4805400020741304282240c010b0000d201a24200c0b8001549401c0412543d410110b6a140700d9010382d010303540c032234008100d0517181c54268004110107840717101e954544140c0d8100540c12401150760322070308441f6000002d07000c106d0b5851129984401c0d1605403040c0a00b0004205165001d100c00601d04600701c200a02c03082c0c6810500c00c4c0e1104d4a0420108054002600955401111348426425915001c882801502c2c2c0ea0061041050103010070743c5910168074041c03681c4100f8030079469101d0302d0043c5040358034421680e05060b1842448081d03040e481c0c000d4071029102d120041160151f0340c03024002d0040e80d40380180002007540c0800b0f0203e00b0300e001401001c02c08014078030140d04040c1c003441d103c00c40d0040202d170750180340d5000c016084210741d40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 234072805 1250 234071555 234071587
    0x40605010905040c1709030403020315091207060b06040306141501021b0109080d110708010c1b02030c0901030606050a120c090c2114071803110d06020d0b0103050c07030c08 76
    0x10b52002e002c0074400b4420406c1c0084000c00580740243e0880315403011111610b0a0b400342110740c01ca80760401d0000c0c0f0044003a20780200513040c0581404200030012000044103680300d54401c6607a65666440801440e0142040c01d9104203080146148041440d00203512025842d04101c40b2020082c2100d000b82e004981090150452008641c405100800042c052042c210051030f203034032a100c0300040c0340341d050041c1c502140301680ea85000424540300c007109604040c00481e07050041f81c0d0000701c00d031581c8510718000e41c0127070b1000c1080e134a0714080c01103202e0750b0340102581031440380740310002c680800d0780b000445010260000d03001550b0030048403083da000000c1035a40030801641640e0040c580c0101640a07107a00c0d11039080c2e21112000e0710048001e00442032420350103007080001c0750404041400343c000240240b91040200d5940070f003244d120a02c07911072281e59449200c81568503121762940b01114080031450294039440107001e812407460014185040040c1840e203903000c40c9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 234074055 1250 234072805 234072827
    0x503061801181b0509010c0c0e1510020a080f0a05070f0c050f06072301020c0102160c06210507021501081c030c09060509120f0d030b040605010905040c 67
    0x489400e9081d615810081c0c40510821402c1e08010300703000480781031100004458400d83c2d06519441d1819a1000065030450002c0505440041e1826000500d411100784128880e91401861403011001d5a0800410f4150102d044046500459941c0c0005c0c0c001d108031020712005c450b41903203a00c0d8030300f002c88951013803840090400191b038202e03030200301c01091000244d41c411180c048a004014050040701e005a83c0043c0070070303a010074250751411010b22645d81402e00007002525089800f080c1900f6640410402c41201243e45c500e20184248021a80041c1050b03160030039a0701030040514141341c2d403000f816912181d80b1070106140d41c1c02000600210b8091861010856948072140c6440d41303103031101c210b05412090580034117240301e4882d10301d160b0300948071104546d0030290200c9058000600294002c442c0d404150f0314442c04014500900d8212002050200314115004041c0d580487c541030099003030030340c14800c030f81c0c201203401c0684a0a40380000d01070021041110140c0500c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 234075305 1250 234074055 234074089
    0x30c04021b0106031406091c0f02010603050d0504030302071707030201050f120115020f0d050409090510110406090b0406020d032c06060f1e0d050709050f010302270601050306 77
    0x2507000040000c1e0441404100000c5006c0d20401d64134022086d41f240303440140c80301d034001464a0a03e58901804d580760a810040c800014800c1d16070340c3c1c607440c0c40c00b5015128045000410100101581007089902403d0703101c800d04c83d041e54000c00c2d03c0e500d040e9400000d05200c4d02249080900300500d080c0e070020071720268640725a581d941d41d442c0a541e4079803c110018003070042d0380c441c88800007504d241c03403203642d540b00d500d807a1600c001c0b00020b02c3d890344219604e00502076140180755190048030114602140140c1e620341c44d10b900600b5100d12580600280f5078103001c20420790b0f030085800400c1c995503090106101000040d81c1c4403041c80441c0d1105410000000c12200400005030584600e00985101c00030001e000d08001c0380082583e50120b014961051403a090708003140c40c81400d51045040329085501c6981c0c06041d82c400711140440390032a10010020351401c90011404c4648101a030000304800e400401120000184400e05010002000c40c1c1e6603215107401080c05888 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 234076555 1250 234075305 234075311
    0x50d0606090918030815060403050a0b0708070c0803070302031302060a0903020a0914040609080c030a02010510150e09040206040504090303050a0608061e09010216050a031805030c04021b01 83
    0x1551809000c0e241c1900500c05410f01d0180e800903010a00d00d4010803d40e05501c1d00704030b60703480100c00e44581030002a100c2c0c11020074840000047d004002d032886441c410745c3e028034a0314044000500501006202100f000300e0040c2413008503000c401200d400010618025960b5070f11354100b007101100094000350040000a011401940d00401040a4900c2140c106481c587c1e11000007007558101620300700310072400f002040020b5034651002c41d403940f00e007071503509003e0301614203402c64000c04030b0000543d44884c10440803032400b9042501400466061300c0030a0130080c401010f250036000031a0144400a011409540c1c9050584004010080041c000d803003c03031a0080c090072058800180c86801d0038000b01e003c03c5c02140c1e040c41813440612031400c4569441c110001040040e0060420395400c00c100d00b11401c0311040204664003034002080ad00000d407600070006502c07000328820701c1c9090001481030740d0700400ca003071480f40101c2c3c0240e224500781d03200c003040c00303c01c16154241c0e40c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 234077805 1250 234076555 234076559
    0xc030907031403070c05040c0e06210906090105070203180906010e0301050a020d051305030f07170406080402100201060503061305011103090a1703040b0a110d1113061106040f03050d06 81
    0xb00000c020700520384100a5414525590418042601c1c0c5009480001c0b45281e0320050a0b8280304010f004954440c032018101811465075107a201c010603036651040703400080400542040c03d02178150008294401513103042054010340c0201201402c843c0d01c1443e5840114030280c0c464404182c1d5500001c000300500e003270001c000d200951091110444180c244000a0300650021442042c8079400c0f10185180c07450600c45180c4c2d03035000941c00c8510000750182c00d5441c55001c000341c0043c10240c1c46003411807e00c2c2c010000c00500920340b40045a040c003405210039180450000d030040c90510203d542034110303142180c058515503503071250320b503004005c02c4900a0000f4016045034000c0314010382d03411504980710000c2c8802c95000d400e02203100041080c5402a42c01094a041ea02260a0611406104074000d4508001c07000203c010b02083d00080b030302403004200700502c805d0501e5142e0003801d5a80e551620300041c806401117030002804000c0c1400342c0c046400c84d80e0544d0007040416 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 234079055 1250 234077805 234077843
    0x1050106020c031522080a020c0103060b0304020f040c0201020705030c0604021207032f03060906190207020f090411310c0c1104020409020403081803060408030c03090703 75
    0x44400d00c140d200500c078000d041d90b800c0c103010414108201c0700c00360140a40d03456842c0840d1300b004c0580e82c5040f04407542a080007185a49014002d00f05003503010f4810b401d400c800041c1602c1c42c5402c00245122b0420600c80181d8542440c003140c1c103801d90f40400c804030002c8090f0b0090040361405452400300081d14900b03440d0100300348c3d00c134510031180c0301e8103911380314036003a59100e0501004062034a03902000b40c1c407901184902d006030000741902c140280c030520209060590903601603110364003800030312401c5010140089200800351104505020458000454181d88072785c100e0b000d00301d0140410300380144012042900d2401604e10180800d04a455515284c030810403902410141480e107108a8450b000d800c50f40300855941220200c0e094071101c4074a070040c150340e98444e908220000e400c4105002400065006491880c0c40e40b0b50301852504101e200301d80c2500c41c0c0c03c440100400125140242c07070f08000700d405001c2c1c4076036994280e10b1408491307805c090700c403442c40112402c1d40c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 234080305 1250 234079055 234079061
    0x302130306050f011509031e02060a0f1101020f0409090c0506070b010e0604140c09180a06080120311403010f0b01020c1504150507021f050403060203250201 69
    0xf2103000c3d00a2a10f613a07149402009124840034110000d205a001000411901c0d0244d0640c5988108200c5411400c1d900003080c40d0b10003400080400c141e6414403150300e4200c086150b01001880c000d620f072100710082c00b20039125a00a03407400d05c0c3c0d90040c003403e2141600240010f044094811f84c0d940c4c01c2800c0003100c1080920940300582801c0d000030f01c450525000f9140c1701c2e101c0303e0031380045442e414408002c0341c1240c0280c135004840203421034100009007204500903c3d2500000810506142c401420f40d001842c000007940340045100f2254094982140c400954104625840d115000103070b542072020704014044802a5034408078002ca0031706034051b6841021030003000302d8401c4003038003800e9400040700140581c000e0490901c8504060141d2031040889242071441d0903204e24892a490300029499800500046040021410860a80c544003142900d803109000d0070311a00800c2c9100c0c80c00b0003011280c010002c502c0b415151200664401c01804050319170407000300c030007802 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 234081555 1250 234080305 234080311
    0xd0e060a033308060a0e120a02032110050a0f0905040201090f0303020321160f0e0d0b10061d04020d0e061906050105120a020c070b0403080c0c01030501050d12030213030605 76
    0x684d029440100b007801100b841002c98030000c00380581400d0f888074241c00005d030002038104096010810441d000d0b6103120400310551700c0c801c041c0589a003424070310071505400d50340206000f401c0c2c00c1030500410340b403800e021044601802000c1a20360351131004071042d1205a00144868440400c040300b003540100150501c9080341410b042c41103510200c03c007180f0b0050355507885a24410281c3d1741001d104e07044140c40d02c1c019007000030710408101e021a06400d9403a4043e96400c070101c0500400e0b460a004075002080340307180c0030f83c4000b0b071281801c0a0340c2c0481c42d2280700700d42c0055030b4202c2c00201d8002c0640300b0343c450b060b25424139000003c0c851030405080790600c007607d0084081510f40c010020340d040c80c0c0e0040d00458490341c0c0c000d89080290f1156241c02910309c903c1c14001900c3c1c0c108402400a14441c14816840f604e4110401c0e1030026142040c5041c58140030042c0855207411280d10312241d0000e42c0c900c05205041003d5009200700d00304c408000466000c003200b4828a0f07000940 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 234082805 1250 234081555 234081569
    0x18010b0c0606010306050609090403030e071d0c0c0d0807200c040b03061005060702060403060e0f0705010801060503040f111207051912020d150c030504050d0e060a0333 74
    0x8603990b4000110215035545c042c013540310384103120900d024145140740380c0d03200d4440e00700025903100310040c0e90300d0004640c1c002c605c035801040990051482c813a184c80e4000c080040350500748076501c440307aa02c40c14403040d50001c2110440014100500c160104030801e119409101c03628043c0300781640c1c0315141340200038065420003030011010f00f8001841c0e8070071401103c0e00009113060204010541d409640142d034004c3d428003020001c9001e0b441115001d25484c002003485035030412407103040042d258042d606012080c001001003d4004007100c1d441548085400c003c1d01c0d8901d0300c52441040d0341c800c1c2d608210314480420760308000140328001c1c2c2e481200c074018001c0629140b07210b503680900800c0b08280100411342e0040c20040c048030041407040120b50f04080c00c000c110411684010900c40000342c82d20103200034410140145481c20030381c4d1920001002002c8041040307413113031030142810555540c60f0b800d44080301c14040c0e8800d144c4030059881a038035a070b52071055140c450241e25 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 234084055 1250 234082805 234082813
    0xf1a0a05131401021e060a0f15080102042402030406050702130606050d1505130c0918020409060603090512090d0209190605010203031303080705070b0a140105060702010203030402090618010b0c 85
    0x44030a14104204103503c100b45c001e03c44d0b03542d0450074401401215000140158981112040040c24803860401a21414000584171482d140b14400c041d00d0202d00c3c8000051f10001c400c60442c3d000c0b08480c140c0d41142829681e440407440030034410030100000401e1a451711801103000c50b80705009110251101c40c060255001620030658a88541d1148aa1086000a400120140c140c100306203103c5c071030030286100c95a403a01d010360b0944503154000c0045d40050144071000740d038803618015000303501e000c1001000075a20075544404480034207201d8400400c943c00c160351000f000c240d44682c007928100d000e003080d8009001c0c4a00c0107402c802680d00700400414994400026a032003581100c00c101e041c29541c1d20281c81c4958003920103410000d041080c940070030103840b0214040c03080b0002c0020180d84980100301c0c01341c0180c05c03507031003490100490b0001d41ea001080e41e8105030110780b0550142c80d00000581c4d0540c50034002c1804042140c00010303040b940344054207031400000103803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 234085305 1250 234084055 234084073
    0xf2909070e0c0424021204060903030f110a11041d06150907020307150f110a08070212040521010c0f0807090f0e0a0902150a03060f1a0a0513140102 65
    0xc40400c3c040c5000b62841e00c01e40032098010760300301680c0d03000c0315515801507400b411007034a60390140c0c1d403040e084040443d000c0b80c01001090fa0001c1a402c803454240360000c41480090701d065111004c201001d08050702c2c00260101c0c954403540801b219400c1024403040044c0d80d10b01080e1070f48070807684820340c0200041e1a9507507040c0f1500d01c40c46a40190b001c0e514004041d6188684e950680200c0d448a039030350400c50102c0c04892281c1805114131030482500c031508044010720680c40100045c1c01c540040c200514050100c40c1a01d0603640700b2681d140034451407524540320b030b540111900301c0560030301d20300d20052508003001071044000c6030703907003401c5a50301c81054035100c5d4107114078000120300c03d80c00c02c0500a20013080390055141540400c0000e0380340c00094040d506171910092500001404055154062090303e004040c1100c640c010f03a80b408042c8581c0340c3d204442118480070008000f42420f1184007103803012008804920886501c03100031000705603400500d00d025104050407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 234086555 1250 234085305 234085321
    0x61903050a05090a02060d0b03121207030e0d11030c0312011e0e0a0911120d02192001020a060608030702090708040f24090501051f030f2909070e 64
    0x907092040800800504c0d5403201603091000951041c05400d005a54a420300318490b5801d118001e03400c000e0304011621202c0c0590320841f00200909204203142c0781002240c1c0e12800420f501006003074508150000300940c1c9480c80c01c6105500070614075001c0040c40d44445503401810714140e0355030540852400b03542c0e60100b9500c1c1e51601511081510170000150003620700c0c1c024144852250b0b02e0302c2d0707916490402207424014003000041c0c054000e4980044d00950402114505d0024030b0030001c0c0c50440da844000c503194550107c40c100311402240408640d008200e08000c035a41702c3c0381003100950b240305040e265040b200342284105c40820120b6501c501c24009d4034000c5801007400d86072241c60355280c40c80001e404800301520308401d142c0071036055480c0b1070080c43c0fa004400102d414907007808441c03a140e0344848004030003035803140c003440407500250401c04425413040f60007100110001114555420030b41912074288401c608008006201080300300071200010040f048549440035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 234087805 1250 234086555 234086561
    0xe060a03060b220b0c10021b010e06090607020a030c0204020a03020f0d091b030312090606090c0203070605010b030f07030b031207030f080c03221518050c04020a090e070e061903050a 80
    0x1404142a500010350721b1941c1c401d40c1e0051040310f5080460401c040b810b410740e2825100003003514419500041c04000d50850140000b03035200103184054402d241c03041d94094281d110040002c0e000c0e990210300c100746e2a000e171381150b138030014030b0022645404a940d00c8501400e480c2c0000c8498400701d59103603c41d09900717540b0509413a415118078183c002c910b0420402811a8541961007076110034000078000800d100c1c0110000c21076025541d40c022506148040d503c1c180d106059920003003040000d2680c108080e50f421403050328001c1000031104001a1a0070788070403c5a5016000240d5a03081541105a00416071519210302805541c0d00038800c2031030200315960a00d4110701034000c08914034410400c486988140d4120109140240066080f28140680000c0c11121390032143d0900c00104902c0b948420304030360941c82d03d200801d0042215000340b1980f50501c06203004034003114014441d0348419600600f000e40c6801c080c1209140000d10640120003281c0340201050000340140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 234089055 1250 234087805 234087817
    0xf040513050f0619150905070c020405150904030f09030b10180c05040b0d1e020405031207020f040c0e0409060605130213060c030c080a260402010e060a03060b220b 72
    0x160500c44044030f41e0304504c00362100f085402c2003907041d103001003010141442418000c155070b60703d103850740c1143e00c140700480300040e0200d5411000350031030014503510800100d90055051800c00c81a818107901a55100c3d03164000501c8048901c0400400d00c071000301d13250403180703200f480d0342c03510b003100384144104c1d403190b0042c0d40064800c000510007410048000d1251060706500085d010500107580c6415480c02c0308440421a0001400c0181780f40c00c12803006c00b185a50340c01840c01c0e030b0543c005204103205910031030140d511040036008032402581d09915103c4040c00030300030007400340742c50002041c0d80c2c00380c140700b81c55007211020111514800e448034140001c0304045160f00b810f00070b030b4140103124001c41c100051520014002420740024001581d1580c4031400c0080c0d0720310505c80c103202111000d1010011010811000d81e900000402107040300742c51242d03580e5114402123024040d643c0044000140004031a62144075410810b10394100304c4000340d4526860f00c059183d503100b60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 234090305 1250 234089055 234089071
    0xf1d06070807090b13060f020607050316030b060d0c2a2a090207170304050a0b0a290f0301020f0d0b061309020a090f080703030e0f040513050f06 64
    0x9000140018000e007250354100e0308a052841c10281d6a0313101e140c96500500c4a058500101c1030108401d0340c004182000c4c02c0e01d180003401207890a580c006000c1c2c00003e03e452540100849000c032080d00070b40c01807040c00d80181110f070382e034540c580c40000a400b84403010000952078500c80100c08200c0007412ba04203040000040d0310080d81e40301c0c5108503004c007484419108030214100080c1c0c81d031040d101e00030070841d040561140b40b41e0401005ea0745000703100340c841362401c00030000000c0010643c0040e00394003203003001c0d103134072032000280040013034640f1a210165101d07803c107506001c0508a03c0b02c03100c01c694210807205058181400d034040c00003160304c1c0c40824031801d507021b0840d0700100e00303080c00135002a083c01360588285000e10007903480443c00c0c90b8006400501c1c207500c001c0d070f6005010008014100249024400f90303403001188809000c020010007500701c1c070f030340c2d0358509d40240000420600030781c200707900070301c1c040c115442c01203e55100e0500208a2618041040781c412091 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 234091555 1250 234090305 234090313
    0x314090c030c0409060e030c0a11010507120c0c050a08030c0120091c0602040e01061b0b060103090f08030a0204060f0c0f020d02011116061205060907030e0f07090f1d 73
    0x101c2c2c41840043e10900c3c0080380e25640f01c0c10740d0028207a0410152054100701001481c6151071400e24001b04000105480c0c1000410008003000c15141c8800c084070000a14117490000c600f410a40c421603820380003640d010300d03866800a907200c00000070b400da0a2500c0c0082200b441c2c002c80380c41087e180500e600700503200034405070300c1902d03000380710403070b01d191100412142c11000d41e1890100d0740701750040d00c01c0700740c02e600502119a0040c00c510321007404231945525041d45464002488100928041c10903458910300d4007000704058034101c26940c841103107512030038102010340103504580526800980581194091144501c0f10035182e20303000302240f038440d60240c080c004542c0010405074107100310400d0000d0b0490003081418134280c040e45404044a0031f04030700074212031400030b0101031141410140b20340f03a0307034003e00301d90008400e003000600c4154a8801030300740400612025407070702400e0b100180081c1290013041040e04c504c1c00030400b880030230b50f0280418140e01c402e100c4582c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 234092805 1250 234091555 234091573
    0xd03020a350402030307050109050a0b090307020112020f070c0e0f100e010e060607120906110106032d0203030f070c05060c06150609040e0c1f020318010c06020301060314090c03 78
    0x100100500360040d0004c1c0a59151101503103d260a5451044048600e0351001000409010091041940040c41d0070003851909085800082284154100b2842d07081d90001d180c801404400085401e5140c0c04501761600303a40c1c40348401c58890003181c040081e82d00c46070002d0751000c040c14890b02603c0140290141c5a404c00004030100200201101c0e0051002c01040c00443c00b210f1f04058000f4044da10201003900301103000304500310742c19207008640c0c101603061002074544010304041034840030740481c040000d074015110b2181c0d03030b107000f0b9090f0000107040b54604585500902445004507000640c0660745c0d0700b81f122034440c880880c41c103a04808042041190030100d04411000024802420004950b00090440c2c0d15401c0f80246035102e10090556810700001842d02c901c4a403000c0d4045180c2404080c0d140d01c43c601880200c040d10b00c00304030720f580c018503035808101d4010380215100d41e11400d002c0e005100591581e40d40c071000e00c001032a445000625510f400c10301502a0460715 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 234094055 1250 234092805 234092897
    0x501050d030f020106120f1104050c0403170f07031101060b0708090913020303180f0406060c080c01020c0106180b0a05010f03020705030c0a030c2d080703110d03020a 73
    0x203004000903000c6540701ca900040550480280303000c1d545c003403980307c41c1c82c4a071450f0024041042d092418012410401003103404d24810003a60201c1ea01302d0b4500da103c1c400c07a94440028441da40c01d80c02c503810b003c14030005040d031007454406035480b020001c0241d244c40b6500c18015001c0c0c6440180000c100708044151400d202041581249445030071100f6004513030300007804e58200402103018030a0700300084440d46004c0c2050008100c0940e8208415400c04400078604230a0380000b40541200089000401c02d0960440d440c4181c203030001c100454803801712214140c0296059944107082c2010303010305103004c04903c800c4980c140c4448024100d0050700794069040402d0942d41400144008186030005011079000e80d4400d956400708418185002c0030031a6082920b03440b42640160400081c5c40802e4201d0ba02c2500640c2590f2158028030381194401c074048406c2e1801d004548001d010942c054002c2d0000c0003ca4a40c07440a407099000c05141034440311246400b90103c0c02919216 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 234095305 1250 234094055 234094067
    0x10080309060a0e0f040903030209040b0103090b010905040305132303030a1215050409050313080303090a150207061e0f0b010203031605041d0907060504052d10120506040501050d03 79
    0x224001400d5041160003130000a400c4550301c0000b90003180d000614541c140c80c041c0b2036a240d50000b420208150262038072900c1c0700800500548208595030000301382454065001d4440310103400050280079919600c00f6180307a143e0740c40b000c0034809000c0218000e8074000c001e0b110f4000c2e00c2d56900c000c0d0400d0004150281c0b145500401407a0114039001c505a15240540089903024a00555507512010b0301a458011160711912280d0014000d0104400011410506040e045414050001c40d1405440003e00c28484010002c5280080105124240170f007462107044c100e000030481d040b202d12000d02a41c0d021911f80f40180c004000180607481e607101c1c3c000c00940e107490407034245502e88d8141b01800460840c0860340354403079010061426000c00c40c000240400f450100c0c20700707103880301080b40c00502d4640078514015000b56402c1ea1a14952903400e00b6200400405102c6130b1414041d1420704010851038109082c640021024101402000d0480c2d0002e4540b044541090300c0c00c07901 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 234096555 1250 234095305 234095327
    0x90317060609030a0501050f010b070b070c0c12110415080a03050c0304260f03070803010b1c0204060c1406060a05060d0b0406091416120b04020c01021210080309060a 73
    0x30021003800303141490b403420030100d003c06205c0c100014003414182004060395070b05900400300f005c02084400c0000d100f15082c5904102d141c03c2c2144404610f03c1d0540005ca9660011120700c0100800d2070107005515040b200d90841c00d5400b04948141c0b402c0c0144075807800e00440030175038000301d25000020700c1000145003241c1c0040603281415210000d41b03003120700340041021491000d000c42a440a028480aaa116820801949400040d684103d0103000500c0fa244003a50b0210b10420368081140c00145486041e20303046507203070f4039140302501c0d01c1106482038444102d29403182c07101c01d80c0001c2e028041c2e0780080c00500b00c40d20b003804000070340d4051900c0d168043d0f11000c400d0ba0507203540c01684c0161020401c081041d6036074915626402d0001400380400740c2825580540f0a5001b0144a0b8001d640c000f000c6002c070401408a00a8441d0f81c0c400c7c0c004ad0b100062001384241e4030319030140210303075401200800d99035480c26a0354a004898031198840303c104040d5000c03e0056108590b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 234097805 1250 234096555 234096559
    0xc030c2601050f01050c100e06070305041205030c0c07081f1e0207140f07060305070219030513030206030103060b040b011d040209040605030d0807020105071805040e0120071509031706 81
    0x121b49022210440d04100390105900501c03070b141d588042c501c013818002680d2180051508220714a050b071280c0910301c0030622481d003445000004104c101ca480004ca03542c07041000211280700d5078400d0a00d40d5441c0c0c1c901c3d400c401e5036a99001402824090140c0f50400c04248460702400003c2060b080003540150001c6a000c0c020015035000c664042c0b04400d8042e03050400707040410300d400070180036904000c0c0003200b15086040c074031082c600400303030f880344868040c54040d07104e003e482c0310107080c10081e410195222101000000c02c0189540203481010410354052042e10349042c019540407082d00b180ca0769075558204045540d092560160889507c001d1000c100071350b48202081c28201d0f9446842e000030309040810241235024080e0315044401481d01051009554003968843d48250098a105507114107d00821410942000d4292070503641085420589421104202d50040300101c8800303a05034000c0c242c4900781d10031054075582544402c8030340c0c00240500440210f0080c111a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 234099055 1250 234097805 234097807
    0x150a0b09151207020c030d1e080405010e2a0904050703290f1e0c0f0c1507020706031503020609060904060b130311030c150a0c060c030c2601050f0105 66
    0xb004004603041c00c28021041a00074156001402e000e25003007103100c0c5803260900c4501d0900e060381030f0a0130b124240f4905540f1f024859526a460000e0241c12811425905485100074004520f414048840e07403000001500000084210040c040d400f0300031240035090f6005000200046036010349403c1101d03514a500f040e021000171192811060305441e0020203048400420003614010741469a03038500744904441c440c035100510701014030805030007a01c40d03600401d154103000f8080110b0039410200d2000f0814902d00020001d649a5480c41002c0000382800d8405101d0f800320303c5030105403900a86002d2900c8040c1c000d0140c0303036201c04c09858201d0303990030000441da00d40d04041e0603185030064043d0034183c0b941c1801d03d105c03200000b4640c840d4110801e4040c003941c2d41d04100c00031040b4810269101c0784840401d0320f01c1c0042038000303001d160501c40c0326001c0541c0b5902c48401d904044c0ca41c0d0645881007214140148480d0141d0700c0308440d2440140001e1814000c1d04220140500d005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 234100305 1250 234099055 234099067
    0x807050c01051303180b04060c0c030c060c02181b0a020309091005121c0315030b010801090c060507020315060604351204050103050705070515150a0b0915 68
    0x41c00c6510807103860000c001c8107a042c42c10107a0200c842d04151140361315000d00e0398100184c19481d40304522900e01484152480c00c030810041780350060095070800508115955180c1024110703902d191b4049122b1099840903c10b4031100c00b501c14021815041055060001064072071107a60280d0040025807200b8482151150b07101003446116100c14001c0c030704584d00e41400d01442d2801900003249a800840801c514120900c0080080a815182c0401c010701208440314030503140c1c0d000582402c0030000085100c03401500a480c0107849080508005030343c89000b16010b00410780d00952503002039052040c1e50800c8240141c10a50080030103280c43d41d9000741201801c040318880d6000011408000c8030344114416000c80d442c2408003800c0c2c1c0d540c401d6121100c80c490b500070141810341d99800710714214400c0c4283d840d010760020455502e601d04540600c01001c04841100f107180c1c12407840000e60504428000444000c4080c660400303002108200e41000d10030040d2803160020b01c12 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 234101555 1250 234100305 234100327
    0x515070516061806020a020904020630100b03040213021b01090c050402030708010915030b1e160c060b1201060608010801060b0f0706020a030f0e0714030a030807080705 74
    0x40e100c01d0321a00308080407010b1522501600d4a07188035042c01c183d400d562400c1000c2a000b0031a5540c455048032001555a1a44001034840c011a0b482c04030b06130900904442249100e001c140c08903c40c142a00360030307030343c40a04c0e204c40400f0b4000c4c0c4e0340152060012a00506060003840e20314842c0380f4016040007140960500301c400c0141041425a46030809081444205c280f24006008151400e5285240605010b489848184a040b1340d10b42d4400100c804114a0070203000074661003d11010346040c0440c980441601003041000b492840501045c62011052442c4103800e00a031101485041c0540b01c000040403105485a004061284600e006d42003e01c140005406540c1303d9501075410070204500719815508149040403040180e40065418203003520f125030360158015980754102230013203018110000101c3c003d203080c110f100141d42d50128104050703602c02c0d12014594445c120816070303100c581480107000300b41d1000c0071900c00f51040d0380c11036004e203403030a25524000381618 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 234102805 1250 234101555 234101563
    0x1504240605130e21070215030c07030c0303181a070e0906300a0506010906050307050d03051b01020c010f0912030c180b0d0b030d1413090908030402040c0207060905150705 75
    0x21119103204c0c2c0005a0800710714005020326411206041c0d03250441c90620844140c51240d20006010310100c10450001c06108c0d8201844c0c80300341d00e0341110f44145601e0041c12000c100208101c41c1e075100800619010b00c85d000c1c0d944589c000800c1d01603d621074005014150084000301f003140c9041000c102c914054089040c090100700d0300003403841e103940381442818200c0603013040340c2e00c42c2048420130541d6400112031003507030000c171b46d500349000c03c1d07140a4420380702e0500110020b64809400301300108042d4040c0c1a081c4c0500028040d920ba5021410210380040070300410000c03060751244c000600c01e50010700c0e00d10590420213500504007c441c001c40c4806d0740091941040042c00c011480c441d80905004140254000c20300d200c40c0080c09884401030303207070841c00c039680800c0c032007180301211146000501d1000000c20850800d0300303144030658021203069000d136050179858405a403000440c0341c225330542e074600136030701d09010400050348180c8408102c100002d000340b03030109100348 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 234104055 1250 234102805 234102853
    0x91a04020712080105031c120e010905010e01052a0f090d050f1c08040b06030705121c0e090a240602010c02070b04061d031504240605130e 61
    0x2c4802411500b0168020a5100c05070000c501030742100012403102604103000b040980c07501e0070904500c00b02400608020f088210750350b4083e40c01c0c40003e0040c230006501c0355146070101402448641e41d07401c1040e12620b40c0355034584c030b0240c0140000080041507030180c46c80d0410004c00c0c0f13141c041a1800078103c060036002c141c480341c200c80c000d000000e030200540315551400710103020016900480c00b4102c0c1d10010405014601420f00180c025034040c0301ca180542002811031071502d1b0380700301ca03960f9102d072103031403074442049058030340d541d54041d6843d080038400084c4010081d41d1041d070502c015000310b00392002c01c3c1d01c10300b4081407a000000362000181060b41d000041084070340310000e02c1c0c40c490b42d21014a40c5c1040205005107503012281c0800350074815424100308103c080804d01c0c1a1a80c0d1854907801d909000340303c100400c0301e1006000c444001c0e200c4500083e41a0014104c501c42d00c5003503880100300400403200441a00200c000e132601074161002c1220020100000400304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 234105305 1250 234104055 234104063
    0x1b020d0e1c110402131e05210a080a020106030c080309030c012312071236050604030905101107120204021303060501050112090b010b07021207090203180c0307091a040207 75
    0x45009100700c8810000c49580e00188210b21100240b426001c10f040c10342030a82101b815035150042042391508010440040344c1c8070104542d00e0705e001030f00a000300528001154403110300000050740d44000070a0703c4880000a01034a980081d480040d503400040c101c00002d540c41d10f03500b40c010b08040341c0c081d2032a007007080217450503441c00d08030081c041003d1002c00c0403060714210016642580d03002e9100c81284440d0794088071310395003404180e00c9042410703000b8503500c40c0c2703c100010107034850004402c8900139104103405010b84102640d0403824005d002e801c66000d04410010f0310300b0070150b400072a0024000510b040c481404818007460b00d90029990681c03550010010380d44c2c089002e03101019a141d040003200c50076910112107984c184626540c8a00c080381a100355510441c1c140c001c04030b030000301c0b13104a03500e43d8810040c0d00211010b01040030011034040f00e041c0c01049219401c4c01c0240541840c03030a009404009043c0328018100044203e80d442c1d025459600c0140030b06801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 234106555 1250 234105305 234105337
    0xe0f1e040f02181003080a03020408030d140705030f04081303060c090503100905120a1803030f1206030302060f070513030b0a0b060918070c02041b020d0e1c110402 72
    0x2801880000d083c18034480200e416000d003006070442c4c41c4c2c51010140ca9201e5101581c404040e10118086c1c042e40d08170108601000a5800c1c04210643c00240032455411002100b960340c00f0041c0c54074041101e078503498824610018002541c80c2c001440c4041498038213156540d1252200003c071303088681e450000c520010828411450708000d204500400c000302403000141c241c2d120341d1a9211000303211004000815011282c80c05031a20281d00340d000c0640b0030119940c2e050041580c030110f08003102080c080f20549a1a100d2070203076100b600e8264005001c503883e1183c2c041c40c482001000b9004001e010b00054202c0c0c1c001c0c450b48002107000d00f5050b03074981400f0f0310020407624401015403140b4820007003405192103101c151403210302218010641d0395140b180543e5429505c00009522903d8100151942c2203010304916002714a907003101c224412103130068a100059400003680301424100b80c00714602c60011a8014a03c203005000d144840017020070141c1e000880901c00100c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 234107805 1250 234106555 234106583
    0x2040605151602151c0f0c0203070303020d0204380901080402011b0c14030601052403070e0a03030507050c010c20010c0b0c07031206030305040909020f09010306150603060e0f1e04 79
    0x4000c6c0119a041150400c00300150140c41d05c019507030f8421108024145038021941c0310030300f44682d040c1c40c02040401e2020a003100120701402140d50411321044c4888003412440709046045c80a984001b00180c4440545488030380042d107414240c220300700c40c0b14a5aa1417080016040030300d44006180090040402c41e417100109400c00c10305810030380c01013115910700003041d14a08062451801e48400c996643e0700c0e8400c1c21680c619044034201d40182d20400300008241d4010002c041481c0a4006d4941d01d00c0000011560180c6042026020748450707180c240491b42d1500e44401080414188880f8144d0240d0f25110100d200716041c103040c50002c6410814107400c1800c00d000f040c00c4560400109040d0b03680a81140680c1c00349840c41a03584480c130045440f52841e04202e850b0051080c195982e40c1e1a10300080c1681034281800703c4241d420000300c042c0203000c1e400580d403070b84484032840c0d9a000c1d017a4607a084000c0c02c0001242580c807200c403d0007503000c881401180038030281e4010b24 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 234109055 1250 234107805 234107857
    0x109050d030c14071e1a0f06180105060c0f1e251401050c030c060604062907030203070f030f0306060f02030a0c1704090501030204060515160215 64
    0x5400d0142c120280a000e28072215100304100850b2001c660000a8409100d50003c03000c01c50400303450000e00705015250400841d0780114030503440741c0070b44045012a9600d81040c004031802d800b00e00205503203400010701a03440c002e000341114100c0c4004a9500104124009280061900d880c15071311600c0c010303448651a042c088080721002d40c50851010400201ca84414121248951000100044540002603109038111b54507c80510220794807940c2ca0440242c0380c0700281c0701d2900c51840d226000804031030240382c0c0c802400c50503501135070f03802c1581007104140d8080c03f011011804200541e1000407042001e64234598000e0b0703030b00c2c003030038640c400c01908885940d0009000d00c6010145032012680c00403c5a0700710503140381c4241803400c240760040a00d4404800300c4116070002c1008500c0382800e6214038100d034000c40342071118650398028411800c1c1c28500b119000003040101d07204004075152403e4219102420080c070b100880b110b1001140c200c01210b05072100841d064800d95 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 234110305 1250 234109055 234109061
    0xc08060a0e0303070e010c0c1e0501030c0e0f0406030c060503041104141314010203010602210c0d18030501020703110c030f060a0f020f0406032a140304060e0109050d03 74
    0x800e0540d80e04010000001c0340d0300b40c1c0c0b0301004007000c00300984405181da071a48203100d40e510055000407108010307501d07508401c505e5880038140031a104204d59000901e58420b008941c0b40300070644517201e40c11041c005000341c040c4040e00350368015072a841c001000445003d4180018503c90390b600b9280d0410349020780c01c85140f0901d40f445541800008038170303440741204070f030340002030441d1100c4520403514211036514680b403008000340d40b010000151107500072034104100702c040c0b0a0a6a90002958071100c41c1c0603003103690f0441c1d84080d02000c103540c0035180206c5101080504210219603d03500c0a099900214003100002c28011000c3c003030340d204000080724508100c018000c20b40d0603404140d650304c3c008113060300850b281c0c000b41f201c0c080c8540c107c5a100c5101c4c1c003c15074864a44c0005030280c03d244090031450850342c2081c803540d0f0070b0850480185000c0b648d99506041c1c501c00c1c01150f0740c0001d07000b40c520030b84c2c0e0300901015100034800e800410f40310b8400b40c000d94500550103011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 234111555 1250 234110305 234110311
    0x1d10030c1b060b09070c020f062506150b040f0510091203020309042706050c16050c090903161b1e05030606150d0504050a020a0902040e060d03050d0e010b06070c0806 73
    0x14001d403001b404005070b507400440c80034800c1c1030780c0385910b03040c00c5022009288090074040c00d1204481c4540414840a5000550f140d5034072048800c02d142d0741c0d604180e0512440c030840c040741809040a0000d850003094207280d22005281039245140c4945140d081e020103840228090b902c0041c0c04051400d29000d11032442810b02c0103504285044c10309100d03425060388004000310390340c0000a00c2e80e248481074490030f040c840401c00c0c0302004c0b4074103107a0b00d43c201c8080328422841d07500090000c0c2000800c40750110294006941f603a1031b15940e20890b034040e0a049014240c031084081640103035844050060b065101031001a14038040515040c04800b6004500843d109a2401000b01d5076004035900801580e60024003555141426410500003079402540141660000036100d6140d40180096410003602e010264036000100700010000490050100308140b101580c0d032030103076000c0c0900e245204004155086800001455503000d903908880301240300c0b5051044490400103158 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 234112805 1250 234111555 234111557
    0x1e07050c010c11060f190e0328020a0f0312021206010905010206010522020f0a080907050a03020a09052a07030908070308190203090d121d10030c1b060b0907 69
    0x71100c4000c0d81e10985481c801881e21180080b0300740070400310300106d502c0007030042c8462820032100c10390f4466252294410921001888418400204c2c03c0d101070300d07003900d002d64540040c51200b941d030b07884048080b21180305400b440f504044502c5080201d000400340300740350845940d81480e000d80003400d10780036604944e04541c016801400242ca0b02d0342000e52000c80110701e540720204c0755841c14040c2c4180c004400440d403002c20b0302032180d500549410701450001044d14501525141482000b1249200103503008178039100800c02e1034420b600594020048048a904070340b03040314a15040b480e600310950b22690001a01000c6c1640850250b018045410180000d545181c4801501c0d0050440a003030260b0400e84030f0001038000c108403400d0100150804990f0003c40c101521800031400c0c41c0c0d80030441d070b91894001800000600040700718001d0240d20800b1441070100d00801a403640381e420702030040d00c0102d001c24140c070300005940c401c01011514402c16014410b500c54007902c800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 234114055 1250 234112805 234112817
    0x501020f0f0c1909110715140126010e031b0708030405061c15050f0103020304050607030b030f07080105160804030f08060d0b0a20090109030b1e07050c010c 69
    0x2103600c00d804606203050031401c50f0181d04512001a050041205540c8440780b400e01c2c14090300310652204003c3d000e502c0c02881850542809100d000064500c048055a040d4100c00014480400807040a00c540c00d21079103580b00c892000698a03007152000f96802c030650380b0114044148040702e80034030641100590240008078606201c90ba0b8038001c07030003550701c142000b09420824048940001c01315000c07003181846101c1c820450440254114042c0790f01408100800c044154080d0080301e00442d4000c0080c101e543e20400200c0081400e001c580c0e6040c01400c00d040c614120410180340500b030081300004041c2015800128021446c44c001000e000c0590300f04804071b070304809140080c0455050030030059039070f4000110326081551b030051680015a003801020b96680c1c0c030140d40c0036007180c0b20400014041085002038043c1c00d20185c0000d07200d40d010700010b1080e00c0d4003500060440484088010920b036901c0980d0002c89032100000d402040c01e18038948240107001c91100740e07042c80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 234115305 1250 234114055 234114073
    0x5090a0b1806130206120109051e06060d050901061505090a060206010b0a0302130b0c0c0102010606020601050a03020d051905060703060f0b07080313050d0207030c0506030c03240a0f0501020f 84
    0x780c0b140c4000300711098a0100d690043d0035500c03007400311420010b0300b11245040c0e6031603020004c001c1405a41d110104802c440f8581904401c0100340350007008014085400c0c03440a89503040502070051020725155201c0318005090356981100085120312501c070191141c410078107201d83c1307005680c030100840d80840d004020740c0039030904582e9040c440c0e2030090398a001c141061040c05a03280d01c40c4150080000b41d28143d410080742422805109a00070301072580d070348808903602c800a00500e54001a40d44080006141181c9090815481030040d40c82c0c00341d00c1010f4054610007080709841301e40000f010410306650510420010781a0ba0303500182d0682890843d24860058030700003080700c1000400700c0c482c081041c14529040da0720200703c40d402501060001d446515500c0f040707555a498510100e002c2c50580d0641e4030604010003181c2c1143e6819a050b94040081e89034140100078840c14101680c4075444060050010407000311015490040020702d04403000000304201d41012100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 234116555 1250 234115305 234115351
    0x30a08090d09051504050a030b0105121615021c08090d02060702100914060408130803070f03030c05220312080601020a031805120706110712120302040905090a0b 71
    0x81056480583d50109031900c01035040d0013520598014030b500420f00840081049251820300d41070700e9007500e9112820201c01562a81c4412082070100c200001d494140010220f410003807141c0c0c00f2600c1110084001a10022515440300307202d600001c15a80400003601e00401000c49606000e10081c03150341303040c2000070740701e5013032440400d6481d403245200d100344400d0604480c110114001607441354182450318410550002c0382c60b100240301e100300020b4620011058072615a0071500e002c0d21520259000c6000b02003014110307050100c14801d40c540074440c4c00d000004030300d1105440e61001c6c04c5090032001c3c1c1070045460010041048d080000c141d03404103600b440c0355071505140803800c08010421905c41c5154000300e82101003c00d0000c049900011210100e806544885868143c1d449405440d060107002d00144480b01036071f02d07000190080302d1030800c200549030040c1002c0d22405138900f41c0320283e42c06d1400340d02c5003078071100b8400e04051660b005203680724072407003050070071740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 234117805 1250 234116555 234116567
    0x6080d02060c0714010e0616090614130b031003060b0a060518011101020a050403140d02070b03060a05040204080c042a05031509040b09060f010f0e0702010617030a08090d 75
    0x8007002c001480400d254080040d80105607564000070720003404102c8500442a079940341c00c8a181002d0380c64a911401003c0c010344a180030b54403e541c4282401650900c42002e40e030100d8140c00e40c50f4212240001d0510411000e180200d21031090707181c3c0720346141007080c251900030b60154850209079404005132508081241d0381c440030321000422406100005a480703141e00409030384c003540005880040c4603402001070007568860b880010100041c0c000d65075491101201d01005640108024480705102a010703690044004000340112070322040840c041c0d8010342d0040c15240e200e508131000a207450b0042c21600c652902e400105180c15001440521141e03e0b00f45041c0603001010803d810114900000c0001014100b1a03682c24540342c0b203100e020017143d1203d0580280382c04101c0a1080c49049812514500c40d0248110304102c101800369a0141c5207000750340da21100040d050024145a6000c10b1510020315181d8800c0080a00005c2c1c00400c4145c00350420021300007816001a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 234119055 1250 234117805 234117811
    0x8060606040303030c020c1e361b0a09080c0111031c020904051303140708040312020c1206010f12020d0b0c07060513020f0306040b0606092e0306080d0206 68
    0x701c1c000c261030b80701090a9087c802d6904407590400c0c80100e0036002c400c0e020408020075101959042410050802e2011580e030300c2d4140c03c8801030343c4515074034003008500141030700002169415602c442d41c2d000c81c1851a846805500045080904200028481841a1200d4800c282000b44184190b003002980764071071501c00b0302400da01072001400381181541a5908401c020f0020071050811103040c40951070050000c0300010f181c1c0320782010140e01c0c0015107030705030740c0080681d05042c04c5940b00801120031b02c0c0c0c001c0c1184148cc0365011280d0361004100021791340000a8062541011102e458056050300031000e41d8140c09100d01c01078032520000ca48032170700100f8925058803801c200c29564400d0390700150400b400c0c0418003500c1c401c0340c0a50109984221814808410400103045d100e8404440c041c09200b8050005070542c144200208030020300100680704100000c401c190150000c400e0911fa9400303150b111212058244c45004013400021004080824132060029520f40d001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 234120305 1250 234119055 234119057
    0x1060f02010608030d0209030d0c031425060b040e0708121e040602070501020d0c050a060b12030c150c070c120606091e0b150909040807120c060608060606040303 71
    0x16200020124400e6004102500c0d00400b130300c4d558001400d00d41c02a4000169a5102c0e0240c9800c0c42800d50003540d0310102c0583c15140d4540c10316031a00c8500485d0007040500c410150340d401002c030031103005100000d400340724a04c00540080d4000038001111201d19000307106510090b418403000c580055050820380602110070360710040700c019496040c10503044129181008100452000d8012400b1800d5441c00c2c0d00b1030b40d0507404444110790700030f001000034005410000c5070b070001c01c41039080000042c102070039110340307448444640340c03560384502201100c80c5c01c0001c440c02ca09205286254016140615550904041d0307113455480108030307c9035210f00da144004690400015402840040c445248104001100c90254502c80002d40381c80b240603070300d0450000134030310301612885c0c42c811864442d02c0c24022a00700f80300600d080903000b81d48080c2c0910906000442c0034412003910300f001d60b200d288500581c036094040e0389098100c0300c503603000b0070100800307921a0400c2d1003c403501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 234121555 1250 234120305 234120317
    0xd0b030c06070602090f0d03020604060f06030305070308060d1e140607050a0c0507030204060603020405032103060609040905030304060c020607080114010f1205010e010f0506040b030a11160b0609011203080106 92
    0x7170340000d02c28011031159160000701c4004280145900030419921560041c6c0061006014a16101c0f081b110b5600000300411230074042980031070300c0340e0403032940300e00013900d5010003030410346a1495001e10315000300c0c0d400107180b8042040200d6600d15070a540345520040003035080411002e00540209454001004140d85840091000c10808a0004c580152080183c161500c1c4010040c0d40a8021640284241c036640071540c40851840390102d200c6002603400c2d070300d031a010403031303103600c070900203035110740c580c4400800b0900c28030040d8015445000e002a0030b12070380501904001c2e0007043c080c04c1c403400030b00412440351282103080c1780741c109180281d808031071041c00750344103203001c0d10301030403a4074110000c030725034004044281c10784030a0b43ca03400b80a07958204009181c4614004c81d00d50550510124200440c0387e00010314642300c40310b200b800c00e03001c405034003d0b81800c00320540d01c020030802441264180000420b001d005101c41c1c4041f180110780f809008030074103105034020001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 234122805 1250 234121555 234121567
    0x1104060b13090b09131a090705040507020a05060708090f07090c090f0b03070f0528020f031c02130302091e010f031a0a02190809120c120a03110d020d0b030c06070602 73
    0x100007074031041b8000f010002c0b03850600b032042e030700d940c0c0e8002401060300851909010441503400054100c0049600100401c86940c03469000c8950351406454030005200b03d0700c01000151023800f0180252000000015034541d103490000c1c00c01215038001261410084410700402d082c61049903480116400e00d140c034228903010840c1d2901c901b031409140d003001044624020b0410380f0034064424110f0342102d180030308148100f503c2e071042d0346980940d4102152411145000c0e038002d4040c203d80c52410048480d030340c0e004601003280407550100d5016110400d2669111310200b16400b40120307026403405181159548900680040c42d02258100d403070001428103440e64045501c1122191401c0c03036140d080004c00b8000c844151001c06850043d18014221800208151250700704003100910f20a00040100304407988484240402c00d038840310301403440c0311018020300c8a80301010f80141e4840702d1001400403516808505842904584003014040d628441600d034801e0f086140140e8402e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 234124055 1250 234122805 234122813
    0x906050d060209211e1209011d030706200c062715040501020f030c0606090c0706050f0105040c0e01140d0204050306010b070317040309030305071104060b13090b0913 73
    0x203580701404080350907005581c1c04940a0204050700c403120b821000e034904503175200c01c858440e4460380d08905641801d0111080741c2d0310640100e4242d083c022014030403a0f180201003800d0002d141c004002150b2805e4103c0d08002c0607134048580108954064144c011042000410034407079a504c1d512503405501081d41100521080001e00c0c4600500b4101010011300e0754041580161041901502449210051900c000301c200c5041d8101c81000e480d003542c039201008040034010b0034400c5110020301c0034400284081c490b942c001e20034032900e111298501400c2100703441507414040104411141001101d982001c2c0c40c101006c41c40300041c0d19018003800701c07402401143c1c0500d030b00d0320941000041c96017082c0c0040c20294003a90300d48040d01280002c4803121201690000c0001721900000c002084c41203001e0001c86205044018841841c50009010345156402ca040240c02c00614075521002d00c0a040c0d000f08031001e01030007152601800500c80860042030500e000ba117180c00e450801c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 234125305 1250 234124055 234124069
    0x601060503061c05101107020603070804080c0a110f061201090b18040b06042a0804020d1a09060115020c060a02070f0303080108060f01180c020f030715060906050d060209 75
    0x11200112095164880e2804e1a603554001148a042200e10b0900c01c25400881801110b52107034019111602e1621003c408488411000304103035035900c018400381042007010301c03010035214000c101412501051404001c102c81c203860045208a6040022070004000304610381d044449000d00040c0d418444400f080d000c1004020012120030180104070402c11080189030160303c080d2000c20a160710040c11500402103a400034a05c0c19041a04400c280d10417942142d0052001c0c2007500f410031240c2d20120003100b188000f03074105181c001008181c04080200b1350051143e40c0c0150702c20343d20310b000079480e620352600260003910002580c56080303000308000f00c000c244040b14248010340d28200140030780d0b000e00890741c0f2402140c4c04982ca081c10f40c038440b03060710340f00d40003180c0c000c0381e9001001c02012840d48030741c250700a000084801400a2010700714650141a40710004c8403005c031800c045039004d40102c111395146c240d0601c4282c94200810081d01d6110b80c0059071030038804006000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 234126555 1250 234125305 234125329
    0x40b01111006150306060503010e1515072a0501050f0408070b07060b100503150d0b01120b0108060c040308030a0e010c031b080601140d0605040c0c02031203010602060106050306 78
    0x40c0c801c4010030600c481c03203948900c0c11560036018207111100161001c80a64015204040004909000510480c111103d02c5600103415002c0baa03101281c50300415140381104840042c0d0800200b2144d083c0605e011500020902981a00111900038408a0712442407070080504021021640d2911031060350300700c3d4098a41401100c1c002030750744621548592000c9800c5503524140a0601901e003405810100c54460580754507046a841241042d140c000300541613038030065002094000c00c80c1602c00134040d1258603115810100e181c2042e1480141c1a80710403050b030300001c1040f405001c0401645e0076298095501e03a581d0300ca0301c48140103010a45420781542d480c1203e05101d8031380544c46a50207203403200307a078003a0200d5640251800c0b482100c0b4075022800003248440700c507a124000b80700381c01407214001400c40d150008681200c941c6a08007000c45e0f0f54002e107a007076203003c0003e1451403d201d81e05514540c10818000c2d1a0b1006105810070b0100103c00300304240c0d1007042d0469 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 234127805 1250 234126555 234126587
    0x1031e021507080c0601031b170c0405070302123606160207091a0a1509050411071a090c0303044407030c15020a0f0501112701050307020c040b01 64
    0x4165841341454154200030343c0c03050b280423003e1400021030401d428088079600d0000c401504130700c00c1c3c0c1d41c14032014180c010104000c00d5820044240e1030340e610202c0e140500208404007051448001e41c03806801d05031101174842c21202c01021640390000a8002d612103420b100084400a100030140d1421b4521340250540c14100b403d160400c41d00301401e042000402c03610f03032030310560f40c4500403d1828244501d1000944a02041c007907420a0780102244e0b001c0380030701502c0c0c131000340c07603141d074900300e400d4084000c0282d20280f010402c1c0c1000215280c0c00102c0103145403a00e0a4000002400c501c511644001410540718140b03220303001d242c84503000c804070740700c00007901d405000d52502c0c107030b01046a5080e190780001c01d1032030302c515200c240301d003060700106000a80ca80350250400005117084a1541d00ca40b19022142c2c400350107040d6442122003d5440d003108045481d12541a030090740741004001d02c10040300540c0007031a4400c0071400c3c3c030000b440c2c1c03081200407100c1c2140ea40c90b1003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 234129055 1250 234127805 234127813
    0x1d16090f0b06072a1d07020f10020904230f1003140a12030501060509190503010e030c01050903090d020d020d120e030105100f0303110a050a080301031e021507080c 72
    0x414018100440382d14060b1a2041044441d1010300090360103039240905e5500400c00800f250a183c0302c245110f80041881c0125003200414003101d41c54517441d4440c41001c2a00401ca00d442da0a06020f00301e1f038034400035283c21705081c00c4401e2061490004003034014800c100c2c0f000ca1001c400c80a03415000d160080c0300c1d0b90040c01e00084403980e454041c1030451310b10605000d5034011700c0c824412035050328020b41d102403401d1003640c01c010528003600300542031041081c01c0026159001d00c100690b83c2d00325409140c682ea2850f801d1400c564000b0072183e400d0f0410807211403e0340d15a1a1820740aa0480d10103400814500100308165217588009241d8128520b40c507101c00c0e0010400403440f00110000d21083e9030321004411040e0051060144030103076580e042c4000303409080f04034400d2051a084a00d00d01c0182c8030315140405005054400050000050050180c0000d613051040360b08910000c0407981940421240e8640c01c0c1403800020000c1561000c00c00d20004498100c843c0d04200c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 234130305 1250 234129055 234129067
    0x2041a0f0708040f1701060311010c060f1d061b09040e0a0204090c0f08150606031b04030305040f08010c090312030207200102010b1207030201030b0607050307061d16090f0b06 77
    0xc0203813400140902e5904081081d0b170201c1d0130005000f55419244d10201c100401440c00006503602d81084908a440d6902c40707244008046c110702c04c140c400300d1180c00d42420360843c203034071070704001d805000004600c014400300c4403901e04040460b600c0403802c1d540050041e0352004070038280b40044000a61003800d00e021002131290b2a000141a984003c20b42500203036a8a815640c4c0e0309442c18818902000c900003a01a04e8903502560303014542c04e140c40d00303034105120711994960082d04200c02280c2c009c0380500c000d0000c010440042c00f8824000c000d19150894050920069480003d195034108078a020440c1c1c800c0d0142d41c41c05500004015501d403e003a05501103080182d00980158648a201c02140c98a1000f600c003103031880d030291010506603001100035080312111a9002501040b00800007641000200900b500503080000c01040400020228501108070400698040044444045507030285441200c85c0031030006081180c800100000e4a0001c4015501110118003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 234131555 1250 234130305 234130319
    0x51f0617070501020f010605010207120c080f0604211b03030f0614030609060f010e07030603140309030d0801051e1906120605091e1f0602070e0a02041a0f070804 71
    0x280020b4075000d8007568400340c0c4043c40e0034201c8007a48680ca00581c0032035000c0260034140086204014094240c03028a140c035101c442c0c0c43c000020400c0505540420200400d110569218003c01064504140c80d081a030407401050501f01c02481100320724031100c243d040601230381c00070070134408515080c000981c0c0d1f1590b000c6140b403503a1242c1d00a000e8280000d409803800b0803198030a03900c2103984c9442d40d09110005000100c014510020306603200340103c04541000b051001c0e14804000451b517a803d22414581048040911002800208030060046039540c1503034400240c144400c4ca44403109140020714400d21307050440c1c800c6007a03d0008601990701c04e0403132400c000281d0041c070043c0d82d94414002c408008940c003900190458003906114801d105240e0b03009060005901030a92102407150754042c29540010003503845004100281c00c10140e5165114070042011401d180ca088154560136140ca02c3c480d020f40381c006000c01e42c0164010035a6002038200801c00d40380c5441300a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 234132805 1250 234131555 234131563
    0xd0b0630070f3608070b03010602211e0301031209030201020c0f01180303020105100f05010e04020a03090215090f1c030309020303040305010c030515041a15160c0e0c07051f0617 78
    0x4d5075905019a0700c1c0440c0d440b220700b08490403074100da4028403a14400120180c0001c0e06200312000c0d42004000c6a409007030344d8501180000d000b905150355952452802010000001c440c07141400020641040543e030081403250517007800365190880ca03c07480300100d030001c442c031185800c16110404040103150741544130510502c0307810a81c070b90301030b124441148040003511901c0c1c0003503004450680310341490340191200fa1b1050501082c2c0c05141c0d40090500e41c1203403542c5200200202d10b40311580750200c00c000c00d9030030907601e25000e59103d0012021350143c4034006030a05489401c801c0454504004071001542c0040c000c01c07018039410002405030605455200580703195012244aa2500d4030400e0220342150658035083d075501d00171b00021005880e00d000300603405000c0340703030103885900441035070078420895150040e060002e06201450083c00000742c2443c180803980c001400003840541810b10400400b1000c60424a444061f00840e0014844044101c20003145150001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 234134055 1250 234132805 234132809
    0x605010b0a0f0c080a14160515061509060c0304050612100e0105030d0e060d02070629060301030f050a06060909051219050d0b0630070f36 61
    0x596440325802e036511045814428064000d4100c01d01000018180c81c05140c0d420030410117085491308040800e08500011000118240c81c2500209449601c104003d9005035200004640310404808204441407403801b504c3e500d00d004000010381da032100c007420170a41d07000301001020566100c829029504403004243c504102010b07000c80085041103414032964142d44001c0c00134081c1c00c8010320211040605440c01c1070304683c0420200e1818101c50000f0310000340241004200616110481a140d80c040c20480c041040005140d8040340d64420071217044940000c4c0c90b0044402e20300b0601e0916213449802480245407640000703c11010350000c1480074012030585849c0e100ca01d5050003036108000600d0080c07448244101242c50150000d400c242100c41000941910900c010517041c2d40844450080f800b002070500c14084091b103d240714922003e2010140c0341081d00024000c1e10300800c0a1060200010420348980c010085107854410501600070000b80a0309400c400f03a0464 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 234135305 1250 234134055 234134057
    0x1a0c010b0102031804053103090806060105040b0a030b130b18161b0b07020c090c04050109140418081e130b070c0f23010e0a1a070605010b0a 62
    0xda540c015903002005031010203043c120002c0003812004c0400009010082c00759035003003114001c910000c40350403100d840c1d1058241c1440154141410040c0c0310b0340c084e42c413503501607100c0c5003040b0741c699001c01501c0c216156a100103407610400c44041e40540140b11160b60003544c0807070704d40d0801442d50864404640c3c02e0b5111003520f00c0d0781c1e00c503802400d02154081304101c68000c103100030b0f501c900c1504000342c10400300e1103000302d40d6075107002032920148c43d4900180d12000d40d404091909031040d42c1c10030440c0710b40910341307032502c0c001a02a44a41c031804101003000f000c0200292903a421000c8014110450194840920b00c0c2400302074000b807241d0b01b0035090000c12502a846580101e030780350f4030500f0010100740d10341229041c3d0f95200305400c4900c8681740d600000c41c40380184c114805403805042c0c3c074020303040c0403030300865840c0c4820130b040c1002504015003803540c880c07810f41410b41314911941c2158811441c100c04141c41544002400c013072401000040b82c01d141c0020341100112 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 234136555 1250 234135305 234135311
    0x1030606020102030f060909030702030102070b010f0b0412080310050d0f03020c0f090f04140a0302060708250c11030a0303151203021023040302030c010507031b0302070c1a0c01 78
    0x580354200e00300c1c0070440700360f142003008401142039850f000142c21750000750701c011640740000715800300b42640c200d20300c111028810b00005020f5000201c5c0114080c0507040d01c501e083c5454619a000b8040c04058080c10181d40000465070b101410121980580400783c43c100070009035181c0040504100748040c0c00600070031010b421507151100c05151a41030052001d40d0030b0f1115001c800c016200940100c03408400c480d4550f01e129002c0c441008006d0194002d8002e0b442c0a48003d010340c0001002100000104000c011058081a0440704005440e1818942910081c0b411101d80c0600d1002241e1610500c5259410140e06802046e2102e0303043c07049220640d07a440071900c3e10185010000c0258205000c1810f91340042da21035140d05440e4540c05002c1c0c0501228082082c8007604e05500507003000590314003415017409a140c0000103880c1c10000140a154035101100004440104040d00018843c1c14001c0e0300020f85c0141059404000b0740301c550500505d00d96006104002d0356500b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 234137805 1250 234136555 234136559
    0x20106080102041a0f070b0103050604060615120b12011a0111010209011b11040203010609150806030601060f09030503030708041415060103020304150c02010b1e03030a2318010306 79
    0x10b0083e1070403502c0d0280502d05100e40c0030312607409600003082480302c0c007609104010205c0c807228040c600841c020005040d8034146410300c0c0c3c0a0b1003480d00000c104c40c40304040c503404582c0c4542c0c001e01c440d10100c2c0008086007032900244070803100100320a032660a041c0040340c04400d03036129004e540303026200e1000d078070b0100c505a8241c5c01080b21040c0403c150b04c10101c458000b622a5041b424400c210417028003c81e00002000c982080c1c1040c00040c598003000c1c44110b4032450b80102800c81400e10700b070340f031414a0000303030303222414050301d41003203198500607c2c030754056940403010319803120540b9120b00e400c0c90000c149140c00c40b0284d03004210f000d140905a20041040078008003840d04400d560342e0303400c1c0107501961002d0022180740d12408801c0720056640d2140441344011039002203564540c0368100316411203610184080c10705400c14514260340c0010403550600b40500b850001d070240e180c090701c8055440c00507403c41590014a944201504001c07440e0320346401d89042065607 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 234139055 1250 234137805 234137819
    0x607021605090103241a0108010b07170c1e0d0f110c04051b0309060a0b0f03150c0714061603110913320106020c0102030304110f12030703020106 64
    0x121180300c1c06411041e00c000520120302d0022101844542c12406004140301c031681c0340e4200c0d01e10310808240511110000c514969010850b80d004040c001f401904014654481c0514114044200c40071400c00240200000e4800d20060200260344401850454403154262351200c140c40004d500180c0708055030310310f490055500359844203940b0020100350018809000040070b018000708c034481119656041c0c0049000b00840c440c072110b102402c443e0802101400c20f44000ca2415031007041c64a8012000303450000e01e07250b80808080a05015407581052007510b0311640c64080c00b00d007908a0394401c00100001c41c2400343d0118140322802508a100c11411a0b40a110784950900d00304032050403850040a054400f001c8d20000244072602d1030324421501843c10704504200920343c0500c91024184400d2a00410150000d00020b01110300000d460b440b00a00c000d01840c2071015a40458481d003001010811001d4041291800076161032a540d400a4504600560800402140003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 234140305 1250 234139055 234139093
    0x2a0503060115170c040b0403031718030a05090d020d03090e0f2502161509051806061815121312030906020f19110102040b0409020702030a0b0405060702 67
    0x60000356200300000c0c41c80030544034901c402404e43c180081003070001003000c912220003040110310a8541e040e07498094408900c600b00014821450240001c00036203000501100326540b42c0100e00e041503a07003066100146580340200000384d000030800d0902020143c010b0b0700e00d020b0719009070510005030703502c2c206880e86200807600c10900900d042803c0c0950031204201c88001c51907401910929140b41c40c1800080f1601c0e8446407440a20380c00c60040c1a0300b10700e07008081c2606880d4440002c202001400104501030602c40c0038803800240074080140724000c000540400828919066070307410305130788485d00041500402d20f000807011030441c06694102c1c820040d480040c00e10001d40d40e403010303801800c03440742c1660100e0f000c000464072104c0000081c41d50742c0b020540c1c6000c0c2403118500400340422211080003aa1041105001c1da08442c026102210314044000d0b0356880786101103820300c40c22100c000c00e10301c207410900080140104105100d5911642201c4224078010109542 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 234141555 1250 234140305 234140339
    0x5060a02030108030d0506040e0a030206190905030a0503100f0807030c140d060b0406050307030804031202062e030203030a1d041103060904020102120f070302100519092a05030601 79
    0x1030b50707104000c40707a10311100d86c1019500c000010000980c0d084003019650410200c03030070880c0141c0041c001c006006121554420307481908030340800c880c1600d55106030f501c0c492148103800b07008000c00060040a030380a1f084010308401d00c081461140e6603258180d60b01c2481c0022207618001c90340110b40302080d05038101030441c000708028602501d540350903006101d0586066000768a034000400c140d142000114002d512801c1c505944a1850814204003103101440108541002c010300c0050201e14131540094040ca00c4420002c405600c03458500070981e9000030b40500000c41c2e07400000d40c0000610300c3d250074075a0b88126042c18101000101d81e0b8106a4200c1001d0620200724141801e5940070791040c418011660403114652980c2d81581000c0c0801898210000310b210415605110890f0902c440e04020f02036407c000c40c4890b42c141252807841d40c06a642c0d9000010300100c02220441c505a0080303200055101629030140e2154a004031030007881040000500e01c2c80c40203428103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 234142805 1250 234141555 234141569
    0x51207050f0d3b0d11090601030204030b1b1e03160207060f080a060e01080f0705041a040905010b04050c0c15040209040210050702220c0c170a0207080703050a05060a020301 76
    0x3c40300110200c07120003055000614112451241d9218803961641006a81c9540c010b103820120700c41c40c8010040410350003400c2c40e04160051208100040c510500c00da009a80911070f40c2030010303800744111941c019149030070f82c1c0790340b950401d40b11440490000c0d40210045541c1140140c0c1030201640d0302c40061251320009038070000c1d0046254070500985070000d0981c000814119581c80d5260300c4110300380c0202c0401c0e0005451f5400e00101000310200800040d1001c2c0011501c84104628014080c110369016036210100f40e01040380c20751062203a228020000c200ca400d0151004171240c200c40603202c03280c0315045001c4270140108001510566004000c0400c3e035803241d0901010300c24400681c014490140405401a80c0304002c1e44c01108521499000034820340081c035080d00c003010b9041041c0a1000201d2003c5814052524144000b88020700d5540a5010040740742c2140c03a4072a484034020600d001c01080302c0850540e81c10b5008104070354450f100c040300c01080344400c0c81459 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 234144055 1250 234142805 234142847
    0x90c0103110316180306020405130b030304090207021c150606080c0702220504030c0c0b030615030603071a030702120c0c0d020409200418030503040609051207050f0d 73
    0x74801d0340454503040f911080d64941002100b8220941601c0010a0b42086540c5500810103020a0806103040c0c030000000c81824090302d400c80300441c3e10b82c4500e0140301d014036000985c010a54940c00c2c410b1405101c60360030f6500d0001642030401440340001d06030b5500c58200500003c0080c46000e000e40509030b4100003515140d4194201b0440b445101c2c214030f0b03107180880346600313203841e01d105440c402c40c000e807100c0080c0003091401500d61119900b20b400e8145060040c8a141c0c0c0712282c002d40d03c00180c018141d5139894540010340b4101440d031203a401d0a0018800c0e440800468001c1c5004011076000c448100a854406100714090903541052035480000030f800245480340702401c0060010307100290322541ca44a20b0b40c2030800224404d500184903510068a050512460031003114401c00f100c0e1080b003d503802041c0b8031001c1c6c0040c0c40d85860350a100288401032222203500d9188032419682d4004600d403007034891400800230401d90141c8a8a0105140241c000c0240d00c1c4140c0303181 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 234145305 1250 234144055 234144061
    0xf0905062101150f08040b0f0604020c0a0501091109090d030213091d060109060614031803071208060925020f01020c03040801060b0c1e010209100305090c01031103 72
    0x21140c01d801c0141c0e2000c0707071030300d468a03003640440e000851806404107070324010081d00c0c84500a024602401c00305000c0280031001c1002241d41e544075540c010390034840829460311036170700290103030190280c80d01c4d290068a01110070004150301100800e481185114415030b1500100242ca42c1700b240c5000c442e4003e02400c903042842a40105005103401000c030b018035446503003aa00b21041c410b03075a5011800c91002d1840c880741080f880b8010319180c9001d00000d414110001c1c494298422410a503040c08400b0400084028403904d4110a4040c100e9403074007010306180c0c0a102c1811402004100a100821000e0801660980c400c0980d440420300c6017078120040d11250124440e040110301584031104100d400030b0004001000c2e081008544840c1481c00b03803401c4503a198410030303859100700800380769075401041d1400c1008186480d96994601488914003a01c503510020f5030040615901c048003e030581d202034000d030441402c6900d5403c48200640840b040c1c91240000f0703400502c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 234146555 1250 234145305 234145309
    0x7050304120c170304140601080709090f050d080f0c16030e041d030d2d02030601121104030309090c022107020307030624031101081302060309070608070f0905 70
    0x1014106089514085242641946408280d0481e00030320650030f2000100b80018441e0b0301103c601211410009008a5450128650b5440c4040d00c10540d01c070b902c0314100410310401c1042a01da8503000000d41f4041c4155503401000344030200d500c03a001d0100b41c1c0100311004410005c1c1c520620000e4501c0c0d1320050981c0b016151101c0b251415640580c846942c1e02c807500030000d0501c0d450007000004c41e1101421000c0c0c00641702815108501e0180081c2c0611290a01c401d42121031140030300c0042c1c1c0c1b030f203d01004a405030704081c5002e582a09040a000c05500504001e00c1200d00981d9400402c0303403144004000c0c4d401c440030102c0140d10244c0b500701c0b070745404c200105846640304019032a12580b0760100e420314000340d0040e10104c7c0e40b50300c2801c000c000e03141d4546001022411020310141150759000d2010350303c0c2d10050400c988940000c00c0d50418403415491250000c0c04503840746042d91500707540710036501071480050110b10110b2203190099002000c00c200300c0c0c4590703d00d81c0c10001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 234147805 1250 234146555 234146573
    0x15010315020c030c06040203010e010b09010b03100f0308090102010f0203061f1b0f02030c030c0a061209020d120e0402030c070f02030309060406020607110304180504020f0901060309021807050304 86
    0x5165441540e00b000400300d480020001003c002e822503020300001e2520b07004150848a0040540c1c2c0c440c4d04144101c070150391034029a0b8151039603060501d850351140c0d203850300342d100b01d030708841070000300c1c030b20080180002ca102603c1040000d9000703004441040c000c880030380c00203075034503a000401d440c041c8001307558a2075880c030000c0c00ba251820101055090b040103071404083c0035100429003903180015070900f0f010b0340782144410790091139031402c00f01c00701c1e8805070140304007001c1001078071083d01603941a800140340c02d03030000e1845842c00d403581400001805210000c1c0c0104402c00840320380c504050080e00d1092260300c91803130070300010341c83e0013841c40c0c20148200d80c140000c00c030445480c0c0d1004007400107409543d005158a250088020f4842155000690500e900522040002c4d003500b0b13000313107a500c40020700405c043d100c91010600d2107203441d2160364800307032140020503040e60560005103098001c0fa841901c411141d4103201080b041600d1036800140204001408509100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 234149055 1250 234147805 234147833
    0x31b060e12010e07170106080f0a02090702070e0408030a0b0a030503040909080d020c0307030f14031305100c0503160c2d0609120f050306010f1b0602030a090c08150103 74
    0x21001143c010954150076041a402d900020406001e44241c4803521000f4403a40b40a440c0076001000c200e4480c0010661700c0c0f110310780080c4142808800500040d209018840051a665444503d1410103191001c425002266003040c028907000390b4180d10b1134025107103003c40b074011015525150401d20040007402c0030000940e1040800c01c400d1070113400c6440280024850a0099500d8009514008000340c6103074501808000c0071800c104400c100c50b9040320381054103507150700518800e40c81c0550500b403412441c0c502a03071800d610b8020268000006601c00c5100041f4142689400c500c2520204035040d400303130282a40f180045032035506020302d15046004620300c0e000d055240d503100700648074160000ca81212100d03180250458101c01000c607031030710301d0610504501c4c1040c0001c0002280c10703442c1d807c2040510b144040d050f00209034050890304090195602d15040d41d5080c080d0020603030841c4da80c0407101c0f00168040c00403803169030721b424840c0111002c0c0d1075034480a03404202c01c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 234150305 1250 234149055 234149089
    0x120c0b0103060509030f0d061d0c03010b030a09140106050306010602072405040f06050c100504240f0603031119050d0311131d0f010605040905040804050d0507031b060e 74
    0x3040720111454605001c0c103c2108451008588c0609080715840060400f034484081000301c0c03420300484034600c00549043d03a511080281d10380d660845924046e04100d80b001d0700d0017030443ca0500c0103200c190807000980c2c20079422211580d80c0d5a0081b039964045100304094901d035a0074000e40c1e0240000f002c20172031410710b45582000d4483e40c02850b001d980380d128001250000545070b0302002d09102700710300b42c0030041d010480c628054582c05143d0150a0400d4000107040c145900800002e48c04540000b25254007001001d45910f005442c40c07410710703040401c03440790000c0c0000d5805900032031848103038400d000d030544101c251025130180038040700618100c00244201030b43c0e101c050508000416134103e40e0045940d8200b2010140c2d031001c0d0405800c3c210800060200c290071208880071503409540000da00d07071b100e0800051034007550704075990001c084452a4280080040c0350000c0d01c0c0524182c2c2c0040c4100001801d400b60240b042d1004126a0984003005141451030030210440c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 234151555 1250 234150305 234150307
    0xb180f040e0313150203040f0909050109061503171809040317071e0329040207051e10020307020a0f02030f010f020a0906020304080c041e020301080a120c0b010306050903 75
    0x164590390360550f00300c40c0c103902481c0c040a408019504e64040c840800e02c07220300156103000d04103c04244580d031103000b0844201d413240348540c1044025400000c900350064401c01c0b080300540c3c204050740d01c06210554184c500d00070f034050085103a50172107103141c8008441c01d040c410800140326400340001d00c154148070184c824161020b0a800025110b03682d90340c0d540d42e181124a000b1907240c0d0860840c40d040504e0f00d00b6041c0c101460289842c01c01c12002c0031851103600d2140010080d106a0000504a021714070240c2d000032084050031035030503081003c0d907054070b10001d101e004078001140e0f058010303449404c940000c00d9040c03640b400850700140565409900d202420703401c0d100549070104802d07030300044c0100010b5001091704068001c51028615180c40d0070a0981d64100456082d071049036035101c02621003203191150b83e80380b0b0050704155101d6a5884038603480303c0b0901000e44003038034180340b101c25140c0324200088000f0340c4000301c6903141e404c64a40c034000f003070002c11110301c0d440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 234152805 1250 234151555 234151571
    0x626220215030a0b1005090a03080c010e12030115050309070b030402041112190c120b0d0510021c0e1509030c120301030203100b09070e01050904020301120204060b180f04 75
    0x1c00400552040c40c03402008500e041c03802e400d100c07007800b00341c0e044000c1010500101059540d41c6544070220380d000b40038191194454a580d50040940440c4141c072403040d8000308024440cc0c8025504847c046010000d00d00320300c90003550303c0c0c40100c801e1200703500710b00303400d116001e4010051a0001c0c0080c00022320503003948201c5800b6841040c80541c5200320004020310907001650100d02c611190006101c00600c40c14048c04135004800d0080d40c60361595141d8071681c58600c42c03842d0300c0742c11500715201c1543e00408000294403803002c1d10038001e85810f81000f003e99a000d0800301c1074a100c014000b4134005000e11292000c05807101c29a40001c110044070074400300484855283c10b00e0115070349500d107104042c80e2480450504000754209012190590740b00b0284907072150a9080100b4031601c1080100d0712442441c0240c0e80c000c4c4040300104039501d589050030f00e03691003500c04101d016142d0b140e008450240c0f000301c0c00492040701c03000300c60b400c0c41d03114295400e502510110310070b8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 234154055 1250 234152805 234152839
    0x3010b0d020f0904140a0509190f021504061706030114011412010c02010209042a050a0504030b070804030f140d02070203070308030901051f0f05042406262202 70
    0x20755060040382000040b0b41445886e81080c859240c00580c4103000b401c80000004451154504100014100820440f03d00d0295140c05440c1c1c078000003010159035480c0d41b6024041c01120070351800c4010b05441400182d540e0905108500c800c4111085400c010780c03900d06911403005004103601e4200405010520110300240500d1403502c1d0240c00260b1503c02950921003202c01185091201030130801a042c1060203800c2d0120f09026241740103a521065888181c0e41489503500080840380d2020801143c2a408201c0d10f0045110b60749000540300b0704541200c20342481c0b00546180e1004006110911166900502c2803610240680351400d58a032210015608100d4078040180d4480c403c0105003082d004049039000c0107205e05406e5607050498494031140b0a020b014095550b5203400c0c002c0001150170594981e188411b40004c90b500c69000030122400481034446a00103130078500302c50900208071390b11608801924005c61036500d00c29210b14074240c0341c140c0e0420405001c2c01154 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 234155305 1250 234154055 234154061
    0xf07020c0d0501020d0b06070b0105042301080a0c05031b12120f030105090609040f03030f0e06041a09010b011b0f020a060c0215190c111c0b0a0203010b0d020f0904 72
    0x382c000c800060b1146044d4055200743c6a240c02214410101004200c00041c9010815415220107540c009040003e011001541000d0075a8124258040b031780001000c00000031481d0041e840707a000510282e5a600a05507a1a0000000706006000c03c4408900342021110000c001d0610001c481680e403030400740031803030303400310b01e8041001c034001006200a0400d80c200c00c0d04400c2c00c3e46c24400c0c51401d915009824185508002c0070940c40e4554113101702d030160031244420200200344c07910bd0510f880c1071200c0210880c00b0030031107424040090604101032295540082042c0c442c0c40050409005042220600785401c0324140c07070000d019005038843c06411009009241c40d01080001180100259101d0803911518108003c000345511079200307400f2141ca4400500741100444081e282c90820048a00440781d01722038803420001e02900c280030701c6800b490050320520199111944410164070003405101028041007226003410f54a5034020a5410030040d1b00e94201500500000c080d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 234156555 1250 234155305 234155329
    0x9060303080f090a05060a090303090c0b09040c050406023a090602010f090305040b07050709110714010b0f150c1f0b10080c0a1707020303010806010f030302060f07020c 74
    0x28108002c001c54880d256500b150000120360003000756a0840d65031541c2d8203001441c841c42d00e034032001c03000105802508a0801940d201d523580300742e02e403260703510303650754000c013503034600c0b4504101ca103800c800d00a404035415251a5805004040c506010f050703e010101c207148172508441100071030b01c051201c0c03104400304240366290302c606490110001c3c25130fa00141e03c85400c80c5080c0b0040d00081c0c21100700c404984458121944a04050504074105100da41c00310b14036a080c41412402c20380300b8002040c90300d2081010700002d001c10564242201c1d040170b030058005000e90310680982c940541900703549042c030003400f80b80101c4150006c2c1442052261107090f0850b104120f0b0f400c00c160f02070307088800015182081d20080c01440200400c401a080702110000090201285071083c542030b1490400d00801e45280e081000d0001d50380c2d803092040e1001402508000308a503460030f1500e10131a40c0540c020a0706840b081000700075004040e1a80382035100b181c90801c1561a00254418 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 234157805 1250 234156555 234156557
    0x100906050105030d020105010602031204020f040e0618240606071a01061101021603031e02040e010305060c03091005150d03090602120c030f070203010b0612010f06140a0e0a09060303 80
    0x61a514042c00c3c1898840c59108113030669040100500400d0341c00030583c0c12082021519030040d407654008120300400e00c07140550402e082154200c400c440c0010518043c00c25207280c3d114001c3d291204075110340005014002520103682000110302c0751001d229003113032004020b14a000000d60754800e02c000c2c061a449030714014a0b004114207600720004840c070340d1610000f036207007903400a206400c01e42c5074040102815520072060504a90114007800c446540b9181155229140e034a5070707206100910040307880748909800034090360381402c00c5c1e078090700960340200a000c100c00b50540148c04003c0151491503510058035405580e40446d80304003070f019031554240c032030610000a0030110f151011154080c0208060015050b0000848820104081d00c00b516510070340300003409422960701d007640c40b1401044100e044c1a401403a50b04842032100100b040300c0d80c6043c01e0f900407207055110003100a0500881d41858002c00c401701c2d110000078445030406440300708440844081ea0810b030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 234159055 1250 234157805 234157811
    0x204050306190c05030402090f0712060f03020a0602030a0504090f110a05070309060801120221030a05040e0601031406100c1704080105061503010b0a0c02031c020d080f0711100906 79
    0x1004402c000d02c144240c2c2c83d50307850410f00d035103015004150b01550117065200c000c8400740020706114440e0501e4008030341c2d440d406012460383e45841c1128003046020580c0b164280710b0300000c4072400002207a06211154851904292501c4110300c018a241544a007905844a00e0544d041c540700d4018450b4414984030315403107840f1030030004c2040303529401c0710091003030b41c40040c0000c8101090340d41c01981e04540202107007040c1c0594003000b00d11f088000b4600e02c004100d200a80d504100030f2f10581c0c9071038420300c096a4540004405447c0000b102815485003400170441c2410001819a0060b4450a050744100c085a880c1c10b000094540c02c0c0120707500c085800d201d400701c280112600300381c0c2141e05050301d91803002d0395001c1d8841881003010b035200004420280341c0c000c1d5140d407007060f00102038541c018800d03025030015101f0000d4020050198548500895015030121030103900d4480500c07260ba95020025100c0d0050115910964440c2045911406820f409140700c0544550004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 234160305 1250 234159055 234159091
    0x1809090c0402041d150109090b030a0c0303111501050603180f06010e01050a05060c0d0f212003160f0e0a03050a05060106020a0f0605220b1501210f0204050306 70
    0x7501009000307000780b50046142c0c1071840d400d070381c080001f00a86052041c0010302c10100c000207481d200107400001c204a0364407100105260304020305c5c40101c8040c0069801003e07a840044025000c01d0251540c006014004951003a00c0342421282c11000002225880031440035210300d00082640b0041c1081c120030018061400e082c41c5000090030162030b1182801600c1c80d150343c0ba0205111180200200040c2c004081e610031606101040640850010549074445a00001d06081c1032041001540001b0401941080108491040829408020645404420407902a000e4808250070465801003403005a607840d920741c070080d4401c10040c0214851071400600b4950160720040640d000400004042034bd070340394083c0c40c0c1e54800c10000700c80c0e031070071580710094540384032080000f0b411390404400c0083c202911401090001e50754401c1040b45c4004444850b45a5205104004110352052140340c040e080700b41c2003040300c20f015051584510100c1d29040c011503980b842d10710f0303c80c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 234161555 1250 234160305 234160349
    0x815040222150803070f0602030a06030807030c05011406100f090f080a06050702031201030f0303021c020a020f03160b15061303031416030c0f060509150c1809090c040204 75
    0x2030302c030041542d40c0c0130318104a52078075042484d480716103000d0660b5800000040c000100d5230b105601855103d0706c500c2d19a09203050003800030824100480b000d610788100e08101481d40d00c0900c1c843d40d40107282094024018500300c42c04280408164148007560b540425451410b251420142c0402d40051a242c0100c2c14400c0a860b005002d0900f90b420400c5a1800300c0b0440c14098150b0741c000b43ca4540c09200707450200e00a21411840c1014442c102044824980140e00181200c541a40c215400e004104070f400351a0312440d80420001030b81060380c40000b409200c2c0c21940203404041c9400020036241c007140155001d01c50b000346000851030709108140c3c0125841100411500031281070036124510f00d1461440707848007805004007900000100040a03890505003940000c040c489030602040d000c0c1d4070b0600c14034000b207038003c8000050280c000a81560361902c0c100002a11081d07a420922140c2c05016181003014080c0020b070000c04e80310317800200004c1c080f000c0f2400b2040d0039107070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 234162805 1250 234161555 234161591
    0x6080f120405030c011b02060a0e10030e1e12032706010510030e0c0a0b0d0b090f18071d010f060c020922020405040602090103050f010815040222 64
    0x8421503a160500c42803101c1d8800280c80d004185007030a08003c18290b103407200d4103011600000952294002421002d02c55001500d400e2100c810380701d0b00100d0480300410703801c0c0c40c14107100c1c4115a101016174541e130102c107070350070b0b121380f00048c143da01258102c4545034007075204a6820300b0814604010344941c401c004581101030307107540040c1a55504000014600141d488a6482015100d5514620941040c840c40f511214020202d040c10b0307036500200f4101c0d0300031700302c011a045d182500541260074682c221500c03030000003182001654883e609000032911804c4425180d1050b20008209807081c80c62002e160415100f0a003200d40c500f01c81c1e000802080e42128042002d481c0e200700c01030315549061600000c00c0356070b545c0c10b4103040e01000b00ca90b5118601039131107401c0c60244002d00075140d00505104800313903024000c0e030b600c21008140c409003e2140c28040c2d844020115040b00f248003005800900c0203141c910340488181d101d005240b03100d1100c5000b0b6a07103900610520171603030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 234164055 1250 234162805 234162823
    0xe0c03060f010903051510090203040302010905010b0609010507290703021306210507050c010906020706050a050103020607110402090603010e0f010603062105070801091a01050901030b010506090f0406080f 90
    0x483c215070360b14155500d09456258481e2a100c0140c01500407501200858020358060322003107904640382d241c2814000d002c0e041d906030988455103420313100c403c1401d0107001c5070070881c2c068507003038a0000b5598540d0150415a01011805141064103e02000b00c000010340901d80e50307a00541ca5040d800c07000104003a1070341c0300c0070a10030160103207034145906405407084c050380344100051aa607410029200c80c8240750b032030903c4c2d518141010301080707104da0141c0f120b540288400c001540e170b5202050202c4400b0301002e54880c80c1840341d45c0001e04101c0c80ca0151002c09880541851381c0f240102e09180c0082c1c020724024004c0748200300c0080229040c5d1401403407070745000d014186c41d08c580c00d05507400801e242050085072200301428000b040044900500901e80200200b09445c01e092607201352180340c0035142003d490002882d4500308440c07030306030307504040400c0c9945d190108014480d8040e8000b41d0700400850842000c9a0701c0e4404c9030000c011000151800300d02c01c09007075081034120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 234165305 1250 234164055 234164057
    0x10e0a1a0f01060c0b10031b080c0d0c05060f07320105060f1002071203020304050901151202090d05070608091212151f09090b10081b040e0c03060f01 66
    0x40100726481c3d2103003c000311302d50441600170740c0f03844051160714060043d40024002c28840c1140d040740d505110580e50403100000203507a0407003030b201304000d0f20720352801025042c5414200180403510300720009002218038596010f203000c4440d41c402a506a400000c50065a10118020007001c3c22414003824416594000c005519003000000c210451f00343c003a600520808091111982c005c00850002d4450000111a01d480921f030080d560b60241c0906401440d4080000621030a0441403000c40400c0d40c86900c0c03c40c1101400c1c6000f500482510341d07224a40000c0f04010a600f0311000d40501001c0c1c0d103e9280d423820040c0e26241c107110810b840640542045100308048803e031080c0d8100d68190300050f4204e1215000980000c1c003980702041c6030940cbc2c4031240900f40c00107044800c541d400402840101620304c2008120781d503d16628010907040000181d4000c403c00d108081080c0c4241d4143c00c19032541b0030120541c500f225150308200001051042c24a401c1543c911303d8107003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 234166555 1250 234165305 234165331
    0x501060e040b06120a05070311120a0c0807050f130308120406060506180d020402120a0b09060a0803090d0c0911030a050a1116020102100c1806020616050903010e0a1a 73
    0x90030031303204160311004000580c0f0b1070343c0b0380c08200070520070380125085c009000601c03a1600501080f030340900c401a00c40c5800d981c603000b100001640038048052092440d43c843c24141442d030a12040503034801c6c1c031448541c409030640400041d0380c98001e0034003002c51030a0311600d46414a014000c550287e001310f0300c40c1c3c00034401c2c50000e40c0380b012101d464140a80d0004114069840410064050080001c400f0311441040007104812039114034000c043c12030b07038400c1648070710090004c100311a004451154004101d40e10190a2003030044420520500d81c20352100d5465810604440d09505c071a4900e041c00000c4c010061074601132650810380d011410041086100018555072003186101210101c00c3c5060405581c02801504080c403060340c1c080c003910f500e2100013081034640c11a03d40e8404c0000d41c0108496100055840c0b1610b01103a09401001d0090b00c01d40b5030341c2068a10a50640d02d8541d103202d03200007031003151080e034451051502001181e41410241d036000038480d07420048 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 234167805 1250 234166555 234166567
    0x14040b130b040f060e0315092407050301050d020f09091f0e0a0b0c0409020d050105120705010206070e2b05071d0601030e0a0c080c010207060314061908010501060e040b06 75
    0x110141422089454505010103420b640345c1c00302e03041904d500f8141d84c41c0d20380c00082000c841e0300483d0810a200c41c0250001b00d11910018050711300301c0980742403001030410705c014051030a1014200d8000c50004160384804040e5500007200c0403011a4a0443d41c6c2001c02c8170101240e00c03102840710041d4404080c0b0031440c3c51051140d0341d2100140142c0500c00c0c0001051003883d01104071005011618820740d66281ca031110322010784420311400d401060b4540d0748541a00c80130a000701034410507800382510351104c140c125002088100d1065012094440c102242c0b0132060b10310507501851410f040302c00c2da40c0d00340036043c401548c1c05060302051150a11007032030940c09120703034004024280001e144050701061480d1166540340240890510800800d0104000800d10201c120903030890741a607881340d070200c042e10702580b84141085036000c0403506900d410020700b072947d124201a800749076951003140d070a441c4283c1c00760000c200a0000300a05040500414100346819901940740ca0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 234169055 1250 234167805 234167819
    0xd0905030a0b18010e03071a060a03030806030c130b0a05060705060105040c05070b0f04020a0b1602090a02131401080c0c19051c08010f050d0206030403080714040b130b04 75
    0x3408041005084204010000f002182c82c0c020b640140c3d42454001c000e0030511942c85907803544014400d465003803084000c2c414448070404081d1040c00701805191200c0d20f1a07505031095074000e00030350343c10301907034840784066140c1240c800b204035500781d000300c0c1584080040c0124000e480e041107014480c2080442c1c00f154000400504440c07050b40c000800c0001d00d44200c60500500400800b103500c40303401d000c040072081c81154000c9000700d6030001d15650300d805482d500d100d0050100f04020150302c3c60030242c5881c409482d4130440d6031802502c3c0030100d401a52237100e40303400000d8000c40c05000ea007035559010240030390080c0012155460300070328041c03165941c08450210f52a040c134028610081100c1840f15508140e210503c10084954815011b44807807001d00134005c0408481c07038005038511b080c0400c440c0c581d8014024902e1a10750303850460780780a0040c12901845056000480710484210083c030041603025038281d01e850340707407002c41070038a000e900c0000c0b411028401440f0700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 234170305 1250 234169055 234169063
    0x21308060402061b19080a03050c041404050a0e07080303012421060b03090c1302030f190b030a2108040302120d0b0406091d03030c0304020906030f0d0f020d090503 72
    0x13104078201519030020b903e12004d46014441c1a408403044400c48010781005940005015042a1510309011980ea00358115190340102d101e0ba040a003007a4451071010308066010386d802c005030810100314121103010061920500350b0080c21315030f00000c0104255159010100004200030005006064080c58010034620504503031103001c45e00101c60b207650104a51100004082c200c900030345078a001013049840d0b0b003000b15501e009a00380c6035448134606203442220310440303c400860105490b901c4000b144402200305880596a80781402c05040d5010841d180d10b00c0d00c40c00000c43c042403c44c0003641c203007003180c1c062818401c0d0b5009101c0025004242c408140c06549481070b00c0f04000c9021074085d00480e400150424a807107800310312800f594008015642a00c8a150b0141c1c52043c8029540d110071110070390f4081003400401c0051604034111074220030014201c132408a48110484d007003420030a01c5c0300c00726228203050742d65550140481074680c45241028100c00d440c04c40440d4403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 234171555 1250 234170305 234170317
    0xc03030405071d0c160f0308011502060906010b0c07031b0302130b090c0d0f1b08070f09050118090212040b010f05010804020409021225050a05030c0f040f090602130806040206 77
    0x2c2d490080b1700150005445131001049030303000216810ba040f254100504002c1c428007605101c442241c00340300c040c03800050307894015000c10740108901e80c600300e0007500b55009680001820b0003a4680000421039890b8102d00a401c40c180c20518103141d071040140c01c0c0784504070201e10340e00708401d01500d50340d0040c5003031b4885002c3d84015901c107a204100d200800351410740f420110719045000d2501c1180781041e09a0110a0b10380d081c940d1a00441641d800d01c5070480d000c0002c4070f291301406954429008621821006c584605050f078131803440005903003290341309009820802d000c0005008002039006e004005d84090f60b01686d003400f00007015580c0c0144003a000c0e9403220102d60454603012002c0621025007010740d81440c5a03000a040070111041d00d48982c00c00818002c5a1741c030302042c20707404450000300103051802c0ca020901c800035000703da078164855a10b0705801c401c240c45007d1451002d100e43d80c0140d039031100110b440c00d001000d41010320f50303500040030000182c07200c101301e5803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 234172661 1106 234171555 234171571
    0x4170c0a050115050901030f0503040f0602030a0e06030714070f0f121d30030a05040e0a0b06070f0507230909060712200c03030405071d 60
    0x303034294134000c0c1a4010803540041000424090500d400c00340f1540c1178a0406580d8088040241143e52041c4003681002803003103007071a40850700b440305140484040d810740c200410300400000320080e02c40a680d000148410a10154200c514030050340b01c142424404000d103003059160748030180000208070801d02c038540100d2984101201c1d0340c00a0140d02099102010180e4503880d0703c001c0c00c16041100c814074082d29810f06c000c1074079440079141e059885141481a03ea5114010560305a003442d00c052044030b0f45ea001e04071004180c0280100e90149124101075082400542c0b10f00442c0d0348048030080c44201d0701e4480400c01c80d084524090b5596107100003511540229003a20018000f1a00c000d525080384c0e100440814120b48404250700c0c2100c1400c0d200d60102203241c06943c03002c002c0000300141000100050600c0c001035282c04440312000148c62324014040c54 = true := by decide +kernel

theorem cover : BRFrame.Cov 233992805 234172661 := by
  have h0 := BRFrame.cov_init 233992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 233992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 233992805 ≤ n) (h2 : n < 234172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
