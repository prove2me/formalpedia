-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5508
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:05:45.636983+00:00
-- url     : https://prove2.me/submissions/5efa4940-b5d4-4bbd-99a3-9de5636c5bdb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 990467625 ≤ n < 990647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 990468875 1250 990467625 990467629
    0x31509080d0c080907060f0f030b12122203080315130e0f1b0f011110050103061a0108070e040b0a03050304240905030d0309020f120601050102011d1b 66
    0x9407600c1c495039040c14440c100034000081c1c2640d4003110107600740d10400b5000180c1620404844034018059250000e4600c0c0d200d000324041c1c4a40001ca54000920070b208540381c0b101004502854031603a036801d42ca480000901c03801c011031170072140741c45680e010303814408035200f0800c4035080424030341c4407000c0360b1091012400b210340e1599074811180c82c040640040140c00b046e4042c01202403c1030301c1d40150a001c0d800c4410402098094005e6035881105d5141d5014502c2c052225401c0e400301c0e200060620642c1043c3c030000d801c110b61040d241d449188411807100c15112440c1c100b424001454a40044020300d80001e15102030b110341c1d00c8503101e8000352515440b440c09541c2040c1600d6680303450300c0c0028902c00400c0607903985101031242c2e41c0c0215110f202c0007016940003c0c00b03043c2d400180402103020780b01c1494181d0307000e054440c0399080c40c1c0e07403040c0b80203203c01c03c00d0240c109036141400190840748044480c800703041d00350780200d1680c000443c08110f100e2030300c11840000f03070307280c40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 990470125 1250 990468875 990468877
    0x31b03041d060d0b09070924060513080607020c2b110a050a030b090c010f09030303110904021b010c05090609040c020124030b01060e13110d09080d05010f03150908 72
    0x10251200b410b4500303204116401003000c0e419140447c00511140c80f20900305032880c40d40f9040651113140c81d202c1400b00600c550010041c40c50100000c00001c0c0d140c1c0019030500b18159503450150744810f001301c00c203080041c11314840c50160340034a40f2080c20728141003120078894400030040090151421081d64502400602409014044103c050f84034035000a0000c400d0f10940c80d14071500e071509000c1d600c80c0d24101c0d0b079038507203030340d00310b030040c5141c1c1d05501420407a9109014401c00340038420894480f84060201c103d05070000402d010380c142015801c41c0c1c031810340501004010001031620b034440380121003520f6800d40380001c00e0020381350200c2c010400c00d01e01c112070400444141b642440546842c5054070300030107012240366a1b8070070580705841c0078540680c02041c2591312400900c2e00f90f1000d15003d0000c1851744ca00a006482001114821311007100c40100105071a4140d00d00ca20800707001d8514004d0105005046407101c0e00d8000c0a503c50741000c81d20740444a08000e6410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 990471375 1250 990470125 990470149
    0x70c0b0109090c0617071119061d0a0c0320100c0201090b0f160f0b010b04151e08070c0206160b1506090d0302101b0806040911010c170309031b03041d06 67
    0x5580023400700381c00c0c41e20303402506810f1083d19006842001d1358450040200d084494554400b114854141c51035403a44c2401c030300040d56080120904010084545074809450942001c0d0f42d10b4440503440703880054007480c060b42000d14402418085442c4e450012800c031a0803410120020304a026a442c01002d0368000c900014417a03024400000364035090389000d0429a0041e05489603200e00b0a4021203c081d901c101180c1410003078003004c12041e004428054001c541407410300d01010654010668a0340480c461103d500c007050808020f010105d4030f4550490440c54450288105207000039055020740301c0740038450501c41e0240800c1500070030600766800709102040c01041070390003103461162111000c040110356881c001a403280303010b1040e01e00c0c240d4001d91000c0003600d003078011948082000d07421194420501c54100f0500e000902442c407805042c402159a6a160307024205045074441600c40e0690041c4004c0c84501c010000240741c04080040c0c1d225207039201800900c03841018 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 990472625 1250 990471375 990471403
    0xa120e030f030d1d06070f03021810020606040b12030921010c0201060510020d0903080f0918060301150b0304120c200108070e03070e070c0b0109090c06170711 70
    0x200c180001c0555080001c904c003001903180e0841111810403916040100c900030b0008203030520b44041d00303000741c0c0500300c0c02c802d0700b0402c101c505060303009c1015850750110758805a48040d003080120b2405000d148814a425074100c03815500714024590303a8010310043c0b910800f2510150801d15138020303d5860001c1011000380a400294030700a40241080c0c040c06005008141071409400c1c000610b011840c4102c3c0c2e40c10748140d1658481481542001ca00c4002012040000e84525980c800700c880c1003d8000303030149111300b0028101030844d034280103a4030011181d21403c00071252088144e961145d0081d90a41c2024213075401184d100035a41001800c20640d14003180c00200951011842ca10003070320341002980711000255443d150140c49564583e016002c00d10026420a400301e07048600da00f000c04c003401150303070313201c0c20020309030400d81900c0c2d555040402072040400084c00140501d00300041d1200e94104103461000d0004c2a6005000c0e0030540304014000400801340d0540382 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 990473875 1250 990472625 990472627
    0x20102030d0f140f010e25030c0540030f08070203160b0d0605090108070605181f030606031401030b060a150f0e040b0105040e042405180a120e030f03 66
    0x20580607090303248000c2c05000301e241b01d5a80000c1c0450720300002000d004015405003066940403410880140c040003461004020050000c460950180c01000d003008003000c44422880422400d80800020b42615a41596000c40b500f00007040d22611103148054000915540da85040d001080c84d0088440d50090001c1d29040c2c00602589444094a007144d04180103000780d503591003c000b0300107400c3c0290005500306084c10800e00d4000d500504042084038420680e56560100083e80b070a103a030460407102140d0307011a400c0c150701d44201e2018203524103042200103401c0c61034650343c4105000040c03040c0340300c002081d00c81c0d5524000da40205041c40c5840141034508000801000204020304081200401c03051114a06401410896901a9141c6080515100285507101c1c4090000c1e2105080c904800d662031a0503100b485010090020204842c1012980840d0000741e007291003d0030380100d11120b0005442da100c400c00a5044d2801410400c4402e0000e820103004c08451412840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 990475125 1250 990473875 990473881
    0x3050d0e0316050105061509280303030b0909070b030103232d0606150a0c1a01031a09060c0f09041b1e080f07030e031812030403020102030d0f14 64
    0x41442c006400c09100d00000e01964444109024403403909000c0b0403003035a0140700a48103810004c0e2000141440c0b11140c4031010507101e140c6088603c542c005800107034403400314440340d0428441481e040000c29008040c050f01d8008a149980010701009104c00a85c8042422414070b0130040c807120b910010a03158010f10641d031f9078009040d41c003c081641340314003003a24041c0a011960398401c0d80060480c40b40720f808444030080355030102d0403040501101c1118000440c2e4021207681440b05400c0e0150180c2d411802d05440d84043c101e003110004180404000002c0004502c2c0c0342c21002d03139469283c40340e0030003d0000309800744405054110b490720f41d9028440003c0d550800b4081a42d407146061458021119542648a28200390205240c00b002c1030f1032440b0b810325130b43d100720a49000609451503004403030940d800902507000301e0754030000d207400602d41020450441e25040004518041c6145e0010b5144d00428441c4120250b035400b095410603803942200b102000e8a841781c0715189 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 990476375 1250 990475125 990475147
    0x80108100c142a030a0819150611120f09090402010509060708030103060f020304030507140a02090c0306130b0a0b0d021204030c031206060c020f1207260d0c03050d0e03 74
    0x101840c103064060800c41c400011240d0790203c01c55611a0f880d581c4c000c107a5031401c02c001f60489481610314401a0780307204202542e04505001c402805040c1c1e40d08000d150071020303541c030b48500004442d95500307041010745041090392040340c00d900002c0c5e500048682d1580010382d00c0f402200d60702900000000307140420444400029130580e031007110100884299058513408a000444009002c68405c010180c08144242007180c5d81666400c100c1342040d400b5030228060240a4440b028031041c01b009101c1c0fa4501031401c41c400c0c04411b0030400c13985c0c40041c0001c410f510148900c01d109ca50020348400341d507415070101c4032030b42c1c46a03011221a04062800078440c401060040d00042d081303015403280800340e401024203c5d26a5551500340030415000c000341080140030059000d150384421541000050001800902030180c0178076244810038140c4030b140c88118402411504015007440c51141c00c1009903c10b40d8141c540681c44400000c0b09034002c12000086240910011402d0001c407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 990477625 1250 990476375 990476407
    0xb03061201060803220f0f120c1d161103031611010c0c0b13050703020f040e0601150e030609060a0b01180807061101091101112107050d080108100c14 66
    0x50f4032040080500d590380c40b80d40b106d1a00f92070040c0c1c03484003441c8000300b101d0031a00d0700764039209009421a000040d80c2d2210b07080c12559090101c0180400750042244207000003a04481c80b4107181400d058a10500001c1238072403100400a03410f01121001002c1841d104400008907004110000c0214071443d0784050b2a407040c9100481d40b080c120780000d150490541640030410b40e000c80206111402e6500b00645810b20741c0840d500b2954035040b0400c0940304218150082c05040d090702d8800d9142030000b8082113003445002d01941c40b4030140031030000c00150303480d402003008a0025090078004012240d17005418490b50f419030681c0804900e440f8085112412a00c04d80c030341030345c107828001d4240d00361101d03da005808201c000203035a2540d402030303400301100d440c000c0c07c1c1d03460a102640d401013020f0009580c84030b40c050102d120020002d0800942440e2000c1d82004034156250180c015030b81c811081440c4c00701602c0c1c0b42e034000014021002607850078003040c0c0382c0e81c40f45001e2101c0100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 990478875 1250 990477625 990477667
    0x150f080c013e1b0a121e021306090b2b0201090302090c09190602030a120f0e0c0907020708120721050c070b0f0f0c0307061e0f060b03061201060803 65
    0x3505000c00d40c203c81d1400c40c1ca03800403141309002000320b00740c544e201e0001002e08180d0107a80c2102d80360082005aa074031008100c2c6400072540052a14140402e10044400100c0402d02074000ea5017000a0550660b4481210001030803000b05002c01d43e10048500c145c00f0341c402504100b014081c0800c40891001500d0b448070151080c0c00c0c0000d12405051500c03600c6d120f044090f803c02c011403850f051141040c0e01040c035a40001045d01c80d501000b00c03044612000c4405c0d41504481035445140ca001ca02c0c5c0381d042203461000b0800346041a40180e1a00402901c500c0010300000f2a0020000c80080040e000c509400354180581d0340300e83c018207503505c4180c00d206203000c0c0b00b4010030b40d540c8400a0f586646181642c290031310152440d104002d50080c02d003045c1603c018044a0001044c030b01908400303814110440485040f090400b03c1510041c1c2407035010141404014801400000700342ca0303200304e00319500343c0d45940c1890018010002c1d60000b40f102e0000049030401c6070081840300b11 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 990480125 1250 990478875 990478903
    0xc07080f0c120a0f0e1305060f03100609110306030d110a02030318030606030a030f050a0306030501111209060f0a110d06150f090f060e03030d150f080c013e 69
    0x50042c60324200f180c4005014a4159014003141640c0c911454141c0c0b00e0ba48c40350f0050711036080e400c07042c80000d1404103800c40c0180d80d1511220f041c802092a03001c0c943c00701d850a411a0305500349540001d898070341000035681080300e111500300e60504100008896160007134252580c504e004c1444d000114020144039000340300319408603103941000034160090541595030560040014038003203034070f80d10820154080540710500880860000e118618103c54030186855986c6651041001113510051205440703421110030803010603086c0c4c0e001903000860400003d0320f0403880821310100d001c1d26274001e00032450004003240441800507865a0401161038003811000007c0d000c5507144914020500c0041c0c00c4201000704c180600200d2110201c010305590601440d403030300c002100c8203254501030318400b0100c1005000d014000c01c0c005025041e0107401d17441150320001e080c0400c8440402d40c8404502243e0860280b1040d18540d02e02c49d00c8505a062050281800d40e51248505c1c000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 990481375 1250 990480125 990480137
    0xa05070609081e160b1504140105091006020a030f2607030b030a021e060c030c0d180509040b060613030f020a0602010b09010e150909100b06030c07080f0c120a 70
    0x107030f48200d603901a140d4011800300e142c036820f209035680e10312042c009850020381032007020780d08001d50340b64012203401d641308205034251585440c0400c01c103824042c100001b81090318406000c10f95000c030f26407207420f402d42428842280c0c03008088800c2c3d14810382421064085000035003408850307c520074020b01c81640e05002d81e01c4400d003050380301c01080c540250302201c11025140c44044e005030015103a1f400401290500481e148410b0565005201d58245500141803000341d4070741005119801844102880182b141402c0204042d40c1c000b03840500800c11074400110310b69112411104841030b01c2084903045a960f180590b00b407000b1090481c49014001c40204c5ca80740305100d04135060000605003000c40e40b0b8a81206010080541100c83c40c0c10000240036880e20794800c014080c495840040c0054000701007010215045865020b01c901c8080052200114009007078030b1046410205090f40d4a22206004465100e001d4160041e030140c4034564001c0c401c1c40c0080c00c09900c40391210 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 990482625 1250 990481375 990481417
    0x3060603110403030e03150f041406011503150b1c060e0915040302212a0c010f0207030c03210201020408060f180f030a020d0804020a0b0a0507060908 66
    0xc0d41950a515032418079800c007400100301183c072403000aa843d03070010701030343c511040c903252030b050300441151440c12000c940d00500041103852080c0b12040548003014040550405030009a40c0004940d04030805071141e58409440012642040041900e0350b1000e07034900481c21030701c58082098480d03101c11481c000000030b040000b06107140c0b003410004050700c62442d24541030fa802034030141040d000c43c440c0e4541a0070302c2158000e03428a00c0e00c1c1e0490241c48441c110590400d43c607400f08015088101306540902e6a81d000545603c18682424030a15004281d481245000080e5002400500c0e45179000002c1c400125201c0c01d48424001240700c040c1c41017881039081c0c1c490791113041079960110001402480401d03884030340048640c582585203010340700c0f0741c03842c150400d844040c180d0000a108002c064041081d41c0011410b400e20000500c2d2a40000d1015220b61040404044e8000f6081645ea44500b04035904590b1290302003000d1007003802e200d00d507600540d10f071400f40a20400c4d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 990483875 1250 990482625 990482627
    0xa0908160605062d010507080f07080306040c050903120306121002070507051e090402060c032205040c140304061b0507020901091802040b0f1215070e0a090e0a020d03050a030606 78
    0x30350380000307084c403200c8002030701c950044459500c0301d101900ca11105009003a44124240700601e840c0d4055100c10340c5a0400c071080004407121003d800c001e00400304100507a944001c030f90304807680401e030b03c01d40d129928000800c200d041d04246003e00c0307015900b0944c1240103558040d00940e030040d02241c210365121401c3c407a14401c21160f001400e45a886451800e1420750801988144003602c4641001242c2c1c0310140342d600102440d03801c541d040580343c5c0d11029184181e50050408480901c0240600e0784080d102564520702405120000000201400119005120f04062042d012040780008080c000d1850f003141c40c04078402c8550304000100305030346014140c00700c0c13041c900f03018018915070700700700c0102000b010043d000611843c9040540d62200348126600950102501c15100c0440c4070103540b040081c01e80b41486a910a0080796444408401c000e44660a40001e522540340e5401c42c1b525050580c001e501c16078107030b01d01c410507601401030100e2540c10344040c4499915088 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 990485125 1250 990483875 990483919
    0xf0e01080316080d02041202040e030a0c0602221e0b0a0813020d05250e01080d0c030912122d0c020114070c05090f0f0a090816060506 59
    0x4103030003041d4014440d642481d0341c040e0344620300038880d5404501c1c24402e003d243d01070342c100b548458032083c080d5282d90107604090107405070102850000c0c2d46050032002c00507003141c0710b1002c06400c983d0701013900044010420071040440c02c015642107109035842c80c907200c0590a80c08070141d64001c0348800182070000b5400d60344076103440d4840409903910308040202001d5060b005a80c00911640c50381e000c203205028a5495041070300307080da65240e00c030b10b0a021012899125001c1c2800b039400410a900c0c002c6011070039001103103031120071015541801c541d207506035044004450a00481d2800300528000b034540002d00785d413113040c5001e0034a059480700801d141800ea81c01c0040145400c2d48034411801d00141d284141402a22a500078052041603000480c3c102e450fa0b10401c414802442d00700c00384d650040742c801c2044154504000b5a104455003d842054056110000320303041000120546205250844405081500c903041505c0640019550706014541d0010300384017900c9001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 990486375 1250 990485125 990485129
    0x1b090307090603021c0b0402090a150b0d0b01090b040b0c070906060216060e01120c0504090e0a02180705091903050609161707030b0a1b0f0306060318110f030d03060f0e01 75
    0x2400c0b02001e51f101e80a11a140310700914412840ba81c1c0c5420a45030301c10826810050441414581d840381d250f60801004c0301c2c403004a8074148400c0340d000b00b1064a40008950a582c1c00b52020b070340300d0748a44606840d2204e107400c280c20031403c0c610041f83c400d43c00110120190490003810001907030701c40d800d40308034500148490000784180030b800340c580016080210a0180d514100b0700d00707551400c203c01100c8860b480e407520754012090010540c50b15200710100300107020308040b86030038100400303001849a079800d14001d0840128000e0303e8002003a510b8000c6401c00c0981301c1c60b1506070032860f1185890304040303401011300d100c003051200785107070005041d400790300041045a0070340e251010305400003448014415101c0711128140c0301481004011000f260300c51302c0301100038907009403c8c0c034101d80001c42054502031081501c9640720425a01142d0403240000b001d643d404e001c42c0c9100031000707455070184114200d0100c01503044c0d1018088900031b43d410f650707040d16076100f61000c2c80c080c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 990487625 1250 990486375 990486383
    0x2030903061f0b09011b03020c0a03151a0d060c0c17270315040203070f08150105060306012012040b040e090c06090114090a03060e190b1b090307090603021c 69
    0x1e89600c044407605254040b500074042c0c0121850002700d880050a841c030300303400071110780715540c0025125654034000c00c01c90100010300005480d4074000400c6415860002c080c254607100c408248240d40220381303240c01d0a030003c040a0300c2041c400c01703a0076207600818503034462070b95940c0e2494858082081c0803040090080140503c07000c10f40b04000c0e20340000d44203a0b8180102e9100050a1a910010744018895031016284002c0f41d0b039001c0145c6401640300344d0082c1020010044940e80c0110500c0510701c240c0300a0016203850466a0725040030301e502414251000a008585038408101030b00031510404c100c82129030341c03d090192551103040071650401000c1c2b004200c07079030080d4000c0c141c0d4101c244a03a03060200c6003000824581c0c9035070040c0d807141d50b01d054461000005000020010240180001c1001074565902e502040000c12009041e916040740c0100c85280034111064800010103c884144e140d44801e0001c10303451000b02d220300055030140341c024840c0000d4623912900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 990488875 1250 990487625 990487637
    0x503090f060c0d0f02090414100801060305121809040c1403011107140a06090c050906060c0d0f030b15040918120309020f040c410a02030903061f0b0901 67
    0x3c000e14007021300784040c00400e225409001d01521a21107100b0130079400c001d80307040012030a25555029108600303030400e206c11307410514240b0104000203420f54103100341d4120140c0c0c5141c48900b4080000091414542c8201000148004e00c0000f00904080c0d581100081c16010720060401d4200c80c5441100000400f05000c0e450216442c3d600702040307124600c0540398030f603405a8400c01103804100d4219a0344040d21b1080c03015003406011a94094419141146003d800c50380842d6039558000c030b50000c2040943c602002d292080e005400d1048014141c10341d10614081c86444507001800ba18016501d00700441085001c5440240c14590b000150010708804060046020b0024038509a0300000e5002c2d030341a180c2c586210311940c0f011a55181505404403c0a1480d414a0f01440d0700103000c1e000c000a58040c8401c0782d026054107a4030100d6034600580005078158000d4200a40d41402a20104004002c030081d08a003905d0f100b0703030050711540c0ca88224110900451040d01c0c00190 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 990490125 1250 990488875 990488887
    0x3070f08060c0c0a020a030c080606040b010e040e190321060609150201060e0a0e0d0809030a08100b040f0f0f0e150a09050c0a081602120d0e07060503090f060c 70
    0x1d80320b001094418040802d441c0750070216004500701e41c001e0360046038500071019040105a4007070042c903400800459040c0001000c0c6000203180d1400c0c0604140b02c0c0d660380a203202950b201700160610034444604c509507000a905000d04900601d440c0012210310f1590b406a4030400b502c10310f0140d5000380c45001d105418803986041518891880c042550343e035802c045100b0000000d424442c900b000000300705c0700080380e106420710541c501130f1010b1158400a00c21031900c0482030b16524812480c0141040d88ca108c0c030a40724202542c006405408000b1780030546001c990b0810068494030910291415036030002c3c6030318108244035000628a0b20f40c080781460350029421181440e000b4207418005459503e907034201d9109580178030f80d40b000002c0000798603402109142e84107542d580c80110840e60040f000e5113405600c540580121000150103031031181030380c0030b000b0002844049410807512003030043d00369032081c0c44003102071080e500c4000c00188001032040c81615100b240d2800c00e6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 990491375 1250 990490125 990490141
    0xe0f0a0e090c0405040f05160528030b04060603050721140f0d050a030609050105100503071413050a05030a051e010e030c0c2403040222091103070f0806 67
    0x200203022000740c1d0090301c2c102203040c0c1e100c3c01024011806010310ba0300346011440c25901c1c0450038641002c2080e0050410400303640c9100000507181e050001c08690b000d81c000700289444420741000b002c4810040500c424010298080e00640b44143c1c1110107546e01c8045004001180d00301e10040a08000340d8400000d821501c15600c040501040b2655489c101c03941606142a2006080000350040b0729003056139403601841c3c000f03140000040005505000105454240b0780e03132410300b807290000104024906c01e4150f5110003021203211900ca01440030503003c0c4040c14410144034000003400441c1e0744ca004501c10051540c064018000999408281040c40070314440160769556520072001400c441480100716616054024103244030413601007181c2c0d00c2003601e0300a1200c09407040e48940c05241c404aa4210740c0441340b01d003e00c02c51110395652680441030242d0440e04054402080100002c407040c111402281560007894071030b050015810001d111ba05115441900030030080c2c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 990492625 1250 990491375 990491399
    0x61c0b15040b03060f10060e03072312030d061a0d3c0c020f06040308100f09091203020307020d0c0c08060f09010b0f0a0e190e01020a0e0f0a 62
    0xc8000e44040760000112000a04202d4225100c2d070160204404101c844210804030502802840c1411090803034000c012980d102001d014024815158918800144006002070460b001000340100207120701016040d450f9046229000d0704c16007820408241c200040039441e4100e219451450309110301521481e015041c0485292900e010174141c90191640341d4001940c0c0d0a6002d642c0d014594000307144030300b02c2c1d602611000447d0015200842803031000308120750025054682010310391203a4214a002582070360007120010751000c000202e0b9203258210b070740c40720301031580e1030181925440c4c240c1c241d07c0200e403d44010703008042d000f1a054040c1c0c401d00c3e10f441c09103400180340358580d04401d1030900c0550308240c801c1c0080d020032804031402d00030003468a0043e1426684030051a012031060111401516016070342c0c0000241c000180001d010703806c0046001c180108180d0401080c000e41c80b03442d9440004440d40d400300c1071030400d06450340b0130100c040e1405078546e10f88000c034214 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 990493875 1250 990492625 990492661
    0x10b010c060507030605040e0705150c030f0f090409030305040303150b1b1c020f120c0d03020c012307091211010c0201051603023306040b0301020705030d05061c0b 72
    0x44c145c0d6480e02282d0b5440d0792107100b000510f11002814818100810890356042905000c00e004904000c110180c00c0040305840126252070042d039160040002c4c0380120b030243c0c00080b81c03c01d1610406a040c158140c001901940c02914100071400d054682c4c0b240e210030078080d80180c0c502c1000100c071000c50b0410200348006600741034905080394418101c078a403855440500059101c6211a19a10f509101101d001c0310038803100c900d040c1210702e4207a1282e003021643c9060542c045801e00e1b40b6a029080760805050680007003804507500003003c071000001b91041000145101000300740c1c3e24555040060007a006041c8201d40300c981c200440d9005250754080f81004400c4c403140080012540d0038034090b034881d070080e080346a032459111500d03c0c0102a00702c0208400e1403c02d19040c00039544a405c903406130740116403030100750b000c40e001e03101d8110024000d120000341d94242c1c001580c441030107510100c07403c802d28050301880d02602040040060008116407005c91000710f00d01040150b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 990495125 1250 990493875 990493877
    0x50f0f13140109061a15071505070c0516090627020318031201030605060d020d020904060e03040b041410170a06050a0306051e090712060b03030f0c06010503010b010c060507 76
    0xc210b0300c5a0790703410503281c0805030301903e080c07175164080300f5141441c4943c2c0c41c030000c0700c0707010b04140c074649603201c51220481c45040c54543d41c0c0040b8502c60700c109610340341f2350f4015049607040100c800d0512900040d510030b408046207401c1c400300c0c1001142c440944030300d540ca0243c0307400c90701004100c8002d5101402d00103861814140e03003003158009101401c08081e1024441d80651701d5418000c0a84600815140c494000d1040321401039a91140c42b5480c150107642c0380006a603103140035001013048410307050881c031010a000569614031070040065420030050000310100e20750070300c44408501380d446004101d0708048085041c000d1242c250b4006811359000c10199542d10116820350754980060b5800e540ba001044040c201e510b03100d01c1c11111100b40626640761246945848034161b020b01c4401061040f510307400e018040d0426581910010152665485a08170303202496012408488050086400008062a040c45162401d2a040e1150600900c290341c4202c010000100400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 990496375 1250 990495125 990495131
    0x5090a0605030c090d030909060b130b0d1e23040309051512191a06030610020c090c0306030f07051c0201020a0c0b13080102070f02061b030a03050f0f131401 69
    0x19601d0742d40081030b0310414000c0e02c844080d40d0130088c3e0340302a10441d41142c1303070030002001100110400c0c2e0003510100ea071000240c5845aa41107100d5025000176602d50300384504031600c24400c203a459125400f803ca299201540c914200c094444002800719409008074422500401103420010310300c01035007146185941c6080c01c0c2d0709401d40d03039440a8880031100188080140300c0281c00e8422289041c041c041500e81d03020b49030740000c00900c8000d250364040c2c82085074560b80345008001d00301c4908001001040a441c01800c012440c3d0000c0b03074068800e01c1503c0703002e90b40c4803001c150801610b201418070022810f100407881502840400d0030dc1c110f100b074460900221303c1000c0c1902c0903100025107140c2d15034540382000000b42c4503030090b4002e641f04024001c0010703503c0340401e160b1527040e2032041c2c81d240300d0700008002951041880c0b030640070000302c0c20744031640b59205500c5031800e041d2000094940000c1e1074041c0c64103c0d02c540203842e203843e0364030200b1035410300c0c440f5210f9a44004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 990497625 1250 990496375 990496387
    0xd0f0f0b010f08061f12020703030c1412010302040b01200c03010b10020d0e0112050f15040204060c0605100b030c09010810120b2806050f0d0c030b06010210051e0705090a0605030c 79
    0x11b0422640b00307020540000750f403401490f0714594040c1c0c03210901c0c048001810700b0490300c50340940040c40c06200003407003584d441458400c2640140c124031031101e075000d0881c10f1011803580d01e640f51890065514405e5203010180442480c001d030780e444840b0741c203900910311850b0040c420740740e814100030030506100307120210782e21a0780140100740c42803660f1021100303141814901c02c1110051800014800c0e40140030502c105503009088001e0590800c10101c0d0036160440c03c00d418044a4104c041890000010014185540002003010580c2079940303104a44c0d4000c1010240a00c5003d0104100c0c100114480800d00062180390043d480e118440301d040d134444003e011030041e00c1d10420780303d51508010043e0b407410341d01d403200c40e6900703640750800c84c4166a124200a5818000104420748080103d0b0380c99208000c001c8041501c0751080081e030604212196408824800241c2004610400100460301c200309030341034644003500001d003660a100e0305031a1030300b00800e40e207044901880702d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 990498875 1250 990497625 990497657
    0x21624180b012304151a1305030705130b01030f0e0c01020106080105010501020a1b0308210711060601050d1b05070c091806020d0f0f0b010f08061f 65
    0x60340140c020080c01800040c034207403902451401c4160b000491003070700403080b40d0040d00342041d00c0a00d03010031100040c2680c05120035841103016900104190048002d202803162051002000441501050071030b00ba6034820405655501500486810484848070501c80c46070582080c0d045040505000c1681481c0c503050708200c540901410065901c4003090b1005542c0a115050142a285000744150740c101710000c1d545d031408410040030211659201c1c81078210384444040035603800380059030398103034004080f040c4106452020540740c0251000c500709900811101d12000070080180ca4a03580d0100150350320381142c0c40e903808250301e48048080c002e501c502c082d030b10700b282c0ea16000d880e20510305001c12400a2600451034642c901040541c182c6840c000400da81a849040583e842440011400180c046101c036071021904000d00302c620058181c2022600b468203a84154000051000c111902d81d07054032200e802411b0b001d5044d080d01803100282804200d40d040c440920428215 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 990500125 1250 990498875 990498881
    0x60c06070302090f0d0b160c0501050f070306090504020906010e13110d051018050703020909091c0e060306060c0703080f0306010e0603040201020615040f0e1c03021624 74
    0x6180c0c000a607000541c224280b8000c6030010800c041541c6220f42e01c190340d130b200c0021002c00703000300884081e09103e40c60821f1003003001d43d820960042c000d0001d800d158880c84a121002d44c0c010b404213041c9900803401490f58030495201d2a00203281092a48a01c8015074034240c01900280d005411841200c084901501449043d0101c90703001d07036900d0020202e4141226400360203d00340c1d80c4e007030004000f81079403003001080a2120000000c1c158039041c4040d0001e10410141c01d4109880008001034560046000c2e805466500ea400040300100802102c0c551900c0080035401101480405d005040036805042e940e80079000301d54046440b40c60b0031966400400c0d0b540c8002c00c0c00000c11005517030020552070102e00660303080c0d003142082c1e40040c2d00c4020081088020000c42c0514076519580c0d07401480f2000d40d618010000505604da0300c6403140d00024204064403286091030802d5813291080322050700d404191f44e038100b003560b550480c003040d800c08006410740c40b00318441d050030301c284 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 990501375 1250 990500125 990500131
    0x5121b0412060b0303040e190b181f050a120512070c090f060e04080a020a210e091e040809130203160f021b01020703080a03020408071220060c06 64
    0x34440c20307400c44091400d14141c5241c1100c0d03130b00941013408200082500d0740c10198000c200c00444401405c0c89806e080024801d0043c841d0744980001301c0c50010200850402e8001c00c40b4402856207d044198030328050b44443c4240c580003c450001082140c151800c1040c00c1032040d81a50300718540a03284150503080600d044d100e517500d03103504102501007845500140328003d00d040c044a45011031b0071801c10310051001d061100b001031110b913018400e2004054280d03112035140000d104003d5100c03002c2c1d011506520105040090303402880c40c02c40115880744604004403400004000042e00c03c10f01c0262045407007000901c10805560344001d9061024040301d240142ca9182880707801d00c164584060b0b0307900b4001580d1000b403040d035001c2007801014007810075a02186ca50800100d14200050b8030103441000d000c80e80074041a40750300140300700c0380410115280c45071039001103082c0b003044d1b0400902c0240305c17070101020700414000c000d0740b2000c0100000d0034008000000da040103011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 990502625 1250 990501375 990501389
    0x32a0507141c020111070f0213060602060a0b0102010603050d0315210b01090203100e0c0d02032e180b040908120703111c0b0d08190806090705121b04 66
    0x824160054507202c030b0032004000d4601d2000f8444c198115403446040d110f04400a44408010581c40b015034a82e0018250801084102003183e42d9032003e000f07480340c109039045c0480700d05040500c0c0d8550320502078807095a070000d018100c15116040d084d001000d50313001600d048000c4242c0060400c0c0404c094805c4800e081c4060141c955051615207811034058002c80340403481801408184c10300e150305c13001038031108644000f86841d00844d07c4501e0246056000c201ca000204000407030b846041c03103451420209008441115402e000c440100d00d02d40036a40005524140c4448000c0c0b10f0b0b0001a40d00c0005400003c403140591204130350b55000c45499403440c91140103100d54540c1c035108604154411020140c2401c9481c6201401c411800c403013a1055900c948080c0340b01c1e0360307800810080390b5010000680e1802c8036001551f8886031040c8600c08116450001143c6080035950b041c400e800542c2e48031300d000c101800c401640d20380500201582060104000b5161961000410140c089 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 990503875 1250 990502625 990502633
    0x60f15021b0a26150c03061210060906090507030905030f090d120201020a0f08370612140631050303070e0f040e060121020405070804020f01032a050714 67
    0x603c6508a01d0300c0018031400034200e801c0000c21101c03090721400d0b2604601d04850423600070b0910307043c1624100f4407003075000c007540c40d000e0005110300c0f40340c1c4104c1c11200712980a2082d035036600815000c440c980384018100340c004000f07813452074504c40000c007010007009007030200311161130b10f075640203600a21700c180c0903030360005518080a030050480320031090213203094610752504c518125034a28100c1c142060504400440c102038408819080c0101c1c00b007076508004095942c241c0201030010302805403180010010351303805c4002c0c003180d0a40304a040d00d4020072480a4140420307801e1041d4174110140494031082c92000038002d00003107010300074554a000c0345e4001981003054404401d01010b21440c5411400043c000000c20030504651050022003031205948480e01c91906413004002d40c420324080c01c000c03d003030300502c005000fa4001c0ea4102c21b0f410811006404540d910400038070b40071f01400e80c007a01c081c0c4001e8198a00401d620740700e414107a240e0f441002141ca500300c0e508481e00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 990505125 1250 990503875 990503939
    0x100b030414210a050d060801150f141f0201021905030601020f03040e0114010903050a080301091404050a3201060302030633040618060f15021b0a 64
    0x304020000490209240c1607108070300241c0d04207010f01c601c00380c41080c820089010444450300c0d80c41400100710b02c40091040c1071000440304c4801006000b03960401440a401080d41c00c5c00f02e0841c166040054615800800c07800034158a00c95101d0101d0f045640801c103019207108008049004900c4980780c864603410103100280c1004c0b602000710000d903205010400c0303489401c03200c65045501d000d1030342a9130340e48840100d91202c905d41000c1c00c075105a080f01810484880000e5040f1000e407441002290781c0c000270a0404201903a020b070441d8004140711010a449540001405000c103100e810317008400c0052461852100c4101261039541d0030f401c10075401c09015140c6c1c400b801b482c0220b80c42400e11002c241c540d4810b40d12802081c545100600a606d555000d54050000c0e450b001ca14080c80b0328110019001c580150107024480d0ba070001840414081310290100740b42e0090710b0124181c922407040f0340b018441440c2d211801d03140009a4002c0800f541e0380ca880300446081000c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 990506375 1250 990505125 990505163
    0x51b010c0c0b01060e090a0b030114040803010303031b020c131d0f011a0d120210021c0b0604080a02131119080705030f0403080403090e07030e0f06070f08100b0304 72
    0x582c0581c404001c0c09020725141140d903031100c1c011a0b00c4892400f001401225010200b401000786001280420b0f1844092100380505140618102c0f0b206e40e0b01403100040799420107050040618800d809a800840c003500d1a00d4401d000c95551070202500046800f0745074031a80c041400d144d201c41098100b003e07d00c501c10303001e0048440242410349420801482400442c00340301c03215402800c1d01070b07480484064940b090200020321103143c03c0a64036855030b400000d00400c0b520341e41c52203045c5043d80300300c90ba08001082e036040325101805842d0705a41a001d2146100c4406224580d65030764103a120f4002501101410007400111589400800003034005410000007910002c02d000060040003e40c040d008a855031055040c58040000e0320745107001d075070441060300b10300140d030702c0350041102555140c1c0c0181e00c00c42104088079445140149081c2d1a0641039600c00c0c0094035500325011400c0c0a0154541c129031610041c4071f005039203060030090307608180d5040352802d43e50501f4130900c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 990507625 1250 990506375 990506393
    0x52404120b1006050f0a02070305011b0e0f012f030c0102190e0a14031e0d1205010806060d0f080d05070809031602091e010b030610170106051b010c0c 66
    0x50305035a030079180b45080010241c07060142d044008600400000d8a0500c54402d21070340d0001d503406002400014900726200c4501110105000005814250350340064034241190707803d0943d040c1c44415142d40d201c03d5980214019030510000003407000c440c011016800c0000340b1404910500041c3c6404078041c03031301606141c1c2c0c001c2d602003203094201a07003035aa401510b80219108040f4000c4c46240890202c0d09020750f42e5125800c4d02440c0080000106012a00c0c003042c14070b0b603035840d030b4003005c40304004100c0b202070041072580d070b2080b80024414100900e0780c507040ea01071804180c010015940301c0c00560b01070511000740580300c1c02400306450f00204000c0e00044480d014500341803035400983c1513103071a010040e01c1000c121002c40d100804024042220b0300401142100070368485a48101c0c0ba4400d58100303001e0318038443c451100500c00d94000084810002c0c4a0f00079074a4002c00b100c05070031101c014608620746a81c4da4440c15424410383d1581507441c0c0791449840050b040120301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 990508875 1250 990507625 990507631
    0x10519030203220b0a18082506020d0b030609030c210910050a30110c01020a390f05010f0204092c0a0f0c08010c020a05101104052404120b 61
    0x7283c3c100b881b40000103007040066904111461080c003110b081090840768064807245800350441d4400660109824010340240c42d0814040c1c0c11074a260303c2e02c072511940c0348264024030200da0030001c0c1c0424101840c100c4512241000c00d0018141681c100000d04054000f0500a0201d43d000407100b00c241d4000064000140356501c410191010b00b402680b807004008441ea141c895079000004414120102518028000c9100031502c927a034011014008000d5004219001c4580c0b03120f81001c1150600600c1c00e88000140004c17800e4200d540d41420083c1143d01120701c2e540301d1550380b40345a12403000e0002800403585c041412500b40520342030f280c424800200b08058a81c3d4400b9110000003646d1800300d50228048950200c1da0500070340108850708060b0440d4240052000c2c020b600161076285140640199000349a5a12545d001c803020074500511048090100b00054a4517440d00e140e000007410840000520b50316803068a607200f5004020008000004c4106004000115545c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 990510125 1250 990508875 990508901
    0xa0801140306010f0b13030c0611280b07030212040f0b06150405010f0207030611300f04061404051e0f07032d060f0506010519030203220b0a 62
    0x40e55040002130102009031740990310b502500001d44100310440e016011004640100c03d1016144c0c0301d010083c00040e0b00c03180980c4610412911021080c84001346150191050885410341c0040d9500c42c80350030f40051860301810783c03d0182264189210301d1051107241704000340303882281645480c452500028103428060725185c0045010b9407042e500f01d500b600c02c00d0a0400019044500803881e0680070340006000070b050210400c0e0000a01c4050001c40c81d460b903801000d40f401c071f0440c2c1032243c04c280c201e40300700f10030b80301191080c1c088100b641c2d00103000d00030101340b045000240c003c0c0d006041e54101d07040c4d40894040742800403944661002c4040404c054022820f40030310303040d070f20011070001400000c1aa40074651030305280d42094040740084040c01c508407014100b500044c45c890010b5401b071810100040d50781d42c0b0031011034080d40115521044100c850031001c030020b410050071280b0b480482c00100035440c0c1d10305920325041744580468051450603220032400c0c1e55840b00c0700d070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 990511375 1250 990510125 990510133
    0x4081b06161404180e07050621060a0306051810090c14041d030301150903051015051e03010c030608033702030d1505010c0809150a08011403 62
    0x101c15030a10760701c5607504001c2450400d82011446109644a206079800401e02010300a81c0d026643c03060740003003281503903900641e03003102c4d540c8051081c148110401480041c0403007060071610080301d0070080d000a4080c0040c07100740d441c0e6940340101d61081d510000b02e00001c211094405504001e8400d00b1030f0512414410107449940b0200f80001600880c080c04441c05105003060301c0700c0c1d00804040044140400980000c0c03103010b40c07698800c0c0101c02c0040c06c030b07285640310580540d16140450354403e004100130900010200010101200e01d0203505c164440c1c0000d81e0f54850040c1c404c141c4028092603070b50502407003018210f4002c00701c1d0034141170803c0c0040051101c08070942d807100210500c600c200d000540be4038512650700e1030402100b0707400491100c1038258004050300d4450900301d8100308045002842d80704000061298a001581c41e580c103800040d002400b414100710054840700421154440391910380c1c10028901001841c1d03240104405e880300d44251005800a8010f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 990512625 1250 990511375 990511381
    0x3060c090a0b070204180c03140a0b0c070f05100209040f0606090b13090c050910080907060c02010e06030117150105060711030a05120301090b040624021504081b06 72
    0x10569682040c8070b032600b03030040411880c0941d00ca0b60800c2800c12041100104140c0c8507160400d6582260300080c5e81a060154481d8607411340000c84d1050300c0d170814000010380e66481d1052449078041b00044035080040d104920020342e04000903580d08540c2000503842c0c021020601c01158100300340c02c40014140b40c010070182d070b00001010140c601c070901d03c3e80d80b10b03040740c0003101c502030591060002034a09106100074990140240c03c004000301c5007403182d40d1800c44122294034083e0741c203c0060704080400c0000c91701a000c4450301742c1c4181003c4003940c0319100061041c1e0026030142c3c046802c1040d03641e071070200a1040c0101e00507009010144c0b941840c02046640c002d900009103841c5d6005900c01c09986c04009004420b5800700803207212150820011007590028810000c032a4289210002240b074075010310707016a0a00285145004241e048000c0c02c00c00ea031401205500400c0030800100c0c01456109100d580070748800c540e00e1024031200344c05420850b40889182c2c20200174 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 990513875 1250 990512625 990512629
    0xc15020f2a0118150c0b0a0b0414071413030803090a030e100c06021305030a0f02010e01020f03090415052713020f0405100b070302160b03010513020d1503030e03060c09 74
    0x40c0f01c1540c1d40f0310f04c0c1015400740550183e0340415100c0c0007400140d205401c00421011031380100025200550303080c000410300c224203074000a001d5402c500810488000ba098101030080030304402c40d40c00704452032495a84d12061600e92055418805a0704243d03050030034590801201e4038015800c2c3c404040f202000440203101451918000708211303000602c00c001405a4142c41026101c0181601d24078070140c600031502c0b0784020000c90104e29014501c40c035940c008550548103568250207540703001300300c0301007000802400d5200610000048000f16142e10340700380c0080e0000c4404040f0302c41030144540d9502c0b003100180300043c0c03070300d40b800d689005888041d10103802030800c0d81c012440c0d0b202c4031000780c1660b181d5000400340344000304143c000d041d8005040480b034030041c0d03580098680c481000450700e10090050782c0d00152006200d603a000b509600402142101120001d004411260070840e07401c031a0b80309500240b10000c007000d00d80f8090240e1030b000104005071324501111080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 990515125 1250 990513875 990513917
    0xf0c070f0b0a020d08151c060b150714010219181e1e2d080111070206030405012c06060108160c0f020a031406070c0c15020f2a01 57
    0x1190070b0400422001040c441411450615842003009010040c165001e0455030341400301c01d0020f840071424020001c3c0282404ad034654a02420281900c1c50840d55858841c2c00c070000541414040d9801c02000c100082d865010900403d100c0e0f903264010090911010200100350300440480c80d842003050303c5c11880306158004558448108008060641e40d0ac0c0c0031010441e88164482051081c1e08c114200036203046011480c69400c900c460b094071000080e0172681a0300c510201c150040140744050315001e000707141e02c01e100d480040b4001e5100c1c400c00c20070509400050100300c6c0c00d6103150710b40c3c40c03086c09929031154007840d14844074074000c1010820042c071101900240000d28055400388031450301164070207034000c1c190514541c0da910b403129030160300c169002840d0250101089003103104a10310600250400d00504400341418400042d0202d40311108055218502841c5c19540041c041107841d0241c443c130300310481c0c4001241540a040d91603405040000044402c0648030701c2107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 990516375 1250 990515125 990515143
    0x211506060f1704120c12050d0f06080307060207050708030d0f05061c12030b150d05010b28030f1d0c060403051018051507030f061206110f0c070f0b0a02 67
    0x7070a454103c880c0d542503400c1061198050062510701207007071a01b40e0410002d29201881074420006800107000c10f504480300c9009030155900708101c2200400e200b40c000e000700c1030082e416146d185944101c01843c40d0311412902201c1c03a2030700308094402c0b5051068540c000c03001c1d25919441d40461507032080080b048440102805480b00c0c005854500c1713540041039001024181c000704c204016103510035504095805000ca03410000040f03145c41c0e45d10242c07113201d4034040c8552605080c005192102c0c4510201100800d40d60b010300c6521403a1714015400b80c0b1884680d0740c004074261071400b6050211850211380100410801080052800540c01c44488050440003c000070342161741d00d071503010740101030b040307104188041c551000c5450b00c90b070046645440400180b241121824141e892521070030800c00e0071103c1400100d081c0360448003800b5a1714459603d40007102042d060590003250b0401d4141d0f101c00e02c00e100f00801c0d010100e024013003a0b020503080907040c04e8004d645007492 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 990517625 1250 990516375 990516383
    0x40506071b1706250207090c03090204020a0509030c01030b130e0f06040b0a0c03050402010c02010e0406350a05030405150408010c17070c050601211506060f1704 71
    0x10000040c10a215000510068030101c08650a191082c00081e583e4a03820307988105000c482d029680044410000c200d242584d4a0b009007000c1c914118102c0c00504000c5032100905071200d0315240180d40700c0c4010078078040d407900c5468440940d00300345460504a03c800b01e050600d03003005801103940e54440180c04e01a02540420702142d40c1c10000e04000e414800c1015501c2030302c0600c8100040070481c0d07441542c1a800070844034403e4001242a80c2040e24068041001c2000303050155200315940758040102400c049451552202402c60100820070350017480030a000c82c0c14502d1b10b03442d00d039200c0743c0301000040c110085140c4409481b071045100d01403180c0a0000b0a208000c04002540d005100c400002c000e06445040c0150843e601c48402c511504607480c002013400340281000c0302c9068104008202503070038032000b100940003403111200401c000c684400009004c25440f00d602c5c02d0405008252540b5107c0d0181100c60325800c60030074440880e240001c2c0360941d4600d685d1060b04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 990518875 1250 990517625 990517643
    0x110a0c0906090f0c0e150c0d0503061002010515041d1b1e060d15030b0702010501090506031504080c0a29011a070b04030e1002010614061e0c070506071a0c04050607 72
    0x104524026242c861034047d60358a016181c042d140054008001d5441804282c80103111017110020803803c0f15000c480c00000741340d20502002450905a02c0280b400300d200030301c0c80017811030760002c1e4984040601c0640710101181000361381303070804c01841d203034014441d00355079480070310344001034800c0c02034140c1007a10340d5a928110402040c48002400150b42003944d880d1203042c03035040207028080c24041d00004500708008900b00b0300300041d455480c103001c402000b0380b03500c8641c0c0e40300666000f1031301120540b189444190214151030802260b4985c0070031134107034140842d0f074100f58022050f4824410107611288811415040c0b07411505aa0350000c6060560b075650314003a10306400c1e0180c82030304000950110400c2c07980560104080d81c1c1c07101e500100104200041240030700c140c0c0c498030000c00c10420711101c0200c000020340309182640c03054448050312200030414581081c00140c508004031840148200c00c00d43c10540c1125a40c48000d00d07080c20710000c41c0c080d2040c50300041040c0c607 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 990520125 1250 990518875 990518899
    0x120a090203240402030c0d05060403081021120f021b01031503050c040b0f01050405040504050703061e0f091707020a0b040b210106080403110a0c0906090f0c0e 70
    0x502840b09410100142c500105104501d880c05203414004480c101d02034814100d680c070075841d0459040c03040341e5102000b4080c558555508030303001c2c0742c05001d640e50b00401c0d01010030100c1e0490703072006481c1c88118032402c05e800c2d46d0504000884035511241d0500580c4540b80100b9035010507113001640030a000702030018100c0004070010030b035000b02415402c804017404403c1040200d03402824840403102440449060302c20403032441d4260044074003103001000308203c0c0e81059080f03e40c0c0310740104280c4c0d00281e41c83d211001620809400d1007009080b01c03216104514491183c2c00792400303005401c0014018954401c0ca081e40b011142e01122100031034000115039412400102420080303041d075454550b5103a018099410540010604801c46030b01410404d680402c010704888065654680707030344583d141aa44403c410030300355400d00404003031201154041c403c0740c0090101080000e0220b10717020601c0100c2d04100364010b205030400710441c04e4641e01c141031424405007241d9005140d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 990521375 1250 990520125 990520129
    0xb13050f06030f0c090d210206060604050f150c0a0c0605120a020f19020d1d0a0b0c1213170303040510020d1509061d040f0f080403020405091011120a0902 68
    0x4011401195803090040c0c03620746c20404074000e0307204184440b411482c1ca404580703a040c1d854007400c40f83c0329000802448100810b01d1329140c100d524403400b601c0040d80ca100341192102c940c0c1b2200d041881c42c0d00c81c210903001c000c10440842c00030203a0341380682c1041d030741c4010b01021350000703000c5402094010851070001041030f0111000100050b5000044805062010351200f0030710301a640440c110322245198280c120b0540034242c200208640d034160304114141c009608514491a0f003072140c000f0070303108502c0c0c00004101c0e0b6004000700701c800e039190100c0c003901551030944010660304244203000028070001105051412018009038079641080c0901c2e00500f0ba0154110a1081c0c40d0b40016103840035074080030980d414201300d0103043e09448a4a54050011ba40007045c000c00100c0b9000880c854880e0b400020b031203566070b207280913030f2600040c094a5041d202002c5907004943c000c049980e17144550890b641020300114140f00c1e0454120000400080c0791064260703c440c0c0b140119 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 990522625 1250 990521375 990521377
    0x702031801080a1419050606280c0804080f010f090b0f0903190305060f030d051815030421020106050a05090a0608060f041506050d08071b0b13050f06030f0c 69
    0x612032013501141c962a040540e15241030100f0250702e0303a02d1606c008521740d410044c046450004108040d42008101646038115120303450024004204d02441c80c84000b0b15020000c000402106004002c403820404000e4212900059905a0316107400c107480c00264071031060940c01041000700c0070403a614250558154845c10203ca4269448105031400300340e010303806140650802d9a07510303510039010040c103684850710703c100e0b40480d209010744080300c103d01303000c1c24000d10041d008102e8450100e0f4814001d810a440864038401d514030b0351745601c24454904030303945005100031f0140703919201c04510071b49040c4c0100390080a81400062548a440e006034004101940c01c580b00c920b40300704000320213802074030129a4401d0520319419413041038050364096440003031000045a10b165120702265110ba0310494081c4d030f9001402c82d5080c08015504028188a0400c60780ca14248424110001003504081e101e1248107841550a80310764060320b07400804d240c1e80e0551522502080092 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 990523875 1250 990522625 990522641
    0x503010b011e170702010c02120c0307120207050319060b04141b090d06090209010e0f010905091501080706090902120f19060b0706060b271201060f0e0702031801080a 73
    0xf54201500038000c0065055110340d8a20105a0941750328580a110408052042c01900d0030a64810700c01d2401088000150451105007801160402a03940c07020a00f042c64004180000c0b02c40451100240401ca000c1d500550130100e83c00c0010322410380c0031015071640039080610074081c50154251300442142120111a0001d0000303215042d10b240000161071140e10480c042d0b006007000180c107501c1d04060a0040040810405241e801c0c061940c000702802420070100d44140044401580128216640a00f8003503001c5d10110b810202c015140640c2d581c44102242d204000215440300c1407541250850344486000c07082da10f1b804280c00314100b200d500c1c04c0301c403881c150700015040304880c01401500d100303120034400744e0740d1500000800d005a1220150000444c51036440c80a0551002c000d0040d0040261918500d4000450300b100c101340c001c541c0c04102c01809001094020482d42e90081c500c2c4010f40c42c00d0111924032020300380241509060000000205550040503007110340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 990525125 1250 990523875 990523907
    0x1205060a0e151503220305070b060604091406040c020307110609120d020f0c101b060e030a120e07061205040f080c0321060d0f050c04090f0308010503010b011e 70
    0x243c010505011100d50003690381d1040d210a035a250754005450442001034186c0503140c80303040550701c1e20340d52039543d00105100d07805a400c0202240300b0a180c403401d096000344004070b814511782442070004a80d51000024150351040c0041c10025809850092030903005488880d02c0d0b4451901280d140a001140c410640c06070344c01d2501d9190340000c02c450b01981f050215203070f001400c0f061100c00c0181c0c00b00100040c08088283e6000001c0c8200020700318071404000030249481180c1505503004020701c1e5001403601c001d92103103900c2502403258480c9201020741034552400001825440d41c103203041c114580c8a000040600040480b140101c1782c000e0740032951524007545072038030b0740e002c0c2c900705561718020144080590703007206640d4800c100c05050b140c04294030ba00c8000f8410784840e400c42d900c1c4240c21101c1e80c191500c1c0142011a032048a00381440c02407850b02508880b8140c21541c001c0c0e2400140c1d02e203680c1e0003082c1c000501881e905064140d400c00d10115028003507070718001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 990526375 1250 990525125 990525139
    0x314030d0c0c0302010b011d04020315040e0d0e06040e1602030c0a03210915020c0a050d1115060a06111005071e09030218070219080a1205060a0e15 65
    0xe071040d8120020240162090b4020000405414019114101603071001012942d070195800980d08050b4002e40e004122003440306d550020040004050b5071000c0c0c1c40e54060340002c0245036119410100315120500121500b83c02c160070310400d5180a54020245000b0044030600340300128000d200301d40f0612030715410380e0f4000c511414041d001c82d030202d052901c182c070095009020b46000d882215451a4400c1204015001410101010b034002c00200d10a40c0a01c03280c9900107001000743c07500b6900a070f1265080842030410240c101803081c80740b001903058007000c0007844d0f0f507a880da01d41640c24a0414864011a40c50800e00c1c0000c0d03040b820201c03034070701000c0c440c1c03258100380070400038101299150190006d4400840c2c804400c1e00c0000e400126800b000302550030002c005590044440c81210f102446003c120ba5001c880440700396070444000849948070340d400f01641641004000c802d010b10300740003011440c2d08041c0d100780b5681d9550400032034030300000780348d64034400c1000400b40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 990527625 1250 990526375 990526391
    0x2010f02122e030602090109080c0a06050901180e16020d0e010c06021b0a12050906071e0203070915050a0509070f180906140d0b041b1a07030f180314030d 68
    0x49002944900d4401e404921540300000310402700003100808101c01408860b9a949002426246504030440903070500441009400c0950503001802c1c000702406142504942030000040005900c07101c04041107400c80c0701c04051264000d060300c5d40b010020720b07140500c010107003003490083c0030346c842144e100490041a080210f070000340c10a61a400341d0754240c02c0f42420313601540e092042414940d001481070203030714003084103400c07041c5c413111000c1c42d01032030390300d1603070002c1e04214050b00241011603480c0401c0c0c182143c07004c11003000e014199501d015082c14000014190700c0000e10304007c004215110051540c4141c0f280e01d0703100d9145042c4900d1f00e480d402560080d004a003d082c0b41c21850080400880c40c01c46803101c48a50004600fa002d034403543c0f00c1c540c0d5540e41c03803011448012007a80c00210054251049044c07241d1010700c154940c441490010546518202005c080180c00c2c61041001c495814a031411690b2061001548601020b041400c502854501010b03907450710640b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 990528875 1250 990527625 990527633
    0xc0d2102210106023c03070305030a140f0a02091206010611060c0a05030126030f031504050c0f071e08071707030905040f0f1b02010f02122e03 63
    0x80403042a01d41611048107a0300c9060072a503800041152410040119084c0e0005814109440403c00381da8500b074010161220358082c610750040d00b04030b000600c000100700e1043d00c544070300c02200c3c0800b44c0202144c20210102000310700b000c2c00c0b0420300380e40041c0c0c0f400c2e0307035a8a140640031225100c0603291a903070760303400c0903240c030a540100f001c590040c40e0005881c00400700407a0591240ca0f2541801d59007040603100380d40180c0d810b0900f403c982c14030074150001c001c101400300d03000d62004013966454001240074901c1c20f01d60340b890084d82480b00b40210000d085050b03800e0b52242a00b042c2c1c54040c6424101c20481040c1d800904140c5130400c10320510031208000e1030118055541d42c6400416030f5410401fa04c50200080c3c00034007142c40030b000394030780383d0440000f482c0b0220011824403070000303580088400940900c444003c03240780c5100c0d1785d502801007001300c1c103801c5421814242004a1094511310081000541001040011048184904d8410314104041d94023029a50302c2e858 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 990530125 1250 990528875 990528907
    0x30b090a0516031811030f01020c100c0519050d0f0501090906180b0a1a10020109050d0507030c140f10022701050703030e0c0d0804050a0b0c0d2102 65
    0x146140011002a1030b544424000e0141c140a5443c0700c14403449040103460351800086013192a95150055201c1d0041c3c40000b400600b000410710030203045046080d45c1c128045601d04440802480000d10040183c00f080c1d40d140320b0072080c80e0401c0e55440c520600604001c1c828182d60350105032800001064400c1d003a4031180c0d03024032904007001103502c107200c103495100300010014078004009000450740d1946070004191034519059044202e030402c1c0016800c12100c07040f40c40140c0d0b54841d0034081c00020040222640c05600f4031910f8a40c2c0c548000b8042c1450150181c144185641480c51b444010409401099100070954440f8464000204060b51006001c01d208410f4070b2664556500208007603a4220016110302d8507002c0503540070380140403840c1c0038200d1801203000000003520380c4d050200805100e130041c16951400c14080100b0407281d50031041c0c0c1c40ca800c0c00244040d010016011500640f80c1c00c20b61051840030240030745c0014046012002e05001051803491012010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 990531375 1250 990530125 990530131
    0x106060c060b03060609130503090a03121206050d030c0503040302090705071505010b0a030c0c0506100e0a1506110c0a09021c27020f09180714060306010f030b090a05 73
    0x34005020300c0c4103041c109544da02e01650600da0200100d0049841c1c0101c0392180e2046070302c00c0d400d590401c1403003030010f0070250b816441620781c04000c0448a941c242c6c4603c0b891030042c1b4032681000400c0c00c0801254070001d200340028180285e02c014182031002c00c006540c0115801400030f41240751000c40141190000300c2c0441e202e400c10300d0301851510303150094074143c0301a071880038106090894110b000d0031444c1501c81c18030814008038408a0300c00c1c0f100c2481101c2d10010070394682d1500d42c084044500050111004910305a10040010301000b000c40840341d00d071038180d00070200e80202070f040c00b12181296034042c01041c0b00149083e11600039203040511100b410240e043e05503c12001da86211044040c020a40304030703a0803032003103046401380460001e0700d4030030718407411008508120015192004510b010780b0741442c910f03408001c58006485035071842d440b039941c5840411104d0101400c05810702c2012400c8400c0c8511030b60104295180040030b24019040031007004001b0070080e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 990532625 1250 990531375 990531383
    0x31b0c01090b07030819090b010902031005010c02031c12020409091703100506210a050109050106230306130c0c030201050c0f040509070e030304080715110d0309080c0106060c 77
    0x40307074002501d24000080c0c9000c00d40540310b040003690303055941c20140b06480c045160322540c401010001c64858104140a42140d800040c0d4030300f4580c1900d481c2c0c202560000d41004040b41610700140c0307020a0820740d0b41c022a12204040000080035118104616800d451052000c1800907810072543c201c0302102d80940c41c4c045040a0340c0008801c94802251800d001c481c284400f000241000002800458141c5450514000b1021100902d030403080e20032551036a02c9600500c181c0c119803080d28010001400c101e20580c107945130001c02d91521080c2c40750303800d60100000c1d0940d00c546501c14140004201d040184000c4480094000b4080540c00c0d401517180400080c001001700c4102d408070410009400d003040d00e02002c101740c001c0003c1072141003040340d0542c6d0502c0d1302d0030000390001d450800040d0614a00b410034035008a42580514820081c0040c00044402004a904180d0607aa890003003801040c6050424240c89500100c202c29071800d20002006030b4813140102405100b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 990533875 1250 990532625 990532637
    0x50c040c05090d031d0a03030e031209010c0818060f03100b0405010c022b12120507080f07090b0d0e0c040204060f08071e050304050c0406080606060705031b0c01 71
    0xc02100c1d980215010150029108080c40303020074041c07074019404900280945420012540200391013804031f40c01200410310510f11601e5074a020b200b1019a21440e6101d1403c21078207100080c020180e00201900481d0000780c01c240483c03c1403c1002c0c0034801502c0c80d55211120020420390b927108655001d1409103405011440030380d000101c4003281c0d07050b074461000c607600b80c081150081c09024143d00c0b0445003200403040d403030b8001040ca0a84c1c012044030105102026028014902c80544521a946080c1c1000203460300303d209a9041600399003180c025a8402c01c0a58906a40d9040340400c070070081b44411021f05181c000300b503a0281c40c426265a0203411040c84281c0c0079500078640400d02c15480c926070070b0b1090210643c043d44034541224264807020f4650320364940840c070500001c400104200c18030130100300418800c0b605031010884545400000b54440070050302e01c501c114800900c907003d021082050320164440c0351402c140100e840034819540c0d5414048141c00300388 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 990535125 1250 990533875 990533891
    0x19081602011104350d080108030901080f0a0e0f03031005011110020c030715020d110705060103061109120d081320041404060c0801082409010b030604050c04 69
    0x1106002d814a80500404001c2c01c060410000e00242c0c910400403140041c0750754510301c1040d2020300001c040c0322408000d007a10b490b40e4800240b00c003905030061440c0c0d078004c11000100d40d80c00010250b1000c0315811004190719201c0c1d400024108028030200356210f0b8107601080c1c00008001140152403201c0707800f1344030b5aa00c0041d1440f0010319015a92900094045484000550002d0841600142c2628646600e0303946442080009554204103503901003004007080e0321503ca80045040d80b00c80c02401c2104aa0b6000c0d6560b005010090240b030b201d52070226643d0036401a1851000d004003042d07142481da115056441c251283c80b03100040702040416044482c00d4409040607402021a5980303500c00707105002131000841400e07820a550b8120710b828000003560180c0120300c140380206841e00001c100508034503040e045209181c00200854204001e090134120310f0902c048070f60170340c680d501c5400074014060f501c411a0180100010001080340100d45030441c00d00c1200c023046080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 990536375 1250 990535125 990535127
    0x2a030917030618010303050301090f0603051f020f07060509071202100c0326090615010516060f0213061214010e040c03141608011a0d08190816 63
    0x140519401620001800048034880d2240c03200940d8040790142c11031010030102c0200080e415003d0344150001400031005010909a80c000c100d08035070f035010181315003400d40d150b203600c8510f110000748030115040c841c10402d250580540c0c5aa4900d20041174954101c3e0800901400049400c3c20190040c600041095100c106645d07503107139000351208460001e8004151448003d030030055051040185640000184c45607403c0d28016006203501c409040c0a01854903150000e480f0a00c80c41000d408000c0c2c50f640401070f162034404610411000c4002410000700400c1040c04c1c18584600002d9940f42e84c110b000c03103003011511680e6071580c4001c040903100d4100c41a010031121051f1402c0b0040106903000d001c41078125019000520390a80e0301c0da10310405000138005154240c0000202c0e000810130700c5c61000c01840f03144c0084c4040024403880e1011b0403403003c191031203100c0c2281701c142880340e40d4044e1107114082000540c00250100000303010403000312448803801040c01a00c100d01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 990537625 1250 990536375 990536381
    0x50a12030201052a070f080703090602010e0f0d0e01090b190909110a0503180607030506031504050d0503040f1a0411040902090105120c0a0e0108011508060403050f0d2a03 75
    0xc4100c5440810329160707800c0796450340003400c00d842d1b100c1a0300da02c40c0850203180082a0341482621650310945c981100603003034ae501c1c50680740d559041282201149000814844000c1245241c00c1102c0c50f030910059030a030390144c0268095500220721400c030440024412140540303a925104009503898148a065a880340c032150443c1c0d0041c0f2001240074000d00145401c0b0328423908080011440031645450454201c0311000002d80714010b02c002410184082c2c45411910f0201102174603258a030142da8104130600d00007040740000c00602400340000c0344c64000d581c0041c1c00007507034030410f4103804480410344003606c40c0800c50034a0815070ad014401c01c001c880d4060302d0340a140e8648800c008411413403800348a400e028441206c110340e030390070782040e0140c51402007141030765040c1f4070900d013128910321580146100700c00061048140000d00150b1240d45031070019a1420000d010250a010fa2140700050505258401d031544c402c540501c0c100c00081400040300061228040b019 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 990538875 1250 990537625 990537661
    0x118030c030f0611030907120602070f0f03110a03091e0e01060206090115031e0309082a040b031b010207030c060f14030c071103030c1e0d090b22050a1203020105 71
    0x1075102d02410007407400c40102018445000704401800d00c10300c0e0321380540548140a04a80d0484a007402030109604101c0800003600c4041c003c20a032001a9400b8140000c0d9000c1d3d03404550001c1501c0514400b42d4030f980004e00030401e81042079503900c42000c0e503102c81c1aa5040100d5017040030103440d14211071006c400b10386e004036050384400d45c44905c612003002d20000590403c200c1355400f084402c0704100d00c00e44a0030501e00801801045a0440344079803410144503c04c0741000c590403840d64000404145240b9404078281c0c90600801c0140d1921201e98001010050303007250020310316411044015081c00c50b92980c0440030318852100c000da20089540d00407500041c0010b40206200b042159807080001d8100c9291003c03042c01d4500c1d01c030700310a002e000115030344000120b030181840000b0340d1200c641051124035051000034511030045c2c2d80030701c2d141141e8610074003001e1200c124100c010b1001138150008035880d489031201800b5100c0d400e401560034180441c00d03240f010543c17118 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 990540125 1250 990538875 990538891
    0x903020f1c0807031505100e03060f04050607081f090b09160203180105120108030405210705010302250308060411040b0706020a020f01020d1d0309030c0118030c030f061103 76
    0xc42c2e90700e814041e001008215202411100c40c0c44000c00c5907200d40301c0407901403040351124055100781c0c0d0201890070302e000300030303440a0a02200348070008500150690700040c143c2044489a5156200100c1c01440405409000109040c00041e0000c440d813084407001d00603549071200360313580075001c80c03105034001d000b00050340100710282c00d04886c200036030b080c0101454024034005c140728803811143ca0a810406c240e410015003080f191410305070421504c06100c1c2424110703018100d070241c0b40e40083c41098141a0000b54501d21f01c0c1000903412041e04070309410841d0401141001080d4650481c2c255000d03618105030008501d007007506403070464280b462181d00c2d00729035a4610001c0c0d0001680340c0154803445200c154285400e0000d8100c09003c144000740b81d00c008660464035010000c24012035400030015000c841c0c030b0124006403002d00a0038842c200c91501c84031510342c01c170168800b5201084c0a0070200800c4044941d2907450b80c000c070070a001c1c00a01d031080400350321003551100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 990541375 1250 990540125 990540137
    0x50d1104060306081b10140403050313051504090507210e010513021e030f0316061104030807020f0f03070902090406050910031202010f0216030210020a09031e060903020f1c 76
    0x4172040c5450b07500001c3c94071080c58207010780d01031883d07a440b41d60001d40086070207810100b9004104856080074100402e41100d000c6408030000001d40302e0b40c400c0303000383c003c0c0c6511040090101402210500d41000284c03070316440010684d13040d140105103030200d0140950034034011400b4029403060101045400a00b12101300781000d0301441c0180c19a50303c282c2601030b1241c4c60071220b1041c0050858100510f4107560240c1301ea02e800d030100da0041030802000c4009000500101d1145070958078a181e044c2c0b00320308442d1901380040d01800d01c03413810507414400c50202003021070301c6402900c0e4a410544082c088140c48104001d041c62080724094141405d02008101044100ca03a00400c0c010780c0c0000207104042e00503050903030344404108502650f01046070801c140d8100030084400192610841c03c11180d40380042c11300d5031a03c00500110645007204c0e00000140c400400880d610601c1001503249603d80a51544442d0f9030102c464000c0c001d40f074460900c110b103108a9540550350306 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 990542625 1250 990541375 990541423
    0x14011e0e0915070206100f270e03030907030c090507020319090e01030c0302090f16050f0c01090609021002070612180506271204030f0201050d110406030608 69
    0x100c0081a006052035071078400c040c0c04140a0b03601001e000e006180540c041e004c17030324000c4481c488003800c5034050155100000b40801140b074440101c0e40c460034001074080c4040c2880041036000c1c00d40480c01d90850b0000006005100100080b13010840c0c1c8201ca00c1c0507581c1d65a404c01040314000c45022000d80c008114841d08040303007003e1402d00030f40301d0070645c00043d2247c9403105014026001228210100f0f0401d00035850032080b8268055944040301c0c007145849043c280781407041c441c07110144140801d42d030b1030502084054480000d08080204040740841c200103003d049003500076070003403003c40c2268580d9440131845600380c0f91903460301c0200005002d45107000b810300d59a80083c14241c0c150100015005100250085203980c0800444514514407010143ca010030b00d09415400582260802d04000d802c0c0d5040341c1e0400582c191201003400140d50b0b5101c1e40d03065080351880e002d00e40b600307040d60780058415078105a80c01c11603552614000d03a50b421142040c48540b6420000c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 990543875 1250 990542625 990542639
    0x80309060d0902011202040b04030308090105070207050603070c0b09010603230304050112020417010515100c08031f090213050d02220f1e0b0f01080a0b19060314011e 73
    0x14040603c10314011000c505003114410880c0c0041c0c00c403100c0604002010414141d00410590304112850004c100c81d042901c1c0103075550b440c0344030349400b400c4d0110004000034001e402c2055a180c2000107810646865000d81b4003d040034003003120406503c0b41c0303c1080302621360440008182c410002e515140c101801907944e8989000310380c090540030070000c40c00040d0b0317034500300d81c806c1200d00114003810610054000840c4020900d4020910740c2c003082802030b40440e0301d030b01c9250000b4200d542ca0300d44a202c030110840317400c074144820742c054a00180044a6900078840c0764141d0408402150f221002c00002c292180c030301960001620740349100821142c1401c903040fa0794a54000b601905165a48058826643c00c0c070090382d81e070756140c412224807805022280c43c02102c000c0d811500710030020b400b20502511041e41d00f03aa0b001c3d810890386405582507015005034400703224040ea1194014080c1c1611450b00d6280341c0d4074000002c0703034140e00300400c01c10310341800a41c00c000e081c030003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 990545125 1250 990543875 990543881
    0x150405160608070c1e030509090609090c012a03020a0b0901060b0d150503101d0d0804120905030a1202010e010b1c0503210106110d020615030f060c040f080309060d 72
    0x50580345c04c0f8000d0904410600001c6021156030302c80c0e154940c641844804002c82040f00820050182205008000070a84041420140b469007400e06546100304588025241143d034410510751030b403120000401e260300061020121440342d1000c8095a0320880d40c0d60136102240320302050b456050143c03202d5002c00c1c1e00000d01c8410300807903181d00f89640350700082c913084120158110f61651100c80000710400400800203444400c001051590984032000308050710040025049400944111360700c0f074415102d5038002c10b4010120b50116007035080a5004010300c10100c2e000d0342c40c0c80e500b688681011b001d034075180c1900501d90501d180740841c0b18049108410803c4802d4041041203510010034000d052411101c0c8540c803031312960626101400e5008030502203805948040c505981e140d40c00500303964011403a0220703a80900c0c6000c046032070b002c00000440224043d03001045407580c4000003038070403601d1070b0440c02c40031a035030310f81513861b440351122243e00034400300200854580d10350 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 990546375 1250 990545125 990545147
    0xd020304150306052121190206010305191b03150c0f020c06130509040c031106041a0d020408011b02011b12020328020a0e01050309191415040516060807 67
    0x9406d5a40300701c2c0c420309410032903100c0d445145107040041a040e0070188010b41418080c45240010b00b1103505548515036100340070150040300c905030b00d0080040200940c2441510002d54525030030a98031391810345252145403900049040c46c02c94441d480324800d0125030400311980d0082c3c0024840001480703d0790384025903507040d4a40901000a0b5502d035010f840344654007031180c10a4440c1949804800c0349109002c4038070484080c401400b0310342c1c0001e800d60001000f49100c5944469440282000e4003c69100d480a03500e40400c00408801e240062044050903a00800c1100030420070281c01c1c081510200000520f25200c006110341642e000b190800c13181e40d0103000c80000001039141000760344022095042e00483c011020540000420550307020901b17145007140381081d40c450750364055010540790740c0a4a40c1e000103101c41c00c1081080031010708142d07108440c3d8a00c00341410718054a08449521403da0400d61022000700d42e4420b498407039441245030344038007408803400d002031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 990547625 1250 990546375 990546439
    0x6041a13020d0206130803030103050709020901050406050a020106051005030f09010c1b05250e0906011d060a05040216020102060105030d050316112b020708071e080d02030415030605 80
    0x1017042030071442c200e02040009201002c0115502d6046140250811034135900c002c1c0300c203005115030b00044e070f0810151400d8659501d0710f0354541078212030072805066160302c01c07600021034111008105500c60001d5105100200c50081d042e180c4621841c04c8500106111000400501070f95960701d100e296802e80c0c09010300304031002e0052990640f040c0c180f90300281c0c42ea016019108010303c40d26180c420f80c0c0101e50001401c00c561429418003012840030086d032400c44c42d240300003074140c0c1c0c0d074049040c00703044040d0007151510507c0d40e82c40b560040c060010380c054400e000000800d445d00061880500200d0340d40c490458607515609140060110f892905114048030804150801004101021005080c00291138412040030019190045a020013190840b000901001000041a50031a103072075440c0381c40107071842d680c1c01d5010381a420250150203010800680568000044d10039140020810329051888480035011950b00c0d21427035812100d52048904d041c3d032a004a20b44030084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 990548875 1250 990547625 990547627
    0xc0c03140d0906020408030c07080c3a0302070501020106120c360f060e13030806010504030f11030c0d0f061a18070210020a1d041b0206041a13020d0206 67
    0x1460f0346000598126400021441e440800c5056614000700100c20051803000090000b07519440081801102c00c90609802d05900c08842c80580c004e0030040d01420291481ca4808601d19140c000c0d10f0740d00c03a100f054011760a00c20301160303101045400303d032030560014612002615100420308400c180b506214500c03420f03c5040404809a009a003018a948600c00a140c1300e10140810481c3c0080d0029020032035040c041054043c03540240314601605410b003103103e07542d42401201e1034030441d08001e000d0502c1410b00000c00c0581400e40c4c412402c12029220200e21903400e111203c4d401c00340242c103007030210100f01c0115401d0b0307001c1c00b80540b0140302500d08488800c0070501420741c02c3d07c498038421843c02080000b50b41409204d41111094009525080a031000104608901d840c1e0007905e0084841c185180e5035aa4000064145505400600c0d01d548a40c060345a000840d400d45540500800e411250481c050b01300d4810002010000008030a035001d00c8052004107504070b0304688 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 990550125 1250 990548875 990548891
    0x60b091003090c0618090c0206040b06041506030e060708090703031211070f0b160507060b0a1a030718063501080a0203010b1806010507050a0602030f04060c0c03140d 73
    0x2003203c52407001d0a0340c4d88500102e98250406540d2182c401d50040090030f16082d080c0c1203107980450310581254000030084d00c241c44510000c0d000702141c0c01c4080c0c40c00e610050000d842c9415400c101c6002c1c1088040d2841f80d0394814041d50510340440384100660018501400000d005e22400d0502c60b201e284005807a00c3c241c0c1884000d41c0c000002900c0098000402101f008800c000b030035030100d4400030b034411442d19100068070074040c0c58802050143c49280c410b1a81e112020b460000340500d0820b0500080b40e8400c03280d1550059800c0d9001070141662035203101c03801b4402c0011243d0f41e54490344500869002c0d010904060405a105007500d0146444503a0118451070701a02042c1c01030000107105104140c219002040001d00034403103031100c005605c050107441c5500000070300300319070303075010a150a9003400d0440380024415440402401140322843e884144072364420764003006071300035283d01076940f460300c010020005010410010780d44a1800301800d03c8090760380c00400d4040c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 990551375 1250 990550125 990550133
    0xb0405150a051e1314010303122f090607060c0305061206010f0e09031306020f0d0c1101030e0f0715110f060105151e0306040b1c02060a1e090612060b09100309 70
    0x5c81c080c0e00c1039000030307072902042c10842510700c90012142c0030200c00b41c56081c072000c0f5003130003119201038103078400c140442d03a2940d5403075080c00c50f40c002d607001c001003003250040c05014004080581c0c00c6801082136142c2caa441030f0000a0b038a060392400001d03280b4440c60f0408401100c2c00040032100140802c2c000d0100200b00005c0c220090640d43c5c000c0c101400b401a14186010701400620741081103095100d804566010061010790360280707400300e0345441d20420b06203000c0003581455000e116189000410702246140803620320500d5a400340e0501000690a44d621001520a9581d400450040255241013074101c0401d00260003410300f0031840c0d9040076090159002e912200d000700104002c041c1c03a06100700c100700c07802103c40e0180004800380340c030b0142c440e000b8002c2c0035038000600042d2035405090114402e04000014000340c003154840200250710a00c40c03000030900302c52080864155a0041c0020744100070314060900b9420b00401030510004168034003031541e40e541c004041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 990552625 1250 990551375 990551411
    0x80a1e021306090b010504030c0b070f0816170c101a1809100207050706050f0405090406140c091c060905151b090d020f03010b0405150a051e13 63
    0x500751000151252610200300f0035124500202070401800b00310510009480c0700f42d44068400c000142e50b00da18151604140404d2804006065820046505512664034044100c495481804d07402c58000780040c3e5a20a405002001c1d030141e0070440c0307007140300903c503440b501c80c0320002228101c0741035500d40850814050b224500314502c44010410205110030070200000c500300c001d00b140f400116445e02502c1c0c076405c0c0a00360400c10006200d0306030454040a48014240080c03507012241850b00c0c1c00001801000b9040c400380000f1400034400c10369200541c2d8250743c02501d1448d03030400302e0a410030014034140c81280d400f5929007403240455010005030340e4444540f078401c030290500481e82105100c008800f054070100403c54950740b41c0703800301002a00c81d410707900f48040d41401d40029002d414182e0340301d0b400c07601c1c0800300482d111410301d81d18007142e015141d5107482501d96090020612601c03840c03484c001d140c41c11403280d505203503210383d01c01c8020301000114642807008010072 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 990553875 1250 990552625 990552649
    0x10f020d060806010e010308041e0506130918080405040b04241a0408152206020d0f1a0910030b101d060a1505160b01030c05030304080a1e02 62
    0x505a541d8414010706804000e414050101c484180003190302d1961000b00c14495400b0748c440c20300703244030418284158040c40c18040d0100521071911400300e4a0000c0600c01030b071041d00075080c10084105800c00080c1c0e841d041654100d020545824142001c0c0700203803d0350349061760480e40e510325000c0155040603480700c00128204100320418034210710003d04c00715442d50318201d29010401000800c1001030b00c17020044000311641c00550b2003180c01d800c0b000010403690300820f20000701d881003281c40d500909004550390410462002c1e040410310448a58074501401c070399006003800e907203150082d86640e0000303416190f030007116265900d54060002c03e4418070000c0300416003d220303a4a804094010400c88038000703d02d01d180940002e039a4500c0c0748600c280c031207904442d0445617031155007258944e102c40186c120170b902c03281c544030042150901c001d4403440c440c00d801003900d01d804400c48003100d1405006120310420f54450481600c00c40d80c040d0311040f03485002c2c01c0161034807031017004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 990555125 1250 990553875 990553897
    0x4090f090506010512070302041119031d0f060f0c0f0f04090f02280302040f2903011d0c04030b24032409120301080d0905060a08060909010f02 63
    0x140a003918500140b400506800c0300c2d1045c840a5500c107010000002e040341200d40441d13004c580d13100c0403040d480d280d00c11400760284100602071040c41142d01900304200c088a54907044a100031f4a01c007450b224450710b1035259440e00076401103942c42c4032210a2135040403c04060364034024140e0b04041069110038032603004000080b4040200350154440d00461500a08041d890071a040c10105080f6800c1042d080e4075051103600f0003c214440e60686001c2d1509030710200c0d001c1d494240b604800940388038681c050b84040881d060782d204541007624101c403c1d691030b4625200c190202c98861b8000208503c415180600c4004003081070311442134014110a40c4001803648000d500c03032800004000140e0080d03020b1089215400c088861030721428401050b03038441600d80388151800c003418016600016100480007243c2c84001150700c05402000d030b281c0424184e510414044203011b41143c0601158502c0c0000b0010300f0110320352a4170020510000908845803403040c0e00300e03003181b00300780307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 990556375 1250 990555125 990555131
    0x50627030c0a1a190c0314040518090a1e0209060312030c0c1c05041403010903050a0c020109080a0302150a0e030403112805040c03110307200609060709090c0f0807020304090f 77
    0x1702c103143d0081c3e11981000100700e803031480d0078240030100c0c1022900070500c268949412001071411003091008101c0c840d0310a020320b0001c40d0f2418110794203040c407c000e81c4582041030100b000c0d8500010307665000d1019082080c2150740d40e003203100f8180c21401078602c0500444030003040352031505002a0140c01c6540ba05600e950420300000c0013101d500510714066898928440c0200381c1010549038a046c1d5854521540640c0c0d01c0101ea1000899200c5d45041c4610340c4540304240c0c02180024800c41140da0200c115a0b5030100c40d010307540d20307451007455500f0400080c008034000e455000c6001c40017806005000410120b180e000c1031585c1c0080c4001c5c0759a00003401146458094035100c0daa0394503003484884041c0d901a9031921000d880780c000e1107050164140540301100c620010a942c45054500f0780c039181d080f0b292547d0f0300303c0750400001d0840c44089660b804600c00d0513082000340c1e80304010b028090b542516906406080c60b002e52005100020700072059004200d089911901c2c04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 990557625 1250 990556375 990556397
    0x18091c020616020307021302031801050108071e1a0f0f0c01062303030d0207050c0d21030c080f1b0c0c1f0c08090109050627030c0a1a19 60
    0x50001c50b03080d44254000c42d0000c02c0200003503a01c002e0020014042000016900d4440d07540011034010300c0c81d1511229401c000000501042c0890700008880400c140e210b1554501710907129000c28a01440114102003880342d01200c0740324000c1c1101c0c044100425141c114200e08602c20b641140900784106c1e91542c10501c000521171441540303640c2c21b80602c400180f200c00000c0c7d00ca0103416165056958003043e5201404401c100100414101a00140341009541001d1340d040c00586019110384582210b11032205101c3c0c403503505103500c0d86da607941c000e440313041c1108003054000c2c0c40303905108598195081c05a84110003800c0078a40384005040c1c0c9001c00041c825400c4400325240001071030401076010340b03500a044900502c0d8041d4485965695180c010380c3c81041a42106070001400f0481d90308071341d500108a00090005000009260004c104142d655052103c2c0a03400c80c251540c00c00c0000410104a8801c0c60f5444541c1c1c20a0310b66851903841d8607080c2c0c80b60000880311200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 990558875 1250 990557625 990557641
    0x6120d0c080702120c130e0c090901090b010f0f0509010b0f0c0124080f21210a060305010509076801060518030c13050a0f020918091c0206 61
    0xe4144103505030f01c01f803003440342c100a8162613010a00c550760196003217800181404c01d0a40c8000c3d4480d900034808489540c580e90085601c0d0514060340c82280f40e100b402103010b14258200b64100c425602240386440d215007100800c94000a2101070550348038191125080c00a01900010b80da02400c5041050b15102549243c0441c405411005801058242c41180110030782460800041740141d075880501d0001d01d0100c0a840540d500300a0498003402440000fa030030041c112030050009110680700c0340c01d4552240002d20601455442401c20b040392110840c0703050103a4041c1980314010001a0407407520305902113803813104085404114072220303827401070081e00b50140b40c0c49410fa50f5810301802901c140305094401c2c480c080c01e6141c41226683c100900d40e07425901030101401c1c00031b80d24401d0054101a40c1d2072860900740381d0300040040c1c05100703441f0f40d100001c001503000c81003403117000350703813040906000d440e4040e010004002d0b00e824418920042e0340f55000305002d01e0030041c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 990560125 1250 990558875 990558889
    0xd0203072f1815090f07140d051609080c0d0303051005130b01030c0207060903030c0606170d0e1e120304080f15060904021327060605030606120d0c080702120c 70
    0x94281d104000c1013090081c40944c400c07840c3e60251041c14403810f10700030142c00c1415805841000b0244504003001c015a1a099290072403d0f0b81d05a200c01500ea9100ca8800c0c2d1074100c046403840e000a1035441300c0010a00c0b82c0c100c1c540020310b04e00c40c42c0400382c40d413020650500107000c0503040d1b02e803504107007012035901d0320034002e82050b2440038003506818180000c00c804001d200180410807036810307000c03c1c1b000c198072080040444514801c0d08113502c1a209880d46185114000032540e1101188a41d0910340a000201120049122030103034010b810041034604d404040300c1d041c401440085440c0c01c0800c100e644829202d0300a0000000c0a56210040031008002d9030040401c8010300c401a2101000e42c420103804600200d100805075400244800d87c9000441c03043c0f00d1304c91040f082c440d440d03001c0d105444058094844680d10300c1c052190194000040c1001d40d400003170283c4145104803c00300c402071203a000c4600c0d11f409071300052603404000002c903269401183c1d010019145c580 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 990561375 1250 990560125 990560161
    0x15030d05070b060f0310050415060806040501060902182211040f1d2e0f14040203100e040302010f0f0c0f03050f060f030a0203060f0601020d0203072f18 67
    0x41303d00c0c41040d90007000c2a11444070803040a20191680b020030100000c02c024404411a1038004202c9c00b5030f40d141e02580d580c026034068800354a028400309141d0a42e00848810540100c40103d40c2d4059205104400740c001581c030807940350f12016a40f1307540c0c0500440c0e840d6180a40a640c40b036042502501c0340313800c25401510490792003941c0001c5100b101d2003450b40400310024100904030300c035840b2030104242c1c0350140c0c13a00320b82c09004035001c0d541d5401d00c000e5451207891290300c28840d03420b00089100540706100106503c5808010700e41c9064041d651161003840042614032070701114406031421072003994140c5841d0111070300c1c1c1030340c05104098411030a00d002e000c1820107110050850001400b20b0b8000d00d000c541004898908000d07481d00b40da4041c0440e9082e00d024030304d041240c1029a0924011701130902d403000910704c0001621403980d00800f54048403003141a01c9859000c40c040f0030400465140300001940d600c050403240d4120860011030550310341095954201d048403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 990562625 1250 990561375 990561379
    0x10b0a1706030709110c0d18050d0c0504020f0c070f0e0a052403030f0304050d0f1e0509040e010f0501030501151a1b0a030228031715030d05070b06 65
    0xc0400003a03540015510040300c4502e500010303928001c2d403400d01070384902894000749118401a0a80d403c3e0300c011003080301c480d81b010303194246803100200300c0007443e400001f0b00882036100e0305100914080e401880c260500c140e03490702d0003010b4100b0030305101495016005440d0260010060300403003086c0e456001000d014100158a059000c1c1104001d10002c0100c58a5542002e40403d0b2010070403036100b00543d4540684030b1400b440c01039038940380845064006214014183c40c154003545002c851103040a0300342d03a8900000784111881d421240c0380035070054940d80ca0485250081c410b101d01117407002c034085807a6066040150954001d46414116006006400c00804072201c40f503030101650b02d607201da6140318200b1010703400a400c9955541c20300940c02950209a00015145011442c2d0612000f411b07a244c62402d41e182c01010000d4081040c1003070114041e030310000a1980201448605115012008003003898140405d480101284002511005200c181d4080319030010701 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 990563875 1250 990562625 990562667
    0x102071505133804080307140d020c0303030a0903200a060b061e09040605090c0d0e150115090905010801060f0b070f020118030f200415120201120203010b0a 69
    0x3480400100020b00d842140003c00c5010795103039000c00101088034020aa18030803652a124981400d54146000e009100101d1041c08002e80d9010300101c0e034441c4100c0002d002e035003155551041c440282842100071001c200302002d09a070a00141c0c4584035a001a030801442d441c001490300004486072214150321810301800003005424000b5601031001c00c140080e26158030104010074064a1180c200680c4103600404024503040300102501c280c4940030014000d100102244c161a110001200b024941408005000841f418a0000355510052414641c200d0381c03115400c08032a400c2c4c010318400d9440384001c1103618402e0035404043d100210b0a1840c20760190b652801d5000c40c01c01c000c0c148904420070010705182905c0345001960054580e00c0351902d140b070140341d050850110071100da444810040418186031044455405028007641260344c00d2940b440080d01c81004100e040041c0b00d0007541c0804502d001441c028071f42c0e0006130b501c420380640060300764981c00d5161410102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 990565125 1250 990563875 990563909
    0x30e090114011d0909012711040230010501020c0102070506030117030c07030602040f2103121e1a0d08030a0c05040503061006030609060503030315010207150513 71
    0x5101d801407014502424000b503103450190031a003418019041c0b40e640400c4200c10008070480c1900102d0311100752007071042c0360690039901d0300002010041c01506402c51403000759140c0c2415401000c1c1b006050140d2580e000005440c01340807090074001051075a03420b801042907507010030001d005d0b11024000380042030f040802140080c00144502d0081e80790784d14402c010100d0510071940e8084484080d512165242d00b08480654024418592805420500090800000b04070000c90215120b201c89100f20781e614110b40e8150400403a400711071343c844000a0760503c0c000c8840f44145060300218022443c607444060303e00a01010740e0240c0031880403140012860780441e580201c04500c002051104c246089510740159008035406100344824055580f84940c1280125099075a0078030640340c60340c0c4070070305488851080581651007480482c007202544052640c031018103204603144a40d0350030303118480c809140180b00c003142c80002e200c0f00302450740e8040e2018102c42d08910761030781 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 990566375 1250 990565125 990565139
    0x6080601170a0f061b0c05060a2906040b12010f050102010903170c0d02040e1015170c090603040c24091403010906060801022214060d06030f030c030e0901 68
    0x30307010794402420741e034410b40c1d5201003004c5980b140d20704c00004800c0803100c030b0a40d08094268255810306649503c01c040000c1c2005005001d410001a081c072040d01034000c09000d803c6015a120140c41d6102c0028403010a008440c4c070040c1810310b840c10710100b41c951500f41441c03a0b10581d60895030459042c803941c5404241c005012280d0900c00c00581c804658a520758450700e40a27007400141024000100003850f4140400e00324000c00102d4085c041c02d03a1382c0c01c1c0c0300c0e2a00d0202c4070740310301148102c149003c40700d0080c4440c03540552606581850044400001242540300f201d08075501302d140f000604c250030301004072000700ca2045810f1110003c3c031040180c4940028810035080410343c00e44030b050f54500390051007003540e0202e82844040c4e2210b207102c1c082d40007207104c0f8512812815030004c00c111061a40c000b115016019001c1300070300402807001c0c55020b54134000c034480d258000000010f0080c0d40d05d240311800b070340e5000c3e13400034a450020720349404860f0261160080301c0c010701040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 990567625 1250 990566375 990566383
    0x1d12040e10031106180607140c01093f03081902180d03020c03070e07120203010e0a0e070b030c0406141305040f0905190303060e070c0204110c100608060117 69
    0x810702100d140d81c560b941d00d440481c1078840003030f05c650080b45c003080c6d1034100510030014000400c829000c0c2e521f51010b00c00110f13100b150500c124040c082c0d901a072500041c0110580c0103c1e800310b200b0500d0081e84e007c2e4001034802c0445421000200e4107001c001815000f0709208040310036003582035107089200b01d0311220300031000d4466407060304010f9038001054001c2101070030b03060f8041c044c5da000a6446000b103030f09120403114100820880f207180c0041c011144203c070b059a101035800320f15600c031010000000d00001011000510541c00c011601c1000c0802841c840c40f07c5045843e0361b141031135401410f9040000c110b40240006002110f1703031101c10300d0140140e82d426600061714010705151003000e0314412101418030700918072031005080e401c441c10ba00050107900d041c0030a0341c0d200c8041c2005503007215110005040c9408000051400b0b8120b40e60340141d021200d818801041c0240d420b0119a10507a041e02c4e55960041011044c14003085004205e0844901e4195800300002510f07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 990568875 1250 990567625 990567653
    0x2090f0417130509220b0a050705070302030304110307270c0507020f0d0213090614100825150201020a11010b030a06090204020d020307051804051003061d12040e1003 73
    0x20400603400003c00c4554084d101c050b6a9074442d00003c0b80440d54100440c071151b0594400c10840d0030100000c02d900e001c1d5082320680c0da4180e004600d1555251148515400201501c940c1030298103000110b1100c2515040f500c5030a00321030f00e590302001030040080764801c4903044203004041c45030b90b0250765500c5440c01da04005441d6200010030510008408911580382d1000c0310345040011014400d21ba0b000d0300c2040d6042c0b00c0c0924649912000381107114603441003000c0d130380c000c0c038004600d4002004050520741c0c40c1d445810f6415102e404070711155803c2d1600c2c80060307502042c1d10180e2588545104c0c036414414001308002c01031b0a001c80e0f1500e2211030b01601c000d032100c00e0f85046484a604440c80e2050307000c411912801c00f250300a0444c4d11081c00c2d92034800e900341c000c1c50395203404d100305406a047c02c0350121525281d81c0d500c0b0040d01070081c14104070b0110400a071f50b00c803001d1200500a00951a103565518100321604c440410b020b0500404800c0f115014000161100820320f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 990570125 1250 990568875 990568879
    0x603050f061030020c07050a080a0f140a290705041401110d08060111030306100f0c0c0e0108120c070b07260d060b030f0a1802090f04171305 62
    0x140300f00001c541e000c0d5020b001c0703549000d000d809465080002029809840c00d610340805403801a40c1d210b04000b1340f04058090a0481d4000425541c0081c801d080607a100301d22030040c920150450102e082c0c101664054103445081c40c0726a10b251008071190110209071088408035594180340800030914000c9000320845074003035904106c0180c1c019403880c051091240c085992304ea92084c4000e10005050314000c0c00701d40040d690415480340030080e0707032080201411100010356407240450702402400340a20601c021001090003050b48041f1040c043c0c4a81002400349503d400a05890054040501c0d04202014040300e00e0341500440c070b0340c0c00c4403044801076481c0d0b01a400d11504415404258943c220b10f101102008a19240050401e005039030700104442907071450000d60a11046a5215902c50b41c0f000047c0c400c005640322604212641580c2c1c08c4030040b07079010520402d0151030001240c4200001c000402c0b90304500b0741a14004040b40a041440c50f40005030400c405000d218 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 990571375 1250 990570125 990570137
    0x130b010905072102090108160f0e120a0f0506060402040806010e040204020f1815030c030f04050c220507021c030221041101030c0e06090411090301050705040603050f0610 75
    0x6000726104030504006068540f42c440856911028410000d61000d107186004c5200300c40000d004100b81d85080211282e680c5502004420080040b50800c0c40c131010103070b215080043c141982081004612011445021103051000807130038a0707480c210b00200380700d1260340104410b0111400200cdc5860450702040f40003c0c552b2181c2c80020b01900513600789450400022441c0250b8002128829590b80c2d8241c5540c0b042a820014002c001e1004641996880c4e008001280160b070341b00064a5002e4014025684c5655404000850301c5403d42c144010400c4100201c6c90a1000e6100d901c0d04052540001c0c000041040c50100200c140780341e040781070550210b950701c90200c500003040d00d40480040c2d6001c240c645403408100800002c052140080e1500400c2000780340559070346800b2103030041180e42445940310400c07014101c4191014020310040c03182e44d20648090040a01504040e00c400d0380310f6060403c000d0450f00000e060100810341a4140201c0351a600080417211115107004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 990572625 1250 990571375 990571381
    0x30b120c040506120109050d121419091b06090905090703120203090916080907051e0402040506211e06040f0e07080d1205060f040207020d0f0c0e130b010905 69
    0x9030000d07031030101800442d400d00180c1b20400601050235660b59007151542c00c0341d01484840702d004c88209801891011310498041200c1c6a218403400c01600000c450114007031050303a46d2101c04e26132080007240c2182064505209658014450300041d082c00d81c4204090320b080a41079030359600b11700c005421035442140d540001e501c01d1007210403040001c0d203160380c14100384c10441040c041000756200001d60f44000b2508024012403508200ca02c02042c0c1d4445145480503810340b0139029103044e6010b81d08000000740c54031500c01421030005112160542252000e10b041c4050800800007844004168211160000034100c500d801240c1501d001031061003081150000781514502c0800c1d034030680e040014060300015001c842840b81d07644003c2004060042003090b10000ea40d41c562151040d800e00303000341001d5000d817581da40010b04402e402c0c8402c0c2c6401043c0b0706010020348034030001d0344003400701b203150401aa4200c2c0b010758070f0103040d00031621176104040043c000d402c0c03035684900c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 990573875 1250 990572625 990572629
    0x6051906260f0c101107080703060b0108040515060328020411040305060c39011a09010b181c02011706130c030b041e051005060703030203070912080307030b120c040506 74
    0x40d02d1421741d80408032071440352a52480d03541c2ea800c03440121881402e00e11800c980d540300c2c070201801158413000400c05401c00d42c42c01c900c4c4042c020f00035070301841a417001c07008040b1488442c01c002050000d000b9824129401800240e070075038405410403110400040002070301c0025403c0e4001c0207420f860362195030088407940901103514401143c003240c2058070f041c1c051155461041c688221000300010318501c001038010907590220582c0c00005180104110880d07a8000c006040c000604a0000d00c44100010250300084035084002401323403400c00c0c11942c002c01c905d01554540440303082c143c5401400030302045000c14180b05041c3d103c03860114928003e0300b004080450040007805180e4803849010341d01104100c10902c03050030030303010460400b038139100482030b15000b818461505e050383e2419400381d880034003242e0800c1401c2000045010510070b00e007154904c90428156242011400201611001800c00f4407a000540b0021007072040040c55000408040c0c0d0040391540d20300c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 990575125 1250 990573875 990573887
    0x11010f050f03041509051501170c090405010b1009080d020304152105150f0d0b060d0311190303200901180b040e042d06051906260f0c10 60
    0x84c0d4880c1c19400c00780c030700e020031201289122150301e21800c0045d0301d81c2c0e180c09501c0b1401c0c4000d4041c1903a0001e100c048a18100000180e41c81406803001003131071140d241c013107400c02c02c80c00b1541c0c0c002a0410000d004a07041403181100000c400c1c402182040c1c00c0100f041d44651003607007007000b8040380614107103211600c28004040002c8a8404008600c0c0c02d01d2030030b015051801c1c24a01c510a0a40c0d080028507110094598403500b041062280c0d87c0c0750024001175940304d07001a004d1000907441c180000108101a251992039060306200c04a4a0f14000d0107442425043c080328103c00300c09201d01c5224038040e1000d8036000d10304024013130009400510507603525080398050b4040050082402e000b5040342c1e90213548a4a8074040300e80f1241582140c140040504140c2d580500c4031004c0402c1c015017085e90880c1c0072542c0c4200340d14003890800d08482e0258000c0701d410491102c8503800510300e04540c4001c0782c15501500c1340d850300341c244030b46034140c81d01100d224001c190501041188694 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 990576375 1250 990575125 990575153
    0x20a020c10210c020f0f060a1d06010312030f0902280b0d0902120313050405151309060c020c0108010b0f161109070e060a031e090b0411010f050f0304 66
    0x910700c2e01581c50058200d1010b00107000f00e002c0588144024000790740c100040c1e90307050100c110080d121540300d02040c040030f000b0756849096110f0648600388400201800000d00840c0f15050b080310080b40104081c059444055030030141a1034081a100035840710403038070300304a1b03c5600c040d400b0800b07440c0d1400801603e40103452035540114490526100b10ba120f0300b0300a000b201d0001e0300400e000c0c08240e9034030550101501010760748038104841e09098002c00c1c0c001070034074000e12440d1001d1010035440380c4039000d4110009c0c0c84010303041c24400b4a1060455542092018000b01e040210018040c19010301c80d0350740c418000118034101071400c41c280d5604640e600010064043c413410004841511a45024850001200801c1c4900d004a0034180040c0002e082c480c10a4806102034000b40300703218000800d030000c2202031004109074421060100d1146080d80058109403e00380d11140c0c1c6880010705000490030849061038122095590385001d0640c80c50b526a25440c160350701070084 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 990577625 1250 990576375 990576407
    0xb030c070311161d0c03011206020a03090204020d140c0405011b020414090708010c030221061305090a060f0c09120f0b18100b06030109150f030c18020a020c10 70
    0x1108011401d4138001d424079899401d4081c1c204c0e40d41d214801d140384184003c0c85a48038451b502003000b0009241a00504480c04507820002110551600402c0c02daa000c0a200c510712641d8414007103c4840c41840030b5082000d24513030310300b414200300029140313014003030030703148046001e01058045684682240701c009410301e81110440c140ba043c100d6a0380314034090a900c6500b032001c04002d01d4407134402d481c2244d2280011016800c00210903a2184102411041e0000351030082c0840f584043e00443c0c1c002c0002c2c0000740703540f140c5400c0820441305004014140941443d251904140e8400d00d076505480e800c040d405415941c91500d03559052440c80020b1804484004100c244102d600c00b00303001d5442e010035110249542c05c818800c84071100c0380e1175071111090006024030607031a03001c5030000302020a482e0000b41c90754201c4c032402060354811100e0038040f1100780f051220003e40d40b1803041083d40c05506003d0528000b07501c40d001119554042e014607a044444244140c510070000042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 990578875 1250 990577625 990577663
    0xd0e0109051e0f0f03070b091606021b040216060c0207080607120e0f070e0604060b0d1a09010e0a020304030e06030f09070b0708091e03070617010b030c070311 70
    0x5040348840c10351058074680129000740200c41e244141d01240c1d61100c2e00d6840007440c41d18407207560740b002c24003024285180b0b62140c0001144802c259800704000781022f60001c2240400302d0b83d8045400401d606541d01850061140c02c2440050074440040580d00c00c0c00410b5120a00b0001c920300303003480d0301c584001c0c86054140845182c00c5000a0000348030582c0602c002e0240711000c940e20034402504e104242e01804040011204c814001034000000900200e141aa071f4103420515401003110059040e07514601c10355114105820141421001c0d1112803096140c03101003030300d0804c010b12101000c0d4000000904040c40f80e03507814801d61009044580780d0800e503440000000d021580385000d481162400b081d1050500290780549501800c6940341452020502c040140600c141414034090940c03082042d507403e110520140c00140d031110540c0340d00040007030002a06074041002d28608105000b01d002c002000c9500303103905400d02c10008840d6501d414946044401e00d1858150 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 990580125 1250 990578875 990578893
    0x30f180114070c0906050d2004150f091404022202090a0b1308030f2506061502010b04140c091f02030c010e030307080103170d0c05090112110d0e010905 67
    0x20310b0f103101c5080c2c0d24a820700700041c1d51200e051060214003008060030541c0c44400c84480060005000811840040c20208508040020b01d05088615401400c1e020786408428810403030356104000780410411503000070b904140c0c0110786481f500050001c0d015500d10108401c0e8140d58040f290402e43c0985041c000683d0381034500100c0d0054031510488078802c540c00610303200300105944502500304081032402c0740b00d00c0d01490300c0c4d003a1840041080030101101c0b000c0f9025201e094010070a9180d160100700310680000c2c0ac441c40551141d2280d0701c1c04281000071f5907000380381340d03010101d420b1080c3d039a202c44001138501410791840300308c0d4401807086041d5099001c001340411101c03400007800f0b03030103202c5181500d9010880e50000040c0c0c034580104007081141c5600e8015140b441015850b01003807044140c150f6101c910340401003480015100314950f07000f1203108000c07800b154200511010340702d50503c0d1740300300d01003e16015120345500c040c1c01420344c0260045030303001013200c100703c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 990581375 1250 990580125 990580133
    0x6050306040c060806031506120f060a15060516060c020109151b03110d0b0d050303130c080a05070509100801021809010506040609090507050c150406050702030f18011407 75
    0x40c0780b41c01201c001400601c0030070028100003a00e11040c0700c1c980c0054000e583c466040c00043d0041d440d003d050b511400824407580c140600070940500a100d030b01084d4031121150103845510968001d20400a04200a11300b900c249130202041070740c000d00214055044000c101d001d09050040945171018400e05410700343c4959105a60200d1590100b6040070300441056003103e5000c010040d131300c42c0802c22144203600c3d44d4088a0002d00c0240b102e020401c041e00c886e841e40c1c1040315104d502d50020070600e4244590743d60f6002c002d040b041b0040000d1a40f6694080c0c5030525482510b004036924000304002e140780b81110340c060404500215110012908908541500d6110f414000c119142c008a4142001b03c219401d8440d40e0321007070900b61070300c100c1200400c0010108010071400b4001c9200451041c081c1c8444150021040b6500d810309090035022110054558403e41d40100803043c1e214180c04141e50b45c0601007e4195200c101580059951820024030780c0420100058507030104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 990582625 1250 990581375 990581393
    0x31518070815060c300309010504020f1f080601020c03010e010218041803050a2d020f070f0527091c0305100e250f0e041a0d060605030604 61
    0x38000c00309450141c2e42d03089050256074450103d0407075180e0050000180c055070b040046402030901040081c000e022800c19610365600241c8011400746d4545090209520301180010036122080315100800801240c800c0351481544600105210407000040d400340c1c02408109080b0501900920030b0030900d40046e070007944100c200c1080c1100c010f1a0f08000d0405109030003451640c02d075880c1c101410340d02d05680c40c2d04910a400200801048802101c1c0e940c0d400c041c1c020f003030141c0c03c41003149210001a00700001440c52600d035500400307040040400c52001e01c07048400075250801c001854200121030420890740c070300c14a401d030400f0f1040180b4001180c8074140d00041c030b43c0d404000301020032826144d06440b07017550510160300500040440740b5955402c030050011400220440b40784810b01107521001c0b20001c5005224003881684e0805c0000020690445041041c80940c9240200c2840c0c0708990303500411203821110304000e0290f00c084c000e820007c08440b01c0c1e01e864a810646 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 990583875 1250 990582625 990582631
    0x1d01090b0a032304170f0c03040f08010f090c060518030102130e07050a0807111603060f0e191202031e0301031a0f0c0c0c04060b0c010b03070b0315180708 68
    0x200c000e0401c000100a0f46600481c2c0034940c003a80d02c1e0b0500202c006150050b0308119405041d0a0041040d1088100104014401080e40b032040c6500c1c10303e4244103600715444221403c14460403e00307540000349244074a00b054402604180f40c0300c0300c041824401c0c18021036180750300b56100003103840d2800c21401c87d003000c844c40101c140b4499a900d8070201c1e40350040200e040041680440418401c5009218092400085104858040d0702e000c80c28011440c4540c425103866680741d107482007020090041c645006070140041c80c40000c00102058401c001141c00740c008520f00c405c10400700c0c401d00403100c49400000007103042c00c03824500309225510030310007258840e200440240c8400c50890180e4803a150f0708181c24161360760144035045c80e500010047c0c02901074040340d1001031340c0e5841010040c0c07201125107502c1e0480112030a00311000d841c00c1c10b02c01c0e405182c04201010803141181c1e8018803502a840341e0f6655007010031141700c10300754444000340079042040b0081b6441883d82d84 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 990585125 1250 990583875 990583901
    0x30807020a150921050d17010603060605090609060c03030118050f07020c0d080c0d030222120609051c050c151608100806012c0105011d01090b0a03 65
    0x10155440c1d030414840040e1102c0500815590101000441e2500300010a8070075a4103100c0240c1d5a20760381e10342030104101e00c00021609481403240d41ca44894022400b50100c0d08041089904201d0064258058141703214440c8038002590078190b12100161698598880101c03500c03540c4403510303c5109100b0030700240c801e07031a00000404070032000f03100c0c0e0301858183d0080c00120128505120b120003a409084d102e4050401c20340385607450400c89841c551900d81d5005860303030f0403000c43c0d01c841c48030280d004044e6035001400344080d0341812007010016500c07400015240c096483c0242c1840f0201443c1420b00030000701384058150482c00800110802da81501c0c0003012030072054807500313402e981015025801d04e2400c9543c9025a0344281c01c0040c40b5468414643d039003458600d8030030300360801600c3c008141d003610880c1003548450b816400b1403010882c411341c14000000c081e4a20400711010002e41c2d10180700031a40a555071001404001c040e1540d28200c6140107400303002d003000d28030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 990586375 1250 990585125 990585139
    0x3050712090302180402180109270b0c0d06030803152403070509030106050d0c0312050c100f02070203060103032105060d0305071a010e04030305090a17130f03080702 73
    0x2202948102841c00c15264000d0401003002107030b0200303c81d00c407002041240c0140040c86c001b240c46901c68001402005209000f0070007495108801590110010740c840d4066001060040000e450703942440d44540c000f4102c0380c60f020181c1005015014561010701240d000000f4001210007104e154940d045040d0780025024a081c1034901d142c0151004400002d01c0500105a8052180c00181403440d4006d00102e201502c810016113401e05400342240c003c40500020410050241e0904030203030a01e04206090180f44a0107680f280202d21480e03605556a02c02c1c14400c641f213034191100e160b0050129219984c4900d030182120420703810110780d0916000000141000c103000700c1e403050001524060495445603420ba03010303045010304807608108003050104207902c080302d280c020188100f40c0209070074641400307022254081d1105506400c450f51100224269110b1010540d0f109040d0540d039000c1414030102c001225008100301c1c61040000009100064000d001028001c07260f00f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 990587625 1250 990586375 990586403
    0x50f040302091e0c270a061b05060a050103060c05280504030b150301060906180207210507120e090f0c1606020913270203030d0c05071103071d180703030507 69
    0x2550400c291107501d50110901b17109021180c4a2030f405607410303405d0300c411403943d1804d54070242088001ca40d07200ba216515801042406907501440400c802c0c20300b03040345801800300d044aa054094490850328464206140f152a8811400c8030001c43e000390b50fa0301e40e03040c07103840102a902d850074050703c0303503080041c0490054400d100d03410440303100d0600050b146a2420121010f50403110307081e144540c4012000106c01d0f02442c00c050701d40699a202a070b10113441c035044a041d401650100700b00180d00100c07503082c0d101c0f0750041e5045110b62041041660781e56102d102a40b040c51010781c3c03040c0c100c4c0d00750803c204458014103034000301250303403940309a40c00d6524004c4940d601c4600300d900303103281c111006035091004002c140ca40098240ca1810318403000b0368061700c0824801d413002030070001e07688080c02054902110383c8041100640560b03072a020319a250703089103814108810316640c01052500503804041b0120f08140c2054440312a030b20304000c0c107240c200c000b0076186d0019605d44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 990588875 1250 990587625 990587677
    0x60f0b0102070608010b092101060f030c091103061903120e1305072f03040308030a0c140d0b1f03150f0302011b03030b0d06060501020d050f040302091e0c 68
    0xc40b8183c0c4c621b03824030303420104014100703d002d131a030380c0039440840810702c1c803000740010a00810015203514003550860380d245103082840b140e1560b2100201901d030411040305e140c0403031308403500008122180c61082a2001210240c02da071750740000c1042c0c07803220343c91a400d030300403208017114102151401d51005203014100c0c15284101c40c01c1000030303d0032628044c0701c030401c0c20a51110291603003410f100c0240786013041c40d43d44a50000e690300500403003000b075614060f010342c1c1e0951300303030349402402c94007800c91002e418061044280c0d00c20380c449940c8a5180c84580c2159603000d0140ba48174075141201c1c40c09001000b007604108a407c1c5048004100d846212140c0b008407a41079488000e00441c80d244038000c404201821810182c85840f81001c90307680180c2030304603d0007600c0001b41ca5140400192408903801d10600601000f8030003a50b802c4200401e4030222070f0180c1d6192841d0780d68401c5042080c240760000003055000341c0a0101021003000902909006455905401441400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 990590125 1250 990588875 990588887
    0x102010f06080628060803071103011a01050906090d060f0506010c08071b09050403090501021b1804020301020712050d0606050c0a03030b01030213080619050f150d060f0b01020706 79
    0x65418540c401c3c004030303110161401c0075180120fa1152000940b803199a9200103403000e075030041c51140d0020030800144000c4c800c160040c40c5044008110342181c034280b480031500810240381c10310002052240058642c541103e611010080c0740b04690801450b0000081c201e085940226a02d0100003540550080003050741e9240c024007107905248955030741180002c0c9110107100c0c41c004403034000078402824051640118800d8a980c505282030200091400d000620096121155150701036403545541c0c01e208204543d42000144507615800840d01a21030300701e00030a0362803501a1614241d0f4031001403c000340030f0354000e201040c0c3e1f941c400c071120700880d60010302c42d410104440c40001e0083d44101c4003048181405400d003004140b6080040569601c45030464101800700411402c1c0b4203800c240020f1152020072071406c02c640348480c0380c4001840c0c00162021810700c00035a59880d816002d03403903404402030055003008070f40788000c7c100b584074260242c41018000300745640619 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 990591375 1250 990590125 990590129
    0xa0c090b03150402040b1507020108070e061b0a020315090c041a06031803040906030c0b0406021e16090b01080f0405060a0903050c0a03030b0a0f0b0703030507030b0a0905060102010f06 81
    0x2001024204040300a0290b1440b010300100e0b40140d03100701d200034545800c1c503207141c2440000c2c0015103550312400058018000209450100982880000210b540341010f44007158030b9034180c284082c80c107101040c42c082414101950501c030b103c05e003d4030428061841407251488006aa026440c0d20007448103890707281c60590070510149045907d50706118000e0750744803000200012810342910b403601d00b5640203422950f45207441c5c00089c814030406a01c604002c21150503190303e400d240420013921031150000001d81901d05800141280c4004c01215100416a84010507031503903a00118004010361010103001c9241c030070020b0100c1d1098100750340b1594010000d001c1642d182d540004c020015801c080b028050b05000d1803160100411520440c10b20030b8030001101c6900e00204000c1102a50101c400110310410a000c04503e460503141441d50504022405448144055001d8000407000e55040101d1000000f00080c86802c0107014107000c0e00200070754003c08840406807001d40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 990592625 1250 990591375 990591379
    0x503120108030a140f090d050c0a032009040f06090305130f0302040b030a0201091703070813061e02120f090409050c100e03060c1e040e010806281508030c0a0c090b 72
    0x244000101c6003011347c8000200c85c412020746020a04000c0000c140c0c11071a00281d4034a00080d6000d0b61900e07000d000c46003080b0f003c54640e0705070315280c1d40340020480c020800030125620755000308101400348060794224540e03c030340544030f9605c030303068020300040c075110a134451400c107210103403141404514801d001e501079644900321400c10181d82c0c050111000c000d06984800c00240001c00c1c45480a050705200311008048400d20780a4001c20140d032038210703119524607082d542c146c081d0700021b00e0100b00030190b484c0c40d1201c03e00c4c03004400034001c0010310340d000350506201600300000450101101e200c00c58802c914660b810008a820588103038507a034040c2e204501088080154030064440b03d00c1420100088901103070a8841b0340e00554803000340500000010f2281200074000d003540181440c180c4c90002030301382c00050541c03154038100800d00c1e80c0d0b050712403c1504180c081201400010b8201c0303613180c800c80c12a0303985100140050346c504030191000706200c039250062248040c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 990593875 1250 990592625 990592627
    0x20a030207090c0516030918020702040606110a060510030b0711010c110d030506130207050d03111303020405090a0813060e041505100c050d031e091e0503120108030a140f 75
    0x251106442017000d0300541a014070142c480300190351903011200d401d015005050150f160000f5205000644046030803071800d100c2111850075034610005400d40c2c216801100204042d2101990301d01164a180c0000d031107001d2501c104510b90384c201d0307403407984508000b000b080a0841c11204a450044004240c4030f103410503001c41c401d952094000a4109c040140f14000c1c402d1807500b00f00403641311440c2110980c0080040e01a1542c0521440036620300480c005441d25004107003048061995000007442540d54001052080f0000c100b036510040e403001e011030741c5400038030300405082c1c1248038200000301e0111803c46a400d05000304641e400840c1c1e000070f203d03414902040700301d0200e14079420400c030000c140940414400c114100009005450004440c0098006107141c0264446898012030a085035000041c0c1c543b0802c407009085400048020b42d040e2804e14218440c0884c9900c608050304c0010039000408001480e0240749626942d016030030b0070300c9d1840786000340c040c10014010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 990595125 1250 990593875 990593887
    0x109050718030320031c0c020622080f0d0504050357031603032304080a020307021806101e0e12030d2c0a1502090a06020a030207090c05 60
    0x4001d80c41012103400c0c08040c0da0900100c07985044004454206d5424120340b90800700b9810b940501c4100d400120551600040070000c4240c005014001030b00104141c10010f91800340c1d20300c20003541d1540c242e0060600c00e03424981803040c0c0d60303041924804650f05101c480502030580100700c4140b0000718088000600b0320044150f20640307062002036140c002d5856100401c050300748010011541034049621380d401141c2002011551740c03040b40121140350300710041c00c0c0350703011a49581c0f05510a1400e652a024104103c0c258020f00d00004d400524009014108540000607a8410281075415044e41d80000c1c074101e030404c3e00000b044030070760640bc000441030703403040c0b01402582c079001d010a000301603116100c5146510a02950301c200c1d59890210174003401c05c1003043e0365224410496644040c8500789552a038107040340003801d803d14000703000d9951405030140c969202004145454803075891601035299401c00340c04800600601c8004194221544107800c0340d01c02607a41c09003080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 990596375 1250 990595125 990595157
    0x622150e040b01170a1b03060518070216080c0427060b06090a0305060901110f090603130203070f083703030f020d06031e03051614010501090507180303 67
    0x9180b84140c1002040c0811201c400403021225005d03403e501400203402c0400c4480d02c411508000d0244105800c081e0104415a01da280441c081000c24411880b241c940741c005916220601811407050101100c1c001517100d004140102c00c14801e44007845041910b4054040c141c4060100d5400c1c8409640d9a40100d012540b0102e0340380e82c050001440d100800c000135082c5145c60f070003107501d58409400c011300d0701d80a01035110000c005203101d0703040c0050195a58824081c1001d600d01681000c000a100c80b5643d0010f10501130300581a1810941c43e44030000141841d8000d680706841062038424500001c5220709480c2102d5180410580103840301d0403241c081c00000540070191154501040d5100910040c10b64452000000a10518502c0c002c614072007403640811050300e0428014011903000004c9804900c008041405c5544281c07030a078400c565070324606102c5602c2c0000116950319154881400740185490340c0c1ca2801512481c3c42c100d40c582d000041c00a4007010200f4445 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 990597625 1250 990596375 990596381
    0x3705091503250e0306240d02090a0b0d08041d240d020f03150712020c06010605090a0b0f0703080c0901020d0516051203160207080a17090622150e04 65
    0x702ca07071807424400711114140068a80742c4c0507141200b03c20100c0e0790025940c0d54010450b2010241551461820030711600050301c203410042100710039035120b00503030750142d030340e52648201036610100c081e07140d949405901011803034910f0f140412100400c0440e0741184243e02c7d460350401c10b58410010f0740c180e1010301c100f400d05410b0490300715041c000103040b581d4040c040310900c09071410f01c864442c82c04000080c1301c0300b01c10100903d07542c410040c00d00c0b48031020a220741035608034144169151030520103c0d8100d400b03035002009880010480300c8402d600307900140709043c00796903134003040c0e110204210164460312040d240075071b01c03128140b4038182c040c101529080d880090b00008041c0c2607150541801d00c04075415032030710f01c004104200002c181010200d040502c1c4001c004480c189200c0c6c1e5a5030041020282c9100e0a00c2d2511a43c403686c003044400511016213100e032548800305419010241040c0646042c02c1421401300c1c0040761f00903100911801940d914110f0410403040c8001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 990598875 1250 990597625 990597691
    0x503030f0d0f0f1b120b1305180615040c030615030903030b031204090f0b031e03040b04060e01090801180201050c0109080723010c053705091503 64
    0x40c01d0748502041010100c98803406036100c11010400c2414403190314001c1243c209103c0074014140740120854554950f4441424808545407000403030380c07a20350b16640113000b10b0309590722740c1c4188030401c8600312130105216507044080d1414803800035070160a4040d5511801002003aa1501c424524058030a0300013204a40c0203080000b420b40140d400b0a0800032078404070a04042c0001c0d0070084c008a52042102c541c0645400304120058200080e80b5540906203030202c21030b030800321039032a000500481c1c0082c0040034245070744560b1164050001e041d03900166003c600c41442c00154601c0c10b01420051750076141018007156038070360054450fa0051030003c0b0702d80d980e030702d2170500145022004151441c0140784111906200075400d4007800c0041c02d030313411240d0512070505980e98000c800d0364010322032619540c2104070200130f107480c460b94002c00c0260080e070111100f181550041c00405c0300520903102c0e00310084040e54800040d100079030780d071203c0c00f00080600415020150b03240c16 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 990600125 1250 990598875 990598901
    0x8130b07120c0e0f060c06010326040f060f020f1f0902040501080606090901020a020c0f0609150c0d02070803091207230f01020d08070e030c0d0c06090503030f0d 71
    0x112801c88508000441e144204080d012907204002030030689811010014640300465203186412000a0465154041032000400681107000310440d07406802d02c02206c1020001440d036110fa9542400110410345441050040382060a00c0005e05101040591158032440000c0c0402c107120703411403081c3e416910b00c2090841d903a54503000181d80c1c1d4011a0f000741f61080c01001c81c1d04001c010005000800380c01d000b91a8810000348a180342c0203d002d03e5601e4040365001001003c81011407018031070030f21000da01111011228a0450440700a004122250400c031080300440300d0040e82c0c0d60686c1d0003800c8160303100340800c0d207003460084050407880314110141d43c13165548105241c501c401808240c407015441c4c01c15280f4605020341074419032b10007480100340421081c00e02411007c405400d00701080104071031051951810403480180700d002608076502c143e1a400c20b6a4248064003440002440c1c01100003500d140000684a8446c1d001d0a043d240065245012000300002d2221030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 990601375 1250 990600125 990600137
    0x9072702030f0711030a090905040812040c3002060a0c052a1c02090619080307050c040e19060f0e0c040b030706200a0501290108130b07 60
    0x6600912140055805089000480c9640342080c40000d05501c1001800c481030f50b005100345880c1940c400d8410080310b203007010029450b103035400e01402c02c2c450024030443d815400700a000c100000e0340550402c440f64440707010450076202d4a20141085901d191203400c0b002d01c00208090318080d0b0040545d0480b5051015084183d55034560818100d003c820001804110516041c3c00002c0c801884100741140c40f01c00c88907036102c2c10400380800d6400640580740e903d0006025484e80d1001e54016080000a90300b8140c2c0d521500d035070781c0d0208004940c07d0054880d15413850806010340907070405500c014002002d0160008014000c40c1c0cad134152000342d240c3c403409074502c80901c5840d2110030340d80007820b01c803001e0740180025213401070392841c0070303601c020010007030107601002011214102140c1007001c2010702274064580110a003018255500e4940180760050000012a90750140c000c14054420110001500d10140c22240117015180036041000001d4034609510341c00940d6083c80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 990602625 1250 990601375 990601439
    0x162d03120e012409020708030703021303080418060e09060412052106040e06010b0912010603060c11060f01150807031407120b060738040c0911030907 66
    0x1075829104481201a403003504107000b00710010100940e003020300901081545448200d40e10203800b884004c186004041c0d002c5200d07036100000f98821001181c004540d540c89548500004086010070b04166119034179110001820009100d000d074403c08411019001c183d545413600b000c400312000e82c000811100704510300580c0850000f00070301401c0001000c11510303100e0144800c9424507202d081c40d0b9071002004115600b20042100e95400003a41c0c2850000b40303440d5002d0141c00b8580005110038244500c400100c0e50040c820880441c0241c05c81c0e505440c0e111340b80014500c01e005a151100100f12020345a50044c040e90340c02910324603000540c050310041800800000b0780ba140d00042d2001d2013044c112107070b801411401d5800312141468665995a00036207e402c010810300d0080500031841030151040107016076139248203c1c41d840b1032505181c00c5100078420300982031401d03c0d2507821444026400d080c0d83c880d0408000a201141c20941125503c16680728a010040704403105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 990603875 1250 990602625 990602651
    0x1e01090803040e0f0708090604021005040e0a020702041803080a110c031209070f140904060b121005010f03020d060f060503030c030702030d050319050c0708162d0312 73
    0x2080181a40c41490070f2904060005540642010740042c00700704801c1c00303201c95050045400c40c0c0080d41142d0300075008040f403209441c24004c6038800c2850500c1d10381004508034a64008182070743c800c071004c024545400c08206501c46d0a080003800050045000408508441d800a254030225884160600b294001c0d081e02c0c544c04500418120b5890405101801000304180000b50214000d143c406604050080810981a00103d44102c8130007012170240101944002060013000d02501d0b015000c01c0ca60b0b680d04d105a40713030201050b2402c0000140c00103001070700c1d02030f680c2c014040f6440d50703403a880b124007402500e4503002d0450340da030b130703000401d540e0410003401c01d46400c602550311241d50f40105810300141c07041d104240b140400c10043d422110810721a2500da64800014a5841e982ea15070502d020310301d801040d51000150b04c0c2e0143c0c00900c44002102d100300311880705070310111208010591146058644041038510b1a00024052030800b6065015060002172079208890 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 990605125 1250 990603875 990603877
    0xa0203120412030e07060212030406061a0a18050d0f0311061e06030d2705100932040207020102250501140c100b030307170309010b0f1e01090803 64
    0xc04442144140c00c01c6042e080d018000c484815140ea0040c1240c140392140183d112118140c222082880c0040000c2c1000103d80c80b60b4090820980c0b02c081200d102d003084095070380100481c8c40442d07107030301c2c0744a00c0301000b80942081e50800303000c181510304160b6500d000324000000840500403030182e01075000c402001414840c002c1c2d290307618038000020300620919400500f80e0307030081ccc000300d80e1b0031a401c2e04101000043c4144421000303096900d00d41d181098047c40e040140d0140ba0460b646d07400795031060b4298156102d007580940140b1441200c51241011119030441da542404c800341c0c02c034a03295000d40031050040c01980c0040840b400c10f1800c000007060541c0401001001c1441556070103c45c5951070341c03c01c1e030f445140644101d034056441d000c2c03200380744400361607542620a40d01d0a109544181d644210400b24200090b054541241c1044032419490362030019130001c0c030307c1d040c5411a25800042e01c94021030111141c600c082513083d203111810303c80c04140000303251400304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 990606375 1250 990605125 990605131
    0xe061c022419020c040b06040311091305030c060f16021e0705060c030c061b040e130b09010506040507260603010213080d030b06091c140d03060311010203070312020a020312 76
    0x640540751398981e9800b0441203a01640c42c40c2c1c00b819090000f400000d141e00041150340004a0b0380c0d40301c6945803020f410800c501298000c245000105100481450000b1000c0c0034a00200000a0300e44e00d0f4460b44d500103c2c0b1640100050b07100c00c04003100204442c1e0180141c5941d2410740300392645403404900d89134424001c60039a03274000201c0821801c4288211030b003106003510721001d111180c011440240c0142d0240700b0500b107a8001081144406202c20351000c4d9006018501c1403804c0040319000304021100c050140d401c1078001400144900c0b200c04c140f0b41c4410707a0f00316003040c00c0000d0342d0701003000f404160190360811141118069841c1140000c00000c0000e05084002c44e500406030761840c042940540c4c410700907a50955569034110522420b5240d0020480c2d0b00c5044c4000c00701c0c42c2d0101240b180c011700d0456000c41d941a040380056a001c0c40140c0d0590761341c8001240c1d0f911400c0800340c00114174000ca61352894554000b42801000c03441240e04000c0482034020100c8415 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 990607625 1250 990606375 990606377
    0xb19090503030415060b0a05092403060a080106052d0d05030d0b090606090609180117070b0a050301030321050a02090405100f090c11070e061c022419 66
    0x3000304030801c40344004403022007400b0401070107041d00c0c5c03900d1806c590180282507410b001e00481c11000985035412054001440441903089040d0603c120100a6100341c812500070702c990217010400c0d410501411007100c801420320045904500200c21342603041504075080350740140704402c0181e50741081d0046c3c617030003000556541c003a02900fa0085a56440d44140518a40c00c200302107541c8e50010b1342c3e00c541c000d0b1021503407030312201c000a06100d02030380d4140d80c26000b040081002044a00003500350207410046400094a80d80c80341c0345030084805080c000f41f1304100510020707214144d100580090305510007607102d0991128019a40119085540303654042880c1115103000c0c028a40c0042d03d221180c1c0e41d4500704896080c0748400b60150201c0c2e503844041d44c0c0c140f14403410b044c281c40003180c0d00b40c807181c41d00c030103510184400544100b4840d0001c0c0b0a2851800031510074034180300e0f4024840702c610305114480c1340300340d0381c040c17003034841114140000710081000c185806510111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 990608875 1250 990607625 990607627
    0x10110d030e0703080a030e0615300105040c06090509012603161a16120c1202272b021201020703030c12020a020303011403070503070902040e0c070308040b19090503 72
    0x75030000c1528007003008000d40592601ca00061480351215500c00b880c1d03584480c04001504031a0180104200401d40c00e6003956207332204000034407020002d03090035103000c0c0d070b544e0030000d070b4400811402c140d0a004030b079005101c011516990a5040d500b420440c442030054034107019404041c50001c1c0004002580c0407800c200342d501282c07144442e80b40d407085486e001030b080c1320070080703004120b01030940341020030139907a948031003001d4040c000e000018030a0150556880c94101000f1511418a40700b020307030000840c200103207900c1c2a00a40f07124000c12008042e9007101054047e0300c03000455002e0317801005a00242d405140280020402c80703010740c6000c107000e94442c0c0000d15001370500500c070614070500605203074540c0801240d0441e00c104034214505071681000038245109a800360b541882055000240c102d1b10f50050000c550100c0c0031024180d0380c2c039484860502c5008802070000d07240400007000100018003807034000008900310b03130b0510628100001144c66080d42039a803540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 990610125 1250 990608875 990608891
    0x1508121620101403130303061203020f060f0403050a1b06020f070b0c0c0d030b2106010603240e0411060f0c0c0a0828060501090b10110d030e0703080a03 67
    0x1000345515540b841503140c51910700c2d01500424025000190078189000d0103200c0c2401814460f41000b0b020380007402038080c281a061601079031f2040c01c010340d00704d580260300001c0c0c034440846584911594064075402e14203010880300711a80a04401e10100301007102c0884008111a031000d0201d00b0b01c0c0782c080a540340e4190803c04107203100207020f1440d00c5002c01c00490708910201c0e210300980780e00d04000ca9071405c030b1000a050035401855000c0e03017035190190002c04260001e900d174100c61283d20f0410200b50810300c1c8a4601403c3c50b4950003019517004100700c0351044030091544240590010710038412180c0009041d80e00c14007681900d0400490450b08524003403100318004001242c9028441d41b41150301074841e401342069940003843c44801e4400e0488030107840c02c40030b41c811030400c840d68580c4080300041101400f114061103080000d00030103030240c0280c01820703400000030305d402410981c04800ac0c1c1855420030300c85000740400040080c4078200a042c0c101d00e55140859490 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 990611375 1250 990610125 990610129
    0x14011e08011104170115121e06020304020a080a0215030901020d0e0105070e0a150c140303041a060915040f110d0606110610050910030f030f031508121620 68
    0x82020384141c13075540d02d00b204081d411a0720b500317150100c8401e17200849002e016030030b244003120392604140c403040140307800300c070304204031680258403940c03003150441346058440301034540c1c8681c00c1e0b5000b0740201441c9001d00c481408000a036521003440740c0050300c0c1c5420a00c1c00410340f08503c0d00d21400da9110401e2090007500658103d00da10350a4410101c01494480b285030915071510310030041c4194040c0c001c080c8110105558488036504045907541d0038140380030040003d1002d081ca0301c1c06649e0010800d41c0c5014290710340a03034909002c20080c581000200001044980303941030115544401e8640c1c8006210007034148800012000164149015005040d810440d401000301da0004c0c000c0100c10020a4510030581c3e6040e1601d58a55440481c20206c80d169908041c1c60522042501c1080640c806403825400c4140d03903003441021402c442c0a00c6010302070150407000c0d089200ca0001d07201c0e466000d00307942d583d240d8040e6151001a194184008a001c2c4105180c1026501c410914 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 990612625 1250 990611375 990611399
    0x1703120402120d1d0f060403080f0412051f140604051f2d050307031b090501030506071107141201020d021314102109020303041e0914011e08011104 65
    0x4081e9440828170707022400180d810300c11404020036000c400b0a14080d0001d0f02410355000c1c210a803008100b10409060141e96181810002e2220580000140402d40258010051546500751080c05244c68540400015140040070407105a0644c500c0d0300c24210001c550000520b6614000c150f0f2001c1c0c05a07070700310030a64843d1520380c243c0008081103651000034100382100d801c403608224061801c008526111404e50214030010705080000c802e00c40301080d614000c0101c0d0701c401c040b05001340a440e488040502c43c00742160700031404401c4505041c21500740002042c400140743c50702442409003242c004e40007071194030340c060f101800007554082c4609003080082300c4c0c034040701540c05030092a108091101e5211201c48c400001c035480010742000c460701c5e03801010703262034548a403110040b8004410040c550040002000030b1102c80c54410f40034604440d0010b458160f00b440c0441e43d81c40b44810710a540100e14003000215418280304210400c12030215282e0740d140380500903285 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 990613875 1250 990612625 990612677
    0x21302130503031e030703060302032b08091e0a060501240201021c0c053c0f04030201140c0f07030311060f0a150806040b01030b011703120402120d 65
    0x343e01c02c101110302038620341c035002248040c20340d29654940d2800340840152800d03610003074061266400120b07100072003200310842e0351600045070707003998443c010440340d0700c03001ea440d942c0c0b40c2c114400c100c00840320020172440aa90350003c958a008086e5150070443d1801d9004500400c9101300c0350055100c1480080450f64040c03009505043d01c00000300b04050820051405443e43d82c000b6904250213a421354940c4015011107169000081d800d0508402c1860616059684c020481030400da09980503940e10700da1049039581010b09550054602201013460341514200030700c91750034038401c02c025035010000c9540280030401d2035442d000c0d00e4280420101c120f150800e200300101200d1426500d54083c0c000040459282c0c800d0740c980b0b400b020340d90800740e45800b61a04200a021440c4010b5040300d116140c0d07540c050303a07034405409904ca900c1440780c501d034104000ca1142e0408641c0d885800a00040c041c004000e14050014600713100c107849903010035500162401c00d00c03c0304401d02c1d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 990615125 1250 990613875 990613879
    0x30f060e0606220c09050d0302060f240d170705010b010f0e010e0112020c01020d06170c0a060c111c02030c010816121b0203040906060c030c020d020d0213021305 71
    0x2001c225020742120400d01000c0d65a0450f41c1d60b0402918101d1007610a6001004040c01c10720b0303c00d40301c0c10004c1d11680200c03411324554450701b000c5581c895001c1c0042c940d5903001c4072440c0d030710f51720201000403050410a0a135039170003c60500f80b0901d00ca541c0100f4a0310712407070000070b081d244000054141c01ca08011841404500b280728000760742c1006c007060400400f440e2030200c06206240b5103000303008007031200020f9031010552400180059000b80107071283c00d0980780c0036000c0260690f07031341d5025030307a003036000b1f410718104100381d80c0111000000d82d44240815807105c07a05d40081102c80c249000d5917090406003c00c690258101408000c5000d0f0083c03804007040d00d044001e103a20701c50500401800c01c940c181529448940030ba1202c040e100e5105031807001188001c00003507903078105025980c0414170b8000006a61800340104001d600d6240c2c5075016800019002c009180d0300c540405e07a00401082e51a80069444451891031405548401600c580c051140c1d40d44049450704094 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 990616375 1250 990615125 990615139
    0xb090a021f09090218040e0115060f08090f07060f0504030b1e090c06090f120a0c06022a061c05010b03010812070f060b03120c0102040303030506220203060604030f060e0606 76
    0x1c075580000c0c41e07400c440c03445e058a000c10f01c080e84c0d8403404d006000d406a90710103403481c4100030802651140c01080300c2c0721141d54210702504d0f4000807a0700c48200b0060881c0540c0425400c11016000c0c3c2c6140c0e07459055402c000e8100356480c1c440301c1b04818111110305011205c8089002c0010705510516000201000101011000100400c5a5108400d1090b108a403c01c0e400525540d511f08892405140101650000b00740c5140c5940144034a000c0e45015014003081d4142c14410158480701d242c0c8107100300198040840d00344602603100782040031018041403440d501c140058000e036030081c080c2d180f20355980e41c540705409051a4100c00750501c160010040000850900411251070300e420000024040e6a0200080d1400d402b40c444c0802c50b1101046904043c103066015204883c06601c00b44402d03691501002050300c50a035407804407501041c01010000030940c0550f82c4a84040d00e214078140e00c0c1d0316800d010102c1e4903411100d264a440811450403c00e0286503009441a01c1130 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 990617625 1250 990616375 990616387
    0x320030703050904051503070b092b02091e0609040c091d0705030703020a0e10150519090b070b04051009060603060b240901050d110d1d03070b090a021f090902 70
    0x47d071600002c0c8270701d400b40720001c1542c4400381e44084200c00411200704025903074403040078051404000390ba03020791013807411000144d1880200c800840c0700c01581c0c10640c04a60340c0d00200315402c0e801a2041c0d85039a003c0b503000c9201c5640e0b10031307c1404102c5509c5001900c0241c08844d02c0e205154001c10b00a811a09082005880b0700e60310900361111a1440d14080d5600c4112007482c6003039511000e40c03952002c0405290740e030400300400307201901d40e07030000021103030350401c0d40c004506201d010780c052401c0011101003054051041e40103071050040d038440d424810014401e442046405507041c4c0da40300c2c01041080b05600c50484204000d0b2222901008112031342c480c1214840900030070300c580040d004140d40c5c400c008880c0022401d110401103503d9100f0303003081310340240e010084028908261000709017202c5002d801c1010811000314900070030f0743c0e24070110f410b0203010a0b80c548500a40080103a42d001d03070424100545084003042c00442402c010081810350f88650941032040120f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 990618875 1250 990617625 990617629
    0x50117060108070f1a07020316090501210f140115090f0501050609130b0a120605060409080a12090b071e0801080a02090c0714010203100504110703200307030509040515 74
    0x103500704445c00660032002110303a28846455610841c10002e42c1402243d6000a09004845011083e07400c448002c1090f41c0e01c070320000e5410400348440c1d4200da00c80b40707002c0000070b082e0744c03003100503911505070303400c400030340c8504907081d1200201407024007141040288020301184c40b91001580f83c0b208144400e500d01000714080b071080851703080c0070307030b002418144840320240c10541c03c102001c0c00201411350390b8500003140030131b01c100441b50300e800c080100303400d072816000304103043c3d821041c00d0303141580580b41a1040d500300001e9030301040e03c2da9070300c00c041003003445524401c4120751500c16100341c004a0101100030f0b0f80302507100740120300c401442000c00c002003000900380c1c1135072a0340c0e881d05c1d04802e0440d03502134030030020070484000390b0040590b00190003039401541c4000c1100011074a039010070095940c101c51219a41c0c0050080b000428421710f01c803070700270840c0c4400e1035991110703000450465111000590102c0d0707000500002e6030400b40701d41544502c280e4002c410500759500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 990620125 1250 990618875 990618899
    0x604020907300b011103030f061908010603051c0f05071b05061c05010909110405070e0d060603020901151e110f0105090d0c020d0303021c05011706010807 68
    0x250701d0801c001c19442051004098041c000038489400300060810031055100e0040d0a00b4800c8a0005090280c0c020b03c1401c00804d4034040c00f46c840000b407490b5506002d03c500034902c03050480145441c0c880005d0002c03003e1080f04055409100613010940d90300503000030b4481640c1c04c001c1040301c060358103020241d000040d00c1e001d50780007250a0001d0b5103c4060305c0000c4180d0005648510009010440140b413900d41c0e200e88000020140060782e41e4014143c211380b42ca55003c3c02008440c041d5000340d161640c040c2c1d501c00b100c0d061120500310030f900403540e402140c00c0103c800c0b42c0c0c1c90301c050055203001d241081c014011446102d0f20140f184800506008880c1d030360004100034044d20b140401e0054443c880000110011596800e15045401d4045c100c182c52022250040949829001d4810040d50380d01d50b0b0040c01608080c11140c0e402c40c000e50204903440d8600c4807144400003102d0850180500812541e12449079650313072100041d0038050180d003c0b409541c0104c5c2c00f000f50781e038401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 990621375 1250 990620125 990620131
    0x102400e010e0702010b04061d07020f0322031a0a0e0c062a030c030403150c050418090c1202031506010219110303130f06021504060906020d1e0e06040209 68
    0x8007842c15241c803141d005070301500300314220a600600b01003011070090681c10030380f900502d54044036003554441c544160f8079010351030907040329030300104550341c400c00c5145000c0c01c8800c1926100e481c3c2c9907803922104000c441003020003044258201c00c0c1b01c41da50807401241c0071140340d44040d00f15121410300207802c501c40c21001c14003c1c6441d40d40d004034203400c21480d200c049011400d49654410080d8215101c0d4410301040340e8a00703100d4619401c00800f4450700e6610801e60319424a00350901d1003c116200d19000c022080315220038019000410740561100140100b80c40156800c2c514410142000b080d40c8000c0c0000180008001072a0303400500d031428044240c172410240030b040e0800508008105111a41520002442c02c5240c1c84618030141210050000700ea440c6848050480e200d401000141c0c0711440000007280c041025948141c0060340b240c0b10061134022141d299205540c01004040748400080b82c0b903908100150040c18000040c0d42c1c041d00e401c1c60603500107900c1041c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 990622625 1250 990621375 990621389
    0x19060e030d02060f1302030c1201051f03082d0f070204050106020a1104020912060f01090e06040b0c2a01050402150c0601031412030103050f1006060e010f020102400e01 74
    0x1205030170342591414046030703403d51000b5003280442c6280e003d2690181000743c413000681000782448e24403000440b070b034200a40c3c1d44030702d00c41e16040141901035004079014001c1140b200c8618101d0070b00381c0400d001481c142484e04140340d107a0003980108403c40314140e00050640d002840202e00090550103404c8480302c00306d0703005132120440340c0860b1a00000003440e11240c4288418005a5030110008a0484004150600190031034603841500d41409940080442925402094400503604007400c000d4180c5070308000c0320400031400315601c005950215816954500600056051809074403d00106031800d842c0b801c0001c01e0320700da5071001440003078507050301d095809480e6001071007204244404802c003603899503120b0800c03a49449a1206040c504d208980708800042c101e80581d41c200c0c0d0858494003c02c62036800155040ca03140780d16402155420081c032503480d09030072180c41c8403415018000d1488041041d1201402d01c424091184d482400441044401e01403040c0714152009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 990623875 1250 990622625 990622651
    0xf0906030218330910050108180f01020a030e100c1b030c080304030f0306060302030903070215090603010f080106080d050414211005011d1f0801060b07050d2a0219060e030d02060f 79
    0x80c2701d4100034250710803040c1035000140405a499054100c2c0510003440700c2030325201350508904a0440d42d416001d50085038410024000c82d0a42019204a45001e8241503054003481e594074501d5910450303084001c12039800032071711242d44c1442070a0107441c10b400d0441c914103000300440c0c1e0700d000d240d078004e00c20400b0f840d80309400f148074002e4641d00138000c0d00064495031203a140d0300448081e401290b82c00d44c40c20b00c00180703140c0005402460b61405444803860303d0f06000021615444513220701c3d400ca450604050a90740440b1603110740100c0b9080030f0141e54044032a9001590410392011041104000d01d0981021500f201540c100c00c11800c401e100710340721800d940c003200840d07200e9852540f8003100081c48000f10380c024021240f00d0303002d0b0b40f003100c400c0b04250340311058401003192002139030800c45200c0600c4801e05060a000400c54030400b19641004040c071620b5400102c0014000c0007a2110350400b0010074210420302e00142016141041c800722825000908840d10030315 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 990625125 1250 990623875 990623911
    0x507030e180c0d06080a1415070c200d030509030d050702100e011b08030601031409280c030c0510080103050c06030705040302190f0906030218330910050108 69
    0x41c03550104c00100010010b403055050142816500c0c544a07400c1041c01d4090f05a181300845011b18034917104500a441e0091841008e445e4103500f40136656000720308010388880301d94140d9500d406990380707d03c03a40e5980c0d41c59506909242c00c19402820010a20030305121400050741c9090220301d1b05e0419180c483c1250065400490b180c80007070809001c0022096461428400301d08011880b8110a803014051500c01850b94032403480b040320030071010740102152000282900c0c1902c1c1e11540000c1780703c00040c1207602c45869000f03050340112414903d680081055040a4602c08c40c218450f080c854180e40c9540c42e020f840745a5400064400c0304000000342c0d10f680104141c401440d0007a00001d5603600d800450000600c0602642d11091b41e8507038000340407640c600444058a81c0035001c0070f0010405545000212406400400c0700202d294aa6000310b11401c1d074150419107040344aa6036a18400134400c0030f82000e000309402c619000f90034840c590b0488056074000030541c1100000710 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 990626375 1250 990625125 990625147
    0x9030212030703180c1a07020f1e040e060f15010f0c0507090204081605121b06190c060507030902100503131202010e0f03040e01031401020d0501060507030e180c 71
    0x6801040d0790f544c42c441070100074400c00000c40c0c010781e459011031100044251b604401c41d0300540130000d40c401e4000303011024a05080016070740d00341c0128801c2001c8150000020103460402a0a103035540c0b0020410050b0002c501495030030660001c02c0320f03010304044000074245100e604412042c0543e582c0345604200e001c0000790004c001000d001c54440f40c690750115100c00b0703a03195084105d440000d001c560751811100d002070807210341c0000c0402c2c0b000c64006500c0c02000c9400541c1c0500300348a0640100002d02503c0c81107901607541c0312160700c003480c196003140c0d806420038007010b00d014145001a19000e0510301418041d050081d00e81c2d0701c0d942012012071440000400e1110210441844107405401034061b1047c02c605851410305660314184d52409140b280480e01807820004001240d6034424600d5451000c0b40058900701e0400c0000301910300a80c803c49c00940000741c035a05160b407103801e0301121034003180c1507a02140c10400d0655811009401c2c40c1410800040e24900d071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 990627625 1250 990626375 990626381
    0xe0a0b2503050c030d060627141201022b231305010c0819091a0405070305072c130605061c051507050c0d03091415150409030212030703 60
    0x40055403080340d5517100000c1030140039040d18400c44006c6415860010304c3c0d210f2050882c0120b035403088560400c585041034000c2280400107041d40c028440e40310f08052444203000601005007000c40819441c42242104030b182c040c4603042c0f09900b864008800c00009010324100020003c403908050580c44101e00071180211180740103100f58a4007006004c0b40d9000592188125041190582c9900d00300307240005a820310718004000c50310040341c4840c0728480c5c4903060341150080088800458507039035110301c0c003400c43c1c12864100c1c400c141d003418000c1070843e4542405000024074481802d110201c141c402e030000200070f10250f100c0b000500c2d107854070030000040d1021550860035550072814181c0c2c0710905100d202c658072060200140c0b1880c012404c44406020b80e074020003900380c6125045004250541c0d048070540c18440040d403e404041201840c010300050095940d820a1070382341360075846140160f03001d035040c0755550004c66004280140542e00c0c1e44072060340c9507210a011002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 990628875 1250 990627625 990627637
    0x1c051309020c0c0a120b160c080403050304180c0203030609190c0908060a02130608060d060f0b0111011e0207020a05101d031b0103090c05040501060e0a0b250305 71
    0x800c501c085111140700c2c50004604112140030b4440c12866915812034540c80c0c01c401c2c101800d0558008042030390001e61a0302070140c00403601d030074802d451103550f841070164070580c81914541e001080600c0b070700c440c10500009201c160201001000c90482d0081e44a00000705644d00c03441c0703030800140001601303054128040107545010001701d00d000c0405030031a282401841814821200022425500c81c0b0841d4040f040c0c900720850300b01c1c901181110b00010080c4006d40200364400a0400501d480c0070b4038044c0c550a50011410300964000100f0702c580d600742c16078043e0b0518008101c0c030107444041c80e5107803078458005603641d8034600200b035901c40310760320848e00010070040b40394180358412900a000360307034450b90090566802003015501c80803110045030300820b0500e20700d038542c0680e0001010511030b003c0040e0a07a0f0360400201183c07002d038002c80204012880c400039034940503128030b010303016002042d41440e8000311403409140c00e01d101c02c02944405e00d242003e1501440648403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 990630125 1250 990628875 990628889
    0x30513060f06030302011d0307080f1201230a060806060f070f030201050f0a090804060305190911280909051011181206071b02090f070e031c0513 64
    0x807a101c0400c24600c01400144410380042d46002c100121600d02ca4650480c402a004011404e20b50f150326a0f95182e800100f8403071b10078004100540f01c10020100700c5008060308038800c80c4625003092419a0031020f00c2d03400f849880410402d11203103400901190b0802010b46d6080e031078210150095485128a41020746112140c0310b05400301a030540100b4881c401c204c1d000821511011000c1041d40e148000050100c4001c2c4402e0052510992050b588505141507071840c0f8444080b07000d003180d2401b4400e81c0d114584052a00f80c42c240702c5421000c5040c0d01d9030440768404824031341d8150760f04500134006d045446080d00418000100440b10290080c11410405941c1c0d5050a2070545c0c40100360b070380354210782400c0c603040c0d01d010050407440b42503810240005a40340d000441d240b00c810a06030098011940608000d620b400aa01303103d0400b00317000242e50b08210f10054101c2c100202e09621035402880940090144840411100ca0b100d0800b07940b03407200c0c8855400601c5854205007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 990631375 1250 990630125 990630131
    0x1f03060603050303151e090604020405130c27180207050f012c030909040203071206020d0b03010510060f0e041a040b04060f17070509040302070303020d08060a0603051306 75
    0x4030074042c1c040000d40c051146142c482109103500d00c01c1c0108000b420505d410801c140400070810703420070304501c07a8031801c000c00041c82c094848d40001d112010050386a1515680d89583c1d481407a0840c00300303078601c1d10000c1d6082400c081c2c10300701e02107005c6901441c1c205855240d122241d040090b015513030041d9014003669132011004241f18001c1c2007068205040400380d07241c1900300822483c0d044004000324000e1440c10f5603036018019003841c090012a0940700e600000140d022646403920150346c40b40c00c2c050380d20006104414241c034415510544a039150000384a802480541c4220441d00319041a00302d03030011134416502c0011500319960403d040040f6482203d0040559185425040f2820007411240c103040c0800c4072241c0c02813030780003200c048050184100683c00c5d03989450408003160040b540390004aa0031210903101107015a120b80001e008068050008000070042032418461502d01000003e8006030503125003024140c1d82c0d030100c3c003564640b00c05180c03103a4000d103042c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 990632625 1250 990631375 990631379
    0x60d060b040f0c270f050415080d05181912050118080405030d361a030f01090203040519030e090c0a20030909070c1e0c06020102070b1f030606 63
    0x2800c00b244c030000001e0700030200032681c410400021003550036210414164480541410148401022902005042e66949035000a40c00104004604481d0300c0d41e903660340c60350b02c000283c06046030244001c600c2040081c3d00c48242c0b0340d107000b1440464050744a0307a91080b4140c04d00900400308545004110000c0409080c03d011100e4010412180d007502108c01c2c950a944040f922010411640c60800c0c2c142189468000c600803030307000c0c1054991848648140ea1001c1203072011a10346800701c0f01d02c0d404010862078001c6a1101801003000308030562841c54560b42d8075854200744e50394121070030b03403001c09102418442c500c0c001c8001170107064100d09003031100808a568000111810008038200c0c1000c2200f00c1da18007030303811541c02034029820647d8002c200400403034024060400c00041c00c0440c400700da41841d82407200303681d410400c90701011500704080340c101140c0106080d68010050b49001640440c1c0c007a501072a207600007a0b184152584841d030203c0c540e400501480d003842c0340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 990633875 1250 990632625 990632627
    0x30c020a0e070918090308010b0d060b03010e1b030103081e0f0c0c0f010c020306040b0702030903190b010509130204051008030c010203010807060f080c0a09090f02071a060d060b040f0c 81
    0x703040c040c2e81c4e804004814262a5294140a071244501c0080008680400410148841d039014120150304108040b41540d02d58003e8442504240c0c80750b10b082d4070240038003803090f00a0000c81d82400d140c1e50340914660440d1a02031162140c00c00240080b607181c070042c569561480251164031208031422640e509aa580722550341e43d0200d05d0b24445c14040a21220300c1d80074a80030102a0b0780035002d000c0f288d0f29030f120038602c86401440d8000b5404108540740e80e2f5641807041400f500507048081e1030107642410710003d1300134140c01c040c1c000c2207940103103d00b015010b08100c0c0c20960499002c0341c55030364400c83c1d804405943d030111100d8400414056007445041d0007941c140d40c5400101c07a942690380c1e0084540e4404070b2070030004034030001d010a131260714220041c41601c99600303140409a694144010880d00c45210400100350b0210300075042062205008002000d43c41014007a07003010000243d41d0400c0f00701c010a1183e40b440c4207091601e95402000e80d0f600400300400004581e804 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 990635125 1250 990633875 990633887
    0x602010b010e101215030c030b0f01060206071d0d02150405150906030402120a0b0703020a120506010207090905240612030c0607201e0c0418030c020a0e07 68
    0x30a80c0d010500e6405084080d0074202d0019116501e02c2c1e4070700c0c08128404a2401c014103a00080540f9401181004008944080d4040d801144a00d41092203850040d110702403092041e0002c00843d044201071000003075110b81a81c2443c2c0107a01c00c161a4861000010612500f851009421906000c035120750161110003802c111b5100b070359621a109080c0c8514403140c422000c050341e21002c28004035015090210b002c900290b00e900840d00c1000554a0301003800c50103d462f600029000240303110360342e6000c60000110080c11005002d2428241e0000c1e40300d644c1402200b801c295074001c00010700c40100800b044060140c0040ba000745070350486a405440201c0341c0741c0c00781a9182242c00f03000c0700001120441242140036100d180c035000011224400b041203400420110900707240a6414240002a011520440201d408043c0041420709014983e103500d846545041c8c0728000c101032042c00c00290355030601e00001302c0c112510000d03490308982e800086a41d5803103000c111010390826 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 990636375 1250 990635125 990635141
    0x1a09031014011d0402030a08030408040e0103060f0e01151e0e090a03090510083d0510170c1e12060406090b060910110a111212040e0c04030c060201 65
    0xe49080d0807203281c483c0312034035440240c600a42550225156901080002d0080c5821505c2001e900b446c003a5152808917008600784c05c295041a900d1510740c40b854118480d44001c80d2a400092020500c064451070500026100720781403008540e9031071800084a00040c0d02410345011041014204025090340c2c40890b442c0440106001d140c000ca11458031111112400040380c0d1920101d0b43c501e50b5441401220b518040022031402d410252040c14007000700c0300d42c1c09226007001107980b40404000c0307000300c0c02010600b8401c4c0c0105030840e00c1102400694424008a05907690b02e8203410b8030050400c0018803c012a0300c04071b038014a1501c070201c42401080b0031138041c400755403103540e0308085950341c078503607503002d401004000c0640c00d00001030382c030500340c034208900c03a40350301c0101505141724110120307500d03402d03400c66004503d42050f000d045020620002c2c80d2a108071803036048244118010440000740c50000100f030b0b034000000300c0303010b1544120301e400000e90315400640600000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 990637625 1250 990636375 990636389
    0x20d0302030d2c010e03040b0a052104170f0a08040c050603010b1209030a17090c040203090102040f14210a120f1d100c03120e0601061101061a0903101401 68
    0x140400f00e20310105010321040c180c2000c015501c0c0030700e0854200200e40c0038032204000e0041c1403242500c4034012080c1031251000d03115221070a071800d89800e4480040e55504003000c01c03000d101d81c00d000480801642c581d13041e80d060283d601d84683c140141702c5480c60703002c0d0b0740c080300000000c40c4205801e006031505045024001e55551261048140c80b0700031890807170b00180500319a01c2c01c7c14940c50015420402c10301c152003100112070082010b0364012107800c1440c3c3e40005040000584110030400142a03a0505070b1202d0340c1c2c600051402ca4010500b442c240d03038100c40c2140021401c0c0310302c0032450f5011401c0c1c1100070712180054804008001c0344000b083e900b06221400740e29101c58128106030003040d03c01c44005880c000d980c0c103001c0c00c8040e403c000b0081c20b410004000c900c1085001c0207400e0050a0075032600100402a440308841d21100703905054040060b800481004148503c44000c003c1c0c40d01c07282000300303141c404042e41142c038907414000141c1d00d0050b0403014038161445 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 990638875 1250 990637625 990637691
    0xf11100612140d05070609060e07230406350a03020d03050c0901020a06051012050102071209030b04080904021210080d03092a051201050f1003050604020d0302030d 72
    0x140442ca40c84418030182200820002c00c5008001440c550049003e40c3c8581c0300080d80c10300b01c0d4a00743c0b80c07101541200005004c030400c42001a95403c0301120001001c0741c00b400b45a060900078560300d545c4c0c0d00c40a540261880e900343c04078284c000d280c00140d20b0082114107036007207400e00951300d00c509445400824546000f00e1301020100c4120b452a103c182c0041c822040150b5891000340002400c0000c03844422001244110124185e00e00c611b02910015031542450305085000018440170102400680ca4042000810750190307607a11039040511a03840e184032001141c043d108e101c1c00040c3c03005078602080090903214113043c0036a180ca074120b1307001c1444e48005a0860b40b4405000d0700b80388000401d00d956089001d11020a5240705076900000d0b41d5440c04034041d42a800702510aa944801c10003e80c0b42d50030000960186803050800142c0e4a90b4849175158017000d000a40982c007030803405024140208101c43c41c404030500d0400965803030b03041e031085918142680c0c81000d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 990640125 1250 990638875 990638903
    0x12041409070206310503040e1f030807020f1f081f0509060d0b07080f09070510030903030905060109020d0515091f0e01141008070f11100612 62
    0x148503040c00e20031a1190020019603d40940590885021130092031803480302d28070701400e11204c00301d6840d40c00d105000960700c66003069021440c11200070060561410001c40c0b100368054484040c034200c94100c50296580c1080d0300201d42030300380b011000c9030410070b500036031040544506000c00e540d00c40d0759542c49a0b034642d8070b90f0100002e400c0759814129009050117000900e021421550405401003e11081e0381c0f469a030712100110845600700480d0b6000100701110410703032589070f0f000c0c5820000d07118076070400000460100d60361800b0b40405580b8040390741050702903071100f0250354120044401e15a5a000b4210107980041e4181da04c0a0826000c64002e0452803080c02c4030341e50040c040c030010b0b91039040701d80300d46110139451441e80300e5004000811307055001d2802c0c0604080483c42038890196070602200c00481c5001104101d1220308001e840340c0d1240c610668200e852406050b1000103403400b130b00e4038039116041182c0034034200d00001c140c0c204005082400d4812502038000709 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 990641375 1250 990640125 990640129
    0xa420c0305060a140402070609050a230a0308060d2f090c090d03020a0b160905061309020c030d1401031b030309090b04020c0f0c0111190f14120414 65
    0x59000c0e1010b54001e1800d44003400051840d802d55501c0b0308010b800113042c1151500d03080103075015000243d131290840541d890501410030001107070740b603c0c0c210701000c2404004500d56101b50307541d80038041001e06000b148131556110110b00c5510b401040c0c00540303041c1e83c45104607001d40c0d40181c0b01c2c065000f201c01c8005003000641c25220b2500c45070400d00304104141404030040c051507085085014940701070000a01034600c060140109000e900c05507100590050060704003904903d2144105203311050a03560bc2c20700d00540b20350010250b21116182103017481c50046140001c2000c0c2021000c5e4442280000c2d10b9040ba80581003c0d0b14030a506001c83d29644090300002d0300007540d98100b40702c08040c03078104c44601b1602501c018588541c070f85640742010320580078410707560000c500148856a2010050341c0b0700310200c2c040c2c4218505a80201fa1404584400806000e040d554050030f200c0002c41d070b032104840d51400c1c1d80c4100000400106281c2c03041c05041c0d20340f01ca9520170b8002d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 990642625 1250 990641375 990641381
    0x12030a240f060f020a0f1a090c0a270c051c1a060403080f0304030c0c080604201c051203010b0d06060207060e0d021302270904050a420c03 61
    0x70250f40e005803107181c90715191040c0584040034165040d004900585e070482850400191140141c2c10203820444150b504021170710040344c3c001140c83c4845843d5030341c7c2014507440401480800100000c29940001c1d081d1100e003c0c40c2d0036682d030741580c500c88001301c01c110342001e4440510054200604400182040b0040c02140000f0301800c906110a5070002e442e0300c002c582080c06802e1151410601c1c2e541c07280365950642141580e0f81044d000d00007007040403013a02030032504450215003d00c0d01200402d5440303800b0742c250204003904406c41020300c41d00b0321604681c0b5411654060b625078491380c0c20b06465003c0749075120050302d084000110315101141f0031050725290303950410301c919504104a0018000502a41d00890061080c1d00d000f030f0510007400e591650809078684c6c101c0c0d0310300340100740d80f240d0301031070103000d2a00c1000005200410340304a041d5004c01c81d034083d000c891603682c0310b1031003100449144581c146280a0300c402d6008040781c42d688003034820b01c1034440e411022419 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 990643875 1250 990642625 990642647
    0x10305010b041a1806130e06010c0b0a0c0e0307030302070e090706050a142728090c0203070c0803190201140604020c01023112030212030a240f06 64
    0x80741008030303180c038003000e1a4010502440d284190a12140c1c0c1308000170310307582c403250340710680c0d00a815040010b039030086160f907807050090800b40164402c98582c580b100400407c0da2000595820b040d2161034061401d08501120103030464644540328038011750366050a01812101d0007d80000480c81c0000248480c185d6403541e896a080c001039000076140d2611300212003800040501400003480d016440d860301800142e040c1001c000c0c0c1275402d01103503640c220440d40b00d822030820f141d190b50340181c000108442d0b6009000484501000007281140134034200100006068040000c100e9400809403440b0701c0d80c0000c0940715443d100b416400c80d01702c0000040c2c83c00c070781030014019141950240c603d11b1512800945454041a1620078482d80143d01c60541e4260400c84509103028240310320140209041e047c0c04404943c0703010750f950840f00e031a40a00100040000d01c0031482d03800800c40400c00c03009022000746031402308040d03070149025400e0b1a8694400008000d803045500d40c40c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 990645125 1250 990643875 990643889
    0x1512100602060f102c0a060f0b160206030403030b10050a080604020301060816020111040806010311040c020307060e120703030203070305160e0405090f030a0908010b090f240618010305010b04 84
    0x101310b8500403a00001c0440202c00a1030019640100601e0320032020003e0310a01442e4030003d14141401c0415600e84031a07041b000300305400b4041340d914070082e800f0307951926030126842c980303996851608501420804003078030f0300121720440d0307c04615004006060785545503160380e00141c0d07582092100b02e0101b44540800070302c90001161400c0c01080401c1d01c0100c09100215094100ca124504541d20990081d249544048010024829103104040004604480c00d1168010300d460084d074a011700900a404103a641103012032455007044410905914000e01580350480c130b040260094104544040100342488005420982100703081840719a00b0341383c81514000ba10144002444c000346540c14038821110000c0d83e84204001804920555684818942c2e090264640c2903a4614100320300452420303040c85030040c0100c1c030455118003003901507400001c0103c90301340e60750286a0250b0708403100180b803050810158050127012503003070700d0034842d607642c803050030b101803080c2d1044003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 990646375 1250 990645125 990645151
    0xf07030c0c1e0501030903110303010623033705070c0b0604090b0a022110030c0803130b0a17150f09010503030702040b010c080d0903110d0903021512100602060f 71
    0x200140d0b000b54406144207010703148c00c0030000c0401c201203246070710030f03040034002c10520340e8065500e1100b8500912000202c4a0560642c1001003100c02c4441907444040703554103030828000300703504801d2601810019006828895030400c0000500401042e101c103030380055880001501c1401c060060401d019070015461155945000fa40e0000b50010401c04d0409402440078a042ea41000d0016004070350910301801190b00e503180503140884c40d40e00044161300140712000d10701d04a0305460040b02d42504003140e441001030021a0b260042d2118103640742d00c9001802112100400c1c1c08203001000e42d01800038041030b1040180052091040350745c1070340100030880041c1000d0b00050303002c08040c100080800030545e00c2031801d41056642901c00d40c0d9800d042c605155000101602c5900300c1005050304152440300140452054000a8000c1d1203405110520180c4502181e442c00b440301141d800c00c0c02c0102032060310b44814401d40b4014401c01001c1010003044400090094036502c0940d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 990647482 1107 990646375 990646379
    0x6040b0d0f230d080606070201090815070f050f220806130b070807050a1103091005121006080a1104090203041202062511030f07030c0c1e 61
    0x1a041944024490f400083c0c0101000da0402c07820350301c0c00d40d2801d05000607146100306520a103518410424506940c0035640d29160290069950b83d04014440200440b554080e034038000040300f02c00c0129084440359080400400341490700c29030607681d92a089582419000c81e0042c07402040c0d0307091307801041502a0a103034001400d00f803001f5141028007004180b802085000020700030080f41d8403900c5070041003540c038203110003040c22090821000d4001c01541000d070410041d48440c101003040310003a42114800e6901c103035145221a030301c1e02400800703820f283d0400c9120b14800c00000c283c160280c0000c0d03120714010400d081c10042d00090003880d03d80d0080c800c180c0030400d400d020400d4100e04180c08120b1845242080c840c0d50711105060940c42541407000c480c3c84002800c0c010140c12103900039005020b00e030001a00c59a031808114030700ba0300c4034802641c00b619442 = true := by decide +kernel

theorem cover : BRFrame.Cov 990467625 990647482 := by
  have h0 := BRFrame.cov_init 990467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 990467625 ≤ n) (h2 : n < 990647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
