-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1579
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:46:47.586897+00:00
-- url     : https://prove2.me/submissions/b7727fe3-b79f-4135-8994-dc293b79825e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 283812949 ≤ n < 283992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 283814199 1250 283812949 283812959
    0xc090a091a060309340b0702010c140f070f0911041412011515020f1203011401090e070e0901090501030b070309030c0c080d030e0118081e0703080a11160b0601090e01 73
    0x190401d409504200103000c1a1b848108036205807080010081c0041c80c030300c8008000c9956031051500020015003a41e0000241500f050301d444956088190326004140042002c101203100746910b20003640055400d103883c0c134040c4031604820020351806422340d0704c0c01a840c01f800707500145118441820f20081d154660100c0200240e5a0380c01a02600c00c0350860201d189001070f641c401d82c0080b054903491070b070800010648054103091002d060000000010a4404507045e031144603000580d5138481140c0d080081148082c07042c2d00440c0d040c0c1c038010050011462504030507600508030300303011911140902d02290014000900034000710700588000c58150f00100d40c844a10f140baa80502c0011454007915080794078003e5031100c00c844100d85040018100d101800a029020300944185401c4100d0188280e001d14400c400095a0b20200107940c01e591055600d1103003904144c9050104030751003000c0c00a00190046e007149206030008071203a10a0340d07080068050014015141c2d41c4d00c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 283815449 1250 283814199 283814263
    0x326040816080d020706091403070210030c180b03060102063301090b0d0b0405100f0e060103020418060602011118090919150e0d080109090809090c090a091a060309 72
    0x3c1c0c07c085a15000700c0c48004111400002541c4115800030801c2e2141c1c0120a0181c2c020060072540d0f500b844407070b503150200d401202d031030709000700402d0384151b5507882c0240009040c500b0007004480075282d00d801c030481201308010300703c1d6650403c0008003084400100140d600349010ba1000c1c03460b07038000844c005400c540c2d0308200da0ba2002520300340400c4e00c0b0390701d0585407225140505902450541400c00c015042d00c4101038100c00c041c10010301d406d85a45842203458030310b20920308295220401001407a50900c506809003044902c81420304298a04200d02c45480c03214042c0300d106a1004511207081c103011181600e9202e00440000c44a1450140301e0044002c2190103031514050644042d101c0115440c194030b90301d5a250300d040ea00b0158580020304811405075401c180611a04540740c844203081c0e402500c007804000e48802d00383c0c0070841300c3d1a6a4000e460354508000c01c0c01e040e0070828200d44044401180ca41340c80c0c1d55540c1245180c41000c02d000d603101e101c84e04060303406000c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 283816699 1250 283815449 283815461
    0x6030212011406120a110409020306040c06020c01020102180f0f060309071a030106200a12121a0f040b01030b04021209060109060303020a02010c110306040326040816080d020706 78
    0x20000000300a950f9060030021400c0f086000080d20b0b8100f040d401d0000352210416118911008000084210b038507000310b0f1a100c1d0407601190200110303c03082c0421501044400307000582480203510300318400720240900b92450035014001c50140a4072011981c458600302c801503400740c06542c0301d1501c501140d0340d0fa45144181f5100010400c0e209442064000c22207040c1d9400c0c1e04d810b10300030b041c11034040103000049481503950041c400c0c0d0100241c0c803c101580c400b241031740d0366000ca10a100450003224501c60181030a40b070b102450410503200c10400c0745014000b01d0b00041c890340701c0300050300600390301450f80d0b074028030000e16103131b0070510024164060744013281240c4680e0f895400b400100e44041c04080c0150b400803145c100117622a00c4a101c00b144282c546c50400c480e4400440d1418106890440c007181000910300d405420720340600c0e800c1d8000581040c401c2c00c150310b0340c0c506803250302242c110080809072540c041c4a106c0080314007801c4107080441d501ea0380d5040900041c2a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 283817949 1250 283816699 283816721
    0xf05010501030e01090b060603040f171903051e0702071d04060c090303020a020d0809220b010309030801120302120706140c040311131e0b1008090601180603021201 72
    0xf140102075051998144038440c1040d52001e400041071311740008002203a003001388111500160449007800081c400d0305075103254042040300b07644406d04011206d0200566519070400c140c40c050411100d400301c9203250f15104200750f0344140b90385450b04100d04180039500050340c1c3c0d618903a1400410040b0040aa01c1180124410404505034100c11a5000c81c07502c4042c0046c1d20440788100545807001c1d12000d4144142c0d40c45180111a03008079180c14100443e19005a0740c1d402c03180b1a08089008014400001740303001c1004070342658000d000d580c01800340c10349140d50220810200350081101a02501e20f219146484164034038151014025074140c0020f8001c051000c108a5a086002c1d203056962180d00c080308143c024081c0a0411440521318031000d031031361741903016051503031b0190701580945440820724000030400d0050035010203042c04100301105003004041030000c00e403141500d800400450b00e0f24402181e44014110036040030358052480d40001c400030b01e05500280e407a00d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 283819199 1250 283817949 283817951
    0x5102c0619020a090603051005040507020c011107050d1104090b01122006090409050c090a09020406050a050904081b030a08090f010e190c090501080102070308090d0912080903010f0501050103 84
    0x740701009014181d000c0c05035100c000c10303a40c0c20300340800c82c041d4002c594020b50007140842c88507901da001400781c41080c1d0b8810b0143c2c01c4030401d1a605d507400b0500d84140d041b1000148450b078508801700714100c840c1c01000e840c5102d0503d00014681e181d400400c551500b182044009507118210b01c83d16402041c3c0480e070441510030640c0300903502d44440e5940c031500034149401c020f42142404060a00450102c0303242c0200380710760125580f401c0c0324502405c000c0c400040c0c1c2c0880b51040c8021511640c019900c160b0000360108030303507502c41c200c484d0b010345c3c030500048d240c840d15045201400d601c11a5006180008500d01800e683e0000409204185260403602900321003480c0900b281c81c207030081c69081e0048586444c00481c162110b00c0303410311503810481401c1e5a014510211007082e0490f0703030942d40005004050640c0f111045400651030b001a122500c0144000b030140d40303044c407540c2c81314050b4201e842e062000910903102c2402c00900240f06140c50017030244010b1009005450103e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 283820449 1250 283819199 283819231
    0x406050903160f140d050f0105010510030b0d030c1a0112060606080403090b130f0b0d050903121513050a0b03070803070f081623010501090905102c06 66
    0x188060350016022203e42ea44036101c620300304807041e10403c0700e0000c1143c10441c1d012026000035000c0104101c5507090b14000104c550400b03007007044154414055030201420082403c2e410307501c28001803407440d49410b10301d92001c2a841c1c000400c8182071607812044031100000a10380202200ea14607451240c2810405181c89950654012505035000340004428401c280101c0d0250802032944c280d041c4010346069030781d200b800300d80f00419081220400c030702040c01c0c0c0c0c1c59070321400751030f80048651001c0c50900b0404e06602c07a0101700100001c540031002030201180d038132101c0c0800300c80070000c08240321920b03001c540040a86500609540688114100000e01500102c19558040d0713001c0c060f072850755000d80382d13100706401044d409501c040c0080798040014134105038a05507044400100400f4810310b0560b40c1c02c41e1310582c4000d441505000341d16001413030200300c14000c6004003000152440444031140302490381c64a09050540d1001d4000c0b0403c0000503d1a205112101030480c4d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 283821699 1250 283820449 283820473
    0x6130b0408031c050f042003070f030c090506010f050a0306030804030f2d2006070524040206040302010f12020c07080c101704050c13020307030b0d02031c0c080406050903 75
    0x845070200c03048400c0200341008540090081039903410342c0600003071f080362620030300d600103030401c1e0060b482180502c070801000c00c2041840032031400249807410040282e803401c1000640100c1c800d141c20000c0020000e920003202d8000c0d445135003c0e6420a06060711540c0b030740750a440c890302707079601501c6e00c180102482d152030b100300f1007620b940703185010741038851889559840c01441e0400006522500c507030100ba4525102c1038094028580110018108000f03000c0250254034640580300070366210707020402c005602e4000c115800c9950a10702010030040300c05041310f00400c0d01200b61001c900001b151040b00000043d01c1e02920883c2d02512107001414041041035500401c1c0070010038540a4140d8491007948101c592050207401660342401c102e200040403403010a03c82c2185603400700c1880062075041c4034450300784c80107a402c02c40c1800d941c0c0020b9a034505c0500c09100f072040c0d244003080701a11550940c0000d540c8020103e45071a22407401521940043c28198040e20841000c0c1e10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 283822949 1250 283821699 283821701
    0x209030f0f03090d020a03060504111e091305031b1e031606051b0a090e06010c05071e03060204080114070c0f0b06060f0a0305060a0906030b0606130b0408031c 70
    0x1d01c8901c1c0314002d61418041e1028032415140d20001643e00c000b00322400408079106000307140c4210700c110b0692070700031401c804120744905c1c0382003608404040e80007440c400361102000d25410140c40410048203074054035200345540f04104951101004100c641144c070640010840300410100200e861044420000355503030340120f20031802c00000314007100d000b14030540d1099401c07076030803001a0b0401d03c80090340300c0e040d48001d1070000003031440103040005075280390446400110034079101e0307403980703d5864090365580e59000c0c8100c520010385400d0604000c201042c0021070b030020b02591150b50395410580241104050034603828850800a1340841c4503264100c182da40c0f0071a0003107076603600c1c1c803041140c2c14002e0203190040d204100c10400c681040c1c0250008615030b6501280500c2c01e00700340f01c0f0228650b071020303804a080003070a000294400d460607902440c2965295142c00b0180c004484107103071503001400300080010081032400c00403000f45800009039542607060711309070549c40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 283824199 1250 283822949 283822963
    0x207060225120311030310091a0102061906080a050f06010b0c0a120201060f0e06030f0d05041202060d0c0807091202010905010507030e06030910050f060f06030a0204180209030f 78
    0x541a0984007406010342c0103040300460086000c0c0c5080c4541054242c0301924540c800c2c0c4401442403000d440030842e04101e401000d11f024045422011103403012000030390340b070740040e00707000152021514500d696034096010b10000c066100884500355202d0800301e884006442c0121007074000c840c0003050410116045030600104a4000e1507844a03a0700d0700004a8a03081c860f00855484000000c2c043c2180f5030400007504080300402e10605209040510300030050303200e009640c00640940540a4010007500c04441e003401c0c0f001501d0b1420303c0040c0c0d0034852080b101050a18140c2800c0105521a074824402c100944070000c0e580e8035210308407020030469030020300103401c0c10b101341300c80d52284018016040c46820f1010304000184001022a0421580c000166000c080701d51044000ca02901c0c2d000b020440b1a410603040100c04500134900c0d00c0c6026008090020100c1c2c0140c401c0e134100d400800700014200e01908aa029800296014444042c420701c0fa41e0408014034501003114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 283825449 1250 283824199 283824253
    0x15030c09090f0403200118030f020d090b03370501050a0e0405120c0a06060602060a0f05150405091501080607170702060a0c03230a1508070905042102070602 69
    0x24156403014178034007101d800d40403a00b0140d502c1d4140903259900341c084e42031020303101e511080d500d04e001840007407401c41c40034203110800a40f8a002c00500042c5005c5075001209254001c5100e070b501c02100440c030509200d0303251011004441c817490528a688094140d480450309080805c0ea03c0008940c20081910094140c8c0c110040400c061901c8000a04c030056009040e988000a1501c4180403144131354012009a00243c04106140c40544a034882104082c1010001424240030049503040b0780c00945025698070000300c0c0c100391082280b850400c0e040944500590385650506844100607200c41001c034501d495419107824007401068426501507000313000d1a6039202d00100a809115108420b05a86800407140010010f00750310100e042e04141e00c0d610708140e510f40c0112192400d1300c11045c0600310301448642808105c1c00c3c11030345440400300d099251820400f140e01c1e400c1030504104110840704054950300400c03030000300d80032034080c0c45010b1060a0310440e0f5a1038600d403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 283826699 1250 283825449 283825457
    0x5040b2706040627020304020d02031509070605070812060303091207060e040e0309241b06060f030a030f031404050109031710051513300209011415030c09090f0403 72
    0x1800130700c00b00382e80c0a141e0050005003400011802c54010030304015142ca4200c1c410301401040010607003040181c0402070416150040c6803803004d07140d40d40940603884900b01010703c40008150281d5080090711103810000b004248080743e81c40074140d0f2204c26120304400b251154070303034411610b4a4410302c0f640040380c0c1d01840c41c025254081001500d02040d4080c00000074110500c8001418406400031184500142c1111102c09100900c0d052008000d1031040800c01c03820340144e207010641095079681070508040ca80c00024042d130252000014441014450718108002c1c002c0540200b0340483c002c2d00c2d000244900202000610441191080030001d0202010086030806540604128806c480c4440c10001d26445011000010b58001f052003004180c24404843c256410229003014100c2d004881e06015400700380b44440510a00d0f89000050320384c40c2352501c0f10703406500c1c00d00d00000110743d40c3c0780c5050040015003003140700c00c1c083c02c0301d0f40c0022030b4204001c904602583d01078503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 283827949 1250 283826699 283826759
    0x300903190503011d061216050906030c032109030109120f03150605180607140f01050421050c010501090f0b0301090804030b070908070e06041a01080105040b27060406 73
    0x44c800b800c240a407099401038076030742c0340c440914400c0c0014840072464010344070040d0724160811000501c083c0c0154401d400c107000b03100680c0e80c0018000441c5169040d1f4141c00402032210490324002c0c000e1103030b0554240302291782007028001c913020308010300342c44501618003440300407800c60b000c5080301231610311403001c148401d50203840642001c4000c0240c40c08004040c00c08601d003030300001c034215000307421348482d90500030050200b103084810410081185243c540c40d80032074000c003028854500b41c140d46d00c1c4039039035208008980120910600922865075904d40c1f0300002c100582c15001d03858544150040c00380342c1800794501840d04213814604207415900c0c1d1840130940901410140801c08a0000c2d95000c10b0000748020800c000e02c0f49120302d00b20f400d00065581d00e0100300c007025000e0304041c0250380c020040606442090b2000181c0c000500040b5110710104001c84240c0e409410b0791400150789030201c0c0344140c40545080c00895603541c402890041040c24403184204460 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 283829199 1250 283827949 283827989
    0x816030507021506060409021b06010803070305190c0827010302180411090d0c06020c060406020d0c080d1802040b090708280207050d1e0530090319050301 68
    0x5a42c3c80d040940206050b00d00355554480201720b034410b41d00c582600060114000341e06400b400703858011b01540303014500c0c04109540c01407040c440e40d00100c1041c4020340e6841c00c0503100d00040e01100e5403001c41c40c0d5071001d062400000321034141e104071260860035440825154860f0096070310024801c2c81c410a00d04d00007040202824040c030740d03100c03022400c0c00300210030740e18000ca101f03405026841c2441c0e07213030030304000038209881083d546010310703020481080a43c0c0e000a40b000c0c00070151030140d10a48461810f5011441015280000309050030594002e03540358030300046680d0b00c212004c00405d121641801400038003203880c10040390b42940001d0304020311102e1284100059104a201d0f48000c0c180c1008a8108107004d49803980034450041c034241c1c00c81c117900168100c02500c0d01c121164414001c1c26071242c9490b4410300281e0104041c1c001c6050b40340310051344140350b00c1080300e04c2c0203000e456880d000340c54501642c0350315094615245001c1c6c01120306032400c1030413850104c1059 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 283830449 1250 283829199 283829233
    0x5060106051903020d02160c03051204050603010e19021305010905030f34030b0106080a050115050c0a0b01030b06100905060f0901050c07090204080d0e0f01260403081603050702 78
    0xa40041e00c05d44e8081150130f070700302c140c00090350b5100c0c0710781c60904042c1c1c250f04000d464214503103100e29040c04e041009014542c0e60030266070440301400c0303c00c1c140365128940071000c00140c9020701000c03400420925802c4c85140e0020003035400030ba8a05100c660b840c020160f032900c40c5540069942c00c1550420443c142000303800e04016040700301414410700d070014640c03d0401c158415109580003000600503554440b44c5181c20442141c07082c440b650400348c0e008036101c4802041c400f405070020f0880950300090002c58662500a8450351081d0703500d040900c0380704400c07200584200350082e600d5101d01d0003651120b060341e60151105041ca444c540e40c0ca00c19074820300080e41407107000d000c90f084440040000d5005003030701800c056115883d0205081c5018100903902081c802a02108007950710fa031610508035140902c1c1c00d11707030010b52840751444031203414421b09500c01c44804220034140c21100383c074040c80c079520101001c60030300e1108604543c02030300c252005130404460900341c03c041c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 283831699 1250 283830449 283830457
    0x405041e08041d01231e0109050301020c010b03010b0607170703050f0c010911060f030415061206050702100b1c1506030c14030106031e0c050904030c0506010605190302 74
    0x415601c040c036180e242c400b14031407080040d42d40b0044040000050203051480790144a00609030340c4c1c040501101e0b540041c4440f000451485418034941080001e1a8400e100d200c00400c405002195109134254a80e4040c181200d1414025820134156200900b402401c5a0030180c0050f46007075130710301c10703c050700f0303e0360003032005a08100003404010400d040040051201c0701e00000002400c0201d803400000450101c0807140c4130300c0c428800311464a04007000c580d031286d401403101c10b82076281100c4000505568024a50400700900e00000700710043d1300040c0100015022548100c0c0303010440e4051b2680011100d401c032260007000d80080c031010545018880c0704d20301d403800f102030302008101100c85641c4140d401d42c130041020080040c3c81c1402205006c2c09a00900060741551521103040740126585a140500d280c510300c207020050040d07074041c1800405010490030541001000301c41c0b0004150b03100c0c01800d000041c914040c8040301e0340a8170450075500030042145064000f500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 283832949 1250 283831699 283831703
    0xd02180d0804060509271e090705040b03070902130f0e16110106150e1306060c020d1707080702030c0d0314070302070312050a0807022e09210e0405041e 67
    0x21080d555603810007400c14406c1c0c2c10f102c03078441281c03943c58055102400d107640920000009403c41c400d011a9500125011054138010780380820320707030b8041c400710303182160a51001c0540f80c07001c01d030100c0214401e00c0700b000700c442c0286540b90150b160400c0c448010400c0d03030811070707003010440e5052660f07000701c100007011032a02000096250b81d6400407480450003130110800100040c024202c0f620f81891903074803d5106030b40c01c100c2c403401c00340040c0c040354080c00c0203840f0324288240c2c40204005100c40074000040f5144541d2a664a494072089031303042080106e100740244a07422080b400d0810410b980303a901aa910468901c444441e00341d640d00882c0160210b0040c0840400810b07914101400d09103466030311603541d4103820900801441002d044c0300c0440d0440500d200c101c01040d180e038144120f010f13800d940c4001016007010004e01d2a580c009140510030801000c26601c000709100c0e0010b01501c41c05e20ba400c403003080208030b46040f28018658803114428100c40181d20032041c69041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 283834199 1250 283832949 283832959
    0x21506040219020c010f02152701020a020d120218090c04030c03120e0a0e07050f0c190209150108130c0b0d06140d03020604030806010210020d02180d0804060509 71
    0x3600026000c002460b02e00c01c400056881a6003000c15940d1080e0704045003c0948003911a0300b0384181d092107544e070050b010f0a00c4152000038071000051504400c034034050540002c55072107550030030194541306205070713210208424440b0301d0003040d40d5000f00e0740c3c800c0488a00c1200d08180204000f104c55014104a011050a010200025101e121290050b41c001e01510038450720742800285003003283c40c180f0b03000b00048441001a000d0480006400103528180551a1051070048000d40c1c010240c0c0c030b20441c4079100316200c000010301340301c51a041c020f039415a00345d5180312210320311042c11038110340042c03491070008092400600400705028807503c11000d00039915001059540c11120844400715540c000800001941011030410408151010040114603480194542100410140900c4020400240355178070a00c006070074015504801c64486a1030a45031000350452a12841c0080304201d40207500e05d8405188126281c0c403004107850f080c01e061003260705402c8082219048 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 283835449 1250 283834199 283834207
    0x801150c0503031f08070e04140304060906030f0b0a0e0a0609020f1c02070f080408010515150c0a0c0b0703080a021e0a020309180403030c080c180f060703110607020d0215060402 78
    0x20803007070049000500300d0b01c0c0c08841f2410035080c0b402d07002d44c1c0f400002c2441e900410081000c190004440d1003210403504001848684030403400b00545000310055034007044184020841d6111114964040d41d0420301c10494103844014102c01c92099000b0f080f8640d00500004218a1501c581da85507642120409421b02190b69620380d0310b40c6c0360940413500c400b030215007406090300900ca4194020501c1c0540c54480e012000442c000750795840c080d4034681400902c0c009019000c019550b059503100c0f0703103102002d40d54803642070280c0100f00d04900054950011482d00b080b2402611000e5880b1803410100001d0540b05000300c0d40010b207018154002071058510701d030ba6a1020622111003545918024900303840c00130212081e064508080c480d0032030502481c1d50700d101c242e852030300501a280c2400c04045000912052003951165070044000400c1000c160340300159008010048003212041d855103a000d9884024420542006910030306e541e400380c840d04011181c114002900051030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 283836699 1250 283835449 283835459
    0xf1206090105090f0d0e010c08160303150905011d1008010507030204050117070c1203061703070b0f0c03160c02060c0105060f0f13051f03030801150c0503031f 70
    0x1421000c40c0e032100c0d6070359035500f00005108107001c0c001605000c4400740210361142c41d00a0184150486120b040040304d60a1208019032601100c810001011503054070038400d10303009001e01a24280008504046800000c42d00420b001e0307141039403410440848100e9006110300070f1100c00401645c240d442080c80050000000e01c140340c020400d0b41c1e00540d8423828000050f001820715105540402061401c0090896000d950524403036442200842ea071022440100c3c0500b100303421403001328008450219a02200100800706a4400c0d80780d940181d035282842c8480003c100c1c2d00751885003003080058410121540720840c0c40301d4500b0154807960303454002c1079241d00180611485603548106004132031818041611045000326545541c001c050804680841c24100d00c10480540f0f4002081c0e12141201c0d03e910380740b00203d4440324031907072401c00900d610000e1152030684401020401c9587c0c1c41180c910461541110045195403242800c1c0100c5070a5508060068043e44802203a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 283837949 1250 283836699 283836703
    0x30d050c120c03010504060b2802030910030f0b01050405090703230a0504150605010e0f030102071406010e09010207030804020f18090106090e01181e02060706051501030b0108060f12 80
    0x101542d221095503869605000600085409641040164110501400440c00301d03107019000701540e414030030000c00d580800705074030b075010350305415034898000d0301c9111031644e05512009101c130b0f800302d091001d61092401074425212324028075800044100010340102d000342c00c1401c001d207500c0412260700c21074650741103003088181c07880709145803940e040c031017400309d4266441c00184610300b080226528103000a4001c0018449841c00369040071040c1c12990b17001e40c10350321042d4010100c1d843c001070951403103881d14424050340010310f541d000491840d40c0c0500c2556000380e81520b031a1506e85860b000c101f090801d001200381e0201d5440c00b01001c10840c8040384c0e0103641480e00125003181020b6142c001d0321240001c00100768500190740c1050f41c10a0300c0001d10f0303a0040a200d42111744851070402125075038034040e42000000542d401041106d9010a200f404003060700c00c3d0010705000110140c03021218376a002540d1035021914034588468192000d800007400d401c100c10000d22468 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 283839199 1250 283837949 283837951
    0xc05120f03041d07020c01021f0b040f0b010f021504020d0501020702040f050a230f06030a1e0308010902030412030e01020c0604050106060215240a12110a090b0102030d050c12 77
    0x240d562402101200c80300b8050001c03944d00010140090281c818039035000030360394040e880b0220f00c1c2144881000c0c82d01a500c0d440285403030f2028006010410005405501030b040c85c500b0b250003d44030450070301d2940c0c80807955084450392000c080c400385c4c46503000c02544030807030002507499542c2006a10010703903a42c85101c2d6046075400300481c05203003010415089840101080c051a0030f1242e06196071801034103016407003491a110200c085d210a004a45000b200000041c00d0199440242c0701d040070750301002c02010312940d50000c05a1302d924100b0142c0c001517400409040881641148043c001d4128901040700c400c00182040200c4010340d250070002c1d581500c0c1039660304024082a503060103101400d00e10414941458209112154080b080b680e054500f90501c040a05003d903403031044020080010304035102901d602ca0a04550030300c2204c5242e072003892890000a54410b2900880d18400d0f0141c01071400c101e052030401001d44001446031481d4141080f0882090703e9400810f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 283840449 1250 283839199 283839209
    0x30207060209061201080d021b100215090a0b180c090615040b030103060b010507020a23040906020919050a1e09020304121101140129040b0a1206030c05120f0304 71
    0x841c8a85d45041406030610041e01c5098003150441c40c1420345004100e4900d41100c182540c034551120000c04080b402e00106a4402131820300c0300091120302a400518554064003d00d64840c0707503103c5005030041003209151044050301300c004003404910b880d2034191b80c003010150041004000c0c2c0c6c3c13403c0843c2e502980241515040205c01170051142364815400c06580070f09100e0b00d004c200c0c1e00018071281051081c0d00c6041441081304810501082d4104500c0c0d0000d44107100d030700b40c5450224083c0d0040101c0301d00420f00c88e4194152211003030401d0044540241c00d4001e0b01c1c0c1401190032410728041d20309240750588060000380d05a10380300840c42940202c1c0c2048000b100350304003d00c0d00807100e0034003040787e04200e500400d2260300e41070329044408200f90080c030010f8010301500001080b20f407400900f54003003000900240c1200080055040c0c56541c0300b48000c10300c0440d000c4030018040981381050300d000c24800b505101e105d086c4161000380c115410400483c0c641c40c5903034410b400c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 283841699 1250 283840449 283840477
    0x1903080405280b13081c0e0303160e03070b0a050c03040f060305060102070b0301032301140103030201150504020708090402090d0501020c0106030b0919030305100302031203011a0310030303020706020906 89
    0xb002c140a41803441941040c0040c10320f0080c0c400c3c5480b008881d009400600a50b12161140d50500907a2540000c0e140210501500d441b80b51440e20160788441400740c80c030114000c40c6a81100e4074000c07944806a4a04c1c000355410302d903941c20111041d03008164004024441040085206903030300002000900460303501156504d010000241840b919a2110701403000038001400002c20014801e080b4403000c1c0340039031000c0c03400122140901800a00d403800c070600d01001000341641034210b10425603050700450041c0740c0e0781007800120702c10840c0c0504448000e02151140c0d00d891f0300244640d43c2c5c01001c0e178002d070880e5140d41e400c90b03000f000b44207882c0e90740340da04108004006e81d071103038020707446c40203003000c139045580c4180020482c00d002000c255a8a0015a58a840030380c844c01a58001c1c040703480440b8000d4941c04103610a014030041c182081503006154046681100d105020200d5503817007503891582e003500603402c848001c0390016000e0140d0306040c1c42e00b0703002d00201036075450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 283842949 1250 283841699 283841773
    0x52a06040b071a01030c060507031205090f0d11031e0903100b04050615090d020112060e0f06030f1e0109120e151323040905100506031903080405 64
    0x20f0002c4020f808945002e41d4043ca0100400c0817031040c8a28000300c0c0c90500304070740e403030340c1c1454100e80041c01401880c144601e03000c01d01091010002d01814000c0b4408101c42e003202c0a40000d449000c03401d40c41100030b0b4001c0008068000ca41200a9400d1080368a0541043c500344006400c113400700d20134618496840c191000e00f0302d001d028044c0c00003c10740e900c1c100140d030074140d01b04511441782c0c1c0a0060042448003011a4858a04c0480c90500e00350f041000d07030380741c403084415031303c050b0b640f00c480e4501d040115a40e46004a100108040013100510b910b8601c20101d4900c44201d40e801100b6550341c9140c8000310302a55240200d280c125a1403000d44901c0074100001d22010810310300304540144451404102141d205505580554900080a88454040007031002991780d01907042400e21102d00104003000802c406564031019041c00070740d40360400c1c16900c2d654681c51081d4140e0020020300401d000d0404660014000e1060307501070201e8050b1200002086d821845581c240c0070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 283844199 1250 283842949 283842953
    0x2120109031205060105040506180a0b0a0903030e04060803070b070c060204030b060108070c0302061909080a21020304080403080906070b0709061715060a1b0b0f0a09052a06040b07 79
    0xf201c0c1c0e6074030a000b4244075003058103190205049004e003d10400051002c81e0191149542e41d4061400611200c81c1c46036a6244400009043c4800c5100c101c0c04a03480b100318208505d414010a81a600c0d0302c0021401c1c4070094585c103480840141003041070200c00c0f0031603004588240001e0000e07500030345a8070601c1c02e01c031000500b9440000c26000c104401c80d0740a100180d40403450380c4e0007940159101d425020008400001004903034030043c800280001c203103030041e8200e1188a003214440d88110003503022204110305034802250010f1400404010900000d42440e0181400c0e040241010341400210ba4601580c014251001804070703114042c1041800d0380410740400c03000036401504c8090a003519101c0c00f20192911441c410000450039460b82481201417000c1c01025411381c0d030030180070f8284400860340c260f8041d1504032903403000503810503240c02941c45c12035002c0e004100d015a801c03406110050048003800e449149035052030307020758941000c0c00c040c0007010307009a6910b0140c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 283845449 1250 283844199 283844201
    0xd021305010b09100f02100b010905130b030106060c03050301051e040f06090e0f07290d0e010b0a030b0f151525080703032007050a1a01140409021201090312 69
    0xc42400740410a82c6131718150b074198080f03440c1885805c001c00200310a4200c1c070068034000e00c4c0703810a9410403944101030602c519039400c4a081c0e04400d800030010746440741000c49050b070b008000940482c50400042046003030126200380c4910307040101c110880321a0000070107031983c3e4205c11074040d455440078031840708903103d00360111a216004151100d01007400d29242d54081c410284100308038800142980f400035440124540001c40c40d41d9680c0000f400c00c00104407107908103940c6c3d0728041a40c1c5035810800306140650390802042031050b0760b000f81c3c100c0000401861503002481000c0c2c1006a51940c05412900b034001854403038445412000319a008d0300d03d00c040c1d1600801c01150080480d2040c001c4890207030301482d0108140f0038800508080440051301540c8080000500d0014070030b0224007140d040f0b20072a4004038200800016601a01d028000c0328405440d00310301003610302d001e92008075818405843c80d02c2e68007442c0e40090031604404800e801003041990480100952 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 283846699 1250 283845449 283845469
    0x504020c0c103b0a060c03261915120201120c08040f060209090412030c0801060516020f040203070804170f030601030f09020d1b21020d021305010b09 66
    0x1052420281d00025030080c491000c01c2e1050400b91400c281c1e45406002c00c1034021400c540c84098079000c0c5165581c04010034401e06d9010540c0024201c946400d000b101c800c940005414035145405003507220b00c04d21400003080c1105006617180d0710b0030541d0080a40c007a15000a1158100504d8106c0c06400007518220440101401c65441c0c405a03811481d000384040341c0280e04070714041100612032a040000780f01d000c583c554002c0d0ba010407c010000c0820b1406030314013140d0341c244076020b108101960105028024640480c03001e0040c5140e179802c985145002900041c1014041c501440c00314040364001d0701c004000070906001c000c00e1080c065040401203070501480741c5803050503819034103540000362103607040685a40c0c8001e4044002d410807405581c00a1010309140c801d45040a00c0821526400e884800e40f15000100d500c00c10850f01c100301044400707440305948035030801001c11000402203a000201c0d01150807008118400c6502070048414559a6208408100304030348074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 283847949 1250 283846699 283846729
    0x1608030a0f020703050307080a0507050703050d030e0604050a080d2009100f0c03140d050f04020909011e0f0e030c0318060a1e140a02010203010f0f03020117100504020c0c 75
    0x1103d244100000707178001040320103658210682c3e6440d030030031600407107a512441c04060602c0c422074101000f0b0144c081410f0f503180300c00d41c504001102098800070f48501c0122405010364020404000219040c0b00003840000e110300c00005a204110a0100f08880c01e030540d0102c84402150290f528140203901441307044407803e007584000c081c040010504000796000808209582000481d034800c0d56098610180c44601c0030700c141d19195410449114049509030722524100340442c8101606120300086805405a0920310b200166115405400aa2007a40350b140d034503180190b84140500241100d10303d101d02035030b9100358001c003082c0c0e908950002240301e0700c02000703000c28140d00500c5002542c59a1050300c03000c803c80120a03294090819000c002106001401c8490154194000c5042e02c184404810410343c58141d0030900d4001030000a01149440c4041d019200768070f43c00319407082c01300101d0840075440d4004201070f40c00144c0511096808000300d403402c0d10f0161080c01c0c0c204 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 283849199 1250 283847949 283847953
    0x30e0c010503040b010b0f07020904150605040203060d030e03030405031903080a0b0a15030e061305070f0302030c09040c1d010303030b011805120114090303060112020a0e040506031608030a0f02 85
    0x800e1680301c2e521348034010321a0f1144481c1c0010080c84203450344068900c3d003500100b0f0400c031403600303080000c085c500c41148603412500c2c1aa010486181c00c0c800c0e2401660702400459510f0710386c0d81e091b03d10780710030300d000380c0d15100c140400035655030701b0441c9400340b841c0c0c81907041107498240340c0501170345c0000c0d0a5107000303800c0c40c2e102d807202c3d2296032800c01103610380c800300e0705a02d001e200c00760000c0c03c0801c248040c1d40150380401c145100e220054400c450f2081c0115103c07640e076016180081056808001e5258001d003032a401646081c0c079060340c0041c01354002485a5546d40060520f02c5000107886419078040c400410506800d84141c150b05c00b400c0c282008403a02d2007803440d8240345e040c002d0b40e01c104886051416800800d6020340f5140c00c0790348074054981840303103800d0b03900e400480310750380082d2601000d0398014141c0e00a4514000054035000b284008401c100809403000904a83d010311500440749940b20164003020010b1181c28081d40d03543c90031401c010300312035010422100795 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 283850449 1250 283849199 283849201
    0x1b01090201080402012d02030a2601050f0a08030406020c010905030c01120f290405011d060607110303030411040b0d15150b040602010501062318010519030e0c010503 73
    0x240c2d800c0080c1c0d41c0d002d5824606880740d811181658000d500c80e841441c07401800301001043c03005d400100500010702c417038564404241000c0300b91b07041c01d0035045480c2100020031004106c5400c0659a07a004001d00034029550107494414591668002c0d900c403100681c03103096048030760350300f094886000d844d041d00a03059108a040001c0d100455240040070407560701c1c2015240f80208d5406030032568400d500112140710861180316004100103c2148240c0c030f080300005801401c0007000045420205c501901943d42604200312034000600c00c0c0c800ea084440000140c0e5005c2c8011841140314441403082c0e08040001c1c0011140d40b00308090081c0500010a40896002071050170102c034001e10210320905003800310700015410340d0000b8060b14020034081201a019040141a10790540d10104a258801d012141841c1c082c0110190b81c102000141c60902c006510210082010f0400500d80704901c501840400101005400020b81c0c03240c04aa0341c420500500d050410709103080d40c11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 283851699 1250 283850449 283850453
    0x2102030708250e010509030106170610061d010e0a170f0d1b0c0f08030703081506090907090b0d0b130c27050306010b03011811030c09010302070b0405031b0109 70
    0x240c01c0d50b0700728540074001284000c010580c802c204907101950081d0007032149540e20410000ca090705042d0544580c06488001210010000c00550860300c15a2700c01d91030b0342c070341c020440e8004861800355041003003e10500821361110f24080380200020111380b01e00c0f01300b141d4201e040c081100201c460715045000b100443e030b9405030b80e42c5009020070b48807803c52109442d182d50850303a00e6204010541010000041d440804030103071003c2406030303c801c0301e55500d01209845440c641e8440035800001846000e44c5414141e80140d403180d090306080e0806600d0340100f03102c0750000d00f0010390190b1901e80c0840302c5d06000c03082c00004080240140f00926082c031000e80000031488000b40490280d0001e4000340c13450341000d40090030050207a69240d41c50720a0f01c1035a40c424022582c0b6031045181001080e00e691041001c503426154501d403c0d900c6d5942280410362107506028101502400720001141c21420018062840b0310021a03680801c1c2c101d001807040c50441c0400746074502244000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 283852949 1250 283851699 283851751
    0x50c0406062a060e0c03060a0b1818010905010c0e09012d1502070f0b0918070c050312010602250303030b130903090e101d072102030708 60
    0x40b211089151464140c807038010011260b442c40c00c001d840541880c45040c40750001080249031803905505031a5940d441d00e06200694600d40101ea402203c200503040050b4040c2002c250801e0b0f1515422155545032884a4292071050304d05440341e07551486e001c80c04c2e40d00302048104041c0d050300c000e200e640c075000003e04103026450040d00d4001e00004200012008098908081c14102203194007100b001c5000035030300d5a040c024004040709900d4041002c00004068070501d220041030414080b004031810364052002503c00c40070710502042080000b0300500c0034211510b091801031503158907041000b882c09201d036103004811160046030200ca072020030f0708a01a45e030541000300d1201c00030008911101c2c2c030003038040d04443c548441c1c0020180d0141e0b13100204c5414008861032030f280d000340e071800701f9258070500030f03510400560320000c6019041000c1d80070103603041426109500010240301d007605100686c4d04103a00100300204141c2208501c1c1d00040c0c1d81c800c01b45480c51000c0310320 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 283854199 1250 283852949 283852967
    0x1c09050105090409080913020d0f0e0c100e270601090803041505070c030b07031109030c0415030606180c030c08070507060603020a09061715060d0c03081303050c040606 74
    0xc3c000c68450b620308060140b104c08031a40150054a0320b810403880090301c8000303402034914400f000e41016981281401c042c05601030081406014029022a02040000c07a003280c01b00c0006020340790540100e10b54503540780d00d018a150b050300155800818040f0702001c0c800410242c14000351103014803003144004151800e40d8a1340b210f0551f50190b0b000b0580300c0d0701a0340d10040c40b0140800b030110422034110715040c080c1000c0c0c3c40602108104c00e118185034029514203a070540c0c0450030030317101450107805c840b03005c8140c0500d02d12050f480e600c8090039500307d50000390442506400070414150540b10b403c010800354502000b0140640c0c100901030f2001816820410401250003000e010b0158403590055600818a1078040d5035443c41c040500810710840c04144148141e0b400315420110b103071400e0b20619040586142d484000308080c01102050903105180904c201100040e040301c0140002c080c0c0300c6d5403055a52075031419525048244008234000c5052010410403d03402441103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 283855449 1250 283854199 283854217
    0x3020606092208280e0915060f1b0105060a17060a021b1e19020303040608090a0c0e0f091c050c1014040218040c0b030c0706050403021c09050105 64
    0x41e40451445052445040c007134003109401d9a4820024070030302070390208540e0000c0c00c603500d0f04215a07a142c401c100d02201c040702c0030380c1003a041b680141000d16118006010034050f5400030b5041000381c0d81c01100701c20510604070b2183c1e45d12000d21001c0d151a01501d00200082403940f940d80d200c0c0304501c0d450701c6001d824641621b0300071a41400c52200101050b1000740320344101c5086400890f10161105000c11103c0b6003800380c0b0059412241744c00743c41c440001e030090011880d19140c40c00440e03a844000740b405449005140c00180062504030940c0d006156103428940c0314100301400808040014181418692282c441e400001d050080340c0154490141031054860313100301409400d0041070f0512070b190a1800d242c0d4280440c9075201640124026281c10f910844201c5400364242e5007514042e00500200c1002c02c50030204000035035100b407000c0ba0b0642083e00940e14202a644e06031803c40141c0c1140e401c180d030301c8110003006a024183c900e0301a041c0e40c5480006400c0e88a00c03245 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 283856699 1250 283855449 283855501
    0x40807020d39050f010203041a1c0c031109030606010804020a05030d050c12040605070b060a0b03090d030c0f0c1104020c2509050103200315130302060609 68
    0x8a0070500a0903030508074040c08450b00c2d010030010b6001d40000d4004903056200a5a00184000c161070401102e00f080c4000e041e0000c51500e8203004014001e13050000f410700a80b603081201c007413026000c0790203141e80c441144003c01c01c0e80800c0005001e58014076a1081e001d103044c03005403410b5030f0010702190000300a0070051580e0b111030001c00e03420348141e00240d070180314220562543d40e502c103004101c202400815154030620082911426119a01c6042c001034401d02111011400c3c510060b508400003c6c0144886543d81c4120301c45504229140c641c03a070401941612029014010340c4400f032400e180040780400d8000c000f41098030b0422010b1300000030921100d003036884c0d44d41110600304200d4115104110840d03590f42c00c0703048850000d40380074148200060900d056000c1c3c40e05980e03000c00c107003640711000024400308542c2c034505980d061060408248000c03205100040c00303003640110b0f2514401c00c60030080d00c0c06101801c918040c2070503104000d1207108922144c1c510056000c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 283857949 1250 283856699 283856719
    0x2070501171603090605100504050f160807020f0a11030105070315060522080a02120a05120304030c0f03020709060b0309030406080718141809210d0212060f060304080702 75
    0x42c0440040c8004c0c079000305064030f07210074400010400f52180d402c46100329001e111640da00c04030614681400d803441542c29000d451001c0205020301c956642c854802e1044804130001300c7c0b0041d10344001c0319426a82045091400c4d00603040078042c1c10f60250031800c00b07005480d800c202103d100074007441070b01c04200c00400c080070000107400c0201d41a90003118070a22070340e1980d440a0319815840000c034480d0300d000a80c0c03035203400c0100c0c3e0b00c8161074002d800740c60031601800701d5600a0b80001d104508111b80c0c40100000a075034034040001c43d5029600400445040c9512807040301c119404c00300088500340104458000004216070a03030304540392403413031070322504c1d401c2d10000341c0c0d1126035560351660040440e488140162034444601d0458102032243c00000500e0030040082d960040507030840100c640d1078030a6040c03e0a40380d030211102e140341c208034038602d8040340c11112240e06242c0e0b60b80280600d6281c441410180c114003241c4407803a504180d52103c0d0f00b880f86e15002409449000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 283859199 1250 283857949 283857991
    0x705040b04020d02030901020904060e07080601030c050904051806010f140f150415030c0c030f0f051e09030c0301050f04060b04091e030906030b0a0501120e1603030207050117 77
    0x10b0160381c2c203440c2c0c0d15000d5440c1e09150500714080e411000740d00b805545441e1000a22074402101503000748808c1c0c41b980740c0c54071880300440103402d00c80740e000240a03080088030000e407200d11403039204000b018047c007108650b20070941e080450692084278015804182400b02a603003c090b030502000480d05148003003442d0000c60011904418007860882000c00c0006a04a0b1480710a0340d074000b0b643c04005205c0c0b004000c3d03511070f00d10b070800f40000d88421186840d43d40034016612a03000b65040403424810001900300910165030b401c0201c00d0808503400c1181e040801110444c00002c8001b8401841c0c605107940a0b400000c1000d04800e4a030b604109181d00e80350320044c2c52a800610801c0c0101d108028032506140500c001ca00090429000240344d40c440e00c10494192401400d1601181c54807004450f14201030f10f244a00c1c0e0380e102100c0d4160f410811014000301c100800045216265080290408000743c0c80b1905018400c01111030050100c0712441e032041c110244158020000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 283860449 1250 283859199 283859201
    0x19080c1b0f0114042d11010c2f040228090e040308010e0a050103170d0b0307030c05010f05090307170f070f0f050d1a070c08070c030c080309030705040b04 68
    0x50100070196520780840007140194003015148603d00400d685400b0800c03003520003244071035100300403107040e0f4141c41e440002181c031020b01c14070840500d41050510602d403a026030122070021481480c2c4404032880c01c0d000310820200c82c054a04440442c1050744400c3d5008800c0e14002d410103c01c40da8a0441401c030b4010b10303154002e00600c0310180c016140900c4d01038601e0100780154201010040300081c0d03904458001d450581c2e81c00b8007031602150100c101200b0a400c80346078568400c1d141c00d4441515102000008001e43c06003c00900d6585401e00141400602140321010132004201c880000e46001a402040300d500c090895040d503500102c007801e042d166071600d00c45001d10540040d064803020124015a07065285200b52140d94808001c240c440100e40104140c0f00784042e60141070840c1d000740c2c1e2001c214209401c407904195280d448a901081d4110340c503440c0c02c0024000d02400b0b00d0110007420110000b10b107400310000000e80d4588082c40754070300c01d640b80c0b64141940d86035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 283861699 1250 283860449 283860463
    0xa15050105150705030d0c17010609171605010807050702120a060b120a0f031202030f0601090b1e30150406050d022116050301110a080c1608030c19080c1b 68
    0xc440f1023070b429503180c2000400d00c0b462403007030410302c1c0b4090000b94455040072400d42c48000b20418080d4205142c20015100d03071000406031401d000046c000080075031034002c568600e0b0400d04000d0405a001407034010111900b0030003070b1780900e03648050303040600d00c0041e00080c841e400440392401010035140890701402200082102c3d28004006c0c4491002001c2030715000740001d8030b070400e0240c0c40e040c0c030500034000c1ca900142c00a000f5004c2c2c0c220602603000500c0500d0074841000c07034104d0507480107c402c2926101c04860300c0150002c10007460640024011301c82000c44003400b08030b1500001840c61420001c010b48030700e4001d0001d0000c02101c00c0030050056890b0141c603151208254135040701da20a00c03c69010794205851310119107030034030458034408043e4883c0115516001000011078003c20542c1556805104991b40490f0401020314810346083c04065907410030402c1758a00200d0360641038051040d031405108020071b4241c1a201080e920b51440d04001e0854030601d442c204c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 283862949 1250 283861699 283861727
    0xc0d05070609082b020f090103020304060b030f07030c150e04020306040f0509150f010e070f0504081204080f011e02071a09010c020d02030a020d0c02030a15050105150705030d0c 78
    0x30001400403090851002e9580c13001a40c0b99801102010440c0d0030b0060340300e014685480c0d003001b040240100c3d03010743d01550300f0501804001800b6000751000c60b140c0404603c090515500102040042000e00001c000141c01d50f00d104d0401483c55560141c405018000b442c1d02c0340e0b4000c40003802a4995a04ca02c4502844010603c854104180b009c1c6c0c0710720304200f0308050000114001401c016107101308504032240007000c1c80b810b0741e514401329105c1060761181e03410481c0400c030008440c4e104011403130000318408841c40d0b8591412880628144105003804010390400307155034005c0b008100a9941c055160001582c4c0d00316a10b0200c983c02c0b403120404e250341c0641402e00c100c2410552102c0e8601c25503408540e06042111000d0307980c0d00595903011300581c009000c00c603203d4440e4490422407880602111030080441c2ea40755010300c031802c0c50012450741c0d000108070a1820b81c03002d130990803407110040d2070205152943e9031a8800c4a801601c03050b240c00c0440e101c13034401c46041150f12 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 283864199 1250 283862949 283862963
    0x8070e090709140d0b0408030402190e070f0f02060a020912120c06100e010303181211040b06040b070605040f0803090a0506010e0105011d010228050d050c0d05070609 73
    0x700c0c0c45280542903240a0284448440340707143c0240c01070402d20403030074110760400021640c6a5696a800c0f159a000902c02ca8124400142c4a0110000190f060001c0c0060701d86110302407a00b44802440c944e42c084400040011342e1000031200398001c0382c0b4035004a00a0805aa40c149850119920640f0010031700c840744507140c101c54030740211381c010b01003d60001c8140d54071515000e8410359050101d02480a4425408004000080c0503180c0340500c00d4100490840c26551a807140804280e990410b0360305603030746105cad0310307980c42c0510908030119022650241450304010104809009074800200320b25500d0021805024070404c0d60550300c2e0b48820701c241d40c0e03d0700b2a503180d200c4d013080004a8280c404c0000100d414501f01071818142d0b44103a5484603500a802d1218008803031102c039182c158001c0c1c8600f5024507641700816a440c0321480310303030100c4810314907002c1d180c810501e6941d8104003040c0000040701c0804030b9844140150b0f0f20705a51101070a0070700000500380c030700c8028541 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 283865449 1250 283864199 283864201
    0x1080c120f09031c02180d120e030106030f030c03020d021903120222080c060a1d0a0e09010e12030c040e10050619020105070c05190f06020406020304290a08070e09 72
    0xa440680040603140c503650401d800c0e6041c41414000003145c0c402c0f000b01402d000723040742d1711014420329819603003240c02000400c03503e070b498558461201c04054149d0014800550300428150100036622401116200801d61011545c1040300300456180008041220004c400c0128040d640c05a540412012440b00014000f00c1b020816021031440741a500d0f0107101c2e0f090724186898019206094102d0300d6107481c8030300703e0040d4030302180d007440c540d50302181d515004110600d0380d03220b00344104101070000401280c1c220103140703084107014403100303004004c0040040009100055030115101080340524a4030342d0802e4680c81c000e5600715070341000009c256001c21400721138440100988580081001e500ca1000031180c20404003030141c01740e030107155061508480004988211030080c3c2c15102d1420b060b6a515080e40c0c460b40c80340c1c00580c004a01032081d015403c49010440c0840c04805101c0600700090700d40303501400e5600c07001e20040070006802103004180b41081c2c0f0340000e003039481c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 283866699 1250 283865449 283865497
    0x50f1b0906040f141002030703090902030a18150f06050f120f12040e090610031103010e030f07020f030a030c1106070f06060f05010c05060402120a0b0405070501080c120f0903 77
    0x4840f0701c11031382845a1210021002540e0010040703425154142e9202c07001e42c1e040050712006984060582c5400ca680c0d000100080c01d5080c00340240148034a10f20341200008419540984001c4290100305a00c0e00c00300300100e81e202c00d004032000382c05542c41e800107400711051034100322101d00b0440e054003c000b05030b040851142c0062007a03500c86c01c5c068a10391501c240b210b83e1000111030088131106602800d00c08500d180ea048202800d004002041d0000413a0b040d60864001074004c690142d030200b1440d01310700c0d00010b0038140035010343c001c203180788c050340b40140402c80051740034003c60800448000d903919144200c0b070b082a04566400310801640c54040010541e500c11481d89140520b80030403a503225007903111401d6000390040441d070f11150200040c4540e4401c1070300c51885454610400502e0000080c0e100c0e5020300094440300d49028005800300d00d0041c0112a164407c0080c1c4400700d81c44520282c028041080c142070941c0d0b4516891310750302c2200210848125900c0b44458 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 283867949 1250 283866699 283866719
    0x6080607020f0106060e0105090d0809040c0921020d14010b090f1603052e17031b0d050d0b03210a03060b090306010e0408040902030712050f1b0906040f 67
    0x1860b0000d400080210580c1c500040b034000074110318290000728204074000143c50a007015160103030044507600d240049400c0090300b00c5880d050918086080c14030100301404a03544094001800c2c4503c1c0100030206600054110480300001020001541012110184258001e04c202c03100504008858182242a820394031000c80d295440e03103212071091528103200c1d014082c05940078101000c1810ba03c0800d6074541040205801415540d8000c00201040b021094400600103030010f542d0366101283e0100d0b40107405180d4035013943c000102081141c1d40304086030804400720713000040c0880301300b00080c2040c20140050140461480e0780c031010403030b0a070051545503021388041240d59581c04498400d4000c5005540d4180c002070010405142140300c09940581303d601401e15240d11442030004a810a9558400160100c4c001075240d1145101d4903410030320786030a80c00f091404e000400107604001000c01450345021411a0280c1c8850060350041c2101e040d600c08100e846825600c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 283869199 1250 283867949 283867963
    0x120709140a0b040c050307050705120d0603050d03060f05060a051209012304050d0e0d05010606120c0c0506010308090d02060315033009130905100615020a020906040608060702 77
    0x1401d862a01009000d83e19041c0714141c51100c0301d84940381035035504441038400c0d0708924000e8403e0301074488a04140403012000b880045040100058100d0460a100c2d1400c94401d030050141880c2150034003c2000d4030391420100c4034125102e43d070f1101544001c0700c00e030143c1c04040c482c2c103d00300c050003140c070f07410b4215001300712040c2d800c202103c045007104901800103540103412500451110301c5200d104021642e00d8540190281240003800c2d0345503400c4580d90360040c400581c00c001c41960b100614001e40e80c8086031850440400600c0d51a401d4548106200051482e00d0000740c0c5000303501d44003c603802281e001008641c4a142181841403140f15100069120b0f010f0915034803542e00c0080c04c0c400741c1e8800004043d0403040640c3e50025507500420b2150752100e81040a002d01d4079441c016016140e102d60090f008020458079120b00740c4003d60000000c001c00402d00000a60303001070141e90440d0102e401110700c0e19a078010600904083e045540140544030411500d5a00000c1031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 283870449 1250 283869199 283869211
    0x60e1b1c0f140d02070e0a09060b090f070207140f011112040314061b0403030305060609090a140603070501020d030926030f0609010e060f010210020a0c060e1b12070914 74
    0x18810443c42c032001240c4034a502d000d030036080085040410210004c40d402041c00c98883d5030005140c0e085180040e555200c100d83c1840901142d1041212599040c40a50001d082e4441c0305a10040a034001600294440282504111910120071000300c010400b81d541140e408a41568ad10b40340e0400c850303007000321500801548a204007080542c6100b00c1c103100b61000c0381e8841403c0906554044000c0e213400b80213140d00150a02000126540d4800d41501540181c0300c0003401d86296104c04203e00001004103219420182c0100700b240d070041200101308081d40f030700056051291030005041c04807920b02703c0154124004544c1c03600010402580180e003442c02c03c000d81e9489500300720304410b00340114070115160f4808a141424140000c3d03041d000140182c07022000c0c01005801242c0000001100141418000609102e880d20400030141b03c0000603085410300038041000060941e00c0860040c408a07000c00c1b4020030510618000c0d011614040c840c0e03d590800300c01040c0000e540c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 283871699 1250 283870449 283870453
    0x50a08010506130b070606031b0305010c0804170c10090311070b09130c020f06090c0a05010c1e02060c10090303050c030f011e0905090307060e1b1c0f14 67
    0x82018038001040d101d8812500010080e10f5080195200c5250082c07481203d141d03488000100c00911210600407040b40c038a001031441500c3c44c04c2c440d00b500c032090130700300c1070203180700034400030400c0b502c0c110b81d501140d01c1403030b59100002e9401929000e4002c3c1200242d625080101d410540c0c070102e280401d0400703200b12800c20b600c5040c498964071840054984c0318503424503807680d01f138441d00078034004403141c01540d6212400c10480b6003808801c5032a51030720b8000804640070743c5001d400c0c0c1000f5240a107461000e40c02c1e2075498009052a03410b030442d13201c140c0c40e440021075903100101e0b0055140d4106030f0782c0c80c001d0b10001b48007500c405003040340440e003002d000429003407951080e00d100d1021820715000c40d9181405904060301051007020b4080000d22000c108500705e8041c20b4052803443c40195650051410400704480e403c0005801982021030380030407286d2040101d01c07405900322800304004d1450401e42d10740d81c0062034001c04108203041c0c150b09210250501e07255880100e01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 283872949 1250 283871699 283871701
    0x20190f0509090a060c2a05120c0a020405040804030804030b07020c12060a0f06090603030e1e1810091107020415060f0302090a2706120b0c0309010605040606050a08 72
    0x1041107410142100e0307510782d66019030200c1000c1401c03900304009941c1c081c00c1c003000b14904020181103100d540f4042c01c400881d0b03648402c042001c200300c40103250054800b01810400d00c0505551240d28200c4080d2141d034466001c42c1c00c0c00344a804031030003107030700541043c1d0355556132a05003080b1900300c0300c040140c09204104100c80c00c0483c80700341203030280000fa00140d982e141112000300303000303030258003001c1d0780c1d842c0400c1e107070b4180c4070b001c2c080c50098031861a01e051000412009000510300c3c1081035410030b0a040b400c5d1156454040e0004e9000010741250382d40000c8901e001c0e0300d0358400180282050825030b02204008001e01c3e645000355418030040c5480300182e680740105228401c00945e450516403945032180d17014005440c1c0090046907003030340d2043c503203490141520141001d01150f95440640404a00c244401400003000c00c510946040d107501d405030000809032001c868001001944c000801c0d4424405004018030421000d510317030b01d0050854200c0c859043c04200302d40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 283874199 1250 283872949 283872959
    0xd0e010203070804061b1509020a09060e011719030e120a0809060c0a02130b010801090e0a03030f02120f07170105031903140f0702130c080420190f 65
    0x442140c0e40c1e1600100c00c02c4c42d20380b51440482c2d0061022101540c003540d00002ea4001843d190000d03800040c55040c0440d11501034010000c80045540c408a41285802e20802c654603140075054115410b41044003404100c2003405403d280d0358982c4010303858489010fa500b099000062400c0b1048d0a5440c2074a01e002d1030b88465a80b0803201000c1c05e00e84003445411468500390000700b910074114030540f0f202c4001a40802c480c035250040c0324071401e8440c40b1420095070b0111034a4018190017038103020051803082c81300c0e1501c2c844000641099141c4000c8983d0b041c00342c040314003000000c41d02c071a0a07e440c420101c550751050f0354000000d41980d10345a000607030030709040c2c180c032001030260414001d00c04520000f81041d0008070280110003107078010131903201015292504809007081e64429181c410004900c50b29503544401501e0164462041980440310350751269021a4110220781010a90342d210103c0300305160b4450800780098003840084090842116a1020b5880d8165155 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 283875449 1250 283874199 283874203
    0x18041b140d121202030c09030c0a2904051908250b070f0804060e0a0e09150603030d060b090a06090302060a03231e1005130504020f040903020d0e0102 66
    0x412a441d034089201c0d2500c1c00807a503000c401c015801c41c40d00f841c08aa400710b5101c041031380c00c1195103035400b0342e0100740790f070315030074288200c20950300225203040201b800c2505141000d043c03109800c000001d80740701490b031040321404440252030010305031151204020f03004116000d0a0081909034040c001d0244000315200d001c070314005034a0010070000c0e80c103000504245401006040d02d056404e00d0b804404140c6080c0204050300b280d81e10011401018011f04c00451500d60006101010b20410040c81240205407045030302c10b51340300010140c880100080c5140506009884030301e160800000d26420500300070040c0d0801520003010440d075a180c00c3e144a140f61001a40040c420022604405d10945c001c14440841c503100c902c40b104d5089080061600490300c088081a11105c581d010b2803801d2030751980441604035072070750341d801c05000c100c10032241d18141d4149900c41c0041000c545d60034111404d0400b002d441000300c0d00303140c14002e660f8040c9110580100d0310185249a4039440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 283876699 1250 283875449 283875479
    0x31115030c0a080406150602061008060c090d020d0606080c0112050f190f090c0302041d0c01180b030c1306080103020f10020c0a030b190603050c010c0218041b 70
    0x207428449410210000002d45060b1801441200c03c60740d03c1030179040f0640d0540800020b455550f0040002c1d1828140303c00d00401c840d002406140c0c089010000703401d03030801c11940c9880c41502e01d00741003032852002c5504e50703094590050070f003414044042004040080e049601070000d990354448004000216001c55009a500784240c200c0d14002a6114020443c1070f482d61b40540800140080c503c02000111034041904035041c81c0070640820075071070300b4040d8500402c0314030401840d00b00d03008001551035140224150600101d81401c9a44220301c1740d9900040841c4400a5134a140120318610030740d00c041011a6201038004011908074400c0420078107036940900344a801500074000c205901d104000aa001c521a03003d0140342a25909440001948075034500c411908020400f060f401300c861501d00200c601e052000c03c0850300c000380d084242c910030708200b081c10740140049005104a08008000354000704240810080090005980845261a07400f005600c80002d4000301503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 283877949 1250 283876699 283876711
    0x190816060c0c030609021507080315030f21040e090309010f05030906011206020f0a0305190b010c02060705150709030203010b0a1412030d0f1a0102210315040603111503 74
    0x507401e030b01031000440e540d0100395901e0004084040b00c00c4105408483c50b130109038105c40400c40441072041c0c0c024466107000740103c04030060103d81210400c040d90ba4800d01ca243e08000a40040015050b404d032030890f0064203120300c4c03c01051030000c130307420399036441019280d0018450000c1c012034103214200380c0c0e01405950024082c0c0345d1800d04da1004507000c0150039540c0b1030b0300300180355241030300c0750041c61824200e031408138591801048a0022200282072940b0007800c003500c1540903a0b110340c80745203c40c2e044445640b1543c650a0a0345031500012a19450350304540034841460782110784481201d10840c000d12240d20010f00f03000c041c400b035120305454000c1c00d6250041504d0004414800961490201c906140820341c00c8803e56000080c0c52940640c0d03030810b41c0e444484103503005110780c03080c0000c05074100306c0400c2002c2c580c0d15400c0c0d4000c00d4408008030328504800c3c0700700d10400d030700200300303001030f98032800d01c0c003420020284e03050f101c1c000d402e00700b400352000300c000d0300c0c4185 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 283879199 1250 283877949 283877963
    0x10b150c07140103060e040308060a080f0c0613030b0103080c010f02040f05060715050a0209031204060503070f020a0209041202060708150103020a0507020604091401081b0f190816060c 81
    0x1501d000b90310031000301580c1d541418540ca6a0b0040707550301d4400361003440345000340d03940482402d0041c140b00403000650001c0c1425000b0032400709810100103803815190074265125991140c1401d09548800a2a04020130240c00f4800000601180b18060320000c98481c0003003181c03c00c042c0e40342c0300302d208900c14940400b8151004001c01d1800704094005280101880021a005203030b42204558045920780700850340807440c4070b440c0c00c0030030003940e941090f9190b444c58a420f0034030241944c00014410010440c0c441d100202e40782c800d0117000c0c1c800ba4054450307030580c00d091a14a100c120081943e05c01407081d10002140300e84202d10b441c0c0a94040b6000d000e880c0003100045001e980400000d80500008020381001038231070600410042801c0100022490450203103175941c0c03003040c0e205410355440304104d070001c03503844400c070440420100d1f91070b001d8000c03140200e0010a07201e0103007403821644c42d2001034100d6000c100080c6854240500d02c00c415203502050341c049034485405480c08d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 283880449 1250 283879199 283879213
    0x203070e0a0f0c05030108010e150109020310030503120402040c0f0807050f0408060108070303020105130b0c0d0605060a02010f15031505090102040b0a1e03050f04032708010b150c 79
    0xc02a0400c0c401e800c4440640041100e180800c0700302c068400803104280090300010041117808800c0c4621340500700200068440d030924107050103800c101c107000300c4c034009a0000c04150b605140b6408e1000550f484400d481d169041e2141c0d0000d4610210b4099004904107028120030510801e2001c1c4940c0094440f0310705e9480c0c5000c2125160489403084030079450030800441e958804010041c000c003c62001000744501318a4000e0031350784003502d58038810b510412001d00044020280e00c2d88400c0320340003a5118540000081d014008541c00250030200008200100c2541074100610b00060a401485400c20101c1d0400e00c0070558030002d400414a003051102c00151500a00d4010034410009030519840700c000e24100d9024009501c00300e042c5560545e010307a01819035062608680c18104540d203001d2182100e4010001c03c000c040203000080f000b41e41021100360308000c4a4000a102a503032151003040c0203100400030380344101d09401c841c1c0c8403020684200ca880901e50130183c044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 283881699 1250 283880449 283880459
    0x12150105040c5414060d0b0f090a091202070b07060902190803040801060b030106051606141807090504080712051903060905090c0f06070204020d1503140307020307 72
    0x22a1403a00c2201251452482c64074000340068120b112408103224043d21400c02c2c51040c0c412107030680d5000790388070340068030701102a54a070f4007034964207104030b02c01245c5107000d40005441c00301402c1c00c1c6580107032424240000e40031198000c00800340f0600c03039460824400c1000b1381e41c0b03160311f10501d00001010000c80001032100d4105035402d500c090501c000308503400c03100072595501c0d604803840710780c0041404c019082003400b030075000300f45c6490411720307550415000070040d100380c081d100c41c00000c0000d510108886584007100740300e050340c3d5000755030400f101425200105040644039502ca003030404200c0d121035208090040e507200444500e400d01c00c2c1e84240101c001031b1540c2080c0807051010b000003046d0660900c0d20900e03140e50001e003041c20700e00c031001103030009001c003101680003131041c0d0f0f200c1e1241120380c130b0400030840e4103d03201d0b0b030240700140289c0304010075040708904000702a80002007180204e001d481c416800040400703a40a00c1d155a400f442201035030507884043c007008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 283882949 1250 283881699 283881737
    0x1b120c101b0e040207020a0305010b03071703030408031909060204051e0a142205220b15060912060103120503090c061c1a030706030218091512150105040c 68
    0xc442c05010b0405820541c140d0002030411481d90700a541da651074802d107888914040c01200081d1481124010070020b641398425030340d0000800040511500101003110202e031050310300c80c6450079080034084910389107040800f1303410501c1202d00906210a43c5010a210728641c0140040301030b11458400341352841c7d010340d0340075400c43c49030004c0e501030351030800e20f40c180c01c540d07410b4502010105107400c0c880316520300c101c084034130300075002200e054807400503510102864000c018541d15aa01080000004019118459005501c44031220303055186503408941d145c100c90082c105058501c1c01144288c65034402210050384603049000c2c00310741883e1200142c0488000c180c58010141022080fa801702d542d0310112107007142003900d02c1840e91804001c00d40181a40740b50541c101041483d032100c40f20b0503111210b2007000741c42d00056040100040c0f54404840c0103100c3d40d0015100d02e001d07501d07203507041301801d440c100160010402d424140202281c0c0e04280d5101101d16050428a031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 283884199 1250 283882949 283882967
    0xe191505061c1e05011a1c0525170108010903091a0f0403080909010602010c090314030c01092003010204060f0309020d0204050106050a021b09010303051b120c101b 72
    0x2214983e1025503031154480700300894400101660002090350402542c0d07111600070745801c85401d1820420318840c0c1c58102c880b10380b000343d100d00c00b061980780e89075011411049090485030720f11000031542e409682c0a0500756171000310f40c02c0704500781d0700c4110442c00e80d000d03d20058007052012604100c0c5600101e46a40718440c0f6400c12030070002c84100494142d40994410380c3c44c641b000c144500103240c581c0000e801418240003c0103c5003001e0300c0a0604400f40c403024100003520311000b820b2680c10710407520b410980c003008001108681c500100e002603424000c000780b4a601d0841a0303641014030854040c0c495503281d10b000c030f400841040b806040f543c541260899891244800180c0f191b0080c83d018001740d450b01c0b51501c51707960000b4605001d107865002030f0800381a4641d01d40d210088114192a054507025035a0030800501c0b00c13410f020100518080c0c0b0441e42a500d01040480280c9107107510103054401d1455410030403000c0e20790751019590200050130802c002c1034000d40d0f440d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 283885449 1250 283884199 283884247
    0xe010e070c03170a02070201080601090302011d0f060d050f010f230f030d0302180901030206070204020a02120304060902010807080f070807090e010905011403031309050c040e19150506 81
    0x2100d80600001d5441d01400f0141c034036495198000c00c40900710341e00006c015178442c1c0c007840d058400600d1070300002c15100911210340c450500440d03002c8034030348941c41440119100685056a522051072060340108411121002e01d01d020304000301c2c14045401c02c010440c1d4a600781e6225081128484600d040b01c0c84da44c065020540b83c507544160348043c00800c041c103406440041e01d4075207100c04140503042c0381504a201c3d0109400510059543e14280d9180303030b4040c0c0380141c44201c48041030b45000e0f00120540364001c4040208010000e05401080040d4400e980f000d80707a488090017a60205810381c4d4500786080c5000000c2c4610f48280803d9602c0000740c5412514181c0e1030b81e103508149401c0e0030162626844100600070b801c00248080300f004025802545032000c07994017060240c0c0035006da060019150804220031211a80603180540100c1e03103051501e007051490940b40d9500f580310411244c0c101900001c004800620b1242290710150100e46814142c03d100f00c2a24421456 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 283886699 1250 283885449 283885457
    0x60f0409050a0615090903090e06011718010b040203070c11030322081207020102030f030a060905071205160207050919060e070e04060b0a1214130c0e010e070c03 71
    0x100d14040380c0700300030b90918180510000030350344c001c0b0105081010303840c0e085944510304180c01d403c0002d500030300d190100c85100050030f0281d1941e070b00484802c40c4801c0e01c240d440c100c0d081481060681c00781c480034451100c0340201310600c0d07044188016030004841c01d07408940c04040e00c40c0031541410f0140d8641e4002016a8a001e280e0107c84984a001c1c0000111a8824400c1401420020096600d54208104016042c2040d44c5d000039a24801d800c12403c01030004804698900c04603080036014001001041c0601e01c0c046100401a880000d40082c0d05800e20b00070665030344c10031507940c0940e2807d83c0541062030400003444000d02003c0c00c103154400903110003400402e61485940090b05002080c503940b81401c5100030078088074408041c0c81581303000f0b030070024106800d0843e60104094141000300c1f030640c090307417401400e003190744000c05151030f004c00111880341340070004040c1c4200104100280c54420003d01c450f800d0040c40c20000c84240402d500b2805400d01c9000c50740300b464 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 283887949 1250 283886699 283886711
    0x60319020a0518060304020619030e1b040c0e03060a02070206070602070b060324011205030c07080303010612020720190f0509090312010302151e0304170f03060f04 72
    0x1550022684003008450000d0800318041140810700320140603d01c604071603560460030681c00240303452044a0032840c1e0656a03036191016140250014000211010709680e1401c05078544501002d04051000381710b145025004508540120100445641c014004101595462280c40025880301c0f5080c0d900c42c0701400030030000307503480c0003c140d214400c8019000505000701414a403245c001c1d001040071181c5203203600403d512a90301030440e500000703125605202801c0c810b00390310446142e0030180c00b4044011440d1480000198100e0f4415075601c440d0310560304590080380545070004080901114181c5181c00b00c640b494058410010700c1044a025040340030702c1e404240c2e034400756820000000030401460103c07400e5500450302d0024500d031185128402d040514140802445500321012038151040240250b495141c0c85c103542040001c241003c0100c42d0b082205e04444625600700d01c501601715080540740320b0120f4015050442c1c032844108446848907055654016a60308 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 283889199 1250 283887949 283887991
    0x111100c021510080601050d0807030e0d02030303040b060a0f080307120927050a020a020a0b04140d112b11010b130f06060906050f1e130905060d110603 67
    0x851218050004604820390faa46000544c81c200b43e01640031500c540c044040f02c00114a080048070310565252410061440070b007000507100d0301700500302a402d8032022080008000031f004440b03010307440803039950012943d1010050540c41281c040e200d99a0000c0c003001c00018180043e01c0701c2c00c040c9080604407a51107000150102e025601c0c0c540c0b003002269190071910308517108843e00070411003015460103812000c081c0d620080d038840107022500c05c0700020305000c0029000c000188003041503032039021034001d009100000c4542030035118068008059602c211382c4c0c0c00250b107413408400351803848032800001ea0340041c02101c00910b5540310a8021302c96942c0c13007240340001d0001070b80042ca00900000302004c580c3d558101100f40b01c40507105200c00c80c1c00c10107807203044001000c45551030b502c100c1071251440503501c084090390710208600e2500a01c10503108191014114100400e039140e104004407480111300c044e007684071a8002c1d4800d401e015005540c4582c040100d5400d007c40e40c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 283890449 1250 283889199 283889233
    0x5060402091203070309061e200d0c1a010602060112080702040207200f0913020103020c0d0e10020606010804030c140d03021c0b03060c130b0f07030e0111100c02 71
    0x200c0101c42c0780d4000049020806030131100b0b11010700440d25250360f0381c1800c0080b82c002261820035a00c144070b1070201584d1500d0700740c011031114507250801d0b11049959840050250410014100d8a143e10781c8421580c024611900078107c3c0d0040e4010f1400364680340e00c541e01034581410546800404100e4180562100d00040c25142d07c5070122261002d8802000b80228610000282c4611301c20240006640d44002c041600300d0440d408135000000d80380f005030028850300000d104103009900c20800d0160704040e00d01c2c40680d056500240c08500070384202e031108002c8038020b0210f008040804d01092051559401c0c15120f0a0009800d62910841a02d48840081d01c6000030f0b40005210014541840c1140111902c20386e09000303d1500c40b000903104d040040a49806210101d07005c1200c0f07041090002c010918124481d681c0c0d490f01c442190b1580c4134640a0b4041082e508000e0541d5104101020180c404c2d80003400740c0850744480c81c1c000d4902030b00c0150861203444615141000b05c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 283891699 1250 283890449 283890469
    0x30903210c030a0207050a1712032d040618050d21021303060b1207032009041208010e041a0a0e030408010b0306010e2e090513061d030406030506040209 67
    0x204d8000701000e9141400b0020007100c242c0110300b00540400310030040c0c040000b254005d03a00d1080100361a603a4030050301c0c9c550200340402d8000d03481c5000290f544200c1440e101406240544400c3c0f1415081c2128218000105070005100d40d120030303602005603100b454400030b40301c04c00d281102d182c1c0e80e0810780c50580e009a8603004040078503200400411a85116000d483e00c001d8603001c101884146040c0e440c1e2296210151070a0404d41d91102c00d04083c040200401d44010210751050070036061042040d00b001282c4804500f0000c00403600e10f1100c0d80c501e20a50b400b52144013028245503200008001c003406403901962244010f41e40140203001a0020b0030700c15000245241400b801c2515018060384402000c030280410300192081d210712600602e80d03c8040c00407107a82d00c0081c411000c0960348141141031502d07003400302c65001554074100e40d6000f05424004240307051805141880c0810000c80c080e842040100b20560180c0c202e2603121500600050408000c40042128040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 283892949 1250 283891699 283891717
    0xf010504121e0c35070e0a0b120703030e06030103150b0d0b19060e010506030615041e0315050114010309020114070c0f090501150804081e0a02010608030903210c03 72
    0x1c0c4d40090300b01048050004058000c0c08016642d5420882d11403d40e00da140700d000d84642d58004400003a840e0340c0c25005480c42000240010440d84140300d041c1da1140c400d400110001030098402c50aa8500f040540b4143c1f40c1248150144500c2e1055034801860006089900204c41d140400045000001c0161094945d240c14041e5442c0c860304640c215031003604007022010341c450051103261070f14000c1d281d104130251030341014070180903034198071070096500c034010610304e41c2c0744440401020700500041f64031881600c9403000c2000c0c461000d0b03034424020090390000314a801c105640c465041907d2080c01030400f050301d002101c0c04040942d000990a540c0c0607046036041050f9154031012200400c0040d604021550501803102d0005921051480400c69031300c02150038850490110350f9100c10504400311901d180f5200880c03990007621403031016520b04080015030020200031a20a07560007400380074456400081c41d88135284c100c9682660340d00600010210041c2040281103880c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 283894199 1250 283892949 283892969
    0x60403080618100302060708040915030201030b030a05060403080a1d03120106020d121a0603150f0613030210020c090703060e071b1104110a030b0f010504121e0c 71
    0x1150201c2481007840841c00d003050088450010414080c0c1c1103100384040e42c0e811034469584150a040051450240b81c010720b00c0c5c2858500790070b5140d03590411140890f40300b80c8003404049d01000405889003200c10003c3c11942100c0300041c0000e101d031034502d500c9285031300c0c0020b40da00280c3c0d071a2112076001d1440710b0a54070025000c50004a84440716004100d03602c001e01d0070f80700080d0020043d628600c9500301c456103d1404001e11070106403240c141400c09007400b926403070a044c101c0d442e0401c00002600400c000d4403034600c2420800b04031003032920800f1307200701e01c6032442d42440b6810540710700300380840c0a0490250607956503c22817a0041c0040c0e90041030280c103004485155441c09820070050003103441600304000320132407042a409420080030003c0200c00000704000d041c8000701603c40c0500080d8060280703426a22101030702030183d4038071012a906800640755072065000c0e01161500308415a000144240849240d240490035141c0c0e00c040c0030b503621200303c006500084002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 283895449 1250 283894199 283894201
    0xe070c030201110a0c2001120c0207170d0909111e0d02070c030606060c03170402190b0a0201050f01030f0f050c040612111e01030903020f100213060201020f0904021b06040308 77
    0x100c2940d51581d205081511006e00c10000290006043c10554504800c082e9461325000c40c80d0364000d002550040a1004000c1c08000d00d22038001d40b5003c483c0681c0b0042504d41c080811420b045100e6004900185103526207031540039040d420b104c455146003000c61001c10090041d0001081c00604020b91244c64100b880d81c1c150318010003558440c0e0413070703010001c070464407070701181c1d00000d03d01e0700460320010361038151141c1c0003023070304821840524505101c0c2040001401d4000f003000781004125a8001c11064031807585004416134280700207410081c0a035031203c00700e54040300490b40720740306000710391100c00c2e004042019200183d06c8040c0256403411f29000740200f101003040794000844103892003a03603407080305130020707000d0503a503040580d501e00c8001050300030820100c500100d842180d4442802d084084080e40c8a0f40704000e028800e0040021007900500a85040e8010220402e0402285a06100c001c0d0803c060040b4400c9a8489000c070402060290500890180d0388204003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 283896699 1250 283895449 283895453
    0x91504240c0302070b0306040207020a062a11010503091603030903060e011404080d0f09050601090b18011a0f13030308070c0503030115111c090501090e070c030201110a0c 75
    0x811601211280d092008401d64000001d501003540c01c103031080350980c01d0300c903211440824028050321500075000940c0c0c0340702040e082e030481c50300e250000c00c0ca55450140c40e09403004c135201680c1502d000342010400300d401200e560080c0d0185501c40000030880d4801444400b170300040b58155441a004115000820300601141d0b004902c0b80a042000910084800403010420048010000741c642040824030304e070301400640010342c1507110b1800070322148400e0b0400075251002840b60301046031501c0b0041280e810501c03c0003139803040c10420240c1d160300c1c1c25052070f0300d511002c1c241922444200810302140e11008040d106400414070000107060440c64080c0c5030701340c0039199000b40104c1d14030007130002d500081142d041d02c40c61618002c921028000999901640316201e280c20b0042d00e05e400300d9034003038807820002e0304015a14414407564071030055500b07404038021007400103910700000d80914026100050003d101344000a81c1c0c15200390a000d0326005000e03100d00040e0300d0314082c41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 283897949 1250 283896699 283896749
    0xc0f080d080903031311040c1214010506030f150904140f0319050c0312010e10090b09040b0702070b0f040503100c0504121407090f0f0b0a0b091504 65
    0x140e000c040341400c01160a09030541940c90000600320752914a65482c414104611509216840b040150061000b850502c00160030061043d00301d83c95a842c0c0a00821000c03041c2d0071355812210085c19841c07450710783d01403440b0310020041080700d40704241811180ca40d116008031520a81c050004580e0282010800500b08000703083c044c6d42c1a40103004034078004690521740a50704525080c10f5a8031543d03806942c2c00d502a1500407885c48007188000035070501d11a9080f03100d81024a040f407841a22101d000701241e000200d05c5800c40c0140c1e002800040c2c0d0142965000012801100c1c88141c0e18a0450304e01c1d808040c41c0002c4450100302000030b4201000344c080c0312014400c0c14480701100401c004c0035806240b10340001a24001e00381010b10108114005d40109501e081daa82103440e41d0340c00001e021004040425140f8119800a440b90703544500ca0032000000c24560381585400c283e0700d51a0400d0381410f034444610741d00300c450b4000840040004001c003004d000030313118151050360 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 283899199 1250 283897949 283897963
    0x3030b0307030206032403070902091002031e0f0702030a12022b0e0d050304030605010609240e18090a17120a02030703140901090b090304030206091203070c0f08 71
    0x60295001d003034240b0050307a511040e0795201421414801403200858002e22004610040c4076805003e44503001c0b510310030300d40013804020010fa41c0506143d0700e12a04036901d1003070034684100a1400d0030503c0d82c50009000500704c98405003030450400034a5000079040250200084810b14003502044181c3d980600141a02141c80841e039070745150038014181041184030f064504107d918440c1c25080c0d0388180c00320383c40c00e800c081103d40f45e94a074600070008200a010384800305480b0800058481284400e07070300040c96030300b04000141c40030320f41600c0b120030002c0d000c0d5004000e0b00c1d12628403115001d00320b1080780300a00a048100203030510920030f07035588040c010400002c008014040501a00c3d26800c543c010400503031341c1d40e480a00310000d242d80001c1c43c030014444000e010103054150810001c036802800c0e004d8640d200d5004d040c1d41d80c4580d120094002c4001c0c09030803001d18081481c0c0c0c80c00220781050b03a18101c0203580d00b80c003c80072608030b00d0300d8001e601c109100c540001c000c82 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 283900449 1250 283899199 283899221
    0x302091e090d05071202010e06040302010510050f060d0c21051b07030f180905070e01090b0a0e04050408130b030114010815120708100603030201110301030803042303160303 76
    0x1d0500d8010700b020040c440c0c0308020740076003500d03403e0b01c0141190b4070075400407152005400950b40b090900e4039000b0b000e040140e03058400c1d8403e1801c04600d80c500840b050142c480010704a034a810544414400580282c10b001002c0c0700e00c0b54401c012048240b02d0078030701c4820103400003c0514000e02c800ca0420802144902100002c4c440c91700065080300d1281c0c88002d0ba8107110040d02a014011032034041c035904151000380c1007030280003009030440d43d800b6407100241c07076080c0744649031030451042e80551050100000d1700000200c61034202603220680050060110fa46031881e5100c0c07182d00102d0341c0e881052441c0c400401041504406e40302800c5540007441c2060b00c0c2d003400072058201c00009814184100410388049042031010807404004051443c00d4810080d100c2c80702c000100503a01c020307000755080441b81c2c00010404402c1701c0c1601c0c1d0200388181580c60ba901d8801042034110004080031aa003042402d42d0101000641101229207560100744002032900400f0382d03d2807032007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 283901699 1250 283900449 283900453
    0xf140f03120109090f0b0408071208040501050f09030301140f030d0503072a03081906080106080c12030a0e010513091a1f08090102221a1801030f060302091e09 70
    0x1c01310018640c400700c510b8280e0099060242c0f9240c90812400d40c0c403a248004002d0061038201d0220740d80c200c41e030507205a0080c4000c201070354540c0b9015540d024101c850760116001080144421103036515441e0b00b5070717000360018108000301c9010a11301440501c0003400b00c1c41c04020419005c0d4000c42000d142c0780c001d4003046644c0d81d80d50303100c03161106070b40005080c4150540010110203c03030350320314801f40c241c2405200d1680c1e5803541900030180c5010b4210f241c0035400c0c44008900f050100202000c00410056207801c406610032180314064030200f03410010204500344101c0c680b0700c190b1001c2c10081d42d000940100102c40e0441912002d10100d0103002c2c0350b2016543c8012020080204500e2030810608a0341c0d12501c0b01c0c020702c205000c0314040c800807445d610142c11850030141c1501c07805450f4107003800c0d040208007024004c01491461840d074491040c101c80d4846d80007054941e54281003c070304240c42c0d900080ca01c020465071440d00000255100d20a60313210004160450b800c100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 283902949 1250 283901699 283901711
    0x100306201e070b040c0602060a0e07030209040201020307020607060b0a0504060e0f04060b1003051506090d030c05071805040c09020a0207090902120a030215060f010c0f140f03120109 80
    0x40c9044240254a454060a00c40400c00e0060003000d10441c0c120316400040d035041d52405140041d5914558015500184103a400055040542e40710310f812540245000f44213a515542c200301c41880001d00803811800288040340c010b0322501c002c0c0070498414840428000b07565800e1200e00481540030921030390910000f040451010880c0c50b420001d40e1501c60a00d81d0355003029000b404000c0d180382d4000200c5084144200d500d5400540200c01142c1c140030f1520403401044014040c001c2032943c4950304940c8a8000b901800c80d40312914450401c0e10140d5940b095030505060210020298a0780c8400400041011004011000e07003035007103046007081400d190003035461840340a2002d00316994050704003036543c0d200401c244079200000b2180924180c0c90003d4403100214459811181202c0104045183c00488030109610607500c48100c59241d03198440c0c0c080c0d09030000d5447c01180704a85482050a22000c40411034020086a865508484100c08000140c0c008805280f80c44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 283904199 1250 283902949 283903001
    0xc0405030118290403050901020703170904180203060105060c0f01020403030804050c030d1e0c06020c01021c0915020a0e030a140d030501120f0c0914060a090b0306041202070b03100306 81
    0x80d03c0749411a42500c1c0c81c0b6103030030360f03600140e150562540002e0210125040f0007054501140000e00b840035060303409121034aa030050800040049200080d41034010f20010700c1a8142100502007030301100b012106403062102d82c040c00caa1043d00190002013191041006000c0c042207900008241a401096000c0c11100000d040d12002e86155462500a00e4000b01492003011913400543e00400e0456881c041c1c400d215000390300083c4c00c14915034244607100002a0203108552a080e04001030010b4041c0b207503405402540f0440c01c900503c040e020040300c07580c50411144010034481e8840d40c011446c0b182480e03150a003001c080c141054100300c01481000ca807450a014038540c80b00c040c0500850b64a0081000b84040d0040c540c81454080784e5483c01c0304104126020700d10503108480c0d41c1e500d50240c00241e880650180ba0168801004200061030a0303e42181d52802403040d10500760b110f40000c1c3c603613402600e1090361000c602c20709006000c542e2041507801d03140007441901d142d2040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 283905449 1250 283904199 283904273
    0xa17010b19170f0c070203100b09010515120a060315061406070507032310020301090f06060221041502060a0507030902100f20032706040e0c0405030118 67
    0x8115581110349800480c04d031035100403e8580c025030080503607903e140350000f06001080b10300c2000b0710035080340d0000103090400c0c0352205040c640100005141440381d9255901085d030203070508030b00d99035612707000002ca80c0d0880d1040c0b12100c074550108402d40780401c1c2d10b0300002c0c1a600c192003910108043c0700090b00000f81c11007100d60240c2d811190f5150483c400c0204140c00c034000030b05000b40004c6240244680d4001c40c107846c008030017040511007610a14003150041d005501c0582e2000010700e4070410314401000400c1b0301042603610303168503402c082d0391031000da20320319004d64003180c28400003005d180100350b4010300360310b02000011071a40019201c070000b50410814000c043c02c0040211344a10000d1100040b00f00800b5001161984d020f960b0354841444a05034007010651030039400c06003440707011400300092000703003050f007054101003410501400818505600300300000c0c1c6a1820301441e40c403403202d04d030070045040362801c0503000680c8041850000036684a0450000660 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 283906699 1250 283905449 283905451
    0x9011218060b030c190305100c080105040e010e010e0307020a09020f1c02041203050715060807090e071518060203030c03070806010e031006090c020609070302060a17010b1917 77
    0x441000b02d80900308401090a00e80f480b001c1e6900326046500103c02048002968001c0324810011640002d85020344c090840b001546031038001032a21004004501c4c181d0015682d80440500008101c0415003580b421034683c0711a4201c2d503007000c5100c100390b14040da4410000c1140380d03825841e01071941c40707812440c40b42049403090760085030203075001c8442581c16680a0704d001c4030300c130b514080c0352308014002e600b00d000101c940c14242012001d010f1001d002d00000c0340e410b40c00400f00b080c01d00d01c021000d40a4203110b440f192140c07510008644511716410408070803d902d03000748030800b481c0304050110150700b14100799801002400041c080050450380e000302c51746801031042e01da240049030040341d2010141d42c14410f810002c0007000c0036074805412204010720401612407090400d0782c444900b2606004560400c1104001605041e001040c80c3c0c2c9040c5001e482e100380400c0c0840c5010801c0c0c001c00848840451810844000480c3d0040aa0458140b03110078250019440030205c40c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 283907949 1250 283906699 283906703
    0x509101d0c1c0201200a20060c06040206090607080f0a0318050c0f0d02030d030c0e040905030712050f0301180f0528020d02070503130512030307140d0e0309011218 72
    0xc94604003d0329298503000524120b45114207540510601f410b15140215584024035186c0c44440c0d0488520300d0500200c07984103412002514003035865408011040d0007d1500701d4211004211502c0050300c0c90008007080c00e004503201d6200c0403410303401401c941030615480242295486000045170000402d401081001c481c0c40d0424030504d0040b4401400c2d1050094051003420f000c441c0e21ba406030407103501c0d1006503a5000c1544002e00c01c010070385a0307540015115800400441000c1040701c00960840400350400500d0200d82030404140c60384240d00489065500e01440000c11440303000301c0700954010b0105101c00d080c0000c0b001541040b01c041d0340300e1070303880344101d8910441b0b40d0143c69002e115404115214510380c14096143d600420221004c02c0321141c2c04182d030300d4005405440ba0301c010000350304554031554240c40344001940107004003039007880815100d101a00a240d07403584220040d64581020100160034401000d03041d900c00741c18640d5801c00d0070b0424002c681495 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 283909199 1250 283907949 283907957
    0x10812031b030c0912191103010212010305060906090304060f0e040b04020406201504030c0f050d0f080907060f05070218040506040201090911030106030509101d0c1c0201 75
    0x1e19588400300304140c04444500203540c020040140e4100e10308040d0540c068141d0380c050102c2024403105486170440000b151640f1820700c4154045842c0150340c0010030009000145040402a82d22001c40c0d400d0f402201c0c90f6010a0401040e00000d0041c6900000200c00039400c03d420448050219540e030740c0c0d58420070060f54268000da40e140d030400010520054021036440351210b6008281c0d004464ac6024058440901d8403100e200015a20441c0c480132801d400c41e030340360707030b9812030381403039808010b440681c42c0d2201d00c0301240080c4070441c8e01c0d92981e22144000441c0b0880501043d200070711220355500248002c005161b00320703006010200386444c0c4160360303942910004481526802080b00080d02c96403c100811000151941c004d5000342c98104d5500d903a101013a05442041c0006c80d1400f04c203100400035140607401c038640060840080c0d4150a0384801520115440718140c410301602c02c0400c1d4409850500c56841041c200f501d1035464081c0b0b040c1c654802c1e51000300028108 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 283910449 1250 283909199 283909201
    0xa02070f1a04021f0f0e190e070e09061e060f0406080708010504050906070809070b130303020c0910141507030f0914010207170106030804030c0315020c0c0904082512030501081203 79
    0x240e1f2101b03400d24034030303005a0b210001a5164602d0141490341100c00c0d0002c80c02d0f06e50b00320070034a001c254041c80b400c001030164a1101079015082c1300c040010402580002013480484001380d08907001c0c0004d0406a070f503119035407400980c01010000180d110314001c80c40e10040c80001c6802040d059803190403030a016440380c5616942c2d9191034819070103004c5100e004102c3d05040f641d20b1882e5800c9074020350031241030020140400480080c10389101c81c81089030002000200d00380402c00300d13412001424081081241d030f07600400350340704241c200d00080c0d0203855004007d8120300c0240280c420070751422580d403502c00000c0e50b564110b0041c10130310b5032100041c0510000c00d402040195500c1600705488543d00d28082000680502040b0b880241c030720b1101e0111022807081d00c203c4400e1500400c0e10715441c009100f032280000d4025504107808100b0b0124801c88045c00990801801034900d0703001942e42402d00e16444180c1700c0e54100341c200b000400120300d0004074040010102c040301552 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 283911699 1250 283910449 283910477
    0x4030f14071502030c060f070804150207060204060e0301050c0c0d030207020316030c0608090c1f0315080d03050f0405070e0c12040c051212030a02070f1a04021f0f 72
    0x24201c0207a004103801011000c45254560f8044044c00d080ba052070304850280c1c46402c46130004400490740d41000400a400040100300c0050b0300c01201c541103a8010300e811199100d0030140e034029009940031031500359011110341000d2241590243c2c003099054102800c900030715403141c3c41e4101d20000c0580100e40703101556000d10011003134044082480306125602e2410031035080081c4103c1001c5004034001400a450209020740546801070002c10f99113103d401b40182c005a1b1087d100815070f46000c0034225413041985100504803c80051500850550f001010340390020608680d030a00942844002140050500f0594050f0710b0551220781c1c0d4103a40981038080d000111070b050800b0700a03c014043d0103405a0266035041d5440c4040b43d60b603000e0241e54800030711054122050800001d90104021f5014103001842100b00500702000c4d5200d0841c0c03032020030345c1281800c1ea0035051104518200208551090401880308035041280c000580545c420400044c00c1c4074052080c814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 283912949 1250 283911699 283911703
    0xc051e0c06070303230118020c0115082a0901030209180d030609050606130e060604050303070b090123060402160f030305090c0607080301050d06090b0411040f0204030f14 75
    0x10003400081e1015407035600608000300a422501025a03100483c0f24868000d840034200b4581079a100c2400405034101804584000758030a00d01c4007041c0d56034100c984981c01180b02c961004020760f034001c154444040c0d145150138204005091440e035007941d446a000e0715a1140b0f68112030301107400d03107141c2d940e41c901e8210078110a28440b40328050ba42480c0075aa4056203c4020307242c03042c80c00c104603a501d00a02c5214821900f601c900ea0303203150b00800542c038044519640c400701c00b81110782815070312804a89236800483d01100c003043c0200400c00110424401d500400c0b403c10084d440703502a102000010308005411180966000900e001420f004400c0e0000c2d803c1d403150040d041c101003170800800510051303c03180014040d245000d4100d1070400141e4007001c0e0802e032100d141d41d1900c000c0201c40e00b00a101201c201341c58261540c0812807280185118601501b0f500907110610820001110305010300c070302c200c602c148801d00104112000817080140c1c0000d00041c4a80b00100b968 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 283914199 1250 283912949 283912963
    0xb090108062403010308040f050904082208030c070905060301090f030e030109080f0d14060102030a180b030702060703061a09040b011103040b1b07150f031e1b0c051e 73
    0x1282c44000100010401031890002c1c021242c25054008c411603c400411814a40554000d0290102400403a42c032000e240180282c0d40c03603500076042c800f580c075100b20b4155004513140c40240d8102d160100800c108038040d4990100040b4000c204215481c0c1d250150210b1412000d0308000d841004000151804d6001150150f04142a070b41c54034480551021194000d040c018015420090840282c1c02141207403030203400140c0146081041155044500300300c1c00e03050560707400c0303180780024010100c0070043d40142c910307501400312032401038405010f13103800f5031107100c6056182000c00d890400c04026176400c10030884000c1407114114004031002d4a0714501c504140c080040c3c006403d202100046c0046206841c01c2c100206002210baa141d40c800c2c46249049003071000848456441410300314041c4443d0304000411401640103175038072031004043e405910f0760351038021010200010284101e01400e182c01050258103540740c0d52100070522100c41c0c0d5000040940114404c203004507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 283915449 1250 283914199 283914259
    0x201020a030518040504080702100f051b1f0213080d02120c0309030d09290415050d060608011815060e030a1a061f09140a05030613020102070b09010806 67
    0x5d001e2030400d42400032480d803000030100d100700340d81441000e580740610308000c1c0c007407410b440d098102065611408100c48550410700158021031301d202000d00c090082c0c9071000700c0c800c00d0040e1124960262200340f03903215005903080c0d90088801c0904641d000903083c100403101e00d0469103170014072940528500805c4c1c3d0460b0b06000b030009007203103640d02505031001c95650103e0844140c2d00c901421391901d854250314195001700704028806070580e0558407420b410b83e1301d0050701c0c0c040d2545003282190829044000029418001001031030007542925100c00915501000a5001040105040401c602c07909041c031581c4001004517039414000c007008150402d0b800741c0d05407031800d5030810000c0101c0e00c0383d218500300707200d01c510740c084800418210320305912441c0e10780c1d0a28844001c4a880213011551001504001081c951414009035004d0307030300e0117041c880890141c0700290404800b50401c400c0c00c1801d10254101da0703485206690800f1003551460040107802108103060030345a084 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 283916699 1250 283915449 283915451
    0x80d1803051504120c05070924030b01080d05210601020c060705101505092208070b0402010e091e0402300c0a1a18121509010501030201020a03051804 66
    0x2d1100d14203400000180b0803440340d100d25a07035030010041940c0c13035660040c3c0070380300313a001040038003420390030b64000c01910200c0110104154030003895100c16903007039001200c2c1c50700d160b001003111404c10002e1110b11300590801500300311421400d60100d060002e00340c00c01c5c09500c00415000d900034094040c4814018014695960003400c0c0760f0341d00da80720b203a00d80a03145450503c00380590f13858080c00584400034113040301516807403400f07582c0c4a50486000640d101142d030700710005020380000d0181e14400c0c0c84e2500180f4050002600549034041106d004000c81c0b402c2100c0c02c1d1907900625101c542d1100d452140307480f280040341c1402d00811014140c2e10344030000c0e81120280018061628450604039801491070405100f41c13160b5503c203403501c0b0030380c0404d0451403c3d040b1020308001880341802829400c954000205c60741c05010000ba01504213081d8100d180c0d02c016806c40d480b21411000744069451640000e50390786501c0c0d405010020045002a00441c051221044006000708 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 283917949 1250 283916699 283916713
    0x40209150a05090f030d09060f260103020f01030b0603130320070e07020a1205070201021f0507030b0307030b070c03170408090109080f07031212050a020c06090304080d180305 77
    0x40034200d03078422411148113000c0c61104400e103140008820070b8a40e015695054000d260060540302651010a22000d0101940c03034036058500358040b4420816003481003150303e51460041c030014a0500318000c1c1054104505080c0a461302d40c100e907003002e5201a4409614110b080865500022840f965843c2444035280341a80000107043c0c4103a070f5620b50142c0f0141c48200081ea07a40c03940e0000200201d0b0001e02c202000c0d030251026103071981c010f00540780c07055451241142c501d040d10b580c054440342d8074000c2c002150361500c01c0001400054006018003400c58071303465440716000300924100010000100300f0140f203003140c1b0b8010344440d452005542858503200d5803942010407007900007055410002906080050314000b01f003c000040c003405415900d80794042d0b0070304031612083c0301c1403460100340614a0b1003880c0c400c1003801001070310303414807044103424140080c080d03400355030047c00f09004c036803808a40c0000e20b00c068100054038110540c40500400107551002d450b50013010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 283919199 1250 283917949 283917967
    0xa0b090703060504060c0305180c010c0206090d03031a040207020a05150c1603050615010f0806040e100605040c0302040602030409020304150e010f14010b040b070c0b040b070b010b03041104020915 86
    0x11b080458400c0003074809000960780d10b400607803600c08c40101140d007a4070117051030b01d455020320b01c040300a81c0060a994902140400440c40386038a41d0001c0740000d42d96a10f10303505840c05e034403124245030202e600703500e00710072500041c6241207940900c5110f08500340601e1240614141120003029040051320b0340106061081229035649110940b80c6000e00d0001440025100002210000301612003240d841c40d030200494002100400c1550420758680e00300c10103107010004142031107205140032a509041105102c10390341c10b020300a00b4940103100030b010722030f004810366059480a400058490343c0383d0400384034030382612030203c89142c03801d41c82c1880603c040d0829401c40310031910a2280410b0a1411003d141e130034461501c84400502080c441090b100004041050240b241090820303107038040341045510a500c0011030420009010b402c202c06050303054018034080c006d2a00710b29250b2100c000c803181c035085542c85580c2c00901e40415956041c45091401c203050fa1035500d4070f50103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 283920449 1250 283919199 283919201
    0xb0f1b15011e2610060f050303030c190e090c03071704211211070c150905060702011101090312060801090f0201030c0207120305120c0307020a0b09070306050406 71
    0x8000d400840240d0100081166100181c402c0340b0821040c071a444403074039004600800315001500b5441e00e52007411003201903081041501000300b5000c00c00103283d0f14000e00c4d104003480f80d0b404140a50010720400803205c540505070b6102e4210201000c84007a601042242d880d006980140da0014512061050044001016520800b882d486052028140c00d00b00401e03494104c0d07004201c84403500c85031016400c1c021a0652102c09802e00c0c010800b10140620141c1c0c1040d0320384090414041100c5043c00203a01c02140207080540440c031000b15003441c010403100240c043c050080500040d19021079210748240f100d482440002040150a6407a008004090360150910500d06084010541010600c94050640c3c0c1c81f1061601c1081c00e5070042d005441c1c458046400d41c00380351000120002c0d5848089042d0303209070785003a0386114084006c44003180280055080401c14800c0040c080d8000801c554803e4100c1140079a039030340c0c50350f40c40c035145950300300405403428a0b0600c8104065 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 283921699 1250 283920449 283920463
    0x2a11010c06060b03160516120e090c071a0108150c0c010510030203010b031b2403042a0b220f08100b010206060d060b0105040308160b0711070b0f1b 65
    0x20310b6440503900c0b0b05d2601c0444983c020407a0807980c41106000000001d180841000768440490800f446001c0d8040c00154926034210380d000c028190000d0a241084006107400b07580014002c0300300100c0d410a03403071a5945000e84003008001080d280850b10941d01a4241c518040c4114020b0040d85805070b4103c00c44905448128040c1d030074424031802c0c80c0f40c00300d80b0b10650710481c407a03107082100801c208942045450103002c035041190141315900d82e2124011841a4040c681d00f220310040344ca0280d00018440111081c0914400c50a2113003e014008881940707481c0c00c00c9100c10421310059603c40c080070b0307201c1080310716008400a80d2503804500f00d000692041d40c104810564040166100c42c421183d460780f00010070700120011345558006414030700d06160880c1000d40726a103d6070150322520100c58105841e0240740b0800c00301450440d07002000e4170345880c100d030050f80c132182d031030100d0b000e10000c141000c554860f500c2412000c2d5000c00c240880030724480c080e9001c1103520761103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 283922949 1250 283921699 283921711
    0x22020301020d02041401120c0e04090f120504031401061a03043207170d1407060c112e0c0c05060a02210106050904020711040f0c2a11010c06060b03 65
    0x107101f030b4031011410b1910488214144079140c00c04030440c007004200061206042c111000541d005404010a00c407240082c0102c800d6141e10341e650b411400e200c1e404507401e9038110b44980c140501401040d98183d0350120351240c07038048940341d4540e490b290519100741c030030b91000e64220b05504207600b0100d500542c9511080c0095074000c41d213810443c0d00000494a103502d040d88a040d06020300c0c3d209031001c03400b482e0035030402410004c085d500c400546440782c07014000204000001d661840e010302c0110740f1030010745400d42d040d000d05410300a900003034252401c0389686d0f50041c000c401d4024022004419440419244a454840d403000300135001701142c1601031120360700d9002d803c1c451440e140d040e41c0542e04c5140c00d00c1d440700200b101942c070941040300c40001417008107406440e68005d040510400b00404640074001140007440200403050507a0241d090420310350000c00c20f0100842c107540c01c071207110311805e041d100503540341c40d01075030082c0441c1ca008400a2403011900103140510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 283924199 1250 283922949 283922957
    0x6020a0311031b070c08010e030d0b040e0a1e0506011707050d03020303041518060e01050702210307050c0a08070b06010833031002090906060322020301020d02041401 73
    0x1020300c407a015818041110100c0c009a001c95220340c9103030080c405001030b14803800e00c244110382c8542d019829103d99081400042d4008078441501c2d485501a1252080701514100305229800004070f9458040b404045c0a40144441c44034600e9007080c2d212902c6600041101c1003540d5a0200c48481d583c00115091030f8011131a010403189400410810300d2a0103600075030071521591500d040342c209560082c030226546030000d401c0b143d148100da8441034016000012a8240b40551301d082d0f500007414034046400c59240341043c040c101e158081c600d034800310703102e846c3c1c3e80d1a0010b503060311030704800305214894152038104001e001d80c02004400d01c16206540682c40b0400191001c05040e0740031000c2c0074202c00c2030380e1901107810642d9104800031881100404e0900c022034144041d0080d240000d5800050307405c0b4030b06110b02440d0300120140c40c4a4070b5407515203800c48403421140e081804183c00d03a8161402c5d0340d0309405441140f51100c80455840f030b1383d50459400d4103245c80e1800e000c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 283925449 1250 283924199 283924211
    0x5060c0c0a0902040510050901022407021506010c15142d0f0613090206030903070b0f0402012c0613051309030219021201060801200405060d180f06020a03 68
    0xc01d042d030080d50f0403150082d00b40001910710030000c0d03450741c010155540c1148120501c141101c01003a80c1c5603e52800c07240316030080d0074401c0009007410f14102615214011900c140f050f04d0341c0c40301c080c0c044650001f000c00115244105403101800209240001d00729018042c0001010709003c1c1441c01040440042c41100c4c851000b00741400c012943d210404580704002a010301704a5110041841c000b180003030342e40c81d00d40c00502d05030800c0d9001d540c03540c0042400020491000b404607049078031084240101d2400ea8002440c00b109881284000780e08200b03c410852008106605480c3c001000c1580700c0500c40c0a00945201d98450584220010240c1c2c41c204107140c4100d10791150564058100000c900298580b840d02c54135089030450780c0134031107554a10083c4904009007a0480011400880ca240240d800c0c02151420400d0341d03000304410411642c0b00b00844540158080e404110b071024900e0740300e405144e540014214640b507181c01803c001059004100051054408100c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 283926699 1250 283925449 283925459
    0x3040f180501060518040b1509010216030c060c051c12050a090c0302040209130e010e060702030a0c06180f031e0c0b0f0c13090516050a02030d0c02030405060c0c0a 72
    0x66070800e120340000f06204000c0818003003811a204028214081d00100d40051031102091031800346c60180701340110040303042c0c86035607410300c082d407400c0340c09102e03141c4141c0c04d41e00d522603079801910442080c0705400340707110b013046028001c40c040b02d43c02d2004030b181640c05050250034400c000d031042040a1408001035810111441a81c91558001b1a01c4c42c19605603400e00000f98460030903c5c5e40403000c41c03113031070b603208490003100c40181c4200000b03d04803070380c200014030f0440c1c050000c005540050003900ca080d03622503541056640c20290100c1c85e4081031100c2040417120032005007034034000e8000002899000254403902c0168191000c045007803000c0c0455203d004504018914009940032600b0102c03044541a00101240c0c40340f4a45485607507026803010f81940003401346521a02005000010030015480803506814a20328000ba600d10003500d03446400204a4001d41d210b512480d094820410380b0b018040c0a0621655000302041440c0d40d41c101809142c400e906440e00450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 283927949 1250 283926699 283926701
    0x120d0c0311030402040c030612140601061110021e040306020a0206060105031017030f1309060806060907031802030106090e19030509102705030606030c09220503040f18 74
    0x30007810001c1c501030442d140c990030403024042c00303d40501015241c10f4040f43c1c9100b0700c0b50521000e8815544480d0b410303a0b480105007480f04c16808241803003e4480c0001c80300201188801450300001001650740f03c560b0030281094490886080750068040b42c084104811a4010a408201502110030980c5c41c14011143c03480100c81c184001a4205002c0001d540e214040348e000d80301d0641501d007000340b61054078507660130408081c602c0304000d280070048a03889220f00006840d0340310141c4014600755000c01c142401c060038078404c069071102e203105242d59200c82d51644c154000c000b03216007590740003814040c22500b110760080740520a0252410350140300c1021030958180c84260418280004019520340105025024448a00c40c401d41403042600c600f0355140800c940c240c1501d0510301032528001000705913a00942c85003105980c66982d400d81c10781d000361070054000d40d20010680c80460591b40d2080141a484041030200b142058070700c800741554103212240d1026141144040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 283929199 1250 283927949 283927961
    0x20a080a0525030903020102040e071e0813021314240a350a030c1a0411090c09210c01090b09010c030903050303190b060909010b0703020f120d0c03 65
    0x8694002202c0c02240c050080e084001024000c0c00010b0405949105400d0306060444891001954100d0502c0500328480c00e1105060b98500c2e0684152400181d488800e1000c01c402a22031035404d06001246203840d0400b585554601c40c003600141001c1000c0c12000d01002c0c000040e45080340d05850707160070200074441c1254078000c2c547c00302d41c91200d40c102c1d590251100c0d0000605028110130070b14442008000182e91103a600c0c001e025a16042005141c0c01102c1a144021040818800130400c92034401d204128100c030038030003a0b2034400c0302880d40d1140d00c50046c3c000925084070b2443c0e012007000300b043c2c6000d050660f00140d5290004568589103030180c1c100d084018842031340d0951150401e00101e501c60b00f8240c411503140d8840d280303540c108a0b80c4551001003800d0303510440040d4010305400000a840d034a050081c01000100c6e0030303105020b80700d944100851104207040c82040117803400f002c51420390350030003c10078144c212a417190b0484181315080030510070f1418403d110b60 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 283930449 1250 283929199 283929241
    0x80109230a0b060d03020c030613050c1e090a0b0d080705100c0503010e0408040504050901020d2405130b060307120510050d1b080601080304080f0c09010308070c09020a080a05 77
    0x3180c4280e82d0f000030020400b49490054086108500c45043e060324100000da0192880d81d0000c03c0e140414a17009140807030002e0a0b602801c84041034501c0009074811740440c1c40d00451f0300f910242d560011802c0140049441c2c2070788103444010440a00c01c1c071400921200d40104140c4180b0f150031110041503d00001c2c268001031410401008454840440c0a8005100710691860140e8803400941034941c10f0707480c01c060742d600044e031032545265403055540c44a80484110041c400c207602c402c2000ea814828a030081c0b4000c4454294500298400d03407051038020030f030707586905243e0001003d00842440f50407400c0d1030500071504560340e001c00c00c030031982c005207010286440c40c1d80d4203000201500c1000c3e2901d800d91800f20b20020280704950103850f183c00250344440c64001d031a460540044042c4541d0342003000d10717402a40b00d50980078152034000030640d0395128280f0305006010368030380c81542c0452000c07882d0b0f01b42651056002d800b41c080303140203000070f840ea9041444506062052 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 283931699 1250 283930449 283930463
    0x90807025103060109420e0306270c190302090c03010e150d1202010c090e0f070c0507171e0f0a0312150b040302100503070905040b0a080109230a 64
    0x1000026a00e2100d001d69600c2541c2803a0f45c01604130702281c428510795071400c040c0c02d06115000d002a849075044a040404800405190074407091011404d00c5402030006004880030508544200c1003044110400000d070031a400c15596a084421a33810703400100c1c4100801408100c1810302c4500740c90680c0c00981c2e4085058985030314440d000c4407621121a0018400d409440105144c80b400c00d4001c2e80c290000f19400030043c40c000c003482d020b07400c00d41e100d503079860134080e06500640c0d11a074000028181205a0f00741d600700319103449515800b903020300b030a01c1c410041c000d10210b94a1070b4011000b00c08500e80124156041d120810040700e114942e01c0070480c1e1011070b02c214025841c6545a000c0020190300b441c849803510300131500507821400300000c0400460030600640c0340c20544500e001b50450900c0f25001f42050b84a100b614030542c0c0b41c40e03040c1c3c0241d44400e5000010a0004000c00c01e00d5010315084103805041c20705024110306444105ca540b0070f01182466009030300600d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 283932949 1250 283931699 283931717
    0x6040302191e06050411102c030d030f1109090f220303022505060103080a050d0e01050403090807060f210c1d01030908070251030601 59
    0x41c4201c048016400c140c9a4950600844a40315440d1100003441806454007161920b0682015050f162808000070f0080362001c61003051264014000c000c07403819000e400b50b10042c0801c8050100900c117001d10390501a110f00d81100540552101914502d984002e1041c41084100600540202c06885410084090001d6000350005e070900340e0006004c1c03502d50f90140f400c41941c0110036000011030100740c0c0000d00020801905804181c59a800101d1542101060341d030261510300c1880000c06213040030034a070715902d01802c142d5a81d0145003900b0490807074141c1306030340078220588044c1e010a60340e0401050b40c410102d803c40130307100305442e1910f000c60b0b04e100480700a0a81d60792040d40c09528000c400707041d02c030350294000400c941d640e4004c200007144009122003045441c924181840c0140310b800149442d000d943d0381c181c045651260388078482d8011480c40c03a56a440c0002012026a21681e5440020000348110081c500301e49940040c0301c06d0300c0403840166941400315044403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 283934199 1250 283932949 283932973
    0x5040b070311011e020a092315161a1b0301050f030c06040906050a1508040f05030c0601080717010204080307021203070b070503160221090406030b1003110306040302 73
    0x42c1d03a0303640e141041000203503120700071000c4c81c0a44000c50491200f01e80001d07440c210340b64054404c001a001c018900001d5000d000d00c00b040140600415070300803901d0300e420005c0510090b0070798548803031410803c1a4000246891511001d10780141c10a808400000c0b0742040407007000760952586030b51810b40307140d00b070208004402e00f10305440e952510440e000080d040e201c00d030207080140484940032803510b080c0820041000d107160800101d4491282008400329403204d0710b181c01a4004d9200b104480d41820541e0661080401a0801d407082c1d00001550340d00000b903907c111080c9550310181c007840c1541c02400c3c0e1080388610002980140017003400352805014650000c00c84908a03880c2c81d12070381d40e00d80703001421204100400d1005c81000340121280c80340500c0780c885803005d0502040c81c094100501c007101180d02c001c01001092070021619070354071510280d03030401e07140c1c64240340c070707003006d1051b0b03d894081240c2c0802d00050072621402c0014000d4011507040c0c01806e120b01c015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 283935449 1250 283934199 283934207
    0x909050304153b0d060203010f170304030602090607122a0507050f01020106170303160e090403120e07080f07080c0a060f03022505010b240304060b0301050f0a0b0105040b0703 77
    0x81c042c190f0401403040e8000c0d81135440c0c60010302c032030740300d22000360300ca41c94141c81d2a25500242e1141d2002810105a50640300d004411101036940c41580103884449800200f85030307010f2480000c00802046919801d60f85e00520340440c0110011802c1c007602101607214150408024801001030340560800d02140c500229214200c00e4103100004000c1c0d5184840c10151a203407840c0c0c0d40680000062207169440c041040c9004140d50500c40403140c001030102d030707081c40010710150800c442070102c49132080d0260840883c0344442800c40c0c40140d04c0d00010782d110b40344441e9008851090b0310002412900100c1d26120115008140404140c68078005484070a10411810f04041c8e007040010f80700300d0211200714260b600c1c10301c5406c10001c12b1a08a003103c03074481c6a54480c0300380320b4980d00c40d240001002c510744880d180000303031640c46503c3e100e006805a15a101d5055081c28204495040020307003880c0b14900144050041814020065841c0d11031070007407070500701040141c140440d0007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 283936699 1250 283935449 283935527
    0x307060e0315060d060c080114090106050306040507030902090a0212180303060904060902030106141809120703030603080a081b04060e0f01170702100b030f03040509040309090905030415 82
    0x6041c0200700b140940d120700840c6c05d103406010200d5071400c01400074020714103080c1701c2a4000d0394940c030355504025000e000d0b40001000b091003692154009409103100740c010707004807035002e4520480b030b05102ca0120043d402425000704484580000036151a000c044404a028401006940b654444600388024600b0040003516520344824000700140c60074404c89006160354038070300719001c5d414410080070300102a0f00301984116407003405034540e00440c2c0011b2010800ca121030b641c0c0c031980340c2a03011b02140d270b0004d040b810001c02c44500058201c0103003403041c16078409140003854401e10342d0307501d03003c0e034052039001402402d13550f0a18209020303a081260414105924a1190f10001714250082104c0c50001600300c04144022030303106000d5202c1e550000c030080c0c8500030140940c903a80b8042c2c1c2c071607580b0566410340400c0c18940500444005801102428095850350b4100103559034050f200d56502510002c40e0302158070b04c540b41064002020b400004000c1030304c0300214001c002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 283937949 1250 283936699 283936711
    0x908040302190803070804091404020a2c09010b01090503030403030804030305040f050d17010503010b0d060f110a020a0309050901241b0606031403160308090106180203060307060e0315 81
    0x40c2c441c0c020400710b000300003034019140301d10500d55581d41044c1010040d0b0302020001c40350900b4000900006030f4965404806a607401580000606004100603407071581060558075405016000d00840355019006442480000c2c0c0700c01120981d1001416035a2080707120281c0021040c0003c0303400a071080e04040d40003401101d21020342203540d180d05080134a90042d15001c10202145013000b01c4e081440b050050604400801c2110010000308850aaa01c180289480d0b17039001c0c3d000032014582d0021180000a408450720340300500c101960301d441c5d03104140c0c04620721480001d000e143c4040034505846007101108030900b254900c1c02c40350007000c0003032010300011400ca14501b86003440360180180c0220f0012405a113541040300b01c00d02c3c0b007030708480141c00400503c240002102a02c803030341545403130003924540c2e80000950041c4503507001254500314102c0801820301c49034010303601401044003501e1100e82d445200f0b48030112070fa100d064040e0010701da606403400100291543c021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 283939199 1250 283937949 283937989
    0x810060518060307181a07030302090301061a070b090c0a1202040603080a18080d020c010c0302010b030a0b011716050d08040906030501020a0f02010b1305070512160f030908040302 79
    0x4078007940000c200360000c0360a003000038080000c036005070111003074890081c0307040c01400c0d218910540c086d00c503600ca010009400e0503000035a04449403000d62240d8003e1080800e00c05c0e426512014140e01c179844079505440340c4a00740f01198641c0d0b00032861400c40341000f0407400e4460702d403800309841148010003c0e64041d07036900000000c103155000419601c602a52046a0190300c5c00034081801d000c0d40128140c0ea000b0f0036044130031500000c00c80440d0100342080344581e0303400e01c0e040303000d4444880e9144c0c1600402d440c030020009800c400c03c6c16180703c5018035001c0102c02c01e0b6165210401c290705071080702d010304204154204030002000c018040d4506600d4152202da2035000d9810561044460b60b500244403051701d5030041e071100140810744001d000456060380080e54240e044100c4004056840c800f191496000303208403000b0742071380c140030b004a240115200d6015480c04403583c01142c2c228841c0c8007110300c030b40b00c0e082c0801d40c0b00b5043e40c106411034003808507501144070001242 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 283940449 1250 283939199 283939237
    0xb040501150806010f0803040b0d020306031207082808010302040507020c1c050606060a08010905070504150e0907050a140919080d02070f0e04120509061b0d08100605 73
    0x5441a80007910140884000501d007952500c0d5000180152070340c00f200f40c6400901050041c200c45d4030444540c41003d2001507203d4031003400007410190099001010080001034600c10000c103940a030080703488101b0302c0706080541d40225a02561420f120034001001680144014649940040e401803a10b204441400000c003020408034094608a00304000428051608102c400c1001c103920803020340c2c103103041800c0418094582131060013007800c0980c8400010b0441c0384104195401041d420180d842c076508c90440240c003185400f0165400385100c1e9000030360a501400450380b2000c1282d40b0040c110585441d81d140c0d6410400b81c2503444940c0d070101182c813029085072040503181c01e82c003400c4424902071019140114540c060320000b80000000c201000310301c40c2c4241c0c0b04e500004140d19028820204032410310512041650048011403502055641240d1807080d40c03081000f1118944052042a60350f44000c1760440c1401c90312280600c00030340300380c016010120761354900a002c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 283941699 1250 283940449 283940471
    0x11030a05090f0d020703020a150504060c0303021213051e1203041109010810060609061e022b021203040c050d0507180e0c100207230415031b120b040501 67
    0x100b941c1240040300507800720f00180150f00e031034841e01c0014007541e60781075a00c9d0315181d0041e000340500e210300030074081c0c004102010b26000e501180c1c00c4000101c50032800d03151004500180170021102540e4921070071081c414040d0001c22081c442045170310003080400068a1130b40d2065100600484a00412801c090460707180c60a5140c080d05042d0050103c5800c0c00b45842c1c00c403600d1f640300c2000c1212a6400704400d98001407a5201000ca0004030710320041811016850248204000521100d04030300c030902d8501c100c0039412104007142c1c00d444002c1c28061030710095006c25100542a200f03040310421052070200c04654115100d80700341d0304001e07a039503101d0ad0040702d0020340c801100e88520100c40000018018090b100008881a8042c07801c1250029640c03000e500481d80c1031580039034502e254014103103550218100051040c04040400d4044012007000340c40212604941c1424295464428159010940e4110750390031100a50310307180c2c0d10744010f02600a441d907550702d880b0350007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 283942949 1250 283941699 283941703
    0xc160c0b0a0519020109080301090203151009081605150309100912030c230f0405120f0712110d02010c050f010905070b0f0904051b0a030b1311030a05090f 68
    0x11005695403210303500d43c50b6000f286140180010031500c11a4940060381c0e0008410314141c9055800c525001600d9594000c4003051b056038000926030301150791402c1c07000da0356210349070b030068038103071002e50703020903446060208031405d5801000d41c0510368141102002042d28051640228040304032040900b0f501008001c450203c00240c924980c0c0140c4010651b407d40146100802140342003404482080f002d0780d18219041800d40301d40400060820719a661310040d40d000d0900142001e02e011505040140d482910a484241034090920b0006801140900204001c0d030082114905980c662003041429411580300300c0c180320251580d0b02c0400e90401290540c02c2e50000002410069400d0a030b14001c2d40e58400f0442c1c0c4820007a107609015030005079010101c1c03c1e0b40106040d1101c1d800340b0082d10b0f64504035003601d040414007440e40390303054000807400c0100303680d501000704480042c08144c0d600c4100c44111500d00701b01082a0080c1a40020f500c40e03010820340b00422086d062683c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 283944199 1250 283942949 283942957
    0x4030b01060804050c060a0c060e012c12090a0b031b030c03180d0215040f02121b0d0b130f0804060905150301030b0403081305060a0c170c160c0b 64
    0x5000106040b041008000c1d04026103803045204982d4a801e00081650044ca108100f460041a09446110307807080031001750451084050300c00100c1c10706440441000540982c0040c40e00c400e4407981d0001601241800102c848045024118154507400e118400400791b2010300084010310743d1500700c1100b130b103003c0040c6009100c483e400c01d81e00d003004030a02c40113000c291003040d81034000d40c107007008075038001031074421000c01005045501c0c0c4e00c0341801c13a02180c8105000c0c0d00074100d1400c55088080120782c0b084540c9000324110309801c071890501c074603900e844900a22448505000c85c1c002601c1c0341e4000b010794450145e45c5044170f119a03c0c80520b070055840300b400b040c46c411003888140360040240704280e0383c000b902400d661441d11031a40c4c000e8094005000d20002d000810440a50044032454540d0008200c80325410400c81210040405002da00e001401301444211041340c0358440c54001c41d178140740642408441c100b61010411540c9080714400038880d40040e00c01c1814001d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 283945449 1250 283944199 283944209
    0x9010518030a0c050909010510170c030f0c09070804120327061e0e0d0c02060c030a02061611100b040906141503030316050a0306120c0f0f0806060f0604030b01 70
    0x40760b000c510b00001d0200390b05e40580000902d0b41030904212003000c2814001d804c030390b2202010300c00c0000764400142040d02048031503806000e103084445802400040c501040907080d079034681e1a0383c4201d41240d40b00c10940b070081011400700d4400012078400c1e041003030350341c0c078a110382d80304c1c2c17030750325014045c040c1d40c0d483c0844459849625a00c22101c094038a0101c110740c0600c00e010380940200c560740c0b54002014040c0c1448810004170f000e544810040e114223883d00c41c1220b0750396283ea08044d64940e0100d4282d03070404010010320180521905034070008000c1c1400909001030750030090009010070078170017500966034468200104099010f80184c1d115a80300000305405c0120b6081207107220064090302a900030402d0141016904250008104c410b1a00540b00c1d03500c91400c40241c100742d40003a80312b0380740c0d29025091109001684c8104d036041d04000da18107982d5031040c071080c04544612a155000f002c0060428100f0070744580c000c4038000c2540385450740729070b02d1080c443c40071f801c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 283946699 1250 283945449 283945463
    0xa06230918040311010501090b18040804050a0803030604060b0f09040507020f0d0e03010e01020702090408030a0b060408030a080702010e0712020a0b0412061424040915022d09010518030a 82
    0x134095442e03820f106503800340c2100c00b01402142d1020011804500d0790124520302c10390808001001d00403050f0a445c0580f200910520300b00f6039810199559400540d83d5520542c941400041e40656040840e80040c07640c40c203039400c010821003000000e00d0028100410b500074074101e4410030a0512690360284410b0320785170a05070b0348100389404c44410141e02d40c1a40c0c41003060b940503030b0340e090315190b00582c0a40215070740d0fa1100d00000c050071402140f15041100450040390120010001c1c016852440d61010304c1951004422400c0e25080281040f03560404c40d01403003000c0004200091140c0080d0034140480d68845009110b50f01c107a04c04c006403404441004204459801f8107074070302070100200085070030144a03a402c8005c4101302261600300c140c42c2003aa94585030060484640c001c0004a990118030400c00007a5000f2402c1500e18480b80084800c1c80500c008403410314403418400d2070a050303219006541560000b400d14036220a01c24041c00719030760810080c001107102e400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 283947949 1250 283946699 283946717
    0x20907200d080f270a0c0e0906060a051c0827090c0705100e010e01060b03060112140f0c16030513150e06090112050a0501050a062309180403 62
    0x800030800d8030040c080f000c041c02604140081e04e031044c412082d04260554000032420a1400c00301d01d400c202040040c4080141200090035100041c41c9078440c01089041c4c80c442d940d002c08021418009003d240e0b0310154044004074410101580e100d041481250130b0307403812403d28030041000200944d1500860440c100b02196400d00a024a40110049200d1410b00840780e5907540c0b0b40c11000c061503e540e581e655281a02c0e40250070805070041d21400800006454086103062035004550082c0492342565503402210400d01c90600f04c0754001c2054600d5894030003100590070000b80103490160400e004010308064400c2c0c500f070a03184652680343e65500500c03200d606142c00340e40540c0c10821050211102c1540008035525015030468100341c0d00d81e58007005981d692100741c4d007074041500e81010840c0740700b01036228505035a001c50710f02c12910303902e0404851101d480d0342c00484004903029181e401a903628040c12606500800041007150041900c01c4104022074055000034140c05c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 283949199 1250 283947949 283947973
    0x70207080616030c12020a020706020609031e0304030513060309060f09050a020111010e0316020f0306091e0102040b0f070c17071211120708070503061302090720 71
    0x26000030024031015181c14076100340000c5000100140c01c10a140c4c540000c60702c001d02c948815219410346560864442c0e141c07030380c000d5907110316001c0c840c050f204010110703443c20700020030740756000b000f000c50385019112144401c0c141c1d04054012024007070b0a01c1084c4040400060b80300191109a80014151050b400c2c4001601d8212030914103892902004402103a404103c40c4840b64082c03c28000044516000600420a03800105114000890560700b525215010f41c820740c3e001701e50104100c001082050b4891101f901c100c801f41d48808074605036240880c7c81310001740e90600c0014282542c900000f1000d5101885401ca008400141c950401004648003000350030b00c0031041100100407144d8650340d12042c080c103103141002496031400c000841030041050000a003650700303142d032410112580c6603014011010940105100880c09040001d0458410f0b40c00f010083c040504030740a000303c01c00003a20b240d081100c107041e043d65403241c08103101032030b8042d1402840d980d0f04030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 283950449 1250 283949199 283949203
    0x1602030f030a090605040509070509010c020a150810060905090406060f0323010603170d0f090804030201020d112e1a1203040825030c0902130909150e01020717030702 73
    0x21341000342404000e000c2800709031150511a940441d46003019a51114207000584820300383c2c8900030340c40403000d10701081a803043c10f107071044034130b50382c0320441151655880d841480225008000008440844c1003002c0d00d005407040d0307000b90103091b0015949440764a2000f001e000c981043e00c210600712042c90104a1482d02e003210030682c0b500802402d8116543c6864004411800b0b9550010119070345001c004140d00000031007041500c10840c200186c6016083c0d500b04d4402a0702500404418100340e600031540c40440321100c00140c0b41c188072000c0500c0502c00c4000c41d6030601034007940c00b140c0c0f003001c610503540710794400190036002c45101c504009a40c20314403031840068006010401c404940000d008a058020b41c20740305144000d078843d1062500b2950001d403040c100c0e83c0e030004529040740e0060043c3c050111078030a075692201c80520685055140082030440b210b030103a84540c400f540302807009400c1900151410384103858480305001d4440c0105411500042402a06501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 283951699 1250 283950449 283950467
    0x22101022a0c01140f0408071403011104030c0b0f190903050f1f110f2215080a0f020d15050a050907050f090a12110901170a03051602030f030a 63
    0x9140010003211002ca00021301c40340702c41902804c50840802c0c1e5115200011040c0c42c05404d9030800c44501d45d548080c042410901c08003041c0c003c0d480d10201b480d200c10140c3c12a02525002002120f07064034006141c4115407050902c0c3c14501c2c020721070b80c0010805000040072091a550b80d01d07420a04509040e0b00702028614103d401d5440320300c0d00c101c02c0e50711210100d01c104600c500003039031150460002c9401e00c03890460144040d80007844c020300522502034152107051510121080c113445011540591042004040c003051080c0001145110560014840b03a6a00b6a026080000e05c03c00c0b0410703500180b4226030b0003000c8003014010350412407800001002c0440d8032800508150300050801d10176138882c6402d506000989844039217401c50750710010115880d4200d00041035040c4690610034442c003c601c1002d01600016070102440c040010b100d009101401000c0d40943e4180c481d58411042a1148072016620300096034041c41100f522140708805140e450b070b039500303005040d030312 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 283952949 1250 283951699 283951777
    0xb120f070e09071215051003150501030213020a0315060f080a02040b1903020c06010e04050615010519020f03040f030507060906171e2d0f0402210102 66
    0x650030708205620000050080c12240084480d1421042908141444c00d407405a401401c42c1400140004807c40100510441703016041c0c0c681200c20384030400080e10020321000c0c1d8001032490103104030616942c024036056215040015070b0340710040c45290750fa6660380c0b0070b0010880100114003a41d41000c1101d5200c0769200d011407901d81045c00c00b034454091105c11032944001d100103502d08502960444845640c00f40407130302e180d80d4030710740d917175981d642214200c503140581800f255110345004501d0b907074071405131036883c20940e400305140d03220f00d80803910070114407034a00718211680d4240002c0020302601c08089844905506210746013050690189040004050f010041164825041445020b09407400005901c6a54101da1503000c0d814400602d80001001c1c0b110151280a1401c49140e01c1d0f080a0346203803c00c00c04280c101003c035800580f001c10303000003c2c014900032000c1030034100d040104c81d00184c41300c20002e00f26002501003140c0c91448441038120345e11034121864810f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 283954199 1250 283952949 283952969
    0x20303150a050d081e030c0a0f0203031302060d2007060606080403020309041a120109150606050f0309010e0303040b0601020105060906100e0a180b18040803040f0203010b120f07 78
    0x1900c0c10b40400d169404200020309020710218507a140c4611142a484c020614641010f44a003030150002a003640b181c0d10840100d4400c18819140c2c500101c1564429040c040f01e084600c0c0c4543c081c0521341e40b150004003000d60355001c00310590450a50903000c020341090305240c865105190580886903d0341100050000b400704200c0000d90010880740417402c20345001c250f4490200b21b85681031410111150301040c8500009041c1c10150700940d0001d02400c2041400a50000321604480710381c02a5000207004210088103003400c203000399006003411000042c0103d0314010300341141c00665046941103200d8052020301d6a09003d01900300d84201c40520303050405000140a201000100e40144058031101e101181e4640901c08004c0c10420038000307003101c028880c0c400508296901904c00d400704601c2e00040701d4046401741c8541c0e07200340c41c3c918688881c0c45280346020140b000301d9041d0b4803460303902219115002c0c9518042d0b07010004081075904502140d08140c02900414050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 283955449 1250 283954199 283954219
    0xe0a08040518061507031b08030f0f07140c030c1e150705030a0c09080d0201020a1413050d060b04020409060305062401031509051021080301060503060f040c02030315 73
    0x1079542c0001c44410707080300ca280c10790764041030301e000c1c0c800318010290000160780048888040c808c2c00070040d0b1291000b41c84044175992a0000802170341004e89a94000a003120010039500300d981005000741000582140d0810f6401d4010307a00d031054040380900101803041e80410100c01c104a6046145425002240c0f039140201c3c1c0100540030050481c41d8550300ca002c0c0902440c016040c44020385039060135160390107003052019010b540002d1550303001544118142c0e00c6c50182500351164140390880104c1c6440c07900c82000181d00d0b40d0082642e040f59104281c00041e541c41c030080c002445080c001040080c910b041503410150010512401c1041c0c5c82410680c0e001c0b0703520303030646202090034001404511240351400381080741d08107003003042c40c060901011046403060b14007181c0880c02c031254000b15022161400740f60201d0014101ca0090005006d41303400380c40030710381c0080090324440794200d8400c0010295400109104056007000003403045065060107010b02400d000e030741c00070300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 283956699 1250 283955449 283955461
    0x1205030402030d1b0c0e090d020a120804030516201c021201141003110a0605030103060c0e06180f04021e0705151008061003080d0f0e0a08040518 64
    0x1100d0f100c2d00ca25081000e080e0301582c240d1a100b940c002426048500f0099058448120907680070b0f05699080c00c4d880740748103142c0145e100295400801c0d50019403180d08080e40c100035200c0600140044091080c1804000a01542422141d03806401542c40200500c0041610754508071400d040354022a085070700151030341c1c00e0b01801012154151464142d100d00001001d0050841441100034400098280049022a040781c201034074040d088a4402c69540b4082000f04041c511905011400910042000c2105030b40704401d541c503203041c0154002c000c0310000c0c1055000c010040c0d207180e58069544a0760900035403100030b120b0190780461074100c1c80100c0b4000380d4503540c0099914040010424100300701408544540316402c3c03e48030440c00d1103106900c1800351402017905074070a030310000d186080c2c0030400d0340859410159045ca0280c021210901903c000407201c88440d49880d4083e01031344c2d0810242042a004041c940c0e1100e080404100c2c0700b02401d1700f0000d0080441c424400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 283957949 1250 283956699 283956703
    0xe0f070f0e0913020406080d120507030501120b0915090d030c0e0105160c0f03080705010b190509040f05030408101817070c09060b0306040b18130611040909120503040203 75
    0x240040c80810302d40351140783c510010b0702030506500b1070403850198130701c180016038010400300f440c0450782c04248203030354841800301d040325801d1003219a003c03480c003040000304981811294100e02e0341c50580755100000580500c06200035100003403941d0003400c5901c541c903854402d05016407503c0c901545c03900c0741d00340000d0240c042c1c4c918031400c20b40e18801c1340702002840200440140413601544440640d0b070705040ca426000404103613032650920044956600d00403c4403084410588440247e15040c0700510064900040040301d0058100003200d01103801040540010070b030420051010030300d140d401d0070070b98032000e03e4080340e0101c050302003001030300c0c3c00703103049a90f101c24041a80790011418607040e10802d42c1d01c50649075161200c041011144840194491001a0340034000102e00c00c2c184448103905160162142c06000301249440b890350790080b00d50340c007480f40070032401301c102c12841142d40b06500904030250764000304820440f12091450090409040c502d0452a003600825 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 283959199 1250 283957949 283957951
    0x20a080c010906021c0e0708100c0e030601120201021204030f0f03021509030405030c061e0f0708040f06081305060402150c0106120b07020714060f04030605090a0c1202150a0203040e0f070f0e09 85
    0x36042a12b42500181540c0b14a6070400c100b400101110b4980d6912840328041902d008803d90050180c140c139030030000c040e81d003290304582e48441c00d003c80d5070554484994102c00a00200c046001c1c8900361030743c4002c040ca07064003c1851101540da5546400304141c030b02180b04505074050581485489403100042d0400f5224451003415603544070349113880303034403c0c2c425410002c154040c00b00300415000683c00321a42030710420744480b840b50301c030b0b908012520411b021006240790300c07410000f80181080011948001800c200d2039041154030038405095410503003003d202055400140414826100b50303503038000c00c40c2d0014007040d506190f02d043c0106e0704001d540d40600e10005622078458910401c860003113070008c400300140d041c05900591110401042543c801a40000100310204100060524650f000b06800d08101c40310045121541100b0742e12025800284400070b040e80c1504401e0380b040c04c504607200d0302c501d0515406404206100142001c002d14409100c0d690388803038910ba = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 283960449 1250 283959199 283959223
    0xc0112020405100e1c0819020c0303030a0504110d08090409231014060612060109030605090606030607032310090612060509010b09040f0507080d110709050601020a080c010906021c0e0708 82
    0x4a262001c0c2804141e26148155027460f0301803100004100c0301040c141c0c08140194483d48980020b95503070020010070719900900941210701c100031041e60340c80d003130b40188141b038469003084000b05d0b004031074070509140d04814044a0f400402d801d0f20400d415100c0d40030042c01c03804804000341031100200d451402164041c3c0124070004001c20420381c0103181e204000c5500c62010701c603900e01480f0301d6458039002d0340d00b0ba00a204001c003043d0042d00900510312100d4100300407010844100c0902c001500c0090038982c0c50b402e0000002c03448204c240503c0003e003001f203482a408400310300d08041102e0f40284040c00701e0b4036048c1c9004259440050007030300715070040d081c035007001c141741040e504080703040e1700c1f04082e803151070f240e41e00d03030707070704002c0c8070161512100c140d50070142d54021034401d48204030340350360058100d201c0713281c005400f00014100d0201c0c01c0000154150306955004201d0384030f40d209040340210210700e101c20072024001c5c80c902030080d101501e00946460340099480d03e1500302c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 283961699 1250 283960449 283960477
    0x308040e13050303040c150207050108070311071514100b030403030f02090405010e0117070e3105010b0f03010903090b0901110613050f030c0c0112020405100e1c08 72
    0x11526100e8400000c085003600b080a4a940e818070745401c0e07840c4180b0b03115082c80f1440d00d8140004d65070012860004031403060319001c030140d481040071401450342180c2c24034100c0d0203210b04000305403000351420300e18642010008090555102044000c140181200b541800303401c028891035641178241e82c1c1050b4942008100d8566a1303417410003a0081d4030220741c0091812000049152014040c1030403500383c03030402e0300d0141d02d5051464a9000500401d1400c204103c0420614400c16000c4401202100c01c001c00d003060380c144840d206001ca40e815500360b91610311460302c40c58502202c0c0d0f41e00e00110000c1001242907600074000d18514424101042000309580345242d0081c1c641c01c3c9804000300546003075203400742911810042e00d90083e00c1c54420980c0703000b8466400001c03203a0400c2042c0080c050310110780011502461a56583c6030f610350240800030b045e0716910758040a0207100d44641c0e201c00c0031101070010411058a00c00c040385480c41d2204046942202141c40390044144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 283962949 1250 283961699 283961701
    0xf08010e060c2d0d051015020304050f01050903120307020706050909040f021912060f0204061d0103020712080415150e0c04030210050a0f020a081617031003030908070308040e 77
    0x415800402c4080d00012510040004d4500b401d001640c4000d110b0b080105000c8807103512855a510400401122503016030300820060095203068a46009901014503000d40351113000c1e0301207400c1c48024508092890301c04014020300c0c0740c061283e10b0150000d45495418484c9000000e850010050700240003507101050080030354441c5003900726000c030f21043d024a1070369a50070154618101420603503500385410210b41c0c0c1c00c212402154204d541d185d4543d040ca00b06036062040401c02d2146182c10706500f0842c5000040d2041c0410850a0007911442494a000c0c100314803151588201c6140052819180c1c031002103001c20b44d001503580217411380129594040f04801c2a215640019510240c20301c0324001d082c1d8894010501c9111301c0e503401c0c0d1000301011090b6a140d07503146000703004083c148120789250909500300760308035000300380650b003030950781480e43c070315900c1a0b80d00a14401e2011b014028160400d0100b0024500c800c004d103025451512b901c242030050b40a210048202c0b80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 283964199 1250 283962949 283962997
    0x40905070e041a0414060609100c0f0b04150c02070611030708130303121505130b1513062f07030503040b1201171002090a0f0f08010e060c 61
    0x4001100401c601800c01c03c240c4840c18014000d00c01c3c0c1c240414441d03801d114405401d10380c3d01d00094010b0030041c1426090040c4502040a0707600c0c1102150204560000c080300420f401000012001d4021910b10505040900f4601c2c07800e01c0484803001f0301c500300480d05221a90004040080f94a0380c50300c42c120504010185003103214480019110840c0800d0ba1009501c01d40075034400c9a05caa16841070503c140f11400741543c095603050380c03203410400340401690919204400700d50711024000246000b6140c0020445589417941d20410500441d042080a40021400c805000582810600b00c003035680040701800c0403003140706003e140740c0480d40803900104018800b4507441410340b034655440719480780b5143c104140c800c440454843c0009005c1c0c0c9000036600070f9412a07409010448124010003019501c00d10050381c0103150030400045820701d030100000904005080100018500044036007951000c900e851047e40040b030030301940e94251012100400328504500090300010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 283965449 1250 283964199 283964207
    0x201090302190b0c060105030d1407170c030c0706080907080c13060e0106020102030619031a04140307052d0715030609020c0c0102010e011806092a0918030504090507 73
    0x543c048018107101084061340d00101042407410781e0000c1c0c00311804010581000c490340c3d1446c0120701c00c0d170310b001c011050205d603003007564a007140301c8113051034900a0160900c1c0d2441e40541c2e4075070319a800203e0140215580a003810b50000200070017084000c3c2880301c000d40781c01c82d000300076100302d2940e140341200036003d170440f000500b41a4429103180d81d403503a01074041c0d802151218455408880401e400c4580300301080180c81c0c2200008031803200c040c1d828801900003034010703603000c10021205404048200000c0a840344104060159034403004150552951054140c8501442030703507090100d0400086c0034000c540c010300c2c0303001c400c0b04084e40582c01440d054100c0101d035800002c04214111001580024044080c1d008000b02c042001c4540d00320f95803806404005003403032218101250164001d8010180620b4500012818460f8000d0314000d00c0600c00556009092041142c00b00c54410501c1076005007101401c0c00809540007403447c8214094400840d41d2140420203141c41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 283966699 1250 283965449 283965499
    0x302031e0103031e0f05030609090a050105100e0901020708120712110702010215100b0f0904050f100b0307121d16081e0312040816080405040b04090201090302 70
    0x409000900c8650710303400c00801e08030852501d450740308503481000e01c80e1446044606000d006550301c03141142c80b560104000a0030181c00900c0c144241d5207181c02140c0d00b1300c203150190241d41c40c0c540506142c1b05000c2090b94001b400010140d2060022002150445088a10b4681401006610f40d66580386c20340705840310255208011307144c0328203194260078140080201c00c1c002d07002c440c581185a0511a03c01ca41160703914115400721070108a2888400007401036001599045420014000c01085c2124012101100e5000314603003480283d90280340d0300000381802c140c12500d07500d84400007805401c41480030000c42307542d900041e03018816400454500d01c03404405d6504a01003038000f0300540206002d0401140107058030a000320130983d82e0b00580721111130103541046e0300d110010628a03c001c0041d103100404002d01680d40c0784511103412400d224070703072854880d400c2505000807950450380f4140141d14004841c80940c1c0c22000c28004c50f64104c1e0442e41c4014807803034081c1501c0c1c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 283967949 1250 283966699 283966741
    0x9100c060f020703030b060306030715020106030624051512040c0302060c010b0111010b0d08070309080d03090b010608012607090c0309141516031b0e0a050105031006030203 76
    0x100d01040e6041c800d41603001044428001ea41c1800410307940d00801c1714520082d94003e6040d403180c001080340c404000d505103007900342400009901980c9403581c1c01911081590b0800c01840804100c420070040044040901400e580c400d0604a104840704124820f4420102203040b03240002000c10024403400c90145601800d00e44e246c180304060350380a0520b05004a0104d035080420f00015201449601c3c12101c0042940407a62290340300c0c030030030b03134080d000540401985140101d11440e040014100c0c1d14910303940041d443c1d440e07044c0700980c0c0006801000401c00c0c440e004001840c01300c201c1e42036042620015003c9481c1c60390113140b520655500c07604c010303420700102c601c1c01d64040d8040004180204103003842480344078009603e5407000240e4124030010800818080e185000075000781c20000d082c000b484440c00c01120004440440070b03440050070582a03405641845240007000b06800e00f006402d600f40074202c0103010120740101400c040d800f100103240c0340490015210404c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 283969199 1250 283967949 283967951
    0xf03090304090c0804060b040b01050901050f04030b01060809070819031b05061018092f06270a0b09011404030b0a1b080f070e030c10020309030c04020f09100c06 71
    0x1d4100303005400302d0130844040e501c01e4944444503c40d420203009400c40310390165912480d20710300fa00151070b65000341803100040c0c0020703c400702c00900c072803004602820381e03621424030310310341a07003014502691600040407581101c6104482c59589d4100194000e6040c204618404c081210702c0801440890f000380c880d100d40001c3c441c44900e0051010f069540c0c40d0440b03800d5001401007881640d91000d401048402c3c3d00406220009030704207251300c1a440c50290b040c082c090203000685039040303498410101c0d80c200f8800d0b80d20000803401a201110300ba11a242d002d450003010300110300903201e000b41444030403940c909003403200c281160003030f40d4810842c14250030720204010081c924180a504500e0020005c000d0742809258034921404509204011540d211041210865000c203071068062041d440e00f110305a807072059444004d42d40b6070045807600210f904040c80e00040c036a102d400703188100b003a01c08074107001003256211030041d5020b04403080641022078640c00103a401074001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 283970449 1250 283969199 283969211
    0xf05010902040f0b0408070605090d0c090b0405070e0d06020309070b030a0c0216121b0503060a090b070e130e031303030801030c0e06060d1a060d05010510090305030f0309030409 78
    0x1005580a001902c0071881291403030b60b00c03144d02c0342d401d00c41c50103610110751010004100c07052241000f08982500603148014038091035032042040c00e11034204c018040c4c3c98004560136070400744038943d80a5070600e4080c00b010000400f00300720500504015090940001c0040c50458003001130341d00034481004600c1c2d417450200b003144014004400d4500040c011074000442d0403901281220941e054901a108881c50994892840c241000d20082c4219104100000c855505100039403007082c59503004281050280341410950000410b92428800500070a081584a00a400301c1610446500240d800d040c1030702e882c40d601980301417002c50000c540c2c000c4105039000e40740c1030480b8800c1054040d410f03182c100341c035081901210344541040d0103210700640a005600480c0044042d42d409220342104000407841d07503801160449050b80c4c030394004202e90f0408118504d09061076140c44000d250559882c10340703078880c0ca0711320498a0b10110100e4005d24080c000c1301c004102c0c040b003c00c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 283971699 1250 283970449 283970459
    0x1107081801021e06090d080118020a12020703120609021e030405012a09080606060708131e0608010e040f020d0c0510031a0d02010906140403170c060907080705010804060f0501 77
    0x4da00380840721541907014460a40b2102c500500c15981aa40c00540301c01041200040820003174009507003850030007420010483d0350000c5c500c000c1002074041e546504051078038012a0040d26074507031068007190302c10015054242041c40140d403480301d06010785e40d903a03102e40c14007901401c05041110304181c0b81c260080d0a01c0c0d603081c0010424060b07a01c07802605ea5071280082c1d16003004031080360308018100460700005100d140140389801210302c00001003501c60500804001640103441e4041080e9841403040f203402210303a60040c00c1000c0380c0c010303504d050359400c081039001c428002d01810070101303900104800c08100348003400014103504050054848000e02a294142440400c042c0584406e80d25003410003540c0d8805030103849071074015180c07803012507400005c4896503c42d0392040c080800061a00000300c1442051f0b44000343c0c880c00320000b2903081c2500541500559070080c2d1007002071141c040381c0c40e0220380003401c2805039940c40c0e0030480b016004205da0f000f8414508000462 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 283972949 1250 283971699 283971703
    0xb060a030903020d0f080402060304050f0604290c04050906030307060c03141503060103030807180308070b01050a0f2303191b210f02060f0d1107081801021e 69
    0x101d0601a900b21007016555900035103509942003070306400203201d0340001e000350409000450f006031049003100c0d0401401e48041d0f00b05502620704a84582060100d10a80045400808801d0352812086801801d00300311540d402d01c1180303da01d01407681070000171204c5d502401036460580c0c016509100f41e01d07020303400400408601215450300321130704001c20000360703c5100220240350040d0082c5544e03400d68070150342c8984d0051040342080314101d800c01085801900510045204041182c4c60f00d4051500b80c07a0228140c101c42e0181d10010303000c002081c1034217954070031220360a54180b01310b0340b1140c81d9100c640c0e061030744603054402c602c5420100210191030400310307805900f01045c2e4945070a00c00708400c6c080d10401d40480000300c20b0305114035001682080483c03084540c40803d51107131380800d91507040005900290080454140c000400707500402230480100541c0a03d800c8103541e81c4041801016419401281d08403400099a4002c000501c0d5003410545841800d281c0154150b13 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 283974199 1250 283972949 283972961
    0xc2d15040b0f04080706151a0715050c0d0f0b0901150206070806060702120f01091203050901020702010516030306080f0c0102011d1513150605011d0108070507060b060a03 75
    0x5a089500c440040d065a00e00e40e0914080d55115540d91702d00760003511600d0150032000407020b5041181c25001628000d85418503c1c122420000780b5180c00d46424000748046180354149035280c1028100312160808070120b81801c4041e80300060400310911010b001001101c4e03c258102c0411000802c040d200c0010748001c80e0715582c2280c4050369480422100303246d003902c140d608440305120840062514180000417010f541007102c054100c80100c0c0c40c00e60700c0340d0390b0607114441e41032841d0481075494020140c1c001c4101c0e00951070304d11241d000804500c9901d8030070900318030340207030001050f11a0f0000300041c2480d90407264803c244510300c2c0c2c0c0b286040c49500b4007641c689055015054800d10010600b61007235005000350341c1201009100b42e0400909203103204140d04801000a0942c041000320f40b01c2c11a00002d001d1b040000241141120b058800d40341350590951100e182e80c00000550320a21914001d6103c03c1c040c948070001e0104040110b81c004801f06100c04244c2c0e041d4041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 283975449 1250 283974199 283974203
    0x605030d0e10020109020a050f040b13050405070b0406090905220308010f05040515040905030c06040506070f1d101106090c1f02430e010b0c2d1504 65
    0x102c02003465208207a088682004009420607003c550401039482d2941034903640302406400420410700d150005140e4103c40b881c80700d9440d55175805d01050000070410319020b402605a89440d00e400c0007400307000c10b4481e01c6030845490b240e80000d03620003901c0280b020b8070115405a0320301c0703203400d290141218009008070242c1e011f062400041510705801558001d186000403c0300724600c00d028803014102c1008141d034584020803611111100410215125501510151025050801b801464410480e00c2e03e010440382c00003000d007540700c0b0410042e48640494081518600e000c9042d61800200c9081c6401030064108104510300c008c81c034030000e0b000841d440420403140d001140070769007a0003180001a481003034401001d102100100030b29521081d8100080c1c1015180007130407034800c414142e1150701c1c520f800c007e01c80030812410b0240600c208503034201a510b00700711343d03980c8080124040054101482d1050801c1402042d40010a42415a1040d11110001011004064600b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 283976699 1250 283975449 283975459
    0xa0b0603070c050c040b0117060307030213090203120703080708041b0905010e071809090f060203040609060c030b0315180d05040815060d060b1306080f0106090c020606090a0605030d0e 81
    0x565011841c051207100314211058560900a08008ca8269280300c0000d240c0d5030544954040400540e44210546400c5200c0e40c2012030310858a01c10b050900094050303a0141c8102489000006500090788d40c0d80103410303140607030460b41c480c2450111511140111403040c645c0c6080480c030304009420482c10307100c2c010103071101600c1305031040343c0a076003150103c1c0520641120612220b050341e000400380c240540e04140c150701f01038a92508a07441910300f214215501c070f4500381044651301a01c50010010f007401c100035150240400d407288a10004001c0d043c050308001000403448100c1500380d2250b180071105034000021028060f03601c41c0c02002c68503ca040307049004500002d8940b44140c01c0600644261076143d130380d0f080a850380001d40b40e84542842e40414014100c0d02c510801080040001d10085983d8078040c0d0840c0c0d1207170481d100b070b107041c85800c820003900001d40540068098558104503540c0303c03400f10041c640390304000d80c54080c1c00c030344104a60b07101c03074620203030102160 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 283977949 1250 283976699 283976713
    0x18060a0c12171008070e0907031704051008061309050102071b0f08032107052206110105130b190507050307030c030e0a021203040b040306090506180a0b0a0b0603070c05 74
    0x100c00244a042032040c620f81c5e6100e0303502440002d50400342c3c3d80c3c20014003c01c03118026142c1d501c85040f0181501032043c080c40205042101d4507203400c10b40c083c040a030803e00c0142c1003050100d04400c4c0800b4003100080c2e140c849032000c1003c2541110351090b04110115220009444034443c0d200040c8585a446800f03001d010604c101e010044810b0f001c5542e8980d0100566410007042030700b0001d0a074002e1107028480c0a90f8200c0d10088107402d08040940003807020f0404030050804108201a802035a1600007000f42c2104444218801c042e0020901d000541d00d200c4140401892011703040070050401c401d2052144c3c21602548c0200308a4070300348a8000381150882c2100c082c00c40102466201403000d2000d03041c01c01c025a0b8001d110020b4910b0700d42c40340304144003a4003507031007280c42d20b40d40d581c081e0601c2001d0001a0b080242500302c8900c3d400141c0302c46076180c07048000500010007400118100403400d51140c2c5100b07002038402c43d01c074a8078010140c0151104441501d503401056 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 283979199 1250 283977949 283977961
    0x306060b0c01062408100306051602060c0a050f09120307050c1f020a0f03030f0c0c060c030203040b0711010b0a03080d1a01020d0507061401180c0518060a0c1217 71
    0x2c4c001a00000085241c041540320b04040341c8411001d0002a0182021000800410024000c0a200d0152025200f51590200c2d9000303141000040c610401402d040c803621004541c080101c5250389982c442460300ca4201c50005034800b899004241100e00c40010710908120300800c1c0d8500c180700441761030741c201184540c05403d100c042121280160428800000000c06030140205a140285000211007a41503412400c4508240300000425811400b8600700803950081a0151190785015421130405940b41034084402610803824014448140c1d540c184e02540701d407408400003002256160380d282024000c1e0f50101c049800310b58240702c40c7c44d12102140d03aa0194100041c2e0061200c200b04601c1114680c01c20301c030841e0f02d65160140c91350981c0860a440c4e0207011407640c078200b042c0e558240d6008807240c0e2025402840340174040032580d0018620f1902c103072107007946c00782c0e0344041c0c4110441da0381003e09001003152140e41e6102c0e2010354028440075012200c0b492480c800d807a01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 283980449 1250 283979199 283979219
    0x1d0f010311061602060307030e06060a140d050c0316052e110c0d0302030c060a0c05030c09060d1509060605040506031501200313050d020a05040e03040306060b0c0106 73
    0xd00014000003101e084075041410070b0030040100352a15802c0a801150540c000b404682c400d440c0480001c1e1a040c1040600009105541d040300085031078840d81441c1c03540414403001c01c10001c900c242c1800d0384003002d02509003c07841032075400034191401001c1d030514035803114005004060046415200309003815007407072111000d00448c0985031001c528003800031248124a41d400882c03a000384071010b4000d4850801030640305109802851310b40090581803480d00d0380003010a240c10b801d0200220304980c01000702c88e00140e4a1509a07984c00140012864501c43c10a81640c810715185a09210008801c0003100b81c5200000c10b0145682e54041105c5500a60040541c07001e410004030b200f51429036100f01103444107060841000a40390000c004043c0000911400760304000344801560780204000c401030802280d190b140e84400340c011038140b0030a4040c040c000c40d0b0356580128592820002da400850781301600b402005e840f80381000c0160800200e0146075801d1400104454000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 283981699 1250 283980449 283980451
    0x40b12012123060f071403040f0f14031305030d030b060d02070c0510050a0201140f1303031104091e0c14090609090c07020a0b090d060203091002041d0f 67
    0x10421081410100c10b4481802e8803000084588450850011001400c0e01c280405486000d410748840110300e072000002d070458035112800601c8080c10401c000003e07600c08008800d0640280540380003101500c1c1816451000c10010182440041241c0a240020074180425207d042d41034403811000d110098066485c0e0b507200c150b0001c0c00340050b03814004032b07078054844107000342d2204ca0107039a030700003040103654900e00381400910001080c0500c59024041c00c1d07812017045001607132910b00346031442c4402001500c015040185c407484142450711035082403010390300b11036000c0e0b565643c5928407801000c0d41410010700d0b052130756807010b0102203403003040000f080c0380e01c2d440e80c1d40114840003002c5038010b00700242d0200c1c090000c80c02c1911405445449a0007100e1a0303980c0340090300400c561400b040c4c5c80200d0b1800104034036902c98031641c4500151540c040405070712501c4600016007441d00058120100703a1000c01e001406007540989089503410420308803e00c2e440c0c0310b041c1600f0042c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 283982949 1250 283981699 283981739
    0x13020c0604082a0c130e07060c080f0f070b15061204020409050105090f060c04050a051002071805040521090409020d1e1704050105040501050703030b150901021504050a0212030c0102040b1201 84
    0xc01000c103d0240513183c0195890311440d00c042c80c011034001581000e4202d099140c49031100440cdc41da081002c00141240c0040a080c0d40d00b04459108000a00a100303000c200300704540d00c0380c0810110f454640001751000d80c014001e01c6246000d140d90b5a0345d040001403a0081d22a090106a07100c6000c0b08481c182c50b00a002c000d012406d110512012000c01c108040c2107104203000007858407000c0d0505074110030604070100e0b0500b000d040a900c0e02110700d8031105c07902441c419450f6030080b21800c03280031240564000c911010940000380a00b1010040500310194055100d4142447e07408410400d900c44c14400b089652000120741c001d005a010b100c2c003081c0c1c1000705001a600903800340ca1111f10a18020a14048280100e030000d100107492041d10040400c20660a41c2c05000201454120a101a070203140c02d07100c040d03545c19002f80180c06001006891840341c4411300885d200c24428400940d9242d9444d40d440c0c285a00400892250f88880c81c000315200c00101350442c0202 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 283984199 1250 283982949 283982953
    0xa0e061602010f120204080a0201090e070c030e0420030703150b0d020f0c011a1003021206040c02071d060103110702030d1116030c0513020c0604082a0c130e 69
    0x10000d94010b403190b00a00d000a800c0c004d04012a48803066540010b10180039400007500c05460b0b140300143c0b0740061600000503108650080000702c90384800000311598041c03808000d400e42e604d010500400f6269806422648601d11a550784024403000318000e00550750208400e04030130310344051060305d40c042c1e801d07581000c00035004405031a401611807034003401030182c6040402c590850849100701c0248103103c0b4099000d1072a0b1070000300f034441c821440d04065141c164448103100c500000242450700c0343da601d025110819108110b02030181807050a44000312102040003d60300c001200d201d8002410802c4034034001103008191521140d0140040401c0c00c00403c040e203442c0510b207402c8000d40305c0c0d000388090301c030b20300e12690303000303600400030741074100e09060511006504034000c0d410440d0040109451411002410b107611907040818291541c40c3c95591148103e2050f41e9641c0810303081a21401528000c42c000b0340c10740007152545680720701c0c0c0d0324038425614620404001c036 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 283985449 1250 283984199 283984237
    0x20f0303040602060a0c18080a0c090501080a0318050325050a0506030a0506040b10090e090601031205030a020d1d010c14190c0203030301090606081e04022101110a0e06 74
    0x150304240c01c01b5101c4401c5040990070560b03103103410002070100d0352104505503c03c5e4103410034003d4840c503c2010b070a10390028804e96040145442d6168100c1c0401030401c03120200c400003101e6080300180150000809456180ca2491000b6480510b0340030f500d0071062008800107103034a040c1b03c1e10421154050009411591200c00540081000504075900705440d462407071011b6880c07015070003061160381c9900078500d0034080008003000000740043c0c1154017030801480031841c070030301c5003081c0b9a01d46010360341c0740d96440110029015600c00916614142504030b2981070395000e1910107905804020810788801010807a01001d001d0090500c407002000340305c0c0419124407603400c01d80ea0904156110001c2c0d940482d14541c400d9025611603551400c00703010040e0b101c200b403504481c3d0350950010b024961041c410100101603c024403c444912042600c026003001e250b0b0079100d104000c0045a8400c2580c1e0103039400030b4900c0000840d0160302e40d1181c07074083d0980d18100d0b1124040400e07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 283986699 1250 283985449 283985461
    0x507060e0d060c020303160309050601030b09070902030108030706230a05180a0b091203070921080d09020102160b04051c02090114010210020a0512040303020d1404020f030304060206 80
    0x24904462001a000650301e905003000c0b031039034000c09500640c0b59000303554034a40080032042400f00d20780e840d0100350410b22410b0200744005000d034103603034000c0004111520340a9065103080d60550000b60520f00220000580420100141403c240140d0060155042e841d850103443c84c410f11101d4801c0340140003052078483c80742c3c0040c1d4410360501c110400044446942c61406906c1c68044614ac9000f00400580304020f202110084080c4600d0500350f0400c0ca1010707000c4103035401100c10000c507264071034080761107001c10380000a40000e240c030b565003040c00a21000e08004002130740548164101c140000c00a8400042205d841e494607500b0300e81450100124000040c134402e8040381044040c1015940c0d90040034020001c403442055a01200340000e0b05005191418014461052000410341074204080300c0a1840d805200c039069541d41c82d0540c001d000340d9600000191402c1c1000b2910410700001c540500d0003203607801c1036041480300701940c83c031a070b00442d0f005800402c04145 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 283987949 1250 283986699 283986707
    0x190f05071b050c04091103011b0c0809041404030f110d0c080d09080c0f0f0c0a0620030d0b0112021312080d05040303050f0a050103020906010c1b080303010f060c050706 74
    0xe141031040041e00c8001003031100084c140c0303580b00416103041740300708000c90480c9800d10440c190084d080096004008008501030040f08200e1000381404100141c0c90701150740307951113500142e140c00d003608500d0400d820002c1c16290289407038000314038940d01520b000a030019003045100708036a900b0314003d0140d540c8482c00d801071400b080d00e05c1d403101c0e09040024281c174060412001d9100081420750b00018890b41b400103444114801c50304201d081e8407854848280b8a02503801ea81003980034074000042c448001100d5040d1072885000100e042d00341481036801c0028010000d03a2038610701c4441c907000030106c2c480e1240001501103030301c03020410482403540380b000480c007500d000c9091a01c0c07100d044007561030032201240020740e10300c200803140b44c60190040c1c000e011b00104100030740c115804a0013100000d0030b20b905200c240f40055040002c060318212071710500d01441a5116969103806a13650402e0081704a9000e01902c081031242c03240d800e00ca2015042030040188502d0010705035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 283989199 1250 283987949 283987997
    0x2070f050d03020309030601080a03020706090b1b2b0f021203150105130803120a090c0302090c09040207062705151b0310090605060a050d0b040b09190f0507 69
    0x1425408203105c910350940c2c080c400540203100e190b015007000391052130000d05010503078000d0014030140300702c240080e50080e02a0750300800e681c1410302800907101d140c64642445c0032002019010100c00300e404400291031003024401c0c503901c803d580124101e43c10390f1984800e00e01d1040102c03091000503d070302600c00758082c40c0c20040c10b005203080e95120580c610301240760000700b084d50002178901152403015005585c00f141c081c50800c000c5074242e507402030b00c0f07130944000382c403481441340807031410328a143c100e0f0b40ba00e034024030444d41e900203890124041c00c00c028120183d500000140704250304154546000260b0007070182c444007e005611402e00340340508003015501c0c3c054040141400110300843c010110845004206442c19010101355030315a00560301070301060004000c2980c0050903200100040b0001060180b0342d00040780c014400e540ca00b41d400300c509014000030312200f52541c4404034a00304144103000303a00c040001650f505590b0400020750700503440c0a0802200240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 283990449 1250 283989199 283989203
    0xb040b0402360601031119090906030b061806010507140c0402070809100e010905010305060607080304080c0f03031e04060914160518130c0b16110102070f050d 70
    0x207880c5003800b8101580514840070000b118040d200e940d0b2020308100140302e94010b009207814402482c011000c04003902481106100002e4a14a41245c043c01440c4010180011a104000150703490034400c0300e8036001c2d1040c40c0543c000c10001140c1039400e400c0795209100c10f0f12058a400c2880da6428000c800b040301540147c040d4090000c002e5660b400100f074a603008450154440d15010f0800c070030f0f80d02d00910f807018042144424081d50360002c5a400c1100e0090800148581c0c03030101050036445000d80007040008004100410442040060703c02000380d0b40444d540300003a0048070799a840155003030244034643e082084000032401c0c0c8035561043c491280494000c6055440b4000d8981d4035102845d981c2213069210240c4c1c603058080001024102c03110074034000b91040d071911017800076013010801c841d40c251260a1054981d02c4100420050803195595204c0443d81860042811002c03201c3e081c0150044074550f200080038003d90746442c44041310149451704000d00b40342ca098003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 283991699 1250 283990449 283990459
    0x2717090604030b041e030c060b0306070914040603060903180902180f121633030b01170709030c41031902040606050a090303030c0c05010504030e040c0504030b040b0402 74
    0x210402000c140c0d4405c03002c0344680c5036440707540001d00d0a1002e45500305c0e1080c2c001d6114604101c3c0242e80540b00c1012a01d9010100c102c01c01b404001c2005403900d504060b00c1d880c10f01c0d001c40304260303208940758901c00c04169085580354842032403805070b100c1c61402521501c01200b812081d803806078480320321500020300c0040ca8040e044081418080440030342c1c1480c600319802080181c0d4410302c0c114080b00d00101ca06e0055240c0c241003c5000010820400bc2568400068020741d00621080756103c4038800c24031640d240512004100f00c903d8013044482404401001440308000004809800c100402d4130341840c2c08081c91998201500050500720482c10300700d02c1854070240100104100c40704001e1280c0e9011b030040c8401d40310151b100404018040050381c0000c0d0303100e0710070425254503190201d0725000030b007012144010000400b412075468941803000300b580001c11031078401e4003034034148400d101d060010b50b1180500c0c80043d2403200e5000c000b50008401c4141140c0c402d2000701 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 283992805 1106 283991699 283991723
    0x60f0207170309060f04090f0e0a110a0b0c010906151a13030c15030c02120d0e0307080f181c02040507032717090604030b04 55
    0x1c503100c2204128030500080d10070a008560000c2401000542c031100102c1e0209142d034400e01c0340700c408030b1401c002251000d103c0d020b285815194000034121814aa031100340b00c413580d00e28859401544101d0104200c02c244000d403250521200000985451502d0424125070206950b80010074000c034080084d40e005c14203a0342244291413031350740c59170041544d02c0010032054000405041c040000800d004002c00d004e2644442d540e54144a60180010280c1c0c07200a44880e08090a170b08008034401085103030418199010441d040b00e282845c0c0341c64080381a000407405400f0350360000313039602001d0b50f20440e0501c490400c5403e404031501c41c41040d4822014180000c0c001c5407600002130285020790b0004010381c1d1503d000304401e030444204080789000c6000119220b00700549515800340d070707075000d0380c42c00e000c003515035454141152500070180174020400ca0700d00360070003 = true := by decide +kernel

theorem cover : BRFrame.Cov 283812949 283992805 := by
  have h0 := BRFrame.cov_init 283812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 283812949 ≤ n) (h2 : n < 283992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
