-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4766
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:39:38.438101+00:00
-- url     : https://prove2.me/submissions/facea808-abd1-4a9a-b2bb-c411ebef2824

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 857014388 ≤ n < 857194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 857015638 1250 857014388 857014423
    0x30501050a05060c07090c030216050a020306071809020715020c030a1d0d0b090a06061202150f25051515100203030a0b030106150c050d030b0303090402090402130305010c02 76
    0xe4813004e0780d45511040c800c011b6041d564165004009000341c06482c0040b8a02101c940000382e82d0401076165642d4035003c901c40e004960010303000501034100e04202c00100102c4280443c10804600000e50110701c00340e84918840d18a007502d1681d50008204507041000a1a03d405040001412025042040a2400c0032052100815407504040c90803020f420040c50b584035202c0040d8a400c3c84400d240107000542044004a0304a045170b1032021501e1080e03400e0800109051282401d5009070800d11801060400c09519040b07055911031901000c00d0366402c3c0c407240150f07601c900d82013030300400442d60b809100c20081400c403c40c3c04007411900c00c1c0d5011200744480c04000307490348402030600900768dc1e90b88404416032825481304010b04003417003948083e00c02404018080460080007115948a5000e9001d80d55105e401024000d04c0040c0045040c44003403400c01020f90071030b08840d500254280b0409005900205a94000718007034800000c00d0128100c009043c1444079842d00c0b07200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 857016888 1250 857015638 857015647
    0x31f0801090201020d0309081606021806070f111305070201060f050303070203101805031803060601140703050304060f090f030f053c07120e100215090c10030501050a0506 75
    0x144d801041840101c001031900140c0c003151494000c0c1b190017030300c140480c1e8080306c010120420485070300610034099280722418070080c803607003002850300c00d25a0041204043c5041e0100080751003034588400c1c0c10003030100c0c40c144204648401140e00442e54100107030344401040003580a6111144041e04040d005035203040426004a6a00c003c41c0c640d42c1d020640e55031000d80040d05002490700c0745980401520b65448004060740c22000800f0360f01c034441d000b5200412120340c00303001e07110003102d003201c210360403d4841e88061305d0316040100240e40040c0c0310300c4076120808443c414040064071509032640400e0f4681001001d8207501d1008406000041208456802c040700300307200f080c600c00c03e44500400c24080c00c01000507000702d80355500d02c00850714104006001e0046100d4050355520200c03042203880c200b205032a000791410002d40c100c001c3d002001000c40141d981e12291000440303152443d07140214100c2620407500c0700009580c2e0006004614054040000070b000403200302d401d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 857018138 1250 857016888 857016893
    0x31302121c1409130e25050301290301061703030f0109020301050112021803062d0c03040209151012060503010c0e060706060b1201091d0c040c0e06031f080109 70
    0x151140042c0e8620070001668030b07880c3d040c002d07080b80054180d0300080d070f1001b00041900503020140300c00c0340008503c0c84040030456003814410800c06c44189400c04001103407069000d031040b1040c950380d9426549807207000c600c4001c9480c035004540305c40002590307603280810856014010681259007810300410041005d44c1e80503d02480e0700485460041e0f40d000c0c3d10741c00384c6003050700c00d8640340c01d40030301c10070046840c0000b0949032480005c1c40302890700f528140042d440c1010121036160000c0790a0000c5005070606188107984140c0903405c0709078041c8c1c81070006131401c2c2841e859000240c041c80090400c04610b008101c01020150000d000b4545003113005815a1683d03040e43e070040e0b00c041040800d10040d0b4004400800308056030a0781c0d04d0000b858444000401d00540409a0074004420030320030b01601c81c000c1011101000d007c401c400c0c4410000a40643c000c8030080000541015180d0768070304d80210b0041101000b01280c00c043c2c0207000340c00354031a92040c50580d1402ea4030002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 857019388 1250 857018138 857018177
    0x30308040203011a031f0e070b0910030204080d0c0203031303060c0306060c051c051b0304030606080328030605031f0507020d09032d061e0908040b031302121c 70
    0x82c5014401da9007400d490361380304940002c01f0380143c6940188034000000580c2501c20002705030b045000d40e08040443d4031058141c041e841a8410460182e0001c0c000c0000703940300c0d590018800b0b1000301564500b98211004d4500c544847e001561000d981d0100d400e1090781600c0380400030030312400c0003410308469449064440d0306600c841034215182540ca01041e500c0782c0d0450322421074800c1000c840010b07040d0569900d40290008403182c0e031402c440407c0001000051fa070369460110500c9019810300340042c491840000030300300a0580750080465190f03424880c200ba400070b842103000c60390600c50b038403500343e0780c010300317004107640101010780403450303010803000d043c5ea40010400041c10911000940c00c0d0090a040705071140301458103104010a035000754090b012105454404424580044c504440780180024684e0108000400c11421594043c5900c641941c003030503c01c4507180c000c103000d0110200354a003103410007802441050748188001040d0009440c0092100050841098 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 857020638 1250 857019388 857019403
    0x117011a060f120108060f0c040b07060b01050f04090506090708090a03110703080d02030f07080c161505190c0201050f010611210c0616020d0c0804030804030308040203011a03 77
    0x740548400600164603241400c02ca9000300aa112050703040c1da5140003541c1c07140c0065030301c071144043c8800422812504c1c101038900743c45003080030510740300d07103071303640c400200098500c181c18030609101d0011601903c0000d071005095050340400c1621780360042043c1741070f0080000052050a90030310202200000314101ea1540c14180602c980001c0000149441070f5a40300030208400019511100c00440c1c001e0744c059629507650144e19113494500755403203541107410a100cc581400244492000042c40f041c0f21400780c1c4450910312280411b050a450301180c560740c410b24800b0b00d00007044610301c101c424031005032000f0030070340c1040c682c000607640040c030602041041c124140c1a1060003804000c031030342e0103910f40c0308000a0751a48440715070000f4007250307403500030b09000074840d0540e60074002401025502822912040740c0003500e840c1050f600994480405010100c001040c0b48010400346000e030712104078030b15262040500b5102e0440c6504492003c840800f0f009450000d5101c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 857021888 1250 857020638 857020691
    0x708040506030415020304030e03210a121508010207440912061006171b07052401232403130b16080604020a03020403080c06011701 58
    0x110b50360780740e03420b00b24009080d032130b8401825403000082c002010740040304882006e10035015682c407409441f0100280d9080c040300b000d038812042102c2903110703200c1c100714014201d0310700340080c0c00a4030180700589120b26030008586c580d40020200184a400c5060720005071a007114008040b03050f0061a54030142041d22484a000b00704c2070400c41c50400050301c0000c180170380b401c45605146800c00b5030310007050350342c480e0340d07092010003142c0c0c544100d085e0b07a440301004480c2826511048008900039000c0302034154600400e202c6000000c0c0148401c003525000c0895164a44a03060400300d02c441040e488036a401c0c4001c4140e8141c5c00d1058440c00314036008a0741030401d61940072028552200403035070b1180000b400410045e802101008a950442c001e0301034000ea0fa641c0c604500f559480b140030380001c500203000107802481c0a400902c10741c8110300d805810942e40f590f90203071035003004a52030384580001c4010f000100c0080d12000800d07481400900202c2d00081d040d03c00ca4140c82c406 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 857023138 1250 857021888 857021899
    0x1b06080c0301150509010309050615100215041b15030903030b060c0c101823060a020a110d061d010f0c0e091b1308010b01020a1a310201031107080405 66
    0x201711a0f00030b5010b006011307001001d55010307140a58030703d00640052114103100c0c0da01240201030540c80043c030110781c80b210100d600f12075281c51302c40041115070340c1040c054804907081d020440300c2803182c03a190500f002d5180810f041c0c4051501800b03484006100c80d0250320203001d81d070000c4500090031400d81c042582c480c0852048048111401c0d41b903003800f100490450000012029034000080908605001003511403020900400c01a441000c5000300160700101000d00480c402c400a40400e040060481c0c420091603980d1b803007130710804145120703941c2c0301e4405109400f1082c0251403621603401400c1000c4c4e034503820050000f02107c4c01881c0180c10900c0091029040d4601038004ac0006000254848994003040c0d1901a010b01442c445542008081c8901d94000120500030320ba100045c140d91010b140250004000014a0032980108412a440b03040300c52900d03060282440c14814008080c1d0703400013500761184000440c2c11074200b0013110000c901c3c0c240581701603a00440c1d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 857024388 1250 857023138 857023147
    0xc0603110d020a0905040218040e071415040503060f041a010320060d0e010b1009050603060607060b120f12120105100504090509071a070b0a02090105071b06080c03011505 75
    0x100711010b981036041181c06c68800600c24408140540d07075042400030444003030080800d48002c00c0e44801d4684180038858001000d021001c1c40c1420013440c800c400e204455080c1643ca800003031414006071800b80c01c0d2140d545c1407105104140702841640c000140c0021040e5156a545850b0301c00e503170140d0089220b62840032159a0741e040111041d11070507020900207860700a420b07600815440c0c030b8151050881c1350369051524050806501121001071016040d5a1948107010107540b12500850f515031381d4044007002030b0341d80131440240c005010014400c840c107040c0c1c0189048510b403901c43d6182002c0c001e0310420035003510b0b040c2c159401030316070044841b015141a01d8a00480e00030070b4006040604201250340300140000c201d4982e0380c1010b84000d00c0d09221280c6118000c4043c003400c0c00c0038000f520381c0f072140d0000c041818040c580b031407400405407500c0002c0a10804000c070241c20a030300410046070b00c55200b541207614941c4640c9507524144009484464800901e4148540440d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 857025638 1250 857024388 857024407
    0xb0f07050a2a020a09020d0c020a030e01030b04180c0e061801090e150c0307021b060a030c0509030d050d14070206040f020312030f060328021201090c080a0c0603110d02 74
    0x186550b890340600314064054a4880a0020b5009858003000701e0703151014180e00d1610015141c3d40d842e8060f15038140c102c0c50000110090080004c60782e0300240c0b074107003c1002c403002c0a03c3c10603190142c8030f002c0140e810039003040c038040c8011b0003843c45030119000c50088950f41c030010700d0460395960b0000581402c044503050810002c0781e012030503032003c18204002202d840001b548602d40ca5800c0c3d90410000040341e010002160b0710494005005111403c020f0740254444240f81c1441d0410a0621443c8030000f40780501d403c80340340001c0c3d0041180200380029000d089180f0030b20031078450151401d008001d607681c40081002c1c05e03c9000d00c2c40d4105544041c0428240c122442c01c00c50340c3c034644900208160710060361240d0180c03140002c01800d81024003004112202c0a00c0c4540c0c84030000c1c1c0030045145500409c0e20020b5594034525030000f80d0a0907030030002c201c08005003c0e403221504120558010980c441020b01d4140342010a40503807103022540c181040a034010b840b000200d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 857026888 1250 857025638 857025707
    0x18062803080705070314060106052a1006030b060409020609091506040f060f0306060519020f060405060f010f03020a090e030702030607121a0a060309050a050a0b0f07050a 75
    0x25800503108200002e090800d200d400702c1c103103041e02e004603a03240c3c55004501d140d81d074480c4240324140010f0403d2201000e1400c0204001c10b41c8040042c031600c0100301c24226a0030140c0109588402ca56905003c0040081c40d203c042e0344000308441c1003140e40f04039000700314144100d210307545c8501c041900044100c40d642030300a40d40f601c00f80555848644034000020009003a00501d404140030031140c40c07c0c1c502c240986400c1e01c050b0340d581801c0194465210059805198103101035001b40102004040300801113544290301030401401c450500003480120140180c000842e0700440c504280056103810032400102c407289500066801c51000645085001d03442c4020b526003e03150501c200076611403c160141101204100410520031203501d00200e41c000f842c0d038004140c00010881c1078000d41c0007011090003030b001d59003a5246a524141030181806040720f03031045020a10000003d0340b07c2842d4020814200f061610b0b4501b40090201d01c500001c20280d2440c2c840710410b0740b40c05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 857028138 1250 857026888 857026969
    0x3060117010e0f0105090603151308030f150105040e061306120f150902010c1401020f12100f0302090402190503010c052709010314070b0304111806 65
    0x256200342a865840e10740003100780c1010b96000142c4940d82001040a1905690640c01118000c00030280040c61010b5003002110040840034410491501c02c40803c030300c4d04c0214442d03d1400300109540c58511710007803005030b001407001c0c1041000e200a103e500e6205014580014040302e03104449659544032070080e10071030308004c61040810358008100704000f070380c0d4214076210325207516043c5004614641152480000680000c680903012008038015808020160305040005450710707603d0418118944c1c0007031401402551410100301d0042c541d08020070241c00c184124485451071500080e400400280001e032080741103080710804d0b40c03030050040b0022719000c0c000b4420400c4040010b803464000b1400c940009003a8841c0d0000c4040f03a40d0560710098004111f07901e141d0840e101c41300c2c1480440b8030401c2c2407196038008659030b40c0f80005035100c2e42c85000e020703458100000500001c0d110b86020b850302021000c0a001281d40c03119600d08d0000c0200318500b9030954401d1003000714504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 857029388 1250 857028138 857028167
    0xc0a020a122f1c060c03051303050c0c0307080d0807140a1115070309020a090c051c0f052d07200a0c0f0f0b03040f06021803100c12020405060f030601 66
    0x1600d49011010204414212803540c05814200840d505d1000280d050320411034651502d051100c0b21100000c1c010009002c80f1891001290004815980400d140c6607040e001003405601491080403001e0348902465031149461910080c1900c420900e0851406600c04200a000c0542c841005d4100304204007188003000749070503500c6081c10301c4050300a01409109038021440c5a00208261595029030316400c4c0680d80c9003861f080808000c942e407030090258000710750f80c640000d0f450781e101034003495014203005000340070500303c82280e850802030001c00e142e1041c4501130400c0702003600708080560360510520764038002d441c90300c1241d040928280700100440c89180700440d0f0041800030301c0c1d00740c03040305007070415407501d481c0010b0b0035010444004110900340000400007407980e030041c100e121844081400b40c2280c0701d00180c10480341007030f20110141d03240718611013541d010034516003032201ca000461509042c8804941d9600c65807660244084000020808517441640d4140140b40c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 857030638 1250 857029388 857029399
    0x30a121d0610140d020d0201050306060705030304060605040c0f02060f0901140109050a2004141201090f0b010f0614210103060b0108060f09180c060c0a020a122f 71
    0x38040002c180c256840b80141450038002c100c500b07800d800c00480040706580c0080181c041080e09a00454a65000a20031a0003040034044c01c2c00003071042020710b00807403044201241c401e0401c020301c4111140f2881c03010030014042c200404864012400c690810044014280359540ea03001c40c501505040d00c0e503002c01d1400500028406100c0d50216008109620003440303e82c1100034400c0701085040c0d045003808030b08010401400240342c020380301e10302010344401e6018400030270103030840b12a520269000b10268003c0002c2042160403580036214182030f07202054100a401060042c6284641c0342d5250000355528510400807210b40d0380c0b404803900b401071503840c1d00e490005007588490f81404200d64101203083c0380f80643e4800e041c59400303401d0a54a982e2041461103081c800800303540356020b1607030140103640314200140044220300b4001e01e0707111801e20501c50034002c20b03400f01205c14962041c5d44001030a46204050110140218140003031a00d0004402529181450f55004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 857031888 1250 857030638 857030641
    0x7080405030c10230f01061b06020304060b09060a080c0607020d12050d1401060509041a30033c0301180e010b01020d05180406080f0609030a121d06 65
    0x70320080d0446000104c0c040080d501103200c06011544603c001e8a0100c1c10926100051003400e10650002007001d2200041512001268031298204da0060350305032151038807912511568213107181802c0d0082c1080d02c0c0050010315140c002925511900303d800d205201c0051041e0555480410940c80749821003000c9500d149640c001900d40c1c0e00c100030300c920103030900d2603501051b041c68038154100c420741d485051814040b04108002000b4091083e42180320340c0b0300d070144540b00c1584810b03044000b50408603d50250240c40b820940742032035010f0940e4420484c0d4585580c0c001c0007484a02d61030108010207030010a000c802e0107011001d20080c0d00c1006c8000100f484134074859600003554075404110400c54001840d09840d0311781510760241e404807901c024490b21800c01404d00f00195881a000754800200103810b64000b40d00c0101942e12400200103a007500f84040307904440307a40001c500d001c04518029103195a01c22403103007031541c1c801003422940d40c200606070780c18100c00c0503540765 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 857033138 1250 857031888 857031913
    0x200a0302070311010501050d1401021b070602070e27100f2c0c01051e0408100606230310180504140a030c061d0f070819020907080405030c 61
    0x790080303031040d4002034102c03486620380d82041c8901c0341a90b40141c020104400c150710380c6030700c2525121031149559801c02002c0c449500451a2000690f0140b0140039224078022000b031a150403600840705e042c08100902000307100c144024400501580140918185581d140c1da04041e900d0000c2a400e9050200d0f1082c00a050383c042c0c4070f03650740514480e0323003040d04081c101013000509072444050f501400310300242d50b00450140800408603201040b2010b000d20000c11107401c44c0c1d0002d55a54011100d40d81d07255568021040030b00418548940b825600d000031a030219280c000200d00d00c40b000020a85c81821501044060305480300b140c0c245000c1d40e0148401000e08544c2038407d44844e80041036202004501103e45640540d00c81d901c40c2074640ba094000c200c568209140b41004184044000380c090000b51035503c00c3d0ba01401c089450304a4041c2420780d584030110400721524003610041e1717690441c41e40c1203c0740c5e1400754000d41c0d40d46091707480d500c0790305001d10030340c410001032045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 857034388 1250 857033138 857033141
    0x210c031b020a15020a080f061c11090a0b10050f090409140d0e0607080d0b03070806040507060c230120090418080403141606171e060103200a03 63
    0x510a104686681c201001000c2c2c90040f801742e62003400004240700b0200d0030600031040f100d50003406c010310540c05a580041c80315620700300c02000b02e03016021151111030600e8045030b0b0707542c0481c5440051012059020020b0203020007480300109000001c40d951304406008410f5961268001e8000c001301c6010303080007281020164038011052003207424a00c2da40c1d2081074031200f00000138003a942044a181c0d21980560440300d102c020b000d90b03c15694880340e90410001c00107140045c00380c81c0b5400c144c2072403400c0076121b4000c002440040420400050601a408500f071400d102410544240d5a90343d1400360446094145440e4007404900d01d00c03011150043c021b00c68100c0d002c0140c03002000116140c0106000e000d0040c900a20040000c6058030031100710841c0039006459400d1050380ca600d202400b1034100700006505807242c4417030344a4003016560805010242850200038180c200444020001c201d281010340741d60703800c042c0180c03c2c602c140344800146040c98031034003850f40080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 857035638 1250 857034388 857034403
    0xa05030a080c0f15150d0302060109090515010e070818070308032a19080105090402060a210c030b0303091003180204020418050c070503070f021206041a07210c031b02 73
    0x52540300d4440001c04034604044030246c0301c0d42c990082c0203170742c0c40c0222500003000a0402566117004850780c400d82049004031450107413011003c2c4028500300090700400c3d10b00000c1c50b40c9000507034a903411035500c0c0005903041c02c0b203030b001000302e80c0c0b656810818440b80c584040c1c0714038001c0f90b400e109003c00281401a00808909560b03030605142d0400702120241c1d820311031203401c9000d500114025082803c010050303800341303041400c01c80c0502440401c0c20348040b1600c0d040300703580c1c0060302e580c01c1d4940a0601c80341000c40045081018610028408803d007100f21014140d13920000341d50b400400041c01921500100115202c6d07036114615010034210f01c2c8420242e9203028002800d01d00742c8815214000d030004002d504180c0c00f076407141c03640000f060041e640f10440c420301c088141e60401260388610301c140b4503040403c0e00100d03082c0d8040000b8051600384210511400310081c4003400b01840e104210303101146544102e00158014856240b0080754148110044c0854a40014468 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 857036888 1250 857035638 857035651
    0x3090409020109240f0e090a09030c08120613020a0e0d030e13020c06010e070f03020c19050f060c03060303091e0604030503030f010605040e0103060b01112a0a05030a080c0f15 77
    0x40c5c024480118200c03011003007090940c4e4056240c201203100e0940781e44c800080030b40f0a00305200c005980f511040c041f83c000000701c403206400301040100c0f43c00c06030b0034001e0306228440f0175414200c50701d2000d0404a00140340c50b00032541d400c03000c0c007450300c102d04c031608001c0040d280b0400c2c01103031b40103070010307502000c2452014401d400c0005042c04240303c40742e110780d10302c2d0b84840c1000080d010450181d40000b080c10414800e4844892000d10030741103044445210f00c009001c20143e101401d4103115005100c400a0310041c030070070a154602000b120000310b012a0294401100c03600725071451200090016040a00410b0110410000000031030054280caa82404141e0341e8070021581c0c0d100f60701031380030003481c00e000420000304503030003010104c44141003000c5c2c00381c820f07840e02d483c0c260b400800000d100c0fa030240840544d010000c1400e0f621005071403080300e4a0510700441d40e981c40001000702212000101074a8840c0e00b03010002c0c5140740c4000360381d00012800f11b051151501550003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 857038138 1250 857036888 857036897
    0x319150321091502030405120f0d21092001170f07021e1b130c052a0316030c08040603050412051c0c05210106090e090309040902010924 60
    0x4903c1c90310704241204078a103598000d40c5094106010311483c1721410007980c505101d401511140284180514110220310750358140318050320843c81480c4601c940000389074a850803100300041007005441400040440c84403243d122748003801215043d00c40009600303046107d50600c0043c0b6808517a241c05951203900711142c030203d003100a0954000d40e0490b0282d0b034898884400c140101400c031081041c00145558462040e03420308109954010b0034900002c1c500152005442e110404101c0d1402c04002100080e010065030095584c070450100c2400b41103c2c003071003c20944540080114964841440303a226980c940d00074001d07107025202107400243e9072043c1403031580300e50240c56981c07007040c410310900c24040180350000d008070004402049010004101003143e001c0041400c154032940c50b40c0306601d84180200440e405800282a4038040010300c11144000401d440d03071402c046a000513164001c0c030050b40c0c070b40480d5201c3d014a10300f56440c03140e9142403c07130440c141181d5885 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 857039388 1250 857038138 857038157
    0x916020607111005040c0509180a0b040c121506150e09040219090506101b0f110a060e040e010e12180a090506041a03070623030c030118020319150321 66
    0x70070409c00c2c03a050004144540c0150610000f20382443d110350b8105018007034025600c0d85514107210030481081c3c041c2da405003902030507020681244a02d8004181680003451500ca1040004118880b2202154807238840701c0046070540d6100701c44d80d40c001102c4101240c500703a5400404024200840d2458459048111640001d030b0040c101c0c07010640c401b00808800703009581e1041c4036050500c0c000d40f01800803192020154030342400f010b014201c83d495200140007168200420342d00d40d402c0751a4140d0410f8134a0300c44540001c1d5a003031140445131816114505c00a400307005014840d441c5034844101800000c07100801d50005001c0c010598040c090114244003228881c510342402c190194801c8004000042c81120001c003c078450180c5c001c1c01d19800c9040b0499a0425604454800000801040344c26511403245010480e2054254118a007503034a100415548099103e00c0c075890703920840440000040c050081c0d03034825002d0b100c58800312806000700c04017039003180200d912800c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 857040638 1250 857039388 857039401
    0x11407090612051e07170a0b1c020321090607060c080f010311100c0f0c060f08010f06031815061406030c0f1c09050307020916020607111005040c0509 66
    0x11a4401c403402e450096244044e4110b0128100000304900f04101c0c031000c000c2d0075451000c0a0394000d13603080102043c07080156041101804003801c80c5202000328148520044c0c40106e0103024024289080e191045640d40904400744617907901194030034000501c41082006a9000204042007551014007550356010f4405181100303010140c100c85918008d983e0b03500c2d00c19040001c0000a1500501104040e13035011040b050603001105c080f10040000d112003544002202c640004925244a00f035141210580c12a5401d00036141010745410365500307001003c000300c1c4189607102007052104181c00007400c3c0145600e0041d5845001811601070701c42c9407401c2940c1c080c0b51540e0300c1d1031070101d50b01e610f40c030564030644a49580350a0b003424511000294841d407c2020300400107155110b400d03204216600b18010301d50b210300798205012940c0725a0010f4a40e600c80c0c0c032801e10030307005407000d0081442c0040d01003501284070f003800100030070040207a01007000c850f03007a500561a6160072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 857041888 1250 857040638 857040641
    0x90415030b2212020a0c0b0a1707020a020d0605040b0c0a080a110403021215010501170f0a0902060d06030201080a05130b0a2c010b0f0d1115031315180b09011407090612 74
    0x5a0320700c00000c27119071446155610110601d60090140c1c01140d07003e40d803d9005c515500d503030040c181c0d00c0c241e0b25000c020a122a001c4510342c081c0c1c80076200c03440c003100242c0c080c0085101030550030700e0390b42d900034070f2030075600000441d00595002016425442c0040c14032943d998869188250855907010002680e5401280c020080d460484003507042556441c042c919440c200906481c41c554888104070050384a40d80100030070f00c4071042c041805420f500001d040742c403014084a201030300e080c00b045960381c1c0b4080039580c0c15130720002c0300c500c5407900d6407200d028145140151107181e00b0b4103c0c95054201c0d41c03089940304c0303074038038024054000b4900811020034450400d42d03800c001030366804000100c00610b80020340038010a00c1c800e403403074444100381c0b030742080300d080d40d00a0880358044140000c0104403000c0c0008a042845a101803049080c40407100810041004000d0030104201600c00c0d00030400780d000310400700d0a00d20b849100200100300342c3c03050320082620b1070080c1e800f10142c2d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 857043138 1250 857041888 857041897
    0x1030f062c01020903070b0406170c160b04030801050a15030b010e060d0e071a090d170d0209090f221a07080708100509041520090415030b2212020a0c0b 67
    0x240e07103446645000c00003810080900041080bd600402041003000c034032903011f003590740607002e003034001c0313040c6058600588118010307040a440350031884001c101d60f420315030302024888000e2078007080014009005132040203051540300c1d44000041031800000f01d255002684400c4010221410300c0d903522807480344d06440c1d003810712415070200200c05190610501e08810b9500c590841468040800d000c5c4103e030b0840302040c0041500080c10705c0d1689454820b00e0b0308100d15807440c20940c18164502c440d5008241c1810310744001302d09070b41c028400f21040c0714100d40c52140d80b0001920304000010004207003283d144000c925001c000c41c5020420b03951110070b9a2029100a480d51217030344602035900d12600f45411515202d01d503c0c601050311020315010031007012103180c1c840c407802c0100b000361040a01c0b041014007082c0d10800c00320f40c0000d0340d00e0308500030004462109030078400d0800896203141c0040c05445841c086c0300310840d030024004560b54000c010304500d05844030f943d210507114 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 857044388 1250 857043138 857043149
    0x406050609181f27150608060103020d021603033e0715050603010b180103080c0a0f0308090601090614040c02030c0129030601030f062c01020903070b04 67
    0x6002c5210b10411a40d0620a402c50f02d64039240c44500c02d01e410758100c52445800204499608802c142d41c0041c214004440080d104507080c080c0e001001598480741c10144100d50810082130f001c520319034060303070440e180b01c10740c0300055541e05900400c500500013010b50440000313142c00408041d11036502281150303c012100044405100c0e41d03440074200302c0c0d0a00424000004010320000506500a801d00c0c40f040349401140c0e9291902c1010308546030201d56500680c8030142221141600003880340c15030707502028039500c0b40c005c101c3d020f103020074402e00100310000c0c6032100b8082c1900041d403a403040c40c1e54030845030302c3da80340c103620800d4800b140b0410119901072000c00d00d00e40f5094200409126451048a0a0204607013006003910400d06801c83d054911290307000c95083d508000c81d0b6650340c203400805055145654030000903102c030344043c006d140c0e035202c1d0350860008043c107421100408140f0780e5080044120301e5000b5404114058420b20070700b4030001d0040004030079074046a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 857045638 1250 857044388 857044399
    0x90902060d0911060c1f0c021e2e1503021f0c0506010b0a11011a130207060c030203010e07020705150c120a0c0308090f03041202040b0d110406050609 66
    0xc1c60001d01e007014044000d011240d45010100f0000b41e51100e4000c2c02da030181c0b032801841034403000031495400a100c1001e5604180c01d04102e48102500000c000450050072901440c0d1140904101070a117507003411070040c1e00340100611032060080d1004010401b442e01d404005488100c8c4610103062000d00c030017504003020125103041102415101c440c1c030101400d05151860342d6a84143c00c03c43d00f40c210f034070400b0380031402d0500349501034456900001d60f41c008001c01582030300165085494544c41c18072503030320050302054034403d60301a41c1c003a550158040c0086101e40c203018001c0c0d0800d025140c07961488030002124148001541c800312000070b82100382c034142e601c01e000c0d4039070b01110341c21140340304a802320080004108020080204156a58211000d0718039004100c4140640315400d1540300034070354810120b0100803103040301e51500211b42e440e01c0d1440071501030804c658181e544182c0c071545038024803404103400030641e0000c407820859223840c2c00400c6000d0080c514184d0708070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 857046888 1250 857045638 857045647
    0x4061d010f2f1e07050f061c0510060e010807080a23180d080103050c010c03140d060608092107030905150d0606090e0a05070302040b070f050709090206 67
    0x5601816449002101a0b8032684402000810384040c000085070000303100c0e0302c010304031103c07510031080d514140654070016102144c5488005500034024001c440e104840c001350001144500d401ea4141210300004280082d2a0280550300c64000f144504000710f811315000c56074541c8140c1c0d4192040c905a140c001a5407200103980d03009002009441c2c4502c00003400f00c1d82030703450344030034648200700c0300340c1400c010102142524145100c0010702d070144400c0740c00500c0020404100500501c07000c1c6070814440c85182000c5840d41c0c0c1e120419086aa4001950030132070003550043e1064900301d44503602d15807295941c855030f80592203410b00d035040a8403449030500c01f43c2c80c014172804c1d010b85020b56080c3c0d12900000c180d803032620f15800300042c0018003448244002d01654000700300d00e08111160a1420f508142c91250080684030a55a6507001030701280c000d5068402030801d000c0304946030b070380b41d02c0d000614000d0314000351440e129483c00060042224010315070003135805004107040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 857048138 1250 857046888 857046917
    0x50f060a060b0d0c020705300f060a020703030209041802150a02070b0918101a09090f070c0b010605120a05060f09070507021e1315060c0f0507030804061d01 69
    0x1080c54040b8503017140100c0100164543c0c58003d141c0078083c26882203488800b100d223001c0d10681e005107801400d904030601407903508802090b81544000c1036900035a07a00810300e8120003e00c41d101d04140d00ca403400200241d144100b4401403445403007981c556202d6a1070222580d90344c02800c12040069010501c140709014040c40a80300e54100a080910400030400e00c00c030480030111400d40c01d18440701d008001001c01c401c80601100b0000d80180e14200c241004148110300c000c281c20300300e404140104101c0e41c80342c210402072a03080009855596140e160040507075110400c1c0c0e030b64103250346000c5031400750641701c1c1c035000b590000c244904401d0048144807048a00406902c1840b00030700040c80580c460f030101c009503134402c6c44509100c0c000002080340200002d103601c04d005290810920011051400c0d1406548803420858580c600f10b00d803002901030f90041c018001d001c0c0c41e00c00010004d209000e00180d65240d01c0346e80d000170301c400e02c8092041400384018005080700000014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 857049388 1250 857048138 857048141
    0x91406132105070b070c030906030605011b0f0210050a02010b0103050903071b0803030a14070305190b1311070c1a03070e06040b0c0f0c0607050304030b060301020c0a050f060a060b0d 80
    0xc51114509006040c11403a1311101c1101808a0f02180850340120380c1008169011912031302403c0705090801c03043e03003008002001c400e041c4c88480c803001015031030102804150341d034007035400354000c01c0c9030650402c02c4001040c1c0d801410441c0003643c20b140c0040003541c002d0084601c1201036000841c1410041e40310a400030501e1440119085240c0300040340140007130000307500c1284c0807100403500a01c50300110080800007441002010b00c0c280a00140f01c004e01c050a495101a0030702042a031104800540d101c103030201d12441c4945400741220403880000080e005207402108120881c03541d512080c1c504402c0b540c20712003920f50420001d0741950103403851505945020b4841401c06480e01d002c90060340c03081c000c074100d0340d0004060440b030010400c0300c0400c86000303940c1d082c2084c4040d59056038a001b00e000007400b0205510005160751000d605462801c0304048c00c8076540521405c003a43c0b40c25001c0422010342c06070f8070000310301d414240120002c07031b040000184d142c010a0002c140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 857050638 1250 857049388 857049443
    0x112050606190f0f060f05090108040609081c14010b040b0d0e16030602120105010e011d040f060e04151e05090705030d0f0210060b040e041509140613 66
    0x10110700e45540c0c0460090f070254400070290110440700c145880c2480c2015096202a9801c042006000c01c940d01d43c0703903801002a82c105a0051010840c00401e141c031011034021a548264802c09121603600b0010240e000302e006280c11421081103a6200c80d08000c007441240207030b4900707103002c0000000702e80c2103034818840080c1740c0c82500c034a00003403010246500e200780c0c0305503082074001c1040500103042029841c0100b50034284801c140980c1800070b000c401240760000649001606100002d0300c46400400191f1116581041102d1300c603035810f15041010743d070070380301d40610035450b0074924814403400d844d42001d08105c43d2043c0000139980b02815000f00192034074040d0340380016094604101c80b544141654030340c90f40748411800c0c004d107015181c00c3c0c500c10340c40c01e010041242107a039004030390594911221558050303980d400c00200280c85500300c038140600e00140300052000c07404491045c0d80c003160660740780342c4030130601c000300c07442034240a84240701041d03032401424820401403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 857051888 1250 857050638 857050669
    0x90f010c0809100c020f0f03060c07032d080c0f09040c120c05031816031202030c07030303020901080601080f060f0d1a0f100315090c0503190b0112050606 68
    0x42d10300050840403480c0600d41c1c48400c00410700d025000c01c110300d44038a5a085406081d42c040401248640000755a010051320752030701910005000b6041c144104080340300c907600c5400925030202c0c3c1e02c207030451050b1000900c500080410b004100c01444403411200028072259000d420b2024110411005024800150003440140c0b40d80101c1000c803400741d8222916103440700c60700e9262441026202451214034440b050701b004250010045401a280c025650400040080b140366440203a20314850b12110511500c9a200e0000425500d07400410076082c003a030333507402a5201c460040d1124070099035030030100400807001440500302000c17005080d0000800605c01c0301d00c2a10b40c02800c40c0101c52603408001800c0401c0051800e50400f9900007045082d14554a450f40d02c44040744501024140322094035410b03c0020b0010f01802d1101920008095174182d100c0020110b500f4641c1e80c10813110086610000030714891403c2c103500007241c03c04064021644c03400f0070450540ca001e9282c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 857053138 1250 857051888 857051903
    0x1602121c0b1012060b04030b0f1e091c09060f140d110712020303070c1b05040e01140711070b13091d06150a0512010603140d0e0303090f010c 62
    0x24220981e074032040c03401d2603151912103e0302010903620700e0381650398a0f0401c0d4440401000b041001401258003558410302c004140d01a64882c03c020800c41101680c001103038190301e00c117112003008003041b001035494140110b030003010700c1000e0984686103584240700124890689400d860342c061840c61890034560015103160110b1039510400b100d40020508082e0140402d81d8001c02032040a15006a0b9541c0000d600b58500741d00003d2940c0281100148403404452801d5000b07002006410094180208140100d04a1182a07402230a00403401030784400b1040201d2480307030194624403100d07600d030006000d04500305102903c140d40324050a000c03500d43c040002030150040d1184e52060501c032800784083d8015040d10714900903003d07020f0000340c10a040403010907034990380c69504582056034040d22510311034003920300500c0c2c20750001d40740740307036403507800c042c401300494000c0714000c1c0c9407203d424030498001810303528010780401d00e800004802092000d50301605080c0c1107035105452 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 857054388 1250 857053138 857053151
    0x604020a05060a0306090f0e01050a050f010b0c150a2f1e04030c12020a0902210c07060501170706080919050a050a030c0b01090506010f030c110f061602121c 69
    0x10400111044007661504980c8c1c0c0d043e51042c503440a004164100c1108034061196040c5840c014580c00c0341031040c036680440000768950001c0040c41f05481760b0b494503e50318491b01c0c04c8059080540100104550302e001c01c0003480d81c403d0701e200c103081e110010344043d06060007000401d25100e0f007003081e5003038480c05050200000107034008210b40043c20f5001c065448140a6206000c82c00c840303904000044e0b4018005076410001c2080d8005403000d0000c1c0400d2181c07543d1540000c9481000381c0a045181070400203c0d2102d00da03c03024050b03258100441d0b04565899608a03100101a01c1d406d40d59008161201e04101a40c40d031000618019020303140d102cbe80d0380e92020314100c010b00c0c0c1280401e400d81ca0060902c44800d4560380100b840080500a80ca040f000081820741612a00c0c1c1c1416507850b00703082e0300d0f4852480b09100b50003940481f0095003001c0c1d00b16596440c12078050020860b0340c0700c9581d0b403a1011070640c4001c03941180f400d0605900148403643c4244036051441d400b41e0300c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 857055638 1250 857054388 857054399
    0x1703090a03200307050d030506091501050d2901020601060e1309030915020c0906041b0c1113050121120c02031204090f3c0b060406050a0207080604020a05060a0306 72
    0x10041a16600c07540c028040344c0300d03811b4090b041e075800500061160840004200e114418a003000e0041d88003440c0c25540c42d000300704100300410b41200100c188008420900794090208550001440d00076000c071030740c1c7d81e40c41074100c64072101c41001c682c212003440d01603110f030071068105070700300e9101303050a8185988491444d000f00c090300b00d59100590120b50045000e0403c119001c0e0030031001c0d101444101241001e401440d8110744004041059141c8100248480d0303504000c89043c00410381e4000205542c0014040c0000780070b0710f40007038842000385201409000390394100580c4a801c1030403011070000b054881300c441d01c0b0103a81500840c40d0401c049264100104040c05180a000492031000c040120851340d44400c403c3c02e00715503011540e0307912400042c00314041108031482d6104900c4040c60006800303146940d98000ca00440e02007842078111010b032841c00d442d070342220f0030943c0d180344041c0e542c101038401a4010b0b101440604c00c03418800b00400001889060224000e40c0c0c3c0d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 857056888 1250 857055638 857055643
    0x2812020301021b0d030c0206070c0809030c12162c0c0c03030f011502010e0c04151e290304020103180b09060a0e030306030601150909181703090a0320 66
    0x1940e21468009000381d01300290184105403507113000344000c20070382c6002030300500030420b880000303481d900000c1a1015581d40801a000800e40c01a00300c80034035203e420b00f2540c0e8039601c074803501c20003900140803400e03135039428500c5155801040100011a284002c1c44602e0202030010300340000100100740d1b174007008000550046d46c0c04c540e066404c1d0715002840aa160240a02c0d4045904000b16030404c01c1002980b81c0b41200304540008091754604c1e49005020007550140f00d04070320f103038904502045407002c00380454081e0030394801c6160000e40c080c680902028103420070b4190a00110300554402c0d0700080345c611890a9090701500c45403070720b41c581c403402c55244419a000b50108070800040d070003038101c0501910011800d5090440000e5101e0780140910300012030115085040d0511401c1c503e00108441c840c100b000d0b1071040000c640c410304103030b020b90b0484110701880c1c03d054000703000c492013000f400c0040c06612503242d9080b5041d6203407221810368143c00256411940f0400d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 857058138 1250 857056888 857056927
    0x5030706110a03050903070c06031a04060305010e0f03210402220603030f0c050c090c190507060c090b1b01150905060f010f0203040b03070329281202030102 69
    0x404056180c040002d801002d81d07030010071607851500244603100c00a0b0003010030300103454640c03e01080f00101c2400c02c180d400b41c000e42855200f4100080001800740640c0054072180e42d800c10303228044013030410340382c1c0c9214036840d444641001c0c03c07081c080d40344407807003864000d84010400428004610000c10305546802c04001020b95114810810950060030f1f5440d11940790803c0095076101e5103800d5114034a004c1200c1c002c2d11600000b5200e03500b11012140d016680c440918142c07a0917203130050840c0c0049030121201c40c5011100c9400e1405940c850b42119442d4420710b00e44007075400556203034841e4420f001225901c5554001c801c0006c40358085c080d0908950000e51860301304100007961081180c505d040c00100b0710114941c5502000325001e503200390008a5498803840400c4008102d0034942d00c4c03c4450b6001c80c101d034020704000212513580d0880d03000340a481862014041c00500a2141c610503030356030010007110300440d287d0090240001c00040c2010b401d013000c1203001e2132 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 857059388 1250 857058138 857058161
    0x4060e1f02060a06060311040302040b0d050f28170a0309050304060e090c0a02060714070f0b040203240105040b0a050a0f0e0106050a020a110f19060201060605090a0302010c05030706 80
    0x4001d0410848121503c65203008210361b19080c00088960303140d00540384124003002c3e0280e0b840320079190060715025200300c441039002d004c446191000b10340709a100c0c03440080c0704101c00f0b4812800c40f140c05a034461031407001e03000042c0c000c0001309450003000541c030030207004080c107803038203e8a404a20280054402064141c448840b010700c0c54040042d4901c0080c0030002038407081c482c0c80e4803154005013556200c04a41000c1c204510040c00f55080b80c001c180d802030214000901e840100301600d1103141c011403007a021550100c41c3e0003203203403061900c01072012100400d6401080640745c0364000d05809040076060039005034980020458001e865000140c000782c2086080080c4003805441d03034010b103518a421420070f01001c000a441c0e4441c100c2c05402900f40d8413901e0f401d0303035401c60f00070552003009003100f20780404403400c0c907131142c8079101c1c010265203003140004e01079009600311040468000d01c03142505055a00640302482d100c034099038284030504c01980001c0e202e10441e4040070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 857060638 1250 857059388 857059393
    0x903050301141806060715020414040c0309020f19090501090c0e030604201305070c1b08030301351606052a0f1204030605180304060e1f02 61
    0x103040141a2485508144425003e0301290800c0401c0350040d0014603041001140c01d10b07512030322803c01e0921a501006d0791046140700140000307200764a01145d6140ea18117480501c078090044006400301c94007000042c0d0850807010150119140250221251408000c1c1045405032116000320440f803098203c0481d2a43e10301540141a070001090a02040110024021032800781c5d40c1c4d1640407181901c101800540c030041c100703943c0c3c0d80d250b491901e580e402020002031401c0d41303008109814604d81990800e03e6012800028544806048251140c48006518603460a0070019001c001141800007120a080320003518034204484c240107400c1880041000101c880144c401c00e4030b0715070204050020410804103002001100131134280c02d04108600a4600000c00904214404e1041c04c441c2c003446807561512030801018200f5240145000c108682c1c03007000300d0000882111076074015a0091204100350b5100d404046c200c0980076001c440501702400d10702c80780f000e2140f00340700581c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 857061888 1250 857060638 857060641
    0x50f04090201031b3c0e130207050105150301020a0c0803181603060c1b020f0f0307090929040f11090c04060e1906050a0212030a061805090d030504051009030503 71
    0xb0080095100c0c29409088044000400541250101150402112402d20000300d91b220309a07603030000c81002e414a0008155601c1d882880c01b03074003d003801c4800407000ca02c3c8284008c11410144280d0394082c5843e00c9a9180c115030340c8402e0126080242160421074008040c040c1a0b0b00a102807295000c0307094500d00740c1415440c081c010703100705840080400c0318028142061400000308026515019204500c4000d82c42000c140383c0d1914402464040c880c5110002d448c3c01664442b0401c0340c0504060070714800b090100103402a6a01d081c8103101c0c219802050220b560190429080c602c2040c0c041038510386200460850031044039003044000c00031074100502908400301c075420360301c21139040e540921034075800104c400c650301800c0c1c00c0110218582c4080c40c02040f054016007040b001c2543c587c81c0048510000e09420300815001041001c11031100307415902904e4040c2c040c0d1400707801d40300c0c800c100440050100a2041d64140700300c0c16078624142c080c2c0309540c0041d00a540f4903540303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 857063138 1250 857061888 857061917
    0x306020d02190e0a12030203070b2805010308250b09030d0b1206042003010e0d170717070c080307020f0613050a080a0201060302030316060b0a050f04090201031b 71
    0x1650200d14501400038040c01c000c02c994030880316a05861440202c85c00520050800300d2030b500668000801111449042c088126259501d90340108030362507480b40c2d40d404820004040c1c3e4400e20000f0401c10050081d503220f00c902c2143e164030002e9403110700c510f1040c0d036120b8010350f260a071118442030b00009400c02020743e01d070040403401101998582600340c40c028645076920001031002d80301d110810b80e120950000440d100d8241d00c0000c0c02030103542814480c5e107496007400e078410030204200101c100802c0d10010700061003411191502c0840c890901001510080010402410484208100e200140c400006180580f0555000705141d6503400c180a1030b008001e0403070104842251140750006000050f2000040e83c03001580380c664609900507800342c131654000941c10301001c59240e2641442040901004c0d00429040c40083c3c0204140502019180102500018030b4210072050b400d00d50098844981b0602d80002e040304251008501050f9147c910000207207140c0d41c0ca0310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 857064388 1250 857063138 857063167
    0x3090c0618092309010b040903110d0e090109020a0c02210d0905030c0105090a03050a081305060405010903120c150b01021b06030f040314070311010c1d06130306020d02 74
    0x40c01c8060b10403c141000c800d810070802c240c00c035040341c0c03088018000400f00c45080d00910754070b050241040c04118003a1801030844603961a0f0341080d8400c0b0080340d01d807503205810b4030500c50380240560b4501d90038503c0d4040a940104060024040000c10500061321440e9500b41c00400c80340d07800c040c0c480c40721502420890b00001c110b04220071700c441402643c4d80403920f03003502402401e200b43d4403025600426041901746c1d00c00b501600810001506200c9040c0c000e140c040c1d24070302c016091035140e204100c2580170318080c05000074201d00050001030b1920065104030b11442c00c241c490fa0400d0f40da024a2038540700305220030180c6624541c0744039601003040c003424081142140d041c06070700c14007049850200030180c0d42044207031004681418040d001024401550704d0b01141e480300380742006170156032180c1d443d206a600e080c01034400d0a2085901100804c424104e40c0320442c40b4404004454204900f201a81040c06130000006501480100f20304003605170096200e1449801800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 857065638 1250 857064388 857064437
    0xa03020406170106020c06130e01080c03060709081009080c01060b04050a05090f1f0b0705030910180317041d0402040b121005040f08030f090f01020708120703090c06 73
    0xa20b156005000290300800c28030340610040c2c0f035154a0303001805800100111715440303201078001c80d200204402c00b011aa80021001c15000c40d0700340d4580ca04100c410703603030a2040390303010340002c1d44000314410360350421881d441c05908410b082240a1401900310b40865025030413070540002c0401660030048003074002014201d07080d000718503181c00000407920b40105410700500c0001c0390620140c1076800400040c1541c0a00c1c00e407207002502d40b290f56036000110b421704c611201d450b882012841440503259207107004640307a440900e10b60301c05810b07046074085812803003024480030420307014290528450034110302414809003054010701044070702030030700076015425203100c2468101b8000742c2e482000c842050000381700d03901c0c0d0602c00090160b07124020100e8000100344038120103c2c0600d24041d02c3c0c07030003e588150140c5402ea07400c074411300b100140404001d01c4885180084030a280360302c6012030a02003946901c1e0341d50540b040038913411000125002c03c2d190500f0224030321110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 857066888 1250 857065638 857065667
    0x1121150a0e0d1d03160b030604050a02071e02031c050301031a070203180109050d0b060a08031c05040809060403080d05092a040b121b0303031303050f0f0a03020406 72
    0x140100c660204000308261404443c0d40d80d250000420340001d600c040082241c1c11203000000411603488513038160882c0d205851030351007207081c03802191582d04c3c40d02c201c40c80e4550112a1040803841c98504444041c080300e010790381402890250341030891090343c50500c060303030341d03480315034030341c1985400001d06803002d0061b01c03184c0594042142a03500081141c62501040c00d90310039011350382004941e100c07100d07005150068658065441003003038454041780111800c031841c0e441c507034550150310341e0380c05450300d26022070b602d0103000c1500d58640d42c4842d0f001409905240c0c0b42c0b54500012071032a41c010b41c0120b90f01c1c000021008502500c51003001c1e0000c0c4804003030840902c0c0341e844044180602548040751441c1c13400003a00b19034030f40d400405600b00103443d8611588000e9241c9481702076102c00d5040d020340540ca1300c0f500e031030040300b12803107203064608400c12001d00761409c0340d8036005603017484202a0b042290414082c0800050800c4603800c1c0e030007581d22428907800070f0040b600d400d0701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 857068138 1250 857066888 857066893
    0x1020313062615032a1203160309080c100815040902090709031208070503160e10020c100309080f090118080a02010e01030203190b190e060a080304031121150a0e 71
    0x11074004042202012400001110000c0d180616190502d0552144a20b00c400006000192308201600611074104662012040e1900300750000103011811200c0c0c440f68000858400c00034100c5202400c0100c012000988009101034050740450325045041e40d8040100300d241d581002000b00703ca5000e070381c0194a20b000062030425034409405804064030054000441c60303801c9603032611500103030a1035180100080541e420300ca0010703445400d00889240980c4c000388021003214000c2c0038040000d944051900e29082050301006440d81000529504015280505030b5090010b6003200014181d01009403070400308910016000050841c18241494010701c100003402c039004640001c008610a000b103009056500080d41c1e0307680c9454101c040709070441b0080380d01034048088a00c1224255001d440f89502d8200c0143e0304e00070f51000610078034019a04080908003101c138040b10514076080c0e4079207500303002d11490500c480d200000c403c91200e0010000c0e85001c5001d500110b0700382001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 857069388 1250 857068138 857068183
    0x31906050618040f1416140a020a060e0304050a03111c050a0f08131d0603011422020a061116080c0d0f0b0907090b0102031306261503 59
    0x80c0400d502c0005106611a5988400101602c0310382d4028858806070180002e429140442c054a604004c0e005102d0010b05c1c5c211100200c4e000c0c0030100c0d0500721264005040704d4a8682d2101c01604c0d03502d000ca00030340424800018161141c00442028610854100d00741c0c44c0c9441c203000303e07802011030f0803000c50161a50b02020501c085083d030402034001091800c040414201100740d403152072014050a9518200022144000100c4071480c414205140c929901c80b44201400c0e00d015010001911592802242d18601c84101020700417429144103020800250001038034804c15a2105000c5164541c03007507940c81c1c0c14060000201350710220f820045081200007942d80410f14490b80c0900e400002d4501405900d101950300203500c03480901c01898500c04090b110308a034481d01c86a1030420100c08015030000c01501c051102c041341c3e10700c0c140c0c03800004662146200c50101115954041c01c810841000907800d845031440d902030a04800e4450141860031010b901e03280c1c1013000261 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 857070638 1250 857069388 857069407
    0xc190903051204060503010510030605100504030b0c09090705031305030f0a08180d0507080f032a040b03241315090618050403020304121a01150c260319060506 70
    0x2520306448040c0d8127403903070301c0b60100194000c0640b0782209900080d4503c042d28034550000061054a1207a10444419107a000e40240c0c50f000b01ea0781035034004c6084000620803445100610340c4566580c08648a0300c100b522081d040d50f02542c001d0304000c4d000551581416008090260031aa04400000305103015003030080d1951800703c1b00f082000b2002641c0b40038403001728142c803040e448990544c3d42d00c2c105000028000f41056616640101c4104168002601004280da080f20030350083c592640c1c3e01c40c1801c8d0281d540e0000c18012016184000070500e031103000c201e80001482d81000147d003080b0f401118249500c1358443c1b9001c5042120a0000402c51520021080844035000c0340585962400f41e00710700450700041d05484185104405204900c001e030f0210020000306549c06989412444c40e4809071150458041891021010300048880131811851801820501d411107442e2910600715030098484601e800c114510321010007401e84a9003005081c00c80e1034500e01044003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 857071888 1250 857070638 857070647
    0x1505030114060a21110408010e010e030a091e0e07091e030f1b030807080301180b01081303030608010f06150302070302060f060d0609030323060a0e0c19090305120406 73
    0x8054403100b1510800202c2c2d10307074a80140002c170550405150300d82d80c031202018024040401c04200725030802969050810020040361a6061140d035001e440e281410000150340c0341c0300c1e1400703007000e1600300009850740a0401040c000c00c800c1e5520f4213041c3c40c0c026124550707180030741c10f6001d01714200f80800026510261540c82d2030340c418010b1080780346941840c14030141d1580302800841c0c2c005a12020400301d0700066058850000b002d0410800042c0c641c1c089a08506d99203001c82d01001c00f180114112441d4400c0703043c4245004101d0544501d4000d00792402100c041041580b0340c0828881c43c42031102c0d5403e5140d0078942142081c1460710000e40e2060090b02e0307030142a00c40404600c464039201240b1706260740140c01407241c2c1c003240c6002001804203024402e03c4980d080d03211340b031020005002c0390250700d006000d9203640703007820340d12419090040c15490850400700f111800480440003c201400503e88920112602c0c0d07084c800e0811891040403200384c0d40c104411302995800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 857073138 1250 857071888 857071907
    0x11120406080a020f07050715051204020634020108011514030a021306080a1b080c09030c0a0303020a05160b1c0b031501090f0e10151505030114060a 65
    0x181d180c2011191070782d5140e00024400c130030000303102c1e80d00014000148000020f1900c02c5a54542c0b5404108010f18421961401000d040351090740d5003901003000341c5040f101500c245245600c0040e105030f003070050320ba040400001c40c040f440c16480c500800b5503030440c2c20280182500300c480864190350020042009440e0350001d01410341c048003050741c21a591b810b55102d5100b2032004001d058075400040c1c1417090403075440c0308075410150003011742000c00300c101c0349181d0a512403541d1038603402d054054603044211520307003610506800540c0c6540c2c4049090095019401030080030020b42080340c10221528151000703008035100810078244a04100c0700898110b6038580c54613818454000003070182d045065a040c81031080010700d00c03026491482c100c41000608001d4002d18080d00c50503140681d20760f520607003182d9100300d031031617494201c5919000480760240c000c58481d0a204241454002c030400000c01c04801400810085052120514030031175026050440707206009020000c3c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 857074388 1250 857073138 857073149
    0xc1e010e010f0b091b0408060a1b03091a13020913050c060a0f2624030a030e0415030c08010e0601050103060e071d060f07120c0812060f04020d0c111204 67
    0x1080081e10707004c0c130b44100380c4000e1f0407250150740f40e9003415006c0d0300140010349000c0942e01209a20000715a01a00c00d6021080c0c1c40140403401039280003512508030801420301a07040e80c1e2003203110059030340d00c41940c8245207400c41c8905500075410050300c0c040e40c40030000c0c000d8104000d50f40406800081080c540e10380342c5010351803840d80c0741002001320003596040b442e10740c402c800d00618400e001e881c885904c406620103046a019082055614140d01e400500880c1c080b8904e01090305090b00301034041c040c403058200402d5070300c0c3d8450310804025400080319035901c40e080c28410905002660043c0f20910f002c3c03201e1410070341e03030544c1900003070030b81c0060200000d4800d8441301e0304030940c2c181000003042d468440301d04a903401100c0d403207582c0031150000d81c1c50b0381e810b180d400f442c95405075907002101d890030520b00020341c25103c04050150740d03124074580800101559a0f00080040c0c0102d200007182e03150340300c50042d0641040070b0b94414660080c10450f8549407006080c0e4003101e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 857075638 1250 857074388 857074411
    0x40326031b072904170f120604150e01031502070c050402090111011b0809010c140f12070302180a080d032307110708010614060c1e010e010f0b09 64
    0x11003034502910941240d050000b0301e400414001011859414000c034491070085c140c80b0f207090310300c0d41050b5040c41046140d01000304148807520a1600c2c225410b07505c500302510002d110814a066450060060b40c0100818075034440144104640308200d511600070b503050070b40c202041643c0d031f812104c0644c007515020b5580458031490303da1252440b14060000c000c0200300c1441519500d1070880036095501010074051300225481400c14829400b020206070b40f002006002c032804400d40754132110b0b4a000981c0b080c0b0910700410070884200340109240d40300107035a1f41d02d5104e0b201c1100c001f4a0741902c40c2026210400040d00c5c040b4503030051102900d0001103031030f0812410111250300881c89455620340000300003080307401c0b01700034510ba0350000449104a81c6e40d00a1802e0b91054001e121407606441d4041450381455006031070b0410700030050b80e0034000544410043c10000c4054002c0e030b03079128105241071602c03e1058091540319560203010b403405800205031301c18006032a0300c8000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 857076888 1250 857075638 857075647
    0x10091709010e10020c120705030d080c130e04020406120b0f181b031c0504150e04050a0c18060c020f210106080106050d020d0b060102030906040326031b 67
    0x1d80c4202540700340c002009001c0d29102c10301d800025540d02164201c0e81c020070b1010118100d42d400055040b0442e07400500912180b0008202140c65200c0900400c0c580141400004810000c4000c408050f09621000d410940390038010071082d43c40903030211025860031641c81c030219007468000b50344511448141c1c486601ca00601c250705d84581a28140301d030003207900c056801440c148080c001c51204030221410040802408009646c019060354080742040104201d0f94841c070840d40f4101030b5608000f0295543d800108040e80c1086610400803544c8030381d10420340746c01c0039041c0005410711001700b80301c50030010013400300800b101010f0300c503404441130280709603906004402c071613050280c000c03546070007541464040c14090003403500d554203002c4c0208103400c20f01e41001010760000c288144402442d16010000e800c0030705800d0450108011800762611160024801103118440a0f14880d08c01003403043c00042c05880c491080b82c04006124100c007000c50703c90028031401e460349590303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 857078138 1250 857076888 857076907
    0xc090402030c150d110a090e04020409170d151511010204080a03090f1d0c13030b090a0308010801060321030906060f090506090f07030c021e0708100917 67
    0x9114481c160158000003d0701c000c00e0110a06001d4041504001c1d001c0c8401c0310310362526540c0d030190000d400c0000f0a001d004000b4085481720180d0094000703400010f200b0b4203a119811000c4c44a404601184400180e8401001c1a4441d01814031031200303507907040500b00403003800102c047c500502c0400c500264181030021007036046400401c8048211441c440880c5800740040c02d0b03e20800c2d148a41c015000200f4281d5400700301c0780b82c100e51052003140d0380c8815451003d034000ca42c100550214441c00400011540c00303110740038000180080c04802c540380340080514005801111641c3d0400c00c1c2040010030150407080070740c668060602010078401d10450050030b50070740c00307054582410f0000411170045a2440140c822030750042c00540d56071818042000000d40702c0d02c1c110780254000a6882c0e2103544808801c41d00d6105488000c1c6410307000c00c0443c401045894141c0c3c003c05810040d035803042022a1104803101c009002000094030780d401034040703d40c0c21b00300c030fa100044c0d1800c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 857079388 1250 857078138 857078143
    0x81005100f020106081605030f030f0318031c0f0e010b03120304080d0f06150f0c123e15280c090509060f0904020d030c020d060b03060a0e0c09040203 66
    0x5d80f400c98201e40f06c16407140152040b045141c03140034040c4c0605c3c10380503002c00021084030a140c46c00c0424501d1525041016003030060b5407084030300f480c0414421130888800d06005854145070901c40030541c11120644c81702126210080008544e151940340007582c0c4001c545820f64504420219869030380e903081c034101318402d0850b119004c0b854103292203109021540b204094494107400c41941c1e26419400341c40101d902c420341030200d003400d01c80e58009402c800b08005c0320680c0340303880c810f092481039400181c056610104c3d2010282c400301c8800702120782c440014036044032001007551100940402d044c64001410a661141040b1031000011307008401406078040d00880401005c20054001803580703116000386c6204040f90b01c040345841c6002056a800c0c540000d044401c1915643c0c01c01c2841100d03c4811000e105540710340e10096070300c00302c1c0310810b00e0244001080001c085420181480740c0103200d20022841c0c0103000b154507030000360844142900340c41c4149251110b000007403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 857080638 1250 857079388 857079401
    0x5010206160e0907210509030912030f04030305180a05010c0803270a0605060108091009020f090c0403060b0d0f02010833040605060c0a030f0c0f060903081005100f0201 74
    0x1508000203c0c140a1416840341130310b481006442101c008464000540030113640050740e04101076442030002c1442460a10324003040c58405a048900d00006800c0307400715a0001e40c403e0f4041800862944141c2d17001030b0741c896603d4000c5509410080c28a030028051444009024010100102c001f640d0804802c0241d024001c3c10f55025401502070b060281e551400a02e04445903410030700030488650203071000030b000c2d10094005d00801944c03030031614000c1041c02c0301664008142510070610703072a142a4140036000d8090166a80c60071410a0301c103130b0b03071500c608034011400404481c0104204610308039a4560920341041d440e0bc410598008194450408200c61680343c14030204041520749440340c5458152814841265114200405402514080582a0005070950001074401c1620056003046410804011001034880244000c41c4807000c0f46c0c10350307896001809154114012540c40300c0300c140d0000145003084081400c5034900d40e07c280a0002e4140e00c22907583c000e42248 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 857081888 1250 857080638 857080667
    0x70b0315090a0b120a0305040b070302010609020f1207080601050d0b120d0207090c0c020604091d0a1506120f170903031305090c070b060d0204020f0c06010e060301060501020616 78
    0x3a529080140900b002080303e6596640710f0b1001d400044038801011420032003994058582c241054501400c1c0c0900b541b0201048007155a00c000c0400c110f1541e2015050080c1d000c01c881c1e80350940400e401500c1070016203148284903809003044100c0c1e9016080755012000988041401030401000c034800d1101c1d181c0d48507040c0501501c0215042d4001400c800711603183c54184009603001a007a01c100144500280d0840001c210030712840300c080e004841d40726207210303404c004001c05400081c20b00d03c2c681c100f1030b8841c40c5202d0326085040e0500444002d0001d20b08201c0c0c8010682d65651118030002600504049102e5a9103651003108030680b0550301d80035041c0e079034803200c1c103aa86003884168000c080c40341d4840d5010540e002e4800c01592106944862a80e0301c1d6160903082181c0782094140c1246d10070b07000c00c2941072890340712010709044a07154005080b1541000c81a2841e064010a0356000e03030325003841001030f60383c002a6070350812920304081d005202c00000464082c1c0505480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 857083138 1250 857081888 857081899
    0x10c02030d030509010b0d0b04081602060a170c1603080403090f09050604050a050408032809150e01022b02040b03090d021006120219080f010605150c070b0315 70
    0x5426400e4042d00f029110700e891000800c0a0003916040000000b00a0740141c10702290100042c00200c00100070b082c009032400d011107419031268000b440c01e5106021040000309400c0040c1c0510700706403100c642020135502014200b40d40f65000002000301e866014082120380804101414011865103001e00040810030070000c0d2503603e0078000d4001a548240224030f44800520044e0720ba209060140d5840f203803551440e2151b4410040300c08490300c001803130368000480110003140d684540a4018414a43e14048488090005045440307024420700c05900403c0100340741083d03d411282c804001120546c40403d07191030030741c000e014035000519003160000c24004500d00000d038070301006103283d0856400f5001c51001209036101c40c40b0f8503206a8010f84203030f0061030161382d00c1d0071a541c54143d01f40404d685040d15450301513130050180c00e69540d110140320031b0500311140c90605900c403003050300d848180c010040d52002c152040301d01181005c004a11104080003e902245900500c1e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 857084388 1250 857083138 857083153
    0x30f3f0213030b101d0c0408010c0306151103040b0a020c130905160e0103080a05090a09150b0c070b03180d030b011b0f0312061706060a0f1211010c0203 67
    0x940000740203a0000355002d60300d9400190607109880c5819064440b18280c1c1805d1208a8000d4401240b015000502d42c03042440085406a401d00c1440060003450380c0202d201e61400d041941c410303019214200030000020700d001e00884000045504458821b01d01d25511103062108034104031040807241c4e4010011704d00c19a0f482510b4001d0450580103e054600340300a0280008002410303105101035414440010804119a50051709850241d03081251611101500240241c00d1540002e109a035440284034030040d54960032002404402c03030841c3c502080d8101c0b0a543d04c169200e10314502c140000003555401d00c100c560b0b0340b40002c3c8022034a0b125031905000c0c000e419414205c3e4005003132120500303500c808024a50b065140c110190101e0001c05450890301e4045503403d0002c010740b1807400041c403460002d0520545440c00e40640901c0c00d1070781c00c200c40072409501c895400700e040031003030050078001412100215130014510180d0311469005a0754100300020180d854082c0c5c21 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 857085638 1250 857084388 857084407
    0x1302030610031a13020103050c04090f0e0d031104290c011b090302060306130b06280c0b0c0d06240f0f02030714070b0412030f3f02 58
    0x346010030380c2c1c400e40600f1034000204800c0c45150000300c4070003e1800f001c405042c0554000d134085504664447c0d041c40c40c01d91148410400e032000e90548201255940e0140485030b101840701c240c0c2c00c1c0ba0351406001d26090000441441e008070700680c000d0001d81140405505041c020040074042c03807a00140d1510080102c0c68020180301440803503100c00004a02c068901c0390007903d081d65401411b460031500d0711018068180550500b104031141c0e501c1300001c4940d200005410300400000d140c003d020740051840041502800514060100c00b401e82c0c000511124040c0f80c0c000f0000e5915074440c03000d03081c4180980719039844a00ea6007600950840031540c0150307207125286150711508140b01801d0400c6075001c40307961840005810600192000401315070500300460b0140086840d4192600c50603402984036600007011141180918406c140e00305800700e450721840c0c1003201c04422084085104c10000c13075903001a550040341841d211101d42841c0441511100000715103614209 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 857086888 1250 857085638 857085661
    0x7090504200a05011202031308040807140d08070f0618120206060910060f09050a0807030b0f0103031b05100e031c020c0706140d141008010c1713020306 67
    0x814000511510010310003481d400c0410a5604580061799042c4a00c0d09101116009402c0900f044100103042e0b103038200880e00100c05000a00141c0d009000c075246401d207810000781c4040c0e01107004e40d60802c03040010841e810140c82416802000240b480c9146180c408014505601100b5404514501d507000f4454590060140c0c0c1d8442d408540031505c3c2e09040000f8240c0896003a180518004400e12400784074146590541029003440c1011a440d4000100c000c01103410240d85075000302d00810611502400003a000745060550752425410750318014000c144110010428441019003442002802c01c20079000750058601080010022075206450740e00c5421080b0401c0d0070290b091403884042c2c821180f08181c680d0040441c5071a04905840d51221403182d0085081c0c01d0250747c901078980d004990f206a00080340d0a02450300c901002003081c544d400200041e0b1401d44500b80389504440c2071140040308001105441e80d80e4100c1648804071500000e426019100a00c010300444 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 857088138 1250 857086888 857086913
    0xc0311040f1506030b0303070204020f03070f170402040b12010207030206180102120f0a0e06070519080105010c03080604061d0907050d020109120503160312052a090307090504 77
    0x100d80600220580c41001c909481032104a40b80c0c07941180010049580254800100c6420183c162400c003801d680010b8202d0300001c8013003040c3e407000010012110762180107009000c0075818414101c1c00411500760100c0e000030700081c015650303910001502e60f100740400900740c0380700d002075555103014a0000d44940003900d01e038403402600724400780e1501b41030080e84c00540668000e0061a60350f0940c000d0003080140c06940c5641d075802c40b03402601c5041c3f0840e03104840c0d580ba555920148801e00d484070b450600451001c0085040c01408a40c3c2d00101d94200c071a0146401c40243d1105030000b8014042070f0311240c0074209100040c0029130391420510701c51a00c090581d0405540c51b414030000c60009140240003c1c9003840030711604e0f0350010b2009540d07000745c3c02c0342d04108402c42203c03d0b240f81d4a40c02d40111300c1c05082c000c0d01a4140c020203030300582c05115140a088050001485020755010ba0f40c142c2e1070100743d2308642d880801c20100100700c0000c06022a00702801c01c0b40d841c600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 857089388 1250 857088138 857088173
    0x2090619051c0b060904203c03060603040c080f10110309060408070f0c060507060509010b03101109040903081801090b131109181603020d020108060109030c03 70
    0x21086480b8048052030301c40d80c091400d0141c120343c0380820070410400109034600200700c035452034400c041c8829050358041e00140750704486e00c1c3ca55406100035000f20218504890030700120007842e40e01c3d00041c0c40160b035000f03101900c407640c03031351500d14064240720b4084d0000f104034800d40b00c4201c4039020024001d40311105a560410485c0300c10520251103100842d82e081080e4444404a40003440803030040240d00d0040c01c00001d0190b0b6695101075044c2c16a00a03030000c4c0000c221001481481d10606400c11020320082104006150100b0744640940700307204003450750b4890180c0c0480c119011103072100c000600400c4605400c1c075026181c00000d68a041c0160502414121038440501c54203400e980c028a01c0c4046503941454202c0321000f20300e044070446070303281c5644c00c552541e44e10540a003110240e48005651080c00303c924058490003884c3d160311004004001503140e08500300d001c07a4082c0b9040d01107541d5000140c030821081e0b0302c0200600d8000740000244000050200d10040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 857090638 1250 857089388 857089417
    0x80910091b08030f0f0901090f06051213050c01082a041d1b0d0f0e010c030c0f050412081c09020418020f0d0204110c0307111005030a0209061905 64
    0x141c0760306000760b03240184009041001c20170842e80405060b05000791045c090145000042240c8a1a41c01c80d80d000607400360b0082403010441d5041c02d00020a1558005480c04008802101e03a440e011340c0e40b00690622410320008002013403401d01d814058080c6040c00c0c1400882540b142a400c021a03030192143c00b0146041003016043c002c0c801c1c2d440ea00401018441c1c805c1840f00000f0624a0743c00044001c00203903640000c41489501c030b0240242e00003841d4000035207000b02c43c60150a80b0fa40e0801c1804001aa40c000803146800070155800d031118a070007160f041103030b1310300348a003071040b0724250180d2030041c5001898006c1c07640104d100c003803003910300b0f200f4030581042c8040e840c0710341d440c002c4d8440781084030300105050501011403074600041c40411408030048610010350300c07512051000360000150242400205d40e03c0d42100d070000e880f101c5100c1060103004000c1d00014081e50426500021281140ea54010640d0150220030160761066034000c100982258000000f003482c11 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 857091888 1250 857090638 857090693
    0xb0601080403050f090607170a03110a09060e042a170c0d09050141010b07080304030e031f0b09072003041d1b0a02030a08091009 57
    0x194890032410380119490b03103800e4100600100d40000b180c01c1110403641000c018012240410070300b240800c074400c9484c0c00715a9645000034004e0076511f040882c0780011004012001c0e920394411007902c125001d500c0d01c800b01100000005010344505001030000444c8180a4550710349060700024014070980c03992400c0304a48111040003450880f103c490449003400b19046042c02c42d00700700c003ca4407a10001400b0030440761a007142c0003004048086401d145c140c0c0156040c080c0810741d1030b0064880381d4981961500e21409040c2c4a14040140910000b00104081602621502400c0180141940c210321307100d030f400c0240c000044901c0980b16040001c1201542010a8004d004130000d03a16400c810310740e000394400007442d00082203054882040300041010404a4499200e1000b070a111181e00f00180210903183c0a00744c4054070350700803c491254a6000812070b450554203042c509444e5840b042203d003014400304007803482d1400c203440b180401c182a491014207407604e00340031101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 857093138 1250 857091888 857091901
    0x412080f0c2a032805070608070f0c08030117032104060b040b030d2601140102070b040e0f07030f051e01060c2a030203030403150f0b06121803160b 65
    0x400c48048046030181c01034410101240703500601e10f074040038100a011910300c416505d052400d401d50740190f0000c2c0c000e20921030040e0340701481c411103011910740b80c60072440c1c1e0f440e42240d500c03046c861440c500040400c0000c0d60041401a10714030a41602005100908a000e40310242400c079011030f50280f50540d441802e03d4140b06103a05a000500180880d0400003400d450800e25458040d202e494800840c4038101000d000322030107010309c0d203280740110901c600064900b4480f03400010034504244000d00007424615042944800009600507a0340c40308502500240082002c2a02541c2440c0030400a0302c0e8040800c40341900c49020000300c1da0360b07540c0031078039a440210000c000c040c3da00d810144481c070610f02d202064441159101009560307900091550f07116034421101c964160908444004e810700c103400c005c455052003404441d00d0480040d41500c070b10501074103481d40c0c41c0d012032401000f000c5c1081e1001ca01a045076555000a0f036400030441c40e0034001c540d08030048002464 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 857094388 1250 857093138 857093203
    0x607080a0b100507060f0e01060b0d0507020d02030a03020906040509010e040b18150a14012c1e040507090609021b030a05070f1a010f17070305030412080f0c 69
    0x70000103d9031000c3c1031140399aa800090720010400f200c920761103103195290203500b0310402c40284940c0312000e42d03e414101d4203030700b40c580c010800e10654009202c2442515001b10441e5043c8040f80780069650250200141d140d00480d004660000301d03800000c618007612001c01401030740984003c60459440c28089400d044101035414510b41000d4200281c012090450035040352191001181640030600c0e51034014000764084804a40c0010381e4139800001c950300074405111144030218246419002d680d10440814013125160f03101c80001814403000b40445c2015000f240c0040c0003590384c2d0381c1248007079002800105140030754004002e5004000000702c070b02d160113a072100340c1081c0d00c1d6114482007182a48040e43c521240340719001c2403244003241c03a07001c3c011310181002c120b414503500300e06800010405082c55801000240081000042618100d0340c0000003a01805c04c2791a04204ca8080e80c1ca00c1c1101c010041160108941c01241c032038600c46954440711450b44990210f6032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 857095638 1250 857094388 857094409
    0x1050f03010c0225120302030a092c090f010905100b061314060c0d030c0e120a1b050d1101170412051e0304050f060108030c060c0a020705030607080a0b 67
    0xb01583c0300c08002c49160411070124071091070f400782040b01141d07864154681840e9032060071001600002200c01e039043e00014090050700030030010b20907050f04032804107580307012400600907850103140060344555007004403103466070b9801c0c000e0183d80c0c0d0901d000c9a48007102c0c810301d0585e50074601000142d050840c10345e40200003107110b005401c2e10300100030110740c480e5040da0b80c1143c4108601d585e2104100080500c0c0c02a65800180c5241d0ba4000148400c030399030b6281d40300d6a490001c1110003417000540c1d070040d80e081601c4644440b00702e00070b800328088650202d908400c000013048148010a80c640c20326400c02e8071000c00120060340d001d650808100d030010034140d10b02c440b0f110300d280316202504140200d224089400c1d060074400510030340080310f08071415407100c02006401c04040c81220700600c2d4030342c000e604051500203241c3d02d4410081015141410110702400304034400c111403401000b0203401c3d5169414443c0000380410b00407248111401c0c03c2200302d8825080050000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 857096888 1250 857095638 857095661
    0xd090315020903060103060f200c0105010f03020d02101e0503090705010305010308040b070204060314061e0c072009010609060201150b04060804060f1b1407020f0d080408030f0301050f0301 83
    0x4019176805d40d07450310000c10407601e6003100190b0303401c41d0482c641c15016144123400e01415482d07031112050143d95094503016004440813400d500003c0005071104000b41c0c400683c1100c01d40b001c0340c1041412501c60840034040404540c80604581c49c65030000001c6008008010075114070b00c4d203920042d82034039004e2000501004041008100048606000e856541e20042c0045261707540c94a4901b1940307100300d2001c205402031001e05c00501400c844642032504080c003181d5462030312901d000c1d0036000310341000c0d002d540781030140c0d04804c0c2819a030480300312008020003002c0d615100010002103160180700050340c82c0c00400a000903800381008103c40484403000d01d00307402c1030000c03920800003601c1255015142c5c3e1880d0760101c5907001e0f08051007003e840d940e47c5810f000740b009155181c08a18507046030405c202400268450785400f9004000a80d94203a4280703441c90011500d1080381d114040501011548005c0707100d1480085040700c1088800d6040000c01d0003c06080700da03c1d8882 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 857098138 1250 857096888 857096893
    0x60c02041e0c030f1b120612060b040507030b0906120a05011802011701051012021b160b120c090d0602030a14010b0a12051503010f0504030809060c040b07080c0d090315020903 77
    0x41d040c031144200420484e01410041c0407d0061b500c25000380c1c00012060300b00c4d4440e0700c82c124003090b800c00d8495982e12411614081c08107041080129443d140040c00700c5002e03141c1c41c0c5800e6100c1c20f0400140c1d20895120008000394840c0d6204102ca25080075001c81c0000e80140121801c801010410f40c16104010108900b100403842c1c21f0350134141070045c200f03515400b8412031002020084a00150703201140180113a02002001d40003000055004041003513801d000d80d0748020740d000c1c6101d602c0210820025521240200082c102241600300201402d000200b00700b8610610740021044200c040b00c01d090f42e0740c0380c2c10110700902802c0c405030300149968203901240003040d040b094011040e29007001c0c10100d0729000c00d003901c1c42210034540454030f1390240700c02c05034007500d1158007801800c0500f65a08103030001d03080350712882c0300386c1a41400c003244501c10b204001003125591b03414042103c0010541080117055128030344000d03160b00451600d4502d040d207050003104d0310709800401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 857099388 1250 857098138 857098181
    0x507090e010203241224060d21110303091b03160e090c12070f090e0d2a0c0512030f16080d020406081902030105030a0f050312130c0b13060c02041e0c030f 68
    0x103801440d00508051802c10075403c1d1029400ac0c4207200640c0a12010f001800348401c0a0002d60350f040001c4078114041e5101e42d4001e4107540100a80d10140d6100c3c80d6207407020f8075902c000900c5c00f0040c9260310341c044130192412842d894001200340440e00b100321288c040550761144001215a088200c860350f030405290040d149110700d04034000d00c0c642142480e0b480a0003003242c00d042ca001441200d50901b100018002442c101300180031400d01c0700015440c040c021142c80440e40100310030a5111034440ca620010000294240d40304074181880c115221f582c0d80200410384007081d1800858902c103060310301404075250003168160303900170300200301103200da55490708014200c0409442d039000070310031042c68005007018940a643c2031060301d481c0ca030703890402e4845204103a00504a212040200f070288003907118a0744111403407410002c00910003800400c2c0a0024207060000d820a85400d4411101c071562109005a0b070302d43c1d00b001101094800d0a040714903030750148a03051395480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 857100638 1250 857099388 857099423
    0x50109060b0d230705181543110d05071502030c010204060e090702060906011401020f070306062c161205040507090e010203241224060d 60
    0x10015460f10208240c41c111460f50580d081c104a0029244c0400040b800607000c94004101d03289032140c3c020031184542c140b0f801442640311440380701d444403568190343e0131001c1c0c207001040541401020100031040c0001c2c15256884036030390a00800c5501140c14090580c02e41441c146002010358003070700900da10350901c50120306003040c02d034141046110400030444049020300240000700101e0326a40c103410340c03010070054003a07002091030085501100c10442e00c8500021a00e0460304503040314448a00d0240040b410003580854014413441a24400420820294000303000c80f02c8039520b002d1000304110744510740203501405402c143d002d820100396603080d500c050b010b0400301c900b02011024810503c0740306449003181c0c10b41b903640100d03504002c1c0d01c0050043d1814400541c00841ca1803510202120315402c5841d040c441000201c0402111134070741d02c00e41030342e6070b180c03a0031100c58030013480e652046aa4207803603107015128440c000c84e0300c3e07061900b021803000c1d034032211100005c2d6011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 857101888 1250 857100638 857100641
    0x71a0a0f03200f07060615090815040b130b15120f03030f061c0305071a45160807060206011206090b1503060f060604060311090301020a090603050109060b0d 69
    0xb0071141c4440f10030001c070000030f801d910408000704010840c84130a9103003410b0150152000c0c4d0301111a64010320104a090b074468483e05d988242e00642181441e00c92203420500c1c0e6806810050030140c5070700034825145201126903403c601c0c01c40740f4180d20f04a5607500d5444455402140c0c00540c814004503840960301c02009900c0302028080c808901400180c00a211528000640109100144405c240074200007071115140020b00070404a04104201151010042c440c1c041002c045448520a003940007410524114610402c03046000d44850100d40740c110741095003420881d203010000340ea070000300301c0d1021548190044e01081c1c1c60a20007840184104da8211060f6994014000005003405c517014002c924400c581400c002c064800e040c50a900030f015403041005460401195a441c00d084405903074240c900410f84a100e20869200307400b8180059134194004030303081800e10b03884500c403000c80341c5d99a001d000e80d0343e0b203503000030480c0d4940c0200c0140702410408008101800d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 857103138 1250 857101888 857101897
    0x190e1c051e030a14190e03130e190c120f0207020a03020f1206011e0e16110307021804060b240c0f01050c03061f050306040c2f0106081b12071a0a0f0320 67
    0x580c854151702ea0a200c01c00010bd031800c01c0b1110108480300c0000354010081e1140c0d001c108005207007149441859000218071010341d1100034412148200d1210240d1240407a0034101101c03841120140c3d40c41d00403c82800700060b1402d40d401403c5840000e590b40740c92415401403940c020400701d032441040e030455020443c074004892a120070400c0b000143c507142d03808407001c1021418a4903034201442c111041d5100c0c5601c3c3c43c03107144400b289034090004111000134040340340c41035075906c40340c200c05503041c500b044900e11029440c000c20050341d00310302c0c001188150b10442c1e850b11944507072085520302114900b25000000c00030701c005642c604141c0d00100345030f4401d0070a0076800000807468a80c05000c80d810120112642400c948628000d00480010302440d10280050350740000c2d8030700079144800d08140c4540b10001c040f020b075034424084440544050700307074000880300c28040004907603c003903520300005100c0310440720b000c0d21030f220740088941c05003c82c0d074121361030070348130b140f076400c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 857104388 1250 857103138 857103151
    0x1e010209040908030106030f181b0305070b03161d0603060f03060f0603010b01020604030c02091017160b072a030f0609030207090c17190e1c051e030a14190e03130e 72
    0x8079500c012011540070800d4000804060ed0b20595924000002110100c03281c0c40394801d0060091f01d0760384134103000c1c03860101d40780262a42c1c1d40742e5403840300142c0001400f10130240c01d80a00400d100c0c409800c040c50601c2003406a000b0300002c0130003001242c6d0f50b00c0031a405000a680111b111340146402d06109400c680c04002500c03c2d02d840345039503032400d0400140054690f110016800c10410400d41c000010702c042c0d80364505042503500d8401202c0c40381d1200c2c84192074061222601e0f104016103120185030003c60503040c510b0145000b000034019070f6801d601620500310002230700c01007801052500f20060341d5072000b40b045201d1618550f40d002e02a40400042c030b0701d062001111074815600074020010081088504403d0600306611304036078540100142040724802086c9400081c5031300a0841d00e10903942e07600c2c241f01d40c0c014403186400111000e00c0c3d10500a49a6250341e0b01c850705802501c0c03c2103200241049195284140e100b000c4d1280c812510030001c2c80c4c134a00000e07901171b2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 857105638 1250 857104388 857104433
    0xa1503091b03120e010203190201050907090e10020d02040305060c120a02090a0e06040b1c03090e0c0a0c06060b03040308041e111e0619020d0c051e010209040908030106030f18 77
    0x40b08e104802c0d807110602000c081c01070b99540300304104134008002050051522140401c102c42c074144c50191641c0040040b030003495000516144004c919504035802180c1000c156140c0d030500b40d0102c03103140d000e0307400e000c2071881d058049107494a0901c01c60754003440c0100108140341c0741c542d0007144102d0080450342d02c540d554010b10110341320404c0e05c0c81c00341c80489403114038018502d0301410940003500181100c01311070003040036048621040340d01100329400c004440300c0d514134100000c1c10301604450303030b10000441440209030308841e01a00451085420300b04a203800012112041030450014050010a0980c40d07164107114840400c000403007040e0703004007011080400e0580e80700d581c02409550324072141c0403107254140103e80d00c8268610740510f121000340c1760142da503484d405000c80040c010310411090101c0075030444600c203e010380140070001180c10300c00c003160000d220f0b583c0420709204051044020a01c04c00b0305000c68001100300070012501c030404001030f511404201030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 857106888 1250 857105638 857105647
    0x302090f13090c18140609010b07020a0b0c1b030a0228080303090f0d0f020709021b0a030903060e0c15030403110307050303040201140c1b0a1503091b03120e010203 72
    0x3841c104400d0f0007034018403030180044c0080c280d015084a0500d07414003c480d058a060110b641d0f00c440b2020b044030f40d40e80305240c59250f140002420541c0d2075102c0300c120b0a0016510340d0300303407002c100b0114030b51800000c40d4888040700c007450384a060741d000c000c4d030180a4a03010030320048800c0020080400ca201d020804a84802045103903030707c15a500307046948081c1802026030803c003c01074034032403a0b19040110501175080a961b8114138069100003d402041c90919000d245031012340700404582214070000f50303070501070880507030790000f03480c40d50500c08200002040055440301c81c840140c0320307084000740300c1a035039456000a4001c40800c080c00d0400c0b41c0300130701000606281402400555a24149031001400d03880a0030901c001d007040038070810354142c8000c030700740303d01c0713900c0c5541c680c0c540410400007003a02c2540d8019462200f80d2104440445506600c0a92000e107d00504034108107049101c001241a0703110003410907044802c80c039400e512030804858440c0040c0105da040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 857108138 1250 857106888 857106893
    0x301510e03070e2a1801050d110a020f06070207060c0c030c17010b01030b132019180b0a050f040f031a070314060d11100201020306030d0302090f1309 66
    0x8042c21540f110100b80384000c1400002c0d41c000700038030205509403151954800103140100c0d09400b0f08000b40b04040320b140009201a4054411207042469610041000e01040c0c40c000070507410591101c0014428101030020042d00050510701a591503002415402d241040c1214030301040c000c2111030914030b020000000711010381c504058041c0b000602c0b02000d0a00d051030845046484003030416040036420103c645a0718401d00944061000108521200c855150701c04100d840c1141c08803800007401c541e00c500d4010305620318000c2a0b40342203c030700a00c0000c0880c5116400703417a40082003001002c0b1480d0041006100020f5003400080c00c1075903c007083c2040312596031056540100d1031040c2c8510811130762403140c5c04a014202000000b020f481500340071980140700a002c3d205c190704590600810108140301000018886000b10802c1003009000c0e41054038060300a00c10031861951441c0607009490f003807500508111842c034400303410000d900c0e15800310801001e40e100d406001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 857109388 1250 857108138 857108143
    0x201150b130f0b0a120501030b06040b060702130506120c030d0503070215010f05040b180103080307090e190615020325150605100302071106090102120301510e03 71
    0x61000d0200161509203064005d440300007041040d0304440e00e040018400a14510344540d00000705840014606100d00041003c9101d4800065400343d489559405100101d4000d40d1040e2002c0d12012150281e196400d5503c0d04041541941750b003003c10b2143d541880f4401644d8885024410cc5000c0c0725814006104a58203030405003101c4c904032414000390070140540301c03a00109a4008403800c90038080902246018080203126840c000013054025110b55896000781910001c060b8050030646000c90b43c0180e100d80404015040207000a000a400c0d40c0143c00c070700c215006189010070002400040500d0110700014a0341010700700004110400303100f2104070100c80300011014180420032605015039629523007018010000140007442c10011150345050540e0095120030740040140d00b003002c81c00c02d02008030404000010164060b650729802c040c500c919500404a0980502c1d5200d0015003202c4900340d011215000d001c9114910101c076000d10340f401c80d10340c1d281e240c0040e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 857110638 1250 857109388 857109419
    0x71212180e0603120405010806040902042c0601080109080a230408010507020f010b18100e0c03042f091503070b1b03120609040f060603210201150b13 66
    0x201009250001c0100c1410b0130403001481d0290005a01c0c10302c1e10b01000200010001010390380100d460341198011912160044401c941e6141c0c40b0544640c19600840c0c184e044a401044051245000019441806208009440e81c000009614100168078141c0d04000c4c0d191650013500c0300031840300c43c00e00764200134202070076500c400401d075070a0065000b441c103c0d00f1840c60904d80d01d040c251000720740e030b003514140385c0f038615a40010090b9112798030f14250861a40c003101c0b507400041c0800c240c4410751001117100c0c501c610484950740080501c207005092100a24118456080c81c0803c06840c00c980026404000048912800d4541c000402d084c12090740c0000600c501c04078562030844d003175410a10302e606010000314109030480c03200400c0e941b8050507042c050140d0342c0124080c40401700900c0d0805d50010320600a20350b8900c1c0c1054a44840d480359000000e400b020032000e240b0601903124003070220000c10075060308103d084201e81d0f00c80b003022200c5a001a0707001441d401c2d4140280d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 857111888 1250 857110638 857110649
    0xa050c0f0a230f0c1002160603020703170106051209011e0605010f110303070818010c0c020906060c060a0209060702040f050f06030f0d030f230103020a050307121218 73
    0x14034000c0b51080715811989440c038032440454000019074032101c280056107040540c400c8030317420032840b1190016401c01c4c04807a80304801c4000000042a05905500102603003446555522405812002a00320080c0c01780107500000b04200300e40e1001003d050f09440d004491000001040b424442c5400c030722009014407906c5140e15460100819030708621248440c138000d0030141d410181040ca8151648001850101844150808201c00c90850307241b010441769001c000700b1180713424600240580000c1f1108034420f0b1010400500c0ea41011000d6a41214880d4010541a128018110060342000c8580c68000c041880765101503503c03402a0082c2ca01c1030007000495052804400c2070241d0003e00c0715010741d20a0351142d020350000100202c20946078178000031411402d240c403001030b00010645902c511a40401e0700d0b9540410040141201d200320740c20203c0e942c3e40d41c249501c42c04244540405c1c4207800102d04c010522058107103a94207210728108055010f05803007210302c00801c2d04803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 857113138 1250 857111888 857111903
    0xd02191509230c060d020a020703140114010b04080a020108040203031c0531030305060a05121e1204060c0c05090f090c061e0a110303071d040509030a050c0f0a 70
    0x60710644800b000902c0c40481c40c2802600c00328000001041003480b40440b4011826400951280d40380c0c401d1013084069a4410400041592641003142c040c040303d14400c0386060450000050070f1007001300711022180114040d02c03090718940c00550b0386800c01032042e0b8241c0010080d00060342d0241c2c0b84501c006a82da600002d0600f0910341841d0290650300030901c0080111041c5c3d900300b0111b0f413079245440c0e4140fa010a032540d55001059208800380d2003e60424040444140c01d000042030075070480c5200d83c0840c00a004004d0207556070140551108542402000140203003880758440b13007490341c0505c4000b00d015a03a071000c150a00d90407a102c01c0080000c03000e10041050178007030f015a14804543c00b40c00c2c45501c0c0c41c2000450769070202d4950040002880f05240341c01034082c580700a61031010351f52240b0782240301910082e52000081d81e103200c0d0310807441d0203143c0f07071280c3c50083d5803500040d8107028680074251000c0d48490403042d520310401c000040601c400f04044038449110380c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 857114388 1250 857113138 857113163
    0x90b1e0c0a03021b09040b0a1b2c0109090c030b0607050f1605030712031701080d0f02121608040803070c140d050d1206081b0901080d02191509 63
    0xc0003401c24001c00c0d01119443c01030a251303901680e0f0004480c2d00103070412120a442d071281203482c001465507000b110102581d00c60b43c0380e10300b6007105c13080b0188100c4006100b10100c185480c03007000b0105600441c007280802106120801450b8070280214400741030004154280c2707400170700750b03400030103007200c40c5c1d8802c1c0c4810601205c28041b102100b00c9203201c801c071060418002030f071106254000c807081d600101c901c090500d80316481400c24080380c2d02c038401155131182905501d9401104d0040d001c0740e1483c0c400740344a4030015001250000e20b00000c0d04020384901c08079038112213854280d80c0d51009010110314020284000c00c0494130400320031402e14604134180e10320065501031a4800c11500716140c3c0820320102d44c0e80a004810b1815000030425070203100000c01150f0000b507800d1242030480d990903040c1202d01e040c8000116100b5040c0c1e030761054540e0b6150550110100160444141c102c0300340c0308032889241071882064000103803c5000040f03004c80307074a1035041e80c11850080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 857115638 1250 857114388 857114393
    0x2150a020a1701060207090c120f09030905220e0a1a010501021c0c02101809050604111603050901120c120c020706200c040204080f0609010c090b1e0c0a 67
    0x140c20000e4009800c40d074550b5624002c0c01a445610b0341c4500006a42c03900740140c030140c42040030070b5881d202c0581c200001050400d191000b00340d0580214007156a048000c40c00380380880d0341c0090325582d14050000a0901d4114401400154942014602c918940c001c0082d0101c1c1c1c0000076290082c8036092591302d0103000a242652280c160540c0e425040c3d0344903600c9500c201c10341d41c0c558040c1d488440222800000310348134030b0300703a1316800241e0381e80c4400304603d01c40707421543c007070300701140c050000024060508100b8482c80045460260242105a001034095000342000000c1410501600001860064241c405542d260300000e020310410290010003031181c41c007030030103a00c002c20b411800d085001d005d10280311840070341140c4850700c04151840410116080180107030040d9180d83d40c4101d55561400c0c100051445c0380580720000e070301030700140b19070883c0180d1903440c6100c480c58400c0e55142c55100c40c80030a00150004051021030441e90001c00d200743d5401c00a2402c80c0c00760 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 857116888 1250 857115638 857115647
    0x150b1e040911100f0e0d1a0601020a080412030e040501080c010f020312010e010806090114221704170606060d0f020d0c210605030a11030f1912020a02090f060102150a020a 75
    0x2400d0304c1d4850051800854042070961480e40d2007c03054060000d00f5469010040c2c0c0740031100c1d00c000301228000180810001c2c10148141d980c2842a22401d56108641c0104019214240180f80f82607101c81c1c220f4401d5849014000b00814031801980d00d0a1410100c041c54083c00348c03c25032141c104200104246c0d9004c000340e81d80404000300820800344280b00c036510425001c1d0580d0011144140c020001206174a99210110360142d00140c51406610001109400c24804c1203401209001506800d405c04101d552180b0300003001c943c40c103883c440704079000300f81802c00300201c80e600780b040310541005440340d2004440d194550440380c01d018a004025110045900490705003821010011600c0004901d000154030181e0481c80b0ba500c40b001c685003004c00390319081107110784045004072580036540111124082c6040c5c091880d07041c007003070381d4501d02d16000070f400c811000c0010f450690411000c40c4c201714140306880340244c001d45241c003502000c0d158a03040710b9001800c0e51009811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 857118138 1250 857116888 857116907
    0xd0c080901020903060103061112010320011409040f1b0215060406061d0102160e1905011202012001020403061a030d1205040816150b1e040911100f 65
    0x240c40258a4204001c01203520790006100040003a601c1c0c0c000c1600ca00c006406442600440a0030700b5282e603501e04020710030700b0160302164100c0206003800040c5501c244070301d480d03007110112080d2901c244241440000d01c00c070880c40300c100f0f540d400002100407041b00d0a0a880c25240d00030001520b40813240d280d0445c016002e58441e900d03141040110301c1e0088048035200b1503110049400401c4080181d080451503003050006404804010402004030701e44540501c1c80d0103010200003014240c5c81c8212602070180b4014054017000041c0190310800741c42d000d0440d80140c02e20801111940c41782644c101e50000c640080d1902400b00380340800244d81030030613038214000d1005211034580076000c0340781090391031711003a2038000040a00560404558007020341002004241c8190b0501d1520201c4403030f46005001d0401c09082c40502c0d204180d203440f0a401e84410007403206010070031000702032212040302c5030072004181010039a5280d0307848401c3c23041f80e25990f0310f0140004004010041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 857119388 1250 857118138 857118151
    0x11060609102904030b10052407061d100b0604260109210201051f091d0106060c1a04110f030c030703080406030c0221070c0b0d0c08 58
    0x11100300720315041c104010380c00300d514030003102160290039120402c458840c039040d8465040001000010095a4182030b8400d00c010a8202d01e00c6845004109207950586440090102030418041101901d440181605481002d0014000c0c078040034008440c402e00310560300c0f0b42c20503a4002003488440c0282015180100c81d101d1405090a5541c0d20207089046072a9070000c0c66400c17032210120075404144419041801c0d09c80c2c031482c003248840c0c40b58007803525400650038034010521010010410780c101195a02c45611000c0c00c0807031a40c0100781100051000d40c0d803140d42204010303401e00c100c6010f80003642e101c02c40d80311903007820641c50500300315560342161790404000228850b9518030100341030403109a40b60303501d00c00000c1d00e45804200402e505001c1d244e000020460078600900031641c40792010f109070150780406030307140c030800c03d50018095100074101980007a810000d26606102d010355240309500c60f00c6124082e0815107400c001d031707507444001c1002540c01481003640b024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 857120638 1250 857119388 857119399
    0xa050709050a03024606140307020c13060f090912091811073309030801030b041a09031201050604050f0d0204020405030102070302011b0e090f06040902060703110606 73
    0x80c5150301207480d5848558168001e0345a80000441c07554070151710000196106030f003903148003c407101c3d040d24218148200c0300810496050000c004500400341d0744140b00380d070042e180720004031003480500040041003c880543d00c060100e422000c06040e200600100d40000803510301a24044041c001c075403582c03005116000034104828100b5181e51040f05040550114000080e403407071003d140036200000700000005089002142003c0750740c54103a10501030385080071700c1c0d6280480c04030350000e94003900150071040180302146200503903a070414402d20319080b0000f0002103601c89a0307020707580b48916410000e64100c8189100c00101c4c058101107030068501490600006c40c41c0300349900440c0241c05c11407892041d0765640d07041d41d008003c050025965400c0c1d5181c000c0c002c1c4501c000b418080d81250320300c401098811212859091300182c540314164407121820301100303600401d519802a1034030b02040c016100c100c00f80540740d01c00e4550048991140b1200e43c1031810080c003d0707000d107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 857121888 1250 857120638 857120659
    0x11401030212030f031302030a060e0a0201230426060f040c080106150e0307080d111c080403080406110a030212090c0307051207030b13020909030f0d0c12050a05070905 74
    0x1403a0030b40441c6d4104054030200402c685551012900b090040403015200528100c01842d11100c0800d21510440c402d90f911481c0015030074040c581c01110030108a0159024082800800300882da040f00902d02c1c0c0520010313a68180104070b02c0d100003150310b039114100407014030007000f5503c0c0c8144050000c800c001d00c8007500345460b5007000004896004108141090b00c0c4106840501c0160080c000113420b44001c051940d0000d444201c0700c4041908a2140c682e070050100d903000c00080c40d00c125696651580d841c0c91300c0c1111120f0000d0001d45509a503500030000d409102c0d030003808600e04684000d611150b40580e45520340310001c1440f2400e03005009458540d0341c01082c114140c650840340c58031500d8040c3d503001d1502d080d41d00b00030040a0740c407060101801400c440141194401c445440a45d501c9205c6d0a8603400340034616140d9840a200e00384414203213803c28640c100017458070a904800115001c3c0583e8025120203060b2a540ca090080087d40084090040e0900b40c0f400c5006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 857123138 1250 857121888 857121907
    0x120f02010807111b27090705030309090601030504080d1407081f030803070e03060a0e0f1b1302120a0b030c030c0d0809010e03030406050301210b0403080705090301140103021203 78
    0xe0b10f00504c41810b40000c00c3c56404480e94030070a10400150341100901044600203155100302c40041e0f9003503404e0310964100003803070320b000800c444c030401e4007410080d11906d4110054001d840054400ca6002001784690603089a00f8440c100440120b01c00348141c5040c80c071000781142e08044e001581c0104240c0b205c100d0380d41070007110411030b54498107443d0341c3c2d03a8109080b6564140c6c941d005078980100d5040c044041d4094000d507000394018025a02809441d0300e4055541c00304a220b807504059190041c64036140c03075a01c064846260402c050310b131070710001c481d0031000011180c030004c460707840c1c44401d81403e04000002c0010005e50040c00d0002224001400c040802c400040c03d071000096440080d0340f06440c0200200740207000c4a481d180c50703020151294000340503401d6007008440740e180d1409803019050440b1a001400100c2d0f41d20385032022903a0a900174400401e1103c02c0100351000d440910034166041c45482400307425505510400080200b641902805ca603c00d0242410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 857124388 1250 857123138 857123143
    0xb07110a0e01030321180b0105040c03021c020f0403230d031a090a1103131101020a030c120e15040311090f0f04170712030510030c05060f04120f0201080711 69
    0x304050300d50001a90070018441c00000b8008030006c0f00940d554404072001007001150b02035042c0c580c122014043d400d00c00e84114100e00900010651602c00700c030380b03036558010350340c01050314002204507507142540320348554441640b01000c0c6105000c600d00d104003511000d2101070000d4429280031b103c00d5030a85402029090464103841c4200d09100105041103d07580c000d03032080124011040d16860140c41200052014407800d64402c5c400f032206012661000c1054294240c0c9900e0b00110368200e034030368030208100c4180380c409011072149c0400455844007440c2d610881507603095945c0b641145411001081001a5540151200c2060102c241021080c4a50054468401030b070039a6486c101207000c55400e111301c0141d03000008001c0c061110345544e403c01240750b0b845c2484140c586841c008030740c1c51240300182c082d0084000034816880c1560040411081c84044d40d070400d500e608a42d040e08000050480b280c20044401004550300005040d901501c2410206000e128001e007141c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 857125638 1250 857124388 857124407
    0x10f0908040515250201080a050112031115090d1805180705070b0a090b01060c170309010b0a0902070204150e01150302070501020a080612070b180a0b07110a0e010303 73
    0x18482d16081c1d040343d1407072102d03006441000c0c041006803580c9810748003060140304003243c4182e001901a01c0025035031107075405030380e04848965016910f010803d413022169291441d103c04802d01406030176112044047d800b01d4024034500e00034181c14440001c003c0c0c0031a82c045410030212a9800302008a40c4c1c9400709404d44c00550026003140703a460540448161080f20360080081c00550144501e01115a0010018034070401100f0103590301c1e41b00a4a00c1051200010103207100800718001140c0d4180c05117800443c69400450669203060026040c0023140c0c0200715266804200b0406600e071030f0041e1710035207440049000ea0a810038281c0081c0c0d61b814010f02c0310040c4a00c0c003004501c1e100790b04890b08260800000c5407103070b410b86170003014800d05a071401c0c0700310141c1d48107910996010a40c401280c9690007000c4c900006044120041d12007842102e9200000d0000001d8004c803030401071428901c69841844000c3c00407040020b1403050740c0090200103e450014400a9001032481 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 857126888 1250 857125638 857125649
    0x110703061508070f1a19231b01060b090a0308091c1b090c0203070204111207020d1e080a0b040e0f0d0e04020a0806102f010f090804 58
    0xc1185060654040c0d925400c1c0d81c09462148a40d0400090700010309880c207050380c984094443c0071151250740c00d0a41e0048903010041507400c400f5041c240d60041c400e480f01103000030310f9034500441d00300ca219400d400c1403607449038405601035005034140080c03045601408000b00000c0c140704201c00410324044003030100a180c04c0c400a0b4401d919540c801454103188140c1015201c0300c542441d11100d11500103541111030b42c080ca03c08a08800c05006043c2030207410350065003000065000c11000c1e006c1c03005820b0185804001d5910703003038a03000c3c1c0c15101d03058030b400404008a14031390042945c05030006102c0b200c11080d03541d031921a0320004194103d1070101011403585800c0002400410401d41c2c40240c40c8540c10703682601041c04641c0249540d05074030740b10403031184103081c80160710075460703000e0000b4085030000d060f84c03401c0c0c00d40d1040000030b4540f1042400c01581002546150103020301c26004080c542d2200b0917400b40140b445c4841c038460140008844d0382d40310444e0b80101e0060 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 857128138 1250 857126888 857126891
    0x20307030f0908010501090b010f080f0a090804050306250801180c020309041d01110319090512160c090c0905060d0e01051f0b04030f0f08161b0611070306 68
    0x206078100d8030410100019150241c000c10680d40d44240c0d01c00242060100d10f03021540450112103007c0c02a1110b5100342d1541c5880840750340c5001420b0010030520380101c51614040c0710104843d24104491442050b40e1044ea100d00d400000c50700301d04900140c0600d0030400590014420b4038031001904042401c550004600030400c4001070b800d50203000103003601b0614241050104079401c003c4a082000440000c00031001d0380300040b0241d11040300c12400780071050010b5002000305901041e88140030b0000d07201409903001c400051540051015148090b850900100380011003480000424180703030100203c80c00040040c0c590307a0b66209091161030041b911001000d100e801c03408403000d03030034001c100d203152082e42d100d8611100d0051138040100c8840202e40810f6440450f410f50303400030390540700500d0540d601d40c2090b83c03800040b10551420320042200c480c002d1311070b00940788601500020780b01c83c0301c94142c0a910315070000c002c01900d05010f07504850041540010740b90000d80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 857129388 1250 857128138 857128157
    0x8090d020f03030703030f0e030a05090f03190507030b0f0402100309050712150f02281701081b012309061308030304120c0b06060c0f03030a02090406080d02030703 72
    0x203031a000d020300702907014040003030f55108250380769220700d01c842c0b1046810800001c01e00202c643ea4029840841e011030300030021001240307802403241e90b240d03500030120f0349511800540b0300803a800381c42d001c859690150f0410320400a41c000c0180d40004024408955840c081d000038084903441c440000c103250f80c0d68203910501c01e0900c02c1c2000742001944008401700a0f20740400140000c94140000600d0491810b200080030700888041e4400c201a101c1401e80040300c4001d90f0403500c1003c82480003c4416071003802e019a5014002d198600c05800c1e105103e40c814060504044880c60401c1001c085040303034425004082d1394206801c1a459442c0c0d8012008a126481005000700240b01c06901c00078107181c000004510036403042030402c09401c60740300180d030148001e0100410326000e403030004074942442c0000d040700c1005401150b00481e850709001d4210780c0142c80e400d5500303400081c80e60043c201030103414014803800c40140010304c01510000e440c0d020703050000303040000b040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 857130638 1250 857129388 857129393
    0x40206032208030c0904060803072102100f0f0c030b0a181512150c17060f180a0b0f03030d0b0303040e0c12090c010f050d1113030c050d08090d 63
    0x1d01c20a51540c003503111a074a00b02140c41d50341a403c0001440d114500300500070900c07440c04001c0d03030076032640080e1580e00201624043e01002c038400043e1400c622600b80d4030740840070300d8041c40f840768004080c0005c405414444010940e41200921400d050510718900304946a0085100c1211882c041c0e880180c41c0841194000c0c19000c214109208114840803803c0306420b81c410364000d228502d411420007122204400703a0781010008400b007004800012540c83c1c000039000d90014006100007003044180700001c0520609050000018803510100006465580700307900032500101c683d4001c87d0070800c0043d503244188546080c01c5500e0300c000e04942d031410029640500b40207850740c0018941161550025000031501e814100b290383d0100d201c0c5540418100460f0106940d40b0240415941c42a00e00c1e50101b5816000140e94119409422003014041c01c110320041c4100c1d680079281d4140360350901d01e25041b50744186441186040000c1d4040110f400d010029540844190600d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 857131888 1250 857130638 857130691
    0xf06010905131d010e0106080d05090f011101050405210c0604020616211425081308030d0e0607170a0612051006090606021e0c04150602060a020304020603 68
    0x1620000d00c1044140b06884840c2d2041d040590900741e80ca0082003219648d4141030344d54000d400c0700c1d4011820403c11014242402401290034407011b04044c260132400300380389400c43d08105d41c2520103400c003031a20030089c1e90214810004042d01c054a6041c00721407040303252206005440240311780d000160030040e10300000ca0745812142c1046003409015a626400491102c4c54440000080e440f20401a2503d003800192111000501c016013011964450035400042ca48a02521020000e01000070000c00e0b02c80480d002e0150f0401560319152041400406d0b5600e002d0341a00380c0c5c000d681000b400c0c42d40003501c030408140e0030303074031f9507003601c4000a08004100d10742025008510b0946401c0910200050204208480750340c00c00c440c070350320301c0144210745c0c1074060f00005810140303810301c01c450311a020402c219465400c0e00c82240324480041c040300e500c69404100410020342c01c220164051041541c07208500c1c1f425032941c80c1c10750001e480da1000800140302c2c8072180031006000c142c0d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 857133138 1250 857131888 857131901
    0x610180e03070b1b0f0702060a0216080f070902041d0c1210140904030e2806020a030206092b2102130f150522030b010e0f0601090513 59
    0x10103680c2d4a004605001102d89030031220781070000724129004909100b48801c131402c4929a41001d42050710683c02c00c00d46a001514040440c41200704001c42d803400d00007003030010244000180100c100d840d040d42d0034401141d02c1016041d205020400281048900d0301e1181c0c0c06121401e0402e503200c216403c0c5a015942c042c10600300c0d1401040f412000101c180415902c1c01c03440302c44e0302c041010070408030720780448000b40084c0c140034105100c0c0c10041c00c00f1a0006c403550280c044000c124140c04a652416840040140d02003200c58007850b0b0140f2019806c040f212001e0207200f00c007108081182001100c100c071a03512a11940114980305881c2c6a0295501207000c034a140c05c2081c442c0701075040301148035285032405100069480b148400e00741205c15001641031440e44500f0306030741c0750300a071800d030350f124500c04001c15020180c151580301440c402c400862043d4107004403200110001072501040300a250280f01081c1c0e0003501c8141203c3c4111502c5071082c0300c1d01e00e0900034044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 857134388 1250 857133138 857133161
    0x130609020a18021305121c0909050906010317040e060f0a0e090705030f0c01080f09010e06070c1509081b0c0303180f03010902061605120a030b0f03061018 68
    0xca144031150300090300180102000a402503440640300d008110039446004030706e0419030f1258103103000280309050031801c403500c00d081c00c3c100295500000c0c1c0564504807a043c0309600540018000c00c07907060841d003040c0380035400d0b0b203041c00d08002c4000c141d201c0c0902968440c0c854090805240d581d40e19004d0040d103418440301e425410b25500b0950381d840c841c001c41c1e129024001441040401c00103515007440310503522064580c90f004914020000041c0540007a035496100e100c0a0100c10025070303024402c9a41e0300e10442c10b00d41444950b203140351141c4000389051510503404a14030f1010742c0e45c1180090090b007038100e441ca950314906a4202d203920307051702003c03d5400d041100e0b8014460624020b6400100c1d10198400300f5088030910038000358880001d20488407858200881c80820901c034104840010183e034040c414103400c600c0c18600082c1c0c41e0301000001e0b0900f4882c45070703000f800754010007050401c4844410060110302444500360004540381c507180103540c014804404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 857135638 1250 857134388 857134409
    0x303010b09040b131b0f050a0503060a03060c051c0b061c0912050a0206010902040503060c0d0b03070b040510030902090612160303080f070e01050a0302090d1401061d130609020a 78
    0x44003001e58202501007403810100e1840000517540c590f41c014040700d4600503c40d07640391b1404c0c50300402620160006441950043d4450a001c40028440d00c00d00d1003a8000343c850316100c9a00b00d80400c20389050a80103800e09041c2222502540c8944040d40c400360346085200600c2400c20311028002c01c0c403800042e01032124941700f0252a50440001d1a0040481e03003506d1640c0c1c0c0710002001a485944900b64041d4492400100802d102c40c01410b000503488002007020030751080007916080035508280f1000c4400102040380e49046540468505000c0c03c0c2070041d1b508580004008002c001c0c04140074140b1805182003103841030001038500703a24024042c41d0707547c5078103009003001000c841c44051641c4e02000f00e910640945920315084005030340c0c0518040c030010044020b5004415001d070441e4400d680310000034030300041d0610250b0214000901c80c5e20301004200103500a07034030401d10b40101c80a00503c60401014006a642c124801207020f950300c0c07000c5040c00c4466801b155481 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 857136888 1250 857135638 857135659
    0x10b0307090518070905180316021011061f050d0f15021605010504060507090b0a0c0812071218020f040513021c0b18101512060615110303010b09040b 66
    0x18a0700d5220741c4c02109070301102c00c4040892511f03c0d54034880c003103080042c0c0c46080110401480d01c91054110803180d07140042800341c61083e01d43c81c09009960703001e507004804803180f64030f2100c091440d00030f10003105d4a00e902801c903100c25041c920410170140c4074501014602041c003860307404407006002d642c081c148045255082582c02804141c034102e80b828103000c04100550301c1000e540701a11a180111441c001d0f24000c141c880c0203100108581d0b981c024011300009900804059128440300c0e203600350314004141c0300004499010705000b000a000a111130f01507103400d00b10041600c0c00b550300080c02d460f038500d02c43d0003602e00c6000950082c8521101c6800341031080c21210100d228164013412625140ca01400c07002d0b6544490b10658485041215205038503082494081c01800200c1d0f502503e8000d000e5095603150720070340d800c1d91280c00c1080103103060340b80e400350071982c0d181000c1d829104060140d1648810310410038040800701c3c41c0384055445600100110300c00174480f0415 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 857138138 1250 857136888 857136899
    0xd080a141c0203180307020a14030a0209270f030d1d0a0f0c0f050906090402011419020f010b03120f13030f03020d03090c0909030c0204020414090702010b030709051807 74
    0x19510886402c002909428510820007030001705030303039070141c0c0140b00551140c10701c0c0102107400200c0b02460fa061050080c00703000358071240d885501901c20400131a43e1003a8041414204104443c20712641350310002c0c040f10300b00004005c4e06c007144c1c2c052401192000000b04005500703040e404c1d4030001e82c050b0038080f1080003600082c5012251140c6090b8108965540f00451502c2071881174a030403a15120001c1d07404c2c03510b40b00e4150300a01c1410b100380c0040ea80c06143c80c5c15007102d00720044015000f6444490701e80c040100160310018040280000103845000c66201c0c0b901c1c0c0c41907a9000000300311170031500b107084290b0b00100c038410070303a100d0300d90f4031f0600a6030a0f4003560283c025009040c4840e654030b2203030045a88494000764911b03a10751901c49010020702100e4800e6040210003024100160785a00042c402030064140405608005074200085400068042c809581c5407503c150b031683c801268210031280702b0301c40081c3da980ca0000d0b10038070344c0e052141a1894040c08401154 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 857139388 1250 857138138 857138141
    0xc1e1915020115060e0f01030504062c07051203040b0c0304090218010813020a170a0f0f020a0e011a0a05040909050d020c0411090d0314040f0806060d080a141c 70
    0xb0f6800403070310684a01e5541c440030713101c07245242ca016070020301040c0c19a440d94020303001241c00c24411500090113070244c4102c03403400c984440078048001c003d0080c4081c9132000b00505000362000b194410501d0000f4610b096403803207179104034642079402213a88500504203005813801030a4106056650f5404d50307000394600f0f4005c6440f00d001c10707541404240e516120815020540358090502070010342407015042c0c1d04018040a80030500ca131540072000601440b400c41c2500b8031030400418207204510401c070081c0d0031504903190301e071403101c0100402442c081e01840d10400915815546042c045001c8806101c0c83d048000c00c0740c24010b0003010403100003210700a045c055400d566810120f03800304000d8806c540101a12480203204d070380a1071030429185000300d4440d0500c038103440708400b0604440d804c264001d01c6002614038080004010600c010741d444041290920701008041d40d030b0500600480c0800002c006065a901300c14045100841d114101c10680c2080c10303c0d000e944940 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 857140638 1250 857139388 857139401
    0x503060306010905090309040b04020d0614100807080f1b270307060c060e0705120604060507080408071202070f261c052d0c0c1e19150201 61
    0x901038071414000040c01c43d900d10a80d40604070201c040c43c5400e6a00f020800030b011243d41c0c95070301c55802c000040701242c417072040d080180440f0300c2442c1c100042404114281c01010b9410081c40300079801c0169040d4001c013200c1e44941c2c498851022615442c07591a03141c000c02015000c49200010115118006452804144140703070b03034990303003120b2000b050546564044c032440020400f0780c00c103100040c00c13680120900142c40011210029907580c006541d4211144083c00d098000f00144004c1c01140c2c0225079001c401c0b82000545800d0030303510b41c00c051040610180c5000d071041d500d045441d2007030054000400420b5019405181c0310503402001a1540d8040490346942c5c600030014650f0103d0414080d02250b43d0300d01c86400e04070f5060701e543e0b00000348141c00701e523202c94a039000707104004036991507001001040d071640c0840038182d03d410074041c4030034031440040b0000c1000c4443c03520b040080c00c200b62244904c015414000a0700d800041c3c000c034650300382d21100780303010a60543c05030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 857141888 1250 857140638 857140651
    0x1202091c021306050f040906021c0c080c0708030a02091206070201290603150d20180421020c030601290f03130f02121b0303090609090907030b01060503 67
    0x10a18042d64a009040341c5003440740b242c10000441d140c041c3c0d0303d4182c1c0b000c01c0085c01000c0149c0303040d11304000d8440910000501100c00c3d80d8400949110710392000009612121107460140390104a0721802e11a0000501d12500c0340e400283c44082078840c050b00041103500e80302212002e08204002070701034100801d440c4002d180e680d0001d0221811200c80c0f81e141440504810b1442e00da0070790b000c0e00600b129075002d4201c1000c002b41000940a40e030682c00b8100782d01000c03102825a801088680b84080d00c00324156072403c02400007188072a50a481840382071840000101240030003039040c08070744a0042c3d454002d0800004420075800b1b8803c01000101012241003c10400802500d020b4207164058005061000a542c01000e403001a03016001d4601b820540d1100d60000740401d152001c0e5a800342c01141483e40c508800320404c224030001140914140b41000c40810418020240070605c100904030104180000c00c0c0103146c051a00941c22160b40d6031a5800600190b0050f0f401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 857143138 1250 857141888 857141899
    0x807050f0a03230c040605011709070803120106080a060617040c1d0f0609270a0b01173904060b040e1803031b0715050901090212010501151202091c02 66
    0xc0c502403801d4411b00b82034a030140c440c102e4954850000b10210840141181c02d14420080042000070040020344121808120584400c2d81400002030108e00f001e444400014104802480000c0d00510100003512038042554900c0d07071f490500442481c10340d407101000302c40d01400704c00c03007a00c1c0107105441010f90020691884d12000248120444116100030301400600c1103143ca1307142e00607803075441c041e400b0102e40c144419902c0d504440c4030300ba402880c4d01c0d050712160751500d84051110303401080c41700d61503076000c60386071001d81c22003900b1a00d606039008800d00c04419581e1268044806403085103562511680c0b41c002e407014140c000d56004500c10041c8038008481000001164490f014400c42409640484214a4016009280704a0f441c0300300e01c220000b130a032684280c43c826110400003282401560050000300342024a1550301641440f0051080f6008403d40d02d02e0f410b01407804c00307660644c44422000900586e002d06501070710b034a0380190401307640c55007914001c1c0210b84 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 857144388 1250 857143138 857143153
    0x3050a2405040e03030708130309090f05010e06090105010f031e15050102120403020a0909060902100f111203070c02010c0c1401030e190206030709030204051008060708010807050f0a0323 82
    0x7403c9550f0300044425100203550640020300500c13070220344625803846801d19042c940e40302c0031100d00340e070f900e03600d042201c5548030f0040019480200c1d401d6048142039601d006a54103140000b400348245120b50818161142c200110711038290300c1d0312007404042d80041004240303080f6540085c510601c92240140308034070b01ca05042c8007c1c421030f012241d008010a80e5240346c5a030760f00181c0640a030030764440d6031f201040070258076200c4038125000c1c0c181d5510f504030080c109016002c0ba50017103d4060f1613000d40d044007100c01001048a40110090801005131001840100d5511310740381c00003402141c00ca0800503216030039420309018401f00342c03424440100708c40c0d082c80e510280450400c00c101c176400320034005414031000a40c3c202e07140b0301d08000400c0c2c80360049004e440003503904c05c00c00f1a03401d604100100c428444160080b403103260108141d403403c4081d540d210003500446220303500398040042c1d07507620041340d07034015070744420600350069210001c0b1004071006401e02e21030b40203465 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 857145638 1250 857144388 857144411
    0x12020313170d06082b1412060307080d021b280f0b0a0f0c140d0815090405151e0c0d0c03110412050f0f1020030703050a240504 56
    0x19070b54030a030034a461000c1c1c118040c010781807a07200080301442c0c103100d4070185640781c1d01c811b48001c01c80010030004c040d05c503050041c1814500000c6511030122608803140e0341e00c0d4190301203429104500c8580c072401d00041348c00f0000380315500c86544909086018103151a40030f01c036680c030404860701c0517100d950b203d5807000c0200070b511400c8820030025174040c0680014500604260200c030b0302400200c1c07441341d15100518504441c0c00d40d61000304010307000300501e07411307021202606081d0a480707101044c10280c0d5401d030f907250350024101d8040c3e8404002916a014003510051903c11342c03020340264184030301080800d41c8480488640741d8182010102c549001c1e02031855038107040c0c0040b030701e014a041050b0482c210508811a0180241c100204000d1401c000d80380e0341e001280301901c0305c81003020504040b114042095035044981c0c090611111004000741c0760f11800764100403e02d50ba600072034000a03d1400000c0b003031310021082070a0758100c46202c5e0825554103950802a407007900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 857146888 1250 857145638 857145643
    0x1a012d090e1b0d0309090f060f060309020a1212050a1101090606030b1003031d010203120f06240d02030606070516180b10051b100b0a0603020a12020313170d0608 71
    0x700c044c010032001c0704108041c071100d03441248880c000890004d03400b038484a02071483c030301a50010307001030f07124040142503240c4000044000d01179414900d40c40915942d07401c1d007031401000c1490500c840494003604841c050181202d600e1030341002048441746614106c070042003180810380d107103400d0f800000d8064401e00c4c0303641c0580c0d40540700e01400340030006103064185090700e41c881c1140000d01131106400706a000003401466501071208003440c00f2000d200c50f003510007207441c000000545261440c42144002c481407040c0000c000750b500c3d80c0307500120700644070f1100c006243d07120348400c0364801810200c030003095480300080800d0455410309100e043c0d8151401150344401310346009a0f1045c0150b00034010b01d805c0c042100e85007500c9040182c2001d1a40041c03003403040d150882c0081d0b0b49455910b95024010700c1c1421801e282c02c1000080420580201c0e241807194004003052445071388890300002c280c0c0c454405c804a404401500b0640e8204890038000c0a040c54404528400003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 857148138 1250 857146888 857146909
    0x13030c0f03110118090b0102120c0c0405091501060302090604030f03030e0c0f011b0302070b0a09030201031103090618010b310b130c030609090305071a012d090e1b 72
    0x50f0203d1045c10b01c40d94900514000c1c07580c0c2e0641c464a643c4140c01e0038000090004503000754041c00b003401c0704005100550760010a901d002e600140b43d16650b144c9150280b90640340d081c900181c0b1411800d010a9181c85150800f40181012058040806d039150700448007128600059580c180c0006090200c40f5010481240c08030343c002041c8601003100114034012240a44100d41c8101d03551007a0103110361141100e400010305400d03013442556014080c904280700c0d1140f141e8070b5890900300e8551075002c00b0f8295014040e01c40c0385076100201c00d40040e40d40d488010300039207404a4450a482c28038100c44505840c4014102c548007000b003842c403c45043c04000b0b0b0138203170142c0b0b013095084001e02e9041e0200060598858000c0744075100b07407084005c05403003926486c3d80da10030f030300700440a0980380300e44410511910005000794462807603105903014807400401007904262600f41910280e5030440c44400b03141041082180400007403002c1d500d9110310454041449040c03e00c0400440b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 857149388 1250 857148138 857148167
    0x15090c0806190e0a0b040f061d250510020c031c03150506030403081e010b070308150303040b1309050717160c020d0303090f03110f010204080a0813030c0f031101 71
    0x1150003138049180710380742c0d40d03115100300300c100b8480040307a40340c4044400621540502011240c2103c03c65042046030310384242100c42000c403040c84a5500c0403090b0304500030140100b59040c54000881d008001d14040000300a05442e107604d5904c0a81014074900700c1c41100007820b258082c0000342031013107640281c0303101a10403403459031a51016100184d0145c446a460290103410b2400361903880ea0707080c06410804109580d4000d90b0a00501213000600a240c402c58925152849660004100c0d030403142042404e544590340200000380c007585c554400046d5a0510701040801503000c01040024800440c080740c031501c408090314035101042603405c0c00304d0021a86000945490040101c00b05d01c81e213404680e02401d59940700201d007403404120082146901203520604083c080110641c424100846c209890080f900c0d6461448060290041e44c0000e10590043c50031010703079000c1c6030050703000714020f42c0e10405000ca0b51040d200580b500760440018103025845020214560325 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 857150638 1250 857149388 857149393
    0x519140a080c0d0603061a093706080106080d0203070b060f15071b1502100e120412051902090f0919060f0e0303010f0315090c0806190e 60
    0x8900c00e003540c0030400a071102008402c24400501e21007218000c102c00f5500c1010041040e155103a40680091031a018040c803505150301044090f40f658014030841c04004441614180c070390210240c0283d001c20842c00f105402c190000c1800f50054000360704070303021701013126022180601d040380c072806550310050402c2c0c00341d404108903103031a102c008441c0000400c0d030007009000f90281042c550020b00101c2e881d6080845a1054404841521008024454403070690002a81000b900c52200c08212038920b51350380500c091440c01000446102c00c8882c0c4880e598030b440300500311211640141c21510b5201d55605040c08030300703a612401e401a0f016028828586070000101c6442000415410541c402c0e08000860007400605c1112103c0c050700000800394000724400301603c45440302c003103040d4030400c0100600341a00000c1c10413690040c1252100021800070079015004800010340002082c0d0008101c8290118906000e21aa94507640410360b180c0c03611410380d43d00c0c143c4000301c4c0c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 857151888 1250 857150638 857150647
    0x5040806070e040609092604150503040f0b0f100b3405160306150b0f03090f070f080c09041709010309021201060518040c050f01020f0a03051914 64
    0x358064081c1040c080d0b40200042940754030388442c8411203089240a44065a6450f015401002c100c0301c0039110365040d4038401d10f80b504110081c84d11800e6000400c04100c40000050180410241c1d154001e5038440003810190a0003014500e80030000d88940700d910410748070000f00d044e001c80c00c461456008442010840d6081041d013000340140b0018140c00c0340445040704002a828400c0b45010b40e02520131440031410340c10700c0802c17202d400c110050660031114050000510f90341c00d5607038081072408e40aa4a0383c44420103414520806000203440c480c070800805ca04420085080942c0e200703a0031914905501410000d00c03000c1038070b0280500403c03030303040641c02d40a00000d125111043c100807980440950100700b21000b0080493340300c0c0d44d54034060007189407822581c00c03141c81e0404240d800d030506440b58803403410240f144030311075004181c4c0054a80d0084c000005070070800003c0c0c4100c590301e800d018010358441518044101c110803002200ca80c011900100c0c4a2503018025090 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 857153138 1250 857151888 857151901
    0xd021203060a05101106070f0e0102010203040804030b1008030304120e18070323090318012d0309060906090c0515220305190501060614090108250305011505040806 72
    0x818041e804c0410490b00401c401c4019804021040c040ca0350307581c0b2041651032403800100200700e02d404490469004105110200d5655420b0300c033034a40000b9551500c0d2503003503909040c1155644141d1160002000b0041403008504030701d003007403166444541000c6e0b10300040004000640412003002c2280801160010344698014040180d580000c4009541d4000300103120041c02c82d41e5101c0d80c1c0c00064916401c184610862095003000e00382030160410809407840303500c00c2c035240300b00000e55524400e10414403070b030418000c868100e581001202117505002c00076103c4450241c2d4120740025000980c1c2c1041c0340030b0207019407504281428000818418100540e0490450140741005600400403400a00204c0440030356140030b01c64118940c90300c1809d440d11944044140320740c2c021000e0801444000b00c80b81040d003480c040c3c010b642c540d60354090a0f0329602005100301c2172030410059898040d84054143d46510440700382030280d440e0b0071509441507000b520030680001d40070425 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 857154388 1250 857153138 857153149
    0x150304080d1d0f030d06061715060403020a030827060a08090a140304060e0102031e0d29030f060c2d070b010e070306060212090a050604080d021203060a05 68
    0xe00501c0300070b610341e07028480b551915210100d010403c05400008810f580c80249116400045c40795052440d0080002c81c2601c1d04a02c0040490200032100c9841c1c00f1950b40356400c071800786a000f440d8180b10364581c1058040e0f60414a4004041c03121010224070101d0b1107078586400400c002c208501e05490f96004031780c5100301500441c0184151040840003c0c0007044070525210b03400d00441d203c600e080c1d4010b10302601141c055040d500200029904100c11281280340341c0c000303c9115941d4030074024040e00620900700c50240c81012061924045051210050701291044040390802c8840c40e031401c1e211842601d080031104020440c40c503c000710400043c106556200c103006c0c00160f6402c00c414070340d10181080314a103110100502c07034203800381104c580006091404001c02401c0c40c101a685401f00010444400360115000400d5a02c5c103400070040c180c0502626101ca644a403005c3d650702585803248003500906100341d50400c1c81406503841410000d042000385c0e0302e04030a118 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 857155638 1250 857154388 857154401
    0x614010509070c06020403060e01240b09061b0a030e0103150e0a0b060408191709010206040b1906150923090a020d0219020d0203040806180c030f010506150304080d 72
    0x61300140c080c8030000200b002482210240c2c103a443c000f14003d02c01e400300c0c600090f403402c69409a2119420148040d001d0f402c25a0403035101036078005e5833125403990440095801c56041c5103148500c10244c400c0583c4a0002441c841c0c0a8800f0b000e012501e400c405104441342c0100c0c03041d110074100141442e001f0390000c1d000c40902910103850682c940c0c0031346052540e00c1e48141c0160701040402c00400040010341c90082c5030a1b9090390909c11a000003d40b038070b0700540b000d42404070403004510301220b00b1004c10107103401640101b004e50b0380c0302100c03008003e002c00c500011030160140052554080200c40c143c01c5c0398140740302580c00130801008070002001c0c0c140130703107941d09100701b04210a00f8802030901030340806001813608c42c0000c00030301c2c003400d01049200310f4000b40000c101c5401c0c0010441c0d040030402600701e0710b00000c0040f0a1800002466130741d8144035100040d1600403044d801203000e00810b4801102d20b020118900106100640300240300300d00070444007a4880782030b842074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 857156888 1250 857155638 857155643
    0x20d0f120e15070813030b01210b042a081005010906080a0b0a060e1906090c0f110a170310091803120b04051005040e070303020601030305130915030614010509070c 72
    0x114200342c8100980800140c3d6604102d400320301c004018002c1d1084d101d0301c080340e2100d08841c10308000c16a503801c22b480d03002800081449074611a444600c06000a1340d00c400e40b003020034000096610807590741d079480e082ca5180d0900d46850000300b50a100c070700070141528030b0380c4001e0280c0041966203888061000b4018001c1a5a900b0003089810040030340d10300800340f00c40440721300711030007040c2405c079282c950056030903501d00702040340416000401d0400b00d040500700350b501152914001814015081001040d0040402c0311591291040010758040d21084554910072a11140704070202c4081d8600d120020100e90343c000e00003403080303000804100c680100440c1144100740400e0a13200c0031354030100f142844410030700c0b0070304180c0315414050f4884001084031500e035440107502c400040c08040c08000000030100e0104a04c01c0c0408020490007204101c3d00303038801f0240103200c0840c00100c40c0d46041442541c14025440314180c1680c600034241c148a884403031040d00e036071543c42c1c0c08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 857158138 1250 857156888 857156903
    0x232d150319140609191104060f02160f12021302130602070f030507211403090418020d0201080603150103060617010e070513140903070c121a070309020d0f120e1507 72
    0x2194042d40071b2502a0004218035101c15200100c200e0b40070781070882c4c404a445214038030510400100c0034558058044480062504500c2600c0d800425010012400ca091100e4000105641c0d01002d0760351390422900d15609840301a515040e04016080c01e03848080c0c03041d482440140a920b18503098101c958a14400c512945000b0303a40e09041c400e641c2c0002c410541003c907041324103040c10b0091642c48a108180021104200e43c00100d10302141c501c043d042000040002e9116141005240c01d110343d109d16401040da501c0c81c11401400305401600c040381c440e1041000540b50501a06030780654000c0070303040f42800e00040c1b0255607401010001415140c14501130345400010465008a041c0401342d030340d030703070312810907920402c1d80d9440140f4072840484240003040307a008024214051a2541d00000d8031010b5084001d040d00b20700180d440303d14120601c00b001100b000107801c25110f182040010265401c060740c2c510600004241c0005070300c15000d880203003160042040b948078100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 857159388 1250 857158138 857158151
    0xc0a110111160303030507180909020607140a03021005060f1e06040303021b030304120f060b0a060f0305390d06232d15031914060919 59
    0x754a2420314680a0b000310704200000c1030044c5a81402200e6009566007410039001402428545072103005100310281c41d43e0741c4080c0002c40d901e40341155800c6800c41288048134082c1e81100d0b032241c0d0101e00440c00751207a082c46182c445294001c0e42d00c3361030003c10301038400c2486014004854401c009060508010103032240031036540d54047e10146006e03034000d29200d030781c081803101c02c0071518640511950090100304680d002c2e075a00c1107c10380c0d0001801d20362001070b25240d400303080c180d10810ba11030444580424516480070100004540c199410b10294450840150200c90b101c062806c5078441c00c000450442d940000c0003110003d0458141e151107203105041d8102c403160f411007481402130303480d90441908840b999800208080310706d0703280700541050b940031410024240c02d14460050441410a40d43c0007030b0300b0741070074405510503503902c7c10104085410110b82d0000751442d2a00e07808400200d0600100f80c030411015003103c28a80320903500c0c02c90f8940a03d042e0541c16220340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 857160638 1250 857159388 857159417
    0x1207120e030f030414330409020a03020c0d180512120c0c120102040f0e220b061c08040b0c0715121109090406020a14030408031b0c0a1101 61
    0x1000c1c11001c040003c1c1d034503907040040f13000c16184440301680c841c10302590101840f5107012048039000103400e1042c560413151307507160b0340d41d40120b9004017440c1c0e1021800ca0f00305a0550002d1002c0324001098450000e0000f0081d0340c6002e50420803126103045000602040c14084c0c4e078451622107010440c3c1441d2031141c92001181d1144c2c0c04d40c0e00c0707600007009200060078100300341d001c1031100354020350405041c408000c2d100c540034412218041e4820000c105542d0040c1c070681c056241c06140105005c05e1030811601d041d00a8034914010b11034031407940500c211005100f1025a0f0043d4050710f02840c0086480d00790300048200c4145000d07030200010703251803c80200f00c5410072600c82403d0381c1c900780041d00495081c0c1c13241c00d00b102130401441c80f85964900d10564040c3e800800144c0720141600225420014410500b4410000000380000d014860380610700c9100c50000742030801c8001c40c1c052034140119010820300d41d00000055000032807401031090041d1041c0350008181c41c001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 857161888 1250 857160638 857160643
    0x1707170309041a03011d0d0323040605071101020405010c0b0408091201090203060a09110904140706020703020f060f030a23070e040606031e050c0f0a0f080105031207120e03 76
    0x1944141206440b000b8071900b81002e0043c2c030446d01c0e0a11201d4503030000e03080c03203d0304d801c0680d200c0f03020140c0d100001022092300040b008481ca41858204034107240a00e444801410305884901c041070014440a0420038140215070503140117940d0300902100d035680e07803a5981342c0504200d0b603015041c40010134948800a150f140060580008928105240145130078140051f00d42c00d00c40d8248504217003c101c12101c0e2070321404040c0d658148a50712401d201c3c2c03041d91400d29000d81401081c2d000507210782e0000e2000d054a0080f02d6244902130364804004440c8140c2010381410441400001c1c03000100754040c03000056900300d40240b21040340343c0580c64213000c8985501140e00d802c90b0502c1030a2521950003e00410309003003080d4007500c02d83c14612404a03c440b20490b0f125000074220164100075075405201100400e07445511070306000d09510044084440004e025000019092600040c124001034540540718500000d94032610b011003801500281841000c081c1c1040d140c808 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 857163138 1250 857161888 857161901
    0xa050f070c110607390b070f1407090c0806190e070309020d0605011806051c030e120c1905061e0c060f09011a030d050304030c0c0e0a0501170717030904 67
    0x2d184000084d040c070341998201a03040748160b100d04802104091251b0034103001107904142d08820012510100f92808441d4540c554003055224007900c6c030300003200d028541004490249a4072000c141d6640c030020710a00c803d6100280554200e50001004004100d60240780c02c500140b1303000c18000340c0c1d6008500141010b540484001e561a00100104523121140901c8401140024408189400c000920f6914040c0c032800540e0224110310702018008c0c113419903c85000303401e0021420305410380c2610f40310504909070188003101b0b02d07a81926050180074040e510300401d4141041510f44070145c4040b40c40d50f21244440d000c00c0007626500342013203194071401a0030380900346840c01002d11400d44224040e65240c0243c0e010000c0c04075900800c0c0008418000c1c94003070b4a0740e4480c00d0480b40c01203c1e000c007a02d154a10365012811a0141a41d41d201c2c2c003c0315414400b690f42c80d11418500c4254035008541038024000902010b0780022142c17000111800440b0300b8480c1202c001000c03100d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 857164388 1250 857163138 857163173
    0x304050303010f1212120b13050603010b0a0303020d0e0109030501020c0c01023009030114010905150a0503060a0f0204150e0f04060b030a0207050a0611030a050f070c110607 76
    0x100040011129141c035070400307880f1440041030740d001c3da0354a03207400034001e90028090000c1c4081b0408100b2041d4486003e402c8001d0050403d40c000002000c014038040d120507009508144441000e07003811750030a8109e81e0b069000b08915044500100c641201e280d5040303041001003580000480e40c02d0010f801c2318402480508000c6200600191800c00c809002d24010700d5010020406501c0d094024100711002c0707040c071030303071221020f001a00510707000d8645c180e510000c1001007a00c005640c0300782d1103aa240d03401e103c099290340e001c000f5000a10301c24547d00d680990001401c000042c0c0080580945807000582420303190b06400108540040c424400298461540400c80c54040d4400021540c296400c000703079400d00d000d03d461803100402c4060100d400081c0c3d1400c011301040400710942d003225003001050134004603c04070703034816680f1510182c180b2000c41c2d9801328410005000d20510744a040c4c419415070b9840600c0c0111800984e84003400f48148000f294240508200405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 857165638 1250 857164388 857164393
    0x70c030b070e040501140105070219030302031e070b042a0b1c02090609010f0516030503010518160c0309030f06060e07140901030b0f0411130501020c06070b09030d02030405 76
    0x641554001c049000c056200d030311843c1804c004015a202202481c46490400c3c030b800c680e1000c250000c42d0b02d074404200c6000c00003190000020905a0100280003c05070b031404211400400190f109228003d02e800079007940743c0c110111340003400c0126480702045c1400410600c880c031000c22070883d803250f03500c90009000c0028201405010059091400d18400f001c11130030045039001043c80b9000e0001a181881510540f00c1c003004c0c00b51040d078207182c1880c2c44144040312289001803560b0400e02c5140d0041070800c00608030600140c041920460015107803801080c1c0c519070845033011020004d030b09110040d200440130440c0c1c500d503904158001c08001c00e0040c85c1001c48840003d0040038a410041c8140310700b1a01408842180d114940034a800724580c6e01c00000926a540180315040d032052074504030b00345681b020030250a410240b050300d59030840d52907005980f03450460704151f40c4407108116041c002400480d8041e0420050f41c02c5030b00705691081000201e0713105440548955 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 857166888 1250 857165638 857165641
    0x40c20030a030c022406030718020d0e0102030921071401090b0609010308030a2a02010603021507020604051c0836130b03010b031509010f14130503070c030b 69
    0x1505402840740d4202039100610383d180b82480c0104100300e0211740c0c0c0603030380c0c0080c0105070740ba9010808603014080303030f80c4030210440c03900d042d1400941c0500d40c1c0800860070004d0240e80c0c440c0c107209072480b6804142c080c000078800409018080d072014448585221030038445a0041080c00351000e1007264244c00018482e296401e0180d520140201018890702c5512300510005c2c4503001501d07080401031300041044401c04490040100740c90a5250b48080c03c0d0001960540d8150069404c403802501c50b0500b444130402208060311a07188080d400460800003004039080c4895814104c1c82c0907429011280c0f40c03a42e8413900f80d8010f100580c82440300030850540000c222906a291406c0d8195102060700b400c40030a1218840c2c015091280d540c5111418464030700303410581c040140201030b1200d1459004402c40c0ca02c209a60103d0950b2030004080c3c08184d0a01c0344c0245801c42108850f40d40e030302c40c207102c908018502c000b1039050200b4046400001c444185c004090352042542401d40e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 857168138 1250 857166888 857166907
    0x1809060303020a0b16020d080a0f0903020a021002010605030d050708070812040b0705030708070302030402040905070b1c0c0504050904050a1505071b0c05040903170106091a07080306040c2003 84
    0x51a0050941e043c8000c42c1403a1703410050700061519030b84511810f00380825521031240700010007103a242155214200f00b000300c105640460a10016071080721241d0543c88180d1040f4202e404078080d064040e440707807a030380426034010b20240c642c03184101149864404223542d00d40c0780da040141e019800b0078018007800700b0000c0184c6080d9101407546040ca0640c90400300007051180060f0101c414164004042415500c5517000100240c1d0000304940c402559044603040702e070302450404040301d6248e8000000305402d40105251404c040d500c49080c14185401c00c44c1011003e80100d4130740c811612540000b81900080c03c064015400307000440b4503054901520b11541c1c00100075401500045000008015032910380c1600e40171794000500ca6800c3c03805031501490350480c0382e4a80c0c0c040000003142ca6020100c603050704d14030388182200d00d00c0300650002c103004400e80100200000d2000641c1401d1951000e00486910f01e410740001852588900c20602d002c039036944583c100048802d023 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 857169388 1250 857168138 857168153
    0x2a14061b0909040308090309031b0415120b07050d1104090c0e01080126030c070305013e0d0c17060a0b18031c0804030216080c011809060303020a 64
    0x3548800500e10364600081c9000081c100d000050009043c00302103004200d21a10420507660203000c003504443c41c551600c4604401c2038965004284070703909100c1d440142c0b01ea1000c650701225666100c45181d40300d56924a000858010f0541041150501410380e4888903030140362104051643c1c915a00c3c0d0515200c1801d80e81c2c45c0c04034000f48020341c062514140d070311200301d6045400316007006098090a205048aa10340105456824840440c1d1145165000f040da41c007100d109800800c1070601714145402e81e0803030791040d0b012204590080a0000078542d202542e1000c07070312a00c1d49016004000ca404940a0300c49110014a00300c0c00c060817541040b40558100303100f281d90072102c3d481d01e013410700036114016015106c0c154207c86920180c400308403100030b4030681d034907490003150045801005010b04840540c018130800360070044be84084200c0c1410f665200020745848410f800041d11055883c19407180745030400040050010742c18841e032005503209031301808158806041800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 857170638 1250 857169388 857169421
    0x41413051b010f031d0718180201080a0207060b0a0305030304060c0e060405130902060c060702100209010e0409050f1606200312150306040326072a1406 67
    0x506207200314030081c90380c110049290b01c001c5454045079941548510440148404001100c80d10a542e03002c606c00ca45481c161038140e40c2410204050f04a644420300c44114000001c0d010800b2100881c0740307000746400905800c1e0103540c0110300c5c0d1341c5480204282e00442d510170344040e0404070501c0b0810880b4001c02c0408441f07450302c550340d0300d0305000180350f500c00c81c8240f510031b500d04003008803c82c070b90707412424401b60001c000c2c549544000d4079154480608490920050081004940001400740b09894100606940e50000c1001d9281800000c000c0f581c0241c3d02486070702c105001c014810030524407000450711010400c80e00c0c0c420082c00c0f1856402c42501c100500d01d0084c00000000420780d6525148641405103549680445114020350f4144198041c000c0401b0481450340145540300903030501c0b44845003d56110050509010050300c103807001400c00c140c0c51400c42004408488043c90140c2c0d100c540c00d03c80da4032403552150444208440e03410017410010291050b00940 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 857171888 1250 857170638 857170663
    0x120a051f050603010506010206131e0606031707030c02150d0e033c090a0803070803041106070b0103060b01200705120f1c201e0d09030204050604141305 67
    0x24401400c2440c0040d45604004228000c41a8050440d1040c000f490440c0c2070750b403202f4580c60100340480d0078800040c100301c1c0415149031500303401d00e40c50702c1035880c1215034468059407800c5900310340d9800c0090b16104a400711241d04400d0000d42d403000700500c281060700070b6140065030b541150101c1002d82d5a1022000b00e0103183c0303079081c4c00030381c201d0f2500b640f0103041d40d4502035514a803d50000b00684900d401c0002c40d488041109070402100301d0080d80100d010350701403020484d03200100700c02c5128100000f40712441d25001000003131343d00e42140b09850014140303160301ca16000113065511800d401d5510080c0c0c82540100800d040c003080f0000041c030420007400140f0181d407000d65a43d4003c00300c0111040d035030880ca044192117160f801d090a04c2004034000c4d0000d1120f4001ea40c0c5400e51a01c030405100d80000f2244948000b80d01c0c11884050707121170384524a035400f004004c18004000ba0b4015440300750303074203800c001411003e10602c2a00405489080d03c3c3c100b803482c1c0078a26004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 857173138 1250 857171888 857171891
    0x250306020d2901021b04110a021605090621121c0b01020102030c04031212050a02090306010f051c1106030c070605060a0303080402060d150602030702130515120a051f05060301 77
    0x2d0715031a43d01060402d1442a480d02c1d8a001105404c04103008080910314000d00d0721011036070707880b02540070586403900602803009610f05078980b000c00c0940c000507a00700d45d1141d4501140641501c0c2d840080c05641c29400a66030f890060440f0040594130190b4685505a031036800c04c03900307811030311600ca204c030070a01c0218118a4400700414691040e804080d000b003c51a0344440c03031600c540c03d8041103046201042c000c0d82400d000704c00194128400892107801503c0011500c0c040c100001400c503003000300110384244003080100311510414005680c45040084034811603100e0800031401410300b5205140c0c0c82503a420003208a03240540726501c2182c03449000c00100354040602600b00e90102d40700c0340e842009400200080421911a0b402c20340184400070b1001d401001410180b4000e688640c0700600360004a411503a0880d2080402c507050003071040d81e401c00c50b4403284e443c0c20f450b040b82c1c81c616041d200c40d031500d00c0c403c417000c500f04043c09042703c17400c6413800b034140c0201040d0300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 857174388 1250 857173138 857173211
    0x30f11030705090607080c010f0b03150601230f04030c050108010b030103020f100c05060906012112032c010f0e0109021e0f091e010e09250306020d 65
    0x1001461803141c003c443d8890704000c42d075081803190398011981420303c02c80081040c40100e20440c0060080041c3c8070b8868041c031040e400c82084c12980052050074165039640241e080240440116070704400070f412070407018001040c041b03c443d001040650300508490f95802d1800700010540d034416009148018418030041005071642441800e00d03803022640c507014011094411200c3e01e140800281c628030409082c481c1c1788101168441c16038400c50720300c4401d1040c5101034005011404001051009031921400c0c00380e1095000c60400081c0b50700e8a40042800420800a08101845052981d645004a0b01e0704402407040721520386480b0002e00039441917400246800308228902c2e00f05c01c008150030082390762100d80c0071403844030013400164203040004091000203403103aa4414965828800420f070000b40582251040511000070000c01c0040090b1103040300703040d4207503c2d01c0811510044001001030002d403010244112000440070062007041c80040800c9100b24105108403e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 857175638 1250 857174388 857174401
    0xf0c080f0c06060d0f020904150f05040201030e010213050f0d1209050406090605090a0b0a080d08041e0b0112020d06021206030c0f01021e160b13090624021c030f1103 73
    0x32042c170006804581000041e0760700e05010a02240900390403146510b01800151685010743c01103009600070398082210221043c0310908034403511110001d50f6044c114100501d02c0c050504c118124405043d0158000c0c5e02da4032080685a801030708030100703820031020f0180e401e180c071559009181c008801d1042502d8440803514003600641602da82d5a1986041d5005441c0c0d4444017000707203013071011503040446401d40104511000c1d14112204410107600300501101c00d203204560301d4000307201c0c55480c7d00e000320090b00000901c000f240c02580000560001c140c291020301015805442a4401c61800b2800c15040441d2030072914403e40c4842c1d2402c075640d074005080f01c040e0a07000f5008021075800e02d07165242601c5407166120300009542d02003158a6680043d03c13110b604001c1c00c00e511740e160000c01003500e025004e84103203950303501c140920510f900300f00e0301d860515070700645008480c00810351400d0030b03681032400b010988410b2910454480c07841240204045140540e0131800e054 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 857176888 1250 857175638 857175653
    0x7060c020705181b0c0d1d1503090109150b2110090206040b040f06080f0c070305030a0b030d111b032d03070b04200108070f0c080f0c06060d 62
    0x5200302c5a001c1d4030020b4101303a00303070070700005540422014640700c00e43c01350007650311111411240300007804a880301303646580581a004180390014201402480070072408001a000144944c403550341791155100405c010480004005082d280085000c610450501c2a41120880782040750000c0c0a6407441d03002b0007180ba2007100e81c103a403002c85d204c03005000142c0c4500440c0c06c1200400000a40000c0d41410594404100e80d201e0b142c01006540d0000794281001044900c6541890b080107194000b078414802560b0140001c0f50000c1d0800411010038500304c0c01c000c021010542541041d08082402c01070440500f05165082000da080307040407a03103510150031550002c031303402c2c40d00c029140200220301c0d03903020010085a80710251401d00f21101c51040d242920501e14011243c0b08491418291802507441a184c0c038945450301308080b20f41c4900e00000008103e82140c1c00c07000620034400130305a40140a103a15103619089400300d04124000d00201d00c10ba60492403e400207402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 857178138 1250 857176888 857176909
    0xb090a0b21100503070b0a090602150a0c09030f0b04050f010606020c1005040e0c0a030605010903030509090c0c15040b07080402010207091112180705031b040b060f0f07060c020705 79
    0x100c1e00895200e50301100c0407030516400090385402103010200d1010b1010000e08041059079650400c1a42da401082e0303115000510940f51000b0200c0024081403903d0b0030009041c40d403894419241540c1c0e44a42d2040e903500401110f01d4005070f014403052000800106a40341c0401d0020001185001800796660401000c01c1e4069222555904034450003042900c0c000d03d004c8103243d0107403820701a119801e0384a050043c0100385440300220f015407103950b091054950584074030b03183c441110100081c4460051a151a24804000d44103c026040c00032207503c055a5000700040d06051501f0301032628000d0261082001c41d00810003d82c1c0d0001e03500013204c5610b0701c00140003c1400c3e080649202da5042d20f10b90450075000d01c864580e41400400c00100d01c07105440d0010f03141c00403d61104005000c046001d1482220107000b460240e000d0807014100070300c035034500324204140e011281c00c01400c0080c8650041110307014440c850140e100320700003600c090844e40b41418000340f2a1142e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 857179388 1250 857178138 857178187
    0x50415050f030c1c03170f130507091e11210a230105030d031b050c010905010f1e05060102030a05030916031b090216030e06040b040b090a0b 62
    0x4801c41c000c11070320103010881d102400500b002c1c035040710fa840da100f14100c071690120000b402d08482c5140c80000e5061046c019107540a1107076131916080c2e180d001c000c43c20001941d00e07004142000610f81d450784641c1207540c00121400b11300c0600e6154030070071590400c9015408407070411024070b002d403110700b480c0c202030060f528221a40d00c1e40700000001303001d40183d400c9a2940705a07041c17031503444e00d104503040711000c40459844c0000180300300c00791a506103501c00c41c04079084001c00c46500903c050000c0c809084000204c0700000c2e1519401d551101c650585803990347c82c0c24894180503001403c04d1390703406000c01c0c045401c000380006c1d0351b4492120f80b001000404000306140b41004d1050000702e110501140c0d00c0207403a1300f080c8442e03140180100c1201d0600c03440005240005000790b03060b60680d4900000000701c10b4800303641c9002d203900d0490b8095402c12010813010280006440980811900c594540c007024091101c010110381009183e40b03020b1003040d6842c044044581c40804 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 857180638 1250 857179388 857179399
    0x507030c050408071e0308130302330c2a01090509070207030f061118100e24120112110108010b07061d01090812010506070201080414120706020901020705041505 71
    0x4403120110407008003075800040808400041c00211108c052541c802987e0003224038445ca020380084109801405c102c24401c2c100d8051108244110300c6000b500c1030b112408141c4588038450703011082e05148010451490800b5045c0701030665901c01b50b25400740c402a20703200c00e242007401e40030350340c1c058a210007401060300e403101d00304114140e046602d441c8100c008647d01d8440034140c0720502a000b540d1a40642160721004c130409109608480d081a0060404075a6503207001140004c4101241e402d041214100003a4030600500e16075a4002e03c0032400c0741c049110b841c5086002c080d1100512070400560313400520210030088121a2501c0d4010340000300114081c0020501200150300004154130700101c0c0c030140121f078401004414829400640c0980e01da10801650b80240100039000500c400001800118580151410480700c07100710355800c01c1c8800c403440b85502c6200104c440d1a004290308890756010808000a00b10490b4148441d0100700001014005248285403092 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 857181888 1250 857180638 857180669
    0xb07050a0815010201021342080405010e120c0106090506090a0906090203010204060905031e0c010503040c03050d050c06060406080316080706051f090207030f0f020f07090507030c05040807 83
    0x10382c001d40c1194810b40302200071100160b5107010058500c1c584442d103071088440d0300300c2e080323107590000c240f66407030b14481c03241703458180c001e11007100d95002c0200201e130a50740e41c5517030b850b5446040002030341d00714406507910396a814901c9a42c3c02d642282e840201060705010a102d002d503a60f444440c0d0010342c24000180e0744040703080c184050107071640c000e074142d440041c0c0441c6241d0b220480b4015600241c045a0a140310034540c03030100015500030b46a01d401180049440750b205000550b0060302958070786440540329103845082c1002d4500c0b40340410310004600b2899030040c4962035204804031002c00240341381848443c5c40740700e242c0c005a02d0440c140316250030490440140da26081d00b1010030840d034a0900c80041005030300101d0f40c418150a038a0004600c0c0d00c6000316032003290b05540d41d01c0e0405c00840c0517104844d8000f44030040d40502c07040510045070411840c8001c0903444000700d0b6034103002c400503040f15488030403a010880204000d00241800040081c00c6404600040860 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 857183138 1250 857181888 857181931
    0xf0c090409210e09060607231c08060d0b06040213081b031c051e040909060606030e0a0503041e1505030708010518060d03110106030b040b07050a08 65
    0x81a00d440700802505035488694a820310715003071580001025119020300c1510700c0200303c115101120040d82c01402004aa0001281c603880c0e641d41c0303160002d1520501e44540c4c42c4509010210194112491010182e45100e99001004035000101074514500450840d25039090071840241041d003d03640000d1041d04a13600da007034880c01416903c081d2003000341000340d0f080c401003159110341d10a20402042e21900090000b2040485051383c84851402d003000d9180060070050614807500314409100002d2501d01074040c0e816414840c041c00a41603082c80c0000d01114a04601c03031803a644402002000510700004940c2612710504030142d5a03002811a106441c143e90071a00010003441e01c0c000450b07070010099400340807252a4071806a80b10402e00c04030a052004454480082c1000b0459604022142e803200e10700a14003034505146552500703094400580c03080350141e400c0c0c8100401d020040340015000805450041d01e06040807000400162000d45a2413100044195070002d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 857184388 1250 857183138 857183141
    0x70609081306050408010606020303010f15030f0507080915090a02040e01060819030f050a0c0312090b0916150509090c2a161a0901090b0d020703170f0c0904 69
    0x720360a4004121040988901e001007450b08540b013021840d41c04c25802155060012013a42e06940340201c00880f094500424a0180c200c022058424035589030841c500302c01e80d5028007403040c0c00c152a040c09504240403507a1808180180308807002c0516018042590310205246031400d404480105440c040d14440030b0060506500c000c2880c419944090306941c0c1c1004112002d9029446203841c1c404401c1041e10300c1d10030784640c0310020740170444020004e40118485001081c03c06000542c22a443c3d803903000f41441503819118035401708051001030a03071804208043c1003c2d840c4030419209007040580a40502c503042841100641e00043c0400381c1001a6550800f101442c040b031400c12a01111754560301c0789c2c2c00c03540741c05440182d05d512031901681504954000e6420900c0d42401e004034600d581010450700d040100d214400144d680e0f40c100500100b003103181d4010ba0302d189910340502180100b1600c501105012401c06c00510112208654800035045845a865070300f180081c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 857185638 1250 857184388 857184397
    0x3050d0b2d10090608041211010606050c2103060f120d0c0b0711070e06060903120306041404080a080a0209030316030905041a0f03030c10050718060507060908 70
    0x40c641070301c8049032085860140c0c22032441e071007500d0003020b030103001c0c00444000206002d524085012a000b04002a00000f0076007003010b02032410341e04240d01036442e81d0035104e070f562000c000990080390007080460f0501009100401c4501200d48444103040b010b0395071301008003c40e1160201081003003140e22541e22005400c0c14210503601d50a08900020b415012a10425102443c2c50000941400d028680c078011403042c040007400c040d0300d441c3e204c01c0d042c031008041e25044a014014410b10340c804005990030748017507200d515201d2078014148030071501c0304865548058130f00000d02020407030200840d503558101d49403c400796510002140702a200c1c02080d80d070144000074103490560175100d84002010701c259920f5040541e503034100000e564210240d120800001c103185007d82c64240c0120b0b81458001d01600e080443c00c1c6608ce0401302001d0b2014084d680350343c104130710564080000000081200c0c00340e0780942c04c0100003416801100070080000340e40761030400c140142a019107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 857186888 1250 857185638 857185669
    0x1a04030c14074a01080106051002060a270b15031c030509070f031b05030d0203180f0a06050a030b0d0b0a0203040f0605070f14040608042301020426010903050d0b 71
    0x204001480c5400e4254076100910171743c903403540307040030200712880d0014031541c034100b05500420841e120150f5180082201c461b6020580d0340490020300101140c03581044580e005014103e030034504400300e15494000c2590541c0b190b080f05810548001a4415911202d451848c001038690b0b904d43d28180741c17450035044150707000e0b6175000c00010002c25514910304442d5969001d03c0703c0d0382c0c6006040d41c0b0041d803100c4001580060103961088800b2170704c2032005003001400590b24650700f102091405c4034540007140000c1d0002900e0001035014002d036685210180c1d07003003400403010f4413210040040500080d00c1203400101041c107024590780042581c90701b00c3c80030000b80c100f0402c00303081340e02050400004110301c090087c01e080f80f84130a0350201d5076281c964220780d965950f40c00290400c9000242a600c80b02c546095800809201070b1005d03082d003a0448004034041d201d03401c40a80941240c00941e03040401d4040045d50110a03525402440d110200305250082c000135801411070800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 857188138 1250 857186888 857186999
    0x3030503070513270b1e040209060405042c030f070b07030f0e010e0705060715050711060114180702250302090a0b011709191a04030c1407 61
    0x1c02e0000785060032448000c1c03c03225020010017080c40309212130690141e10301c0411440101ea08240e030b0405400504040c00c0040c00c0310b2904d6100d5000608680800e02400789500c0b91441c000c95101da001e0300190010800b00046043c00b81e00c1003a43c440d4401ea4400505009600000c40c11b1207019030080d82c04900c2d802000d000e0081002841070007007400100042d440d104034000040c0b0383c28030707078212004942c00c411204145a12510000090400a8000010810701d003003d03100b2001b061140e18042c20800c92070b54100c0c44503408100a400c0c00000e4030404803200f009000d152500014144140d100109819920030048000c840e00c3c01056403010b504a15a00100800007220b0b6100e181046426210742d18502c0c0802c100c101e040004803a504920b503c000fa00c480c00c00180b00d18058142e208403110020640c0103d0700b0000340b03070b0070780301100410a038000281c20800818030606060008000a0843c10314003800d0401c036030701e106100b0201c0a848000c0c10b5101461401280900c00b00324030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 857189388 1250 857188138 857188169
    0x501082109120d02060405060a090314250c1a0f0706110d090b06090a061505030a0908120f091612060608060c0c07080d120f15060e041503030503070513 67
    0x20f0207521800300705c0b01100c00d8050900001c2c9140340b41d1240302e42181c1c15680301402420401042c5e122a40030080c0310101220360024882111001d11480718550711802002041515280c075120510300c0d042c0800002d45000d200c1c105840320034405a0f01c400d50000c2002c583c4210b202d02c407805034400d40300465884c6090203e10412300402c0100c0600a5031706454040d5140d48084080782158aa0b00481d1809051446000c1d4403d203e0741c05540c00c00048800050032004c40d0342c8840107503120f50090810380030401d04010400d41c600003140e0380142c00c40c0280503502e8011074020359000c21805443d41441c1d150081806100082d03004801070301d00d11003140d0203070408901c2504c00b6000008111040e101d5801c01046124010443c207541f0760040c0c0b2104074541c100d440c1040a8008084803040341c0365150802c80541718690305400082c60652920503907a503000b0288015074000d90101007083c0a80401000002d522030101c0354015100d24060381c0390003076444800481441c550100c103003004490b6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 857190638 1250 857189388 857189413
    0x3030a05040f0b04080703140f0106030b040b13110d03170403020a020321030c0a030b0d060f0e01061d0601051b030d050a0c0f03021615050406050108210912 69
    0x20081c4161110b6901c0044566981d00020311503120758014090302d034022650400018070440840c20881203d50240d03545005055007650031140c0380da2003641c034606450144014032104010050300a103aa10003111031550503250714242c0fa80d9020f03a14000d010f01244e40043c1072043c601c002d1401001d01c0c0620700c500709401c00940e07628003413405a11a0142062000840624028207201d1110300c0054500b5652403c142003100e0300800c3d0340c4000d050f1100b00c04001d65541d80020080144221400503140003455440421500d102100d040c59038546a07050140030910300b40b500a103500d4200c61002c40d52a00c004030b0341e50080482e4900b4042062003101c1c0918400310162034404500002005982c1da0420010141c0d6241c19561020a12480303400307004500c241c0007852010402c07006030040b4242036543e079102c26002d1200b40032159075401804100301c61070246074014202d5000804500c1128640503040c0240610f06001d01840047c01c488280c56040c00301c01190941410f0b14034920300e15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 857191888 1250 857190638 857190647
    0x10f0e18040605061804030c020a050301051f23190302032b030c1d150a020703050106091527060303200f030f0c032b050a0b090f041103030a 62
    0x54a080b40e000e410310300082c00c54140070592001c0310a04652901040d00c1d1911309445e802420310b41030b60003003210000842d0707a8509000d250700a08100c01c15a441900c2a0340303142d030400c80303a00440309881500341200b486d0300c1002c0b14800920021100c0380e60008400c0c02c21549500c0591009416004101030f4001c41461440e03151428040c401d00303400e02c1b04100b42e04130121907000d810200407828503024001000c00c0390b0795844041038040d191030301d43c0da81c0440d0740f4025002001d6050059004101c01d10420200f0b018020044c07924007400d020522350090844c4800c8000d00a0012010b0340c58010045403442d544800c10f000125401000b1190320b9044c0101a40c094190f04017103031140d420507004141c000141303050910080400385d82440d00c04c080c40d05060307100801e40c050a00c81070105840d940514005000d81c000f24050805803580422120320035102d0060860310940c1c644009007903252105425540d002041c25002e900640c1c6505d0880c0881c0708101510b50188004900314101a802 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 857193138 1250 857191888 857191891
    0x9101a0a080a0309240e0d14011e050c030c0307020c090403030b0f0a0b03060d0302030909011d090c1c02031504110a0801020f16031403070801170303070905010f0e18 73
    0x203136844a00c12522020f0358604017011184600f00c4403c2e807900000307250300c100e1000340c01d0b01d03000f00410038041030303500d031005007040c141d0b01071900365515584640b42c200d5217031004502203e101c1c0d050280c1d02c3d015034400c0003400010540940f034400000040c8105109021100214100400840c0907051901f002002803051110090013498041c0f203c8142e0b12308000400115800d0860f683d19540d540000d000760041107203002c5040d4401800007490039540c5251560180ca078200920801c107800702d49203241c005000e8070031402034006043c02160707038072040701c2d0410f444e003001d1954403e00540c0c400700f4686001100100d001083d80320170302c4204650142c0e0700d0201d0b0021184600c00a45031240c1600300c0c41101080240d0070010448107420400d085502d0300c019000741064483d01501010422495204442c0320300010214001441000c0304003c1c4944c0780119075008504500d4800d8001c1d002a040307002d1030b0b061199442001031315038842d84481d142251f02502e9000003103041d80101603608030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 857194244 1106 857193138 857193143
    0x209040e0106150e1903030503040c09020d0b031c08180a0209391b01021c094803020d0b04140609101a0a080a 49
    0xa10070b680003001a80783c9241ca84001d400003c1540c01c02c2400c035845071401e0240714040100005041c0d0540f5030504086650b82c0342ca00f060b50402c00030b94080c01d245400003869024001203900050a02e010940c00c851030381103111045005050130343ea082001605400000304012900d0742c2a001120442050343c0c02c080d1a03401042d6807523002c40b84c2410040c3d00541e00b40c038a40300844da03001000c0400e005404402e800040300452446961111084060003140d0300d08030070750070345c12642261414442e07440c10103078058a110140c412544199500200014020400e5030160b842241001d01480c0390f01e084280e1840c41203120030020718031860451120404001600c8005109140c207002c0d5004400300d14052a0075243c20180c50039400541e00202c1c2889004800082c2d0f41e564a402070001046201d000d81c44000035103180322006610106080002900850205040300c0060 = true := by decide +kernel

theorem cover : BRFrame.Cov 857014388 857194244 := by
  have h0 := BRFrame.cov_init 857014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 857014388 ≤ n) (h2 : n < 857194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
