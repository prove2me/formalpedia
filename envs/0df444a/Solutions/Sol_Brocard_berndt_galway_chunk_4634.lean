-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4634
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:14:55.653571+00:00
-- url     : https://prove2.me/submissions/8f982e7c-d48b-4c1f-a3f3-a572479f8719

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 833273381 ≤ n < 833453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 833274631 1250 833273381 833273401
    0xe0103020a020c0d06052e03241503031403060a030201034109190303050a0912170a0b090408070f0c0e040c06050705060a0f15090213061b0b 62
    0x1403003c100410071108208103051981c001c1408030b0300114040006a900e1301c1c0441c0440c4010341141c8141c0d01261510b046981724081c450216030541c00c403007040c0c0e00c5584210024000c0320b0707a0f9000282c82118141c40d41c140100307001140204294004020800d200032529840481c07420ba980a0a021540c4008025007440710810603e02e0350030301500ca07010325801140403a00c031540d188003d1400c03103a5100d0055550b101e0b041181e21099401010995070002400b03900180d52011180c2400140c0e80380c0d988801e082c0c00c1c00360b01c41d031703000803508031060100240034086250032402080c02080781c10f8004000c0f526580d00078202400e41ca40101d903180420150311580076803036601040d2041c540d85c0d98007068592200c140c60840d042c00d404180071903080c0c0700b507060350806500702d40201070a8480391141d200500308404064009600c60100081491024512500a2207888401a81d51020140c6a404043c81d5041101000040000c5280035501c0504d54004241c10511828964803030350448 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 833275881 1250 833274631 833274643
    0x50d06150b0a0c0212061006080912040602030c0607091203050d090c06021605011d01080901201e03010807180e010c0504080115050109090902030c04060306020c0f030a0e0103020a02 80
    0x40300c510a00002e2050020b584180e289046510079220040400e0f02540040e0700c1e118202e8295810030012281000041d120f05092a00001000d00b66200c01001102038403669001d0f40080004d6440007400e000c50a00400049510041529003c1112414207041e00d1a0811048010f000c111000c00c041021528035400614816800080c90581e160b852030060340b1a9080b008811021002c000c0014265004072422224029024404a2100c014400644d0b0310f01000c1d001c409a9035079040444081030100543e003a9040c180b511264440140c1c4140300d500744641403544180c84c13428401000003540009280701552440343d03022024068900a46d030041400e642403150301d60178145800c1106802600800a54640000900c26580c0410718403034501042d214042c0001c8034030000700a8a0350542c0051a1544024191402d146480000400b600c580360010346030164000f40d00c172107900d410450303485410b01e090042c6081104103240604000e40391441d481c11705800040c100c017014400e01c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 833277131 1250 833275881 833275889
    0x60204050d050f0706020d1e0c0215190302040e0606030c13030c1a190f1101110c070501110a02010e0a09180c170307082d0d050a020301050d0615 64
    0x1d451005105401d109a503200c11084407000c40c010700724041070f61032020800381d10200294a03861850403200e031100e24002c1c0030b91101800c001d10f0100ea04010f0b84e4005074461000d2940310f0150715a07884011041880d45e0080094060510410040000c05820740c40c640c0c1c813850480d1040e880390341d010f0b05034107a482000000d150300c200b01d11020082280b41c0e81c403101a00c40c600200581680c80f202d0080880c418204480c180d448540101d03540e01344551114040001a854007101414064100500f900c0c00c40040d54070300072005c6202c4403086000c1060304014082403030309103424089140c03429111030240f003020341040307056005d521464840f50210402052902d0080185060a4154000303641e9680310440e0039950840b40098048180d201d41005011a403003e5480e050080d618401194000700c0d030700d43d012041089542c804050310010810014010a0240da102c0140105d0b0b802c0300c40c014a031a0329144140014412621045202d0503015840b41c000a0070300343c51071451800c200150700c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 833278381 1250 833277131 833277139
    0xf0f0633020c030f150c0306091602010b10030617240402010c0c08030d05090607020304050616060608160801060b370e030f010902181b0d06031e050d0c06020405 71
    0xe21030044c1000005c41c6000d007480076405d0382c01a26000a2000644000d54407146c0c800448800f00c1c0200c007540064400d510101e000004446406c100030031401d600d6410307a41d0101e0b40d0303154100481807105c0050078081d101c90002d400300b1040300c0008400341d80c0c1c4401c116640e48007540010210390203019101c01d250b8000c1030551a10b5590303804c1940da036101d41503001b07030607040c4404100c41c0c06000a815019040e250040c0d400c090900e818042150003001c440300c001c4c08010381e03160101c1ca091290f940034003809405010031146042459040358140c0d8400300007a03250040070058810080c00f524919586024403600c0304903003030038120034961050642c60603003e0408140c0611a001408091070031829400e070f60005050901c003500b00d80403600040e401003030300010031003a001407c0004e40d0041050541506a81d01d000301080b07990080b507641c491784c81d6610b03401d00c02d00c40c0161590501075100105002e000c100c665401340c880241e611000c080c082d2045200c820020590151405410064 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 833279631 1250 833278381 833278393
    0xc050a0501140121020a120303020d0908070516150c0203010f0516030b010302040503030f09030f0a1a060f030a141f02040512070303091e090f0f0633020c03 69
    0x42c416004100c00303218500c04000c29070940f50207070400805802e8919002006030785481d252010b84162441d071800202d0030036900300b0040884c0411071040d2485c0502030b00441d13884250600c0d00c80d00d020854004a0541c40001c035041000c0c080f4042c86d028640c080349880d5005100502c0030034050100401043d00c12810a410448100940414a0212106641c2c1030252544060054040b882a401841e4040e04100804007040d20300b103008046004024049440861004070224140b40004104450b032083d80101111208000c00c05541c01a00c21291201c1031105500002d55411050300e00402c81020980403090284007400003a94030801c4000041101c81d103200700c8c2000b584940106031040f0300030304603100310003400a2440c007a6039254807030914043c10501c100300c0c2c042c0301c00d0701c00e01c84540359903002c24400300741d00428205200c2c0c50740201e5642c00c004003000590f402a004080c5100500a80802c000488001e5005000c44c002d491481802d0080d0120704111026030025090300c070755 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 833280881 1250 833279631 833279651
    0x11e030c031407170105241e040603020310090524030c10080609181902060405180a1b020d081807030305040806090102070312020a03060905100302090903070209070c050a0501 77
    0x200d002d000540325101d201c19261703a218010882900840c50031401544001e9001096006c840c000030482502c6906071145c8020000d91070007091361003034110b100065004820b00200e4004801042e0142003900f0341842140b408010030b00d2071070521008400140c100044101302078909125a01001c1c01c00740070b03a1040b15400c8c0000d85081000e071a100d0064820341c00040484d41501d03800c6e001c40c00c00380041e00089050700e42d10048a00346a80c00e0741d0040b02080006019520141001f142d03010364000d40b0003619008000b04111440a4055500c1440c2d40c0040110700e41d010610b5800716a10341003c84e042e4940c500c5d9101c209201040400252040c103401005058100018100325640c8100703c1c4c48654070740a1090a0340034001008000c6904c20b04940500540c9401509500390307a0700e800619141d8903c00341064400c242c1c4c0452603480850018015410034001607940710701c94000661400d1440c0c2d0103e030100c0c0d801000c0d40e08200134081d085081103014040ca141003a0044000e1240d01d00b4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 833282131 1250 833280881 833280887
    0x1e050703090308091b090718091e0615050706060911030405250603090816230105061c08070b090312090a03021e07090e070e0105011e030c031407 64
    0x1060182c1c082000c030030003c1c02e20100001c020300381c0c0c825682c0032408403101a09006010a002c1e000e2400d1240042c1c1014060803816113510040000c95404520040c82c4600e00c0d007140501d12031000400d003003d200f88001d900d1001e40b0403d0315524074001d95190280c1c10030100a00300c42e0003100c809070400c15102d0640f594500954020740c0540c05980c0160071103200c86400b03400c10240503034a0120400c5c10440d41d030003079000400e018040d0320f12a1510141e03c45100d044011810100c600c5800d074103511600c3c00740c103002c0355000413070080204414201130780020150004241c0c101031044040403101e003000321035412f984200341e000801c034055044c940322150300d980001c5801c21418440fa00050940e030380005da481070b500d40680280c4419071090b214070418104828440c1c800f4441d40000082d603268500c150600d00c40305001030302846081500070151020180d000780d0411091810169144200c40c2c10300444070b80508001a8004100c60160701418207112007440c055040c0003000001c0d50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 833283381 1250 833282131 833282141
    0x30304050d0905060408120d0603051504031e0912050102071205040302040b01080c0921030a02010e060705091f180909030f03020c03041703090301060612111c1e050703 74
    0x341c59101c8407020340c2c94809000080c015031085014990081c960f1400d104945801000c04480940001c170702e45880e900e52500c0c1100c143c1c4098103002c401000c100505612511810a00d9040f80702c0c080f02c4610000000d010349075034090703403240380c2040025500700502581101e2016611900700c1d03000704060040600190000d10003a80603a0030001000d10641c8244132541c4144031010103581000c08810600500700e5800e00c07105c000c0214020120b541312803c002918050072254008036440004007802400c00001518003010b0000502200c0c00c19581d003004d00c1c819007444031504103c100081c0d001c6851407003143c4140700c010083c01c004105a40260040c0c13420070300076101c034071845200d01001c50403481112203d0040303810902c41444210408081c03e00103461035004c9901706000301d0002400c4850580c8620081016043c010001c0342c028094045410410f040c0e1509141c031364680f0031150740001e404011495582c8000680080c041107400410201c001d0b4100300d41e05d010400074009203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 833284631 1250 833283381 833283403
    0x30c0c070806191b030203061306080f1c0c080c01020d0906021b06010303050910020c0306090307050613170919030302060a18020a060804051c080709080f0c06091203030405 76
    0xd40011240786400f5980a0705500180440300da490410790928124000c0d00090451a44214042e501000d0791403180684009016038030007814840c4443c02d0b05614083c030302d4260308105184e002c0e52440701604040e83ea12203542008038240d80b1030301d2000d0140248140380620998600d0301c40050180b15aa90281504400c001c07400b12103002c60581440ea01d80c0c0900c0000c0020b0820820104942070504c0030403806885070040312140302c441000681415404c90301940190320110b904014080104482e54010620314005103212410b0740341c02290004659207201c00040028014400d6113490821100c21561040c06001454807480e00946403581a074150510034281000101030000402e000e800596000380305140041c40c00302c0940320b01c100140261510b0088081130840d9800303403580e8111a96050340c5480503454004405060b04080760442021684840352410a15400140d124200740007103841e1a215280c600010391955415400c807a0680004001e00080000000b00d00c0682 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 833285881 1250 833284631 833284651
    0xe0403080109020903071403010e030304061406010f0f0302090d02090a0c0305011a220f03080301051f0203030402041505030f102409050a0b0a03050c040b03070812030c0c070806 78
    0x25980e03680c00d02c1c00782d001d9651031541c141c0045800300004005100b40481050028001083c00000361f8205070840d0400c84056a100d41c503030254043d609035900545138442400d0900c0000c01d000c244005144644101080301410350008030302d034407540c0301d05a000ca0f070741e802041202d03945000d00d0030001900c009410403000c02c3c00d0100214a020398190703800307480740c0e1400510341010000000c242d2801942a4080100c16555a010a8040f06601a50055406141c0036981c9515180c24001d00b0fa18802401c1c103810f030a110075110081e40030080701d070415011034020444c400c0000114100c01c042d9801243d00d0f2003107140480c44040c0100f03a90f481c08040c1001002541100e05600c0500020010036110b40c8c010000c0500500b130782c0703601c4079402490f010700000396411008040740385a4101e800c10b031030903480880312203510f1500f40200e03d0000030907005040401d2418a02035550903240310b01081d0440003100007140e103d0101c0a139600d02c80d24208441c0155502c28071281ca441c0706864400301 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 833287131 1250 833285881 833285897
    0x20a0204050703060803121902071208010506070201050306120c10090602060906060a06080c04091a0f040b030318011103070303060e091f0b04021306200105090a080304080d060e0403 80
    0x4881d00031321400d811109003c000d10318049081808001c01d1000522410900000d010000c031103443ca84064198248200065454140150404ac0150380140d21091240a040219100503607010050300d4203d441640e2225541240c9030303246041240000410340c001040554103603185521002000855400c2e400340c503010f40312801440c0c4c8a020480346140c020600d4402041090710900c2500e9215410026603820580c0b01c4000e403080c1d0320010b111091290141c0e121601518105d92181c01c45d20301294100859103031040483c1d100d000e86403014805550840418000340d004411100500c040481500c2d80c494141c94040e0003010980030b00710284181ca400183e0340e0f40005400550060785c1c95903818044101d8100344080d180c12050030b41c2054007440810521030710007031007102410b601e403610590b14101003030801e0a0200301200c00366580c10401401350744400865200b40e05d50300010201d549603a542044001c503c200c90f004c4071560b2800100180d000200002c580c0640d10a50712108 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 833288381 1250 833287131 833287141
    0xa060e0f18190603171e0a05071a07020c13060b0f0408070510021020070303050106080702030a0c02130b10050307020c0904020f102307060617030d1515020a020405 72
    0x4120381c043d004c02840040200c81085075444410080c1030988070414150340620150060b035549600080f0904001c04e402080f14000c00c83d81c107880d05260200a50281c00d40c0c904000025030f40d811011a041c040c0d80d041c3e0f681d100e0311550350800c401801c000c0c0d01c07513130b507420301940c1a4082d070b40175200e210b4090148aa002c0786914217107902e1907102c0d503140d004101c1c41102a00441c010800381f107464078094007e40e60182c18805420240170018002d03200000c0540c5003500142c0345000013400941107400410070407054070703040380c910482c482c1c0507510640181c41c3e81c010080142496503401c0e900085002071001d2199221000710320600041d402d8800c40343c0004140003000701d058900940c0405231801450280c1041c101c4c14200200c180f0700980c9640b9202140780308034881000c1011241d10015104060101c5030090000400d0900d80c034048030203030415069240d00901010001441e100c0d1000f1424000c00300410001d003a900d218080d81006014002c0d5403051b4800040780030f20706080c0054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 833289631 1250 833288381 833288431
    0x20906210c070c0b0a1e080412050f070b0606090616030f170f06030a020910050108010806010e1b0903100b040b090c09040c090e16110106050a060e0f18 67
    0x7100141d11100942d01a8146440a104d5421080b252001c01c20442035071070b9032503c542130202100c140c03510b40c0e00c1c0314149405c2c5001242d619291480920504205401b2201002400c542c83c640e001b0610b0b007015200d6000049452107505205a8444008502002600c145170b11610915100e9150003000c8861210700791000200141012802101003000414a807011b0101941c007070b03002801c0e1581e04620b80d001495401d01540c880508002040f400d11172035800050b9036000d420100010703d03e961421702100c40310200104580e150044242c20031840a45040503501e1541c0018107840b0310f444003503c10001440c48880b228880c508000108243d41042410a80074083c16803449252a00e8202440090701d60348540f64100900c450000408c69001c540e43c030b005a41c135004a0010301c00c0b0b5600100001078400d00c0001c0c5900d41502001b465a580d000801202e4440c1403012030403003110005081d4496100d00307941c10011007072500500d1498010404c2c460342441c04e2446200130020040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 833290881 1250 833289631 833289637
    0x90b0406050316020a02031002160606080c030c01030203160c081c020d0b0103020702151c0e010603110a0609120c0e0f0901060b090a1809080f0c0721120201020906210c 74
    0x6e0f415810940d0509aa40c42c15001001d02e200c482c000040c84803410303994002104e11640c400350032508a00030310102c0345404d12169140000c01d281c10340c10b504081802c0c3c0c0c2c40c103141401d60818002883c0c0c4680410540000791800003018098501080d502d0780010f501950154001c070700094504000c1c0103081d8000e20070360394680e030040d0a500b00c4280301e0444020603400034034030944600a00ea0682d040b1704490050904400301c1000108001d80b031454024040000f24044500c00c0301041d030706201055001e40c1d00021110b0700031600303815400380c1c140b64510034200d40207100b03081000300c02c100c544800080020b0003480940d008002e59503030345040f030155020300012158003201a480807c07800c2d8400024181c19044010000307002695a03580c4441c5030300801c140f26041c0380c00321320405080010301550004040e0791244d1410801e1a820b031110004007140c1c01000b480c0005115440103201354140c0c0c0e0081c0f80506010756410110f1207103605580164850540c160420000070a428482070507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 833292131 1250 833290881 833290883
    0x6050405010c0519141902010b041a030d030507050f16120201230901060509010e0406051302090105090a0b0a0f08011116150902360c031501090b0406050316020a 71
    0x29040e141c0140768115103c02c82c1105800004a0506c40c41040500b404c00035125460282c0000076005191424481920141c642505c2500441c846020141d1000300351036610b01c1c0c1c54a4001500c1e40d0b000c1e41030310640200504040190004240199401005036900150707a004079501c00b112400d001c0c04a00b80c8144542503910f548441e80300e00c0400315035280003900000c00d1030000c1185030700c5401240000c030b0240d002e07003140304640c02440140603c6101d41c6401103003414030b8000c071035031035004100f43d86010b20a07240980c0310307400000c02c080000e6000022185004150000140d036549000103030920750301450980d0f501c0c10031f070200090207003801c80b203040e0f0626900031492881074580c40851070444a051140c03640350400107005035104d00490f0020300307054103c5540c0d100300555215030101c9880c0d03100701a460403c28080d0002c058002e03a60b2220317040007503120708142400102c0e030100f120303030082000c10340c00b240200b8031039004000b0314401c00045c0c01041d02c102c00607004a030b80b01c59201c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 833293381 1250 833292131 833292157
    0x2d150e151b07050603090c090108010207030806010e060904090809040b012d02120a08010929060318060408033310200703030905010212030a0b010c0f06050405010c05 73
    0x3001c44415541010942500c4120905846455a80b0004034840e41e008450030b211035081100c070b42c000b915010308542c2c0075054010085040c01e0b03056030050401000588924148200003001910903030700c00b022a0a20403001e0020303c0804002c0c58280269009030841d64400c81c1028079071010782d40300c0c2d00040203066003010003240b18a400c2d440c45407030503c1c9a030010110b00561411880819000f0000c040180c80c0740e40340d00d49985400354420442e2044498405c02200c03841c030148411041c501c0c00356500308100c481640c0c9854000d001c086510442031542154011401000240401000518030980741c0e82500b181136203034400d010200c1200b01c0340100040040080b02041404e06580810450780326040403840c5002180c1c60103015040300c0c000c0d45103644643d90030b02c10580c4c40302c5c41d44001e14082c00103101f030519020300b44090340402020000040d5a408846285c0d038030455a0001d083d40001000d001120141440401350130200d5040c0c0b400d6080c0032203200041d02c51801c50b101301100b14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 833294631 1250 833293381 833293387
    0x20c1801030f020111060f0402010210092a090c051b010903021c09170a021f020703030e060910051908060f0d30030e162d150e15 57
    0x1070340b181210242c03540141c0c100070f8100c8852100a00400c411409224100000101861300d44002440c05000090480035942001030701c0d00020b404501e0310090083c2c01415240b40140e500b541c00d071075540c0e613001e00075103400c0a02d050000c0c0e4014005001811640340b40661480803100c42a080c1c0c0c0c002c02c40140103a004280944840003e8180f07054582450314080480d00d544440c0d8688032014414204c001e80c0218228030214603054903201c9201d41c80500181248208081c065114034440c40b02038284400304030042c6490391201e044680c8d400d40100a040209541c81c0b0003061604407a00211280d080b00030b6904201e03001d201c0d10307440303180c00902c4512030200eaa014403085040300c400c1119000324801c04030b50110100c091600c45400d9040307511042441c0070030300509650071031501e03680b550468280c601d401d0082140d040700340c1d5200d203080c0902003804600082881140d0068107141070034490301050803460b500324141580c01ca0342d115040304224800300180d00c0120207074038049200030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 833295881 1250 833294631 833294633
    0x90207050a120e131406040614011103070b071824110f01050f090d081027050c0931050a06030f26070f080d1812020c180103 55
    0x1007501c084015051520301183c6005002040103060b108803211240d90300c0740d00884d002111110000d9205500719000c0c4100f070300d8804030b400e88030000c68009040005040401220f40e90400031104d040344d101038014140d18100d440109040300a0344100b2100820481c005981c090b8807407040080e00c05691200000c600c8080103642b90309504e011486140243e031040036150200f8400c042c4a0846552004510702d80b0882c114241001c440e1000144084102171001c0c20700c0c011111000d45151040b00e0b4003034866665115010844012918076003400c0004100b202c1d01018081e150306002550800944c911880d0609001c0201c040019a41400c040c64241c2c005140e40103540c010040b41c0c0005040381d265200c45d2450b000f441002e030b600e040011410441380c0c400c1c010034400c011100701d0340c0e4103008081d40c0d802a2000309810140840b0741c04280340d103981d509a400400103403001c00480e01100076610f401c1402c0510f8459000250180d000724244a0400f800300000c07224108040051981c21 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 833297131 1250 833295881 833295893
    0x207080304081005060d0b0a0b04051008060a0b0102030c0a0c150f02062710020423150c2d0f0c030a0b04060207020d0b10050d030c0f0f020406060513090207050a 71
    0x3008205d035030301811844c00c0380d0210b403820481c94000d00e864000858800c0c0c1e6081404240c0324090848045010040c40c208112500030840e180c00954107a0041449007490004074510300808008440501592600200304681600e120701124201918140d1120401400ba10b000138003400c42005604150b00190f0500c641c483d081e640034802004035400d02c030300d0078081850010354001d89080c503036000400b801095580d200c60b13540306c145814041c481d003c0c00c00c0401c400b86540340d02c51840d000040b8000300020400d100300c1d040d0f60f4041016100070034000ca1288401030200038244054011560b03020f00e45240810788400d000710103001080c3e19145955507204000c0700138001c2e40c08560030302c20740c80140d03106007071b101c3c1a80c000c4122241d10b080c0b110807181513405d00e91119104181092178080000d401440400a06802511000100700b072400d2840f244c12840c68000c4d0711910300200131070302c184c01001806c0140d1076540300d40040c40d00c9400394012440f841402801316400300c5641000220 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 833298381 1250 833297131 833297141
    0xc04050907110a0b150102011805120f120408030a0b0301050402010206011509050a081501060c02210309031501061b020306010902090109082b08060d02100c081902070803040810 78
    0x11010301151003109280d00c034844e8540301928119010001060403d5843d80d09019072070550380e106096400103d9640d403100d0361555800400c103410940440c00c0012400c040c07056030100d007a003001c00e00ca280703018a0003604c00e034021034040303c1c0e640c03500d10f01c440c0c242014492644100d41c11f80003001241d08240c2000c00240c0f001c044141080110703000401c6030b486030350085004003401340c010400c018421400c4072018505800c8031081021002d00d00000d41d889890004141c0d05139420a260800ca0b941014114400d84c090107425200d0b881140a2551000c0c1d4154100c80195845944031007024007800c80d443c500c1c5e00c1c080d506901441c014400c40045600920301c082c014103107007803069569030b0030904005c4415800c20031a842444c07142244400f5400450350441c60f4605071040f80352100000c0e41844010314040c0c080d2101c4913807954094042c003501070403d50481c000c69262000d1031115400810941c42203001800340300c1002070450400000e80b002d86007404d020f030942c80c0c0c090b001c00d0003c1c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 833299631 1250 833298381 833298407
    0x6060e07030e0d12050a0b03120703030e0303090601140a152304060509191701020705060114061912060b04150309020310090201140c060603120405010207050409140102130e0c04050907 81
    0x296030b40c07a07c40144d139020090310306410081c000035515981e450901900310b0b0000e02950f0001d40040040000c1d543c2e0105520703041d0348146840c80051104140800c0c503000182e0090186602e010340316500c0141c01030f11204400d001a14103444042e8040081e001038000c1e071141e400420000e000c3e200c50341c60503a02000791140d2280034146071558840300d05048584805020720142d42c0020803005004c8213204035405054401c4440c2030b9581841c010924a21500d900a03d0380203000c205080340d01d12610040d086080c4031403090210f15111402891140d0240c403c6c1c1e401e2960500310319210500a0003400c01c0581c0040185c00f4071040b64081001070040400b040b410440281c460651404c0002d0140c40400440002807200b0311b40399080c1443c0594410403810009420302c8104241e0780d0000c0c2c00001d40d201030310302140d031103a2071601c200c00e1000d4407034140303440d400855500c0c40c1084a050070b40490345034200c418800c2d150031482d406a44118052590088075500c00104c0c01760142110320b1400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 833300881 1250 833299631 833299651
    0xc090507031d01020c28061b0f0311040909050f0d02030913050105060712021c0309050d020a080f090103060f0603053c0402060d0f332106060e07030e0d1205 69
    0x11b03403455882c24102c0301c408580c2c0fa401840c0d40303450180c00e64090800017034070886043c200801162841e140e2241d0041d44650301310343c0c0d126480d00c0108003090041c11440c0802c2c2d4112513405003510300c0652217030084980d103070003100e10902e450001c4e01c460103030302c0c104da03405040b031072601d04c0030f84400584034402c820003003e610a5100501c845000061440480400c43d540040d884015142072070901488940c001c0855100c2e150701c00101d05150704859011002c00c0c1e1b110307500d0641e40c0040c0d0251041d40d102000b1031030b10380c2c80010910b800d504054130030a4880d0101c103240300b510705048400692030707224460345c1c1c00460f0104070103004055010b4100d4002480c49080c42c01c0129001c0c261140b010030700c81c1c52900c070b0701c05030450900ca4051305881094a20300d05d000566200b000d150f051958400c1d01c2c608503810a0504120040f1780d0901e0740b40390054418450142c95030140400301c0c5080d1358000000e440c00c8088602e0304000b01d1a2420242d00e039907859408a1000500d801030140135100e0912 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 833302131 1250 833300881 833300953
    0x601030213150e09180d0503060a05031509060c0319020306130e0d0306061119111e1504060c1106040504020c0604140313060c0c090507031d01020c 65
    0x742100321200320032002c5699400502445076001d214040c02c001c0c0140c1421050565103459901c004a910084000c0743d141440d2296500f100240010043e41d002d15014001c84901040c10180d42a2051142e95128200c0c0da00da1240c44130241750703110440700b00141c90b070f2800607074080c415542c0040d500b090005044001c240040c03038814088402c9080460802c0e4404400c480310560503000e2200180203a040078408a80074141d50754480412183c284605440c00c4083c904101c0c0705604110346410107020042c0c0340100c8007100c0020ba02003d000c5118000c00203030303039502e464142c084806640707940c0da52594641d02907550010500b0300800c2242e000d0b40c1404046a9074441e48060301b50500c540c1d0081c83c0c2810315080c013441402d20b00c41e804140350020001d40030200381d081d080c1c40843e4640d141c024a00d401c00e080824000d5820b40104440e2800c00081c041c0c500e03419000304aa00c2d00d00103414502c41c00d418030907401c07849007906080894100c510308400740440204d4458248a403500c10a071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 833303381 1250 833302131 833302139
    0x71d07030b0a080a052107020d020310021306031b0f030e0703390f0b180402190e030a0c0b091306260106050105070602030601050705070305031c0203010e0601030213 73
    0x42e626004510194801c00f013080900c2410454000060001040000154a40b40d48140c061040400190064484001110464808000d945c403020394504c011902c0b10040c00381000c030140d40340310b0800040d041c604000344036190085021001e01040d100d21035422403140b4141d024107460340c440e51803405031010000100d401d10000385e0782c680315040003000f40c00b0340b9811019441e056049082c101462200c05219410149200c082030f1501c0030030b907503151070702103000e5100c004d603c100301500140045003040da00840201c04040340c49030f90b2269405006444140365450401070406085030350211410409071043c0c00090101590180007545985092240002034840e25070080056004061248010000405544002040001c000d0082502d0320000030302c140251680a0148c0f58004049800c50b8054001c07520000d80c80b6094400c080c1e0749003001900c076044034218071942c00d1103181d80040703441c952003102c5c181e40082c184d100781038480400450094002100f40b1200700c001c01c0c0045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 833304631 1250 833303381 833303389
    0xb03010e190905071503060f03080405150d021303020901051816141306020d090e0714191110330b030f04030f080412031a06071a0108071d07030b 64
    0x4007034203041700c1204404030344240c000d0482e00150701a440041101750180f00052201c4101ca04440d002c8480e20a0f07824407000c4030b19035116210310000710510005244245405c6101e0f54012240210b403442502c0e80e030b80c0d041c4000700f4103200b4030b541d0520341c240c001490030340030005490031606d85251542515202043d00b6405a001c0c2001d502d0254140004000705581000126000c448501d4003580b001e01d05000160b41e101e0160180b005d0001c3c902840c10541005420788040c00002010700e0101d11410b1006403481180d03210440180c011090350740c4032454603002c1c17200714580c000480e0700c0f03042000080285030400a40c01c0d040004401e04002440d42c20403005e50f01448600c00b80c107942e410180380151400c2001003083c000e20000c101040041000c5289a048541040c280880d00d0441c040700d0381d11554178030401c1035100c68046100420f0010350221f10141c01941d0a8000c4070307989072184070b5500c0f4603030301c40d203c500d0741e0040d2051100b0003180500c03900030006080102e00340c02c06200107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 833305881 1250 833304631 833304643
    0x120c02130f1d060a0614060f160c0308130b040f0b07060b031c08060405071e0314010b130806151314010b0705061005091501020c04180c0b03010e190905 67
    0x10841d280e00c46404d001901d5024030450740109820f244080000004c0d00c0410114040c6140118014001207031455581d03400e80071000c030455210704440d0b10144c503490000720310f411111440c0482024400007052146809080310140c8030500f2464107590701e040800707282e81c2d00c80034040b11420f880e4504000151010001c030440081d03107100465508010700001403503150020725062040d41000c050180064110b0f4400d4101d00440e1143c4840c1d600e040d4003540a06000544403010f00c8542c400003617003a04580c054070110703404031001011143d580d5002035544000380c8075111442c0c68607521850a140c100c030480d00c442c07944040813907540703c2001d142d441400264489540c2d081d00040080c1084014455107621000c00071b540a041c0d41002c2c0450401000100b0701c140c959444180c400090f8000c00c5450f500303000061052142d640050086050850f080d182220b24400016000c602c0554803c1900e058801030111311455644040c0f4404282c5800400801c0e0b6540c0c400909003c58020320903 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 833307131 1250 833305881 833305931
    0x2070e04060e121606090f0b07020313050604050f0904020111010903020d030b010c030903030513093b03031b0d0c0305150a0501140c0304080303090a120c02130f 71
    0x1c00a8116524000642088003d85880580c1c4404102c004801c3d0358040c140c0c200e03160810750000320300c03840f850501c00c601c0f6501d2015141d0301d400c03c104100781d40d00000502401412862100c40c43d641c50040c1300c002d02440c028141e208484008140650501c3c02c0201d920500500d0700c1c61151510f842101c0c01c42d95492070950040c0c000c1180c0411654040c060b060580000303181619800d4616100203014040fa4003005080000000d80782c4a01041c424a200c064034103803034200945000800e03032a14105074040c240c2c8038a401880d0410404101c00b0382280441d0340d5502440c90742e540d070043c00c408114890540c501114050001c0c0d1001d0f8150300ca609520151a18002060300b01440034205040c40c00c01281d100319581d107000d200c1e81e41d0101c8000c4500c0072041c0c5407612030400c41300c0942036000300d03000285648404401c1004e80540040d028400502401d2103841543c00f85404035101701c506240a500000c04498041c203001c0158405040d400d541ca4000070255030f40b141e040c18000d0702e102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 833308381 1250 833307131 833307143
    0x317071a0c0417371101050904020d05100e010303020714030109060f0f1a030d05131223122502030303070c0515090a03050a02010b0a030b07110708100c02070e04 71
    0x61800c15a441c0203007080707071803800303403044134070300c0311075200d012403640506030001e1407070b0040020000164003990559038000070081c000d6466011084a14004003000c45242070590b008010008540301c60325400c0741070700c1c4c2540c06001d54604181010707a02200d8000c0ba50740542d81e50b03a00c1c0011a01c2e6100e988100c00500b030700807410b2001004074030151083c15890310b03100c02c11282030740c04075034000070394928085060030282d488554030344c2a10384140d103903404654544281e203101c00030050720080d00400e580f6120491040c0f03070395034000c1ba544c0d04850305030320803415010011802494840404503802d01003c01101001103040d602282c00d40d003007a00d8120125400d400000c1c01c10105001d40d4801c6c06584003480401d00d010052142d40e00c441280186c00e024000400c1c000300e030f100303400c000c042d0316014041c030581a9403440c0240d0315070300498801c00001c00c1c0d075048401c0900c0104007002218003440080488400e40100030004011004c0301c80103503c01c084d00051220401407019100350b000300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 833309631 1250 833308381 833308393
    0x130c021e100f061806060e041116080c06070903020f06030a1b080108070b1201030b041a0702030d050717040204050a021b01020712050708031306091b0317071a0c0417 73
    0xc401000d980c1c20074138000100703003805414007815500140713000182d10216804111840307500c11101c194801c4100c5100b11a0142c9201d4003070000040c014502d0407924003c43e2215940d000c421030319107030709002c020352083c18120380c441c01c3e14081003e1030700304100003000100c80030f180040c84a0701681540180c08640c0765001040042018000300e8024a0140c108901d0b015044013100141c08050000801c0440c140c070110b400d2107903411902c0880e450590340b1760018100000041e54940001c2c000032465810540000d00c0f80e8070031090140403400b0401d0144042d00c0d00d6080001501006020040c600e078284500401c0c0a26002e00c0100c02c1401c3c40010381d900054105107407a18000100c000a2060030001d160000b50001d080303039030240301c10481c100d41000c185803070006000049006484c08030010044c44260002d00e00c1c5030120b901c500302902d011510748041010601851201604040d5859049a00c0a0400110560160a040031241350039103130841800340d0206001030324440d51004d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 833310881 1250 833309631 833309639
    0x20d02120a260f04091a06040f1e03030804060509030d0c05090901090b09040305070f2003061b090127060801031101180902130509011202130c021e100f06 68
    0x2442c00071603203a0b040440c5031412000c0215411144035030310a41440c0d59452220326030070f00c40c101d61401c20541c0203085c0b07540d840d03840c0728000340f00b4841e00810b01d801016040040d54003002c0d000320b0048960585920100e80c1e150740320740b801844003d040010300d0000300b001c048019564400c1c1c021544583e190542c85403104802e02041410507003000e00b4203490034039019080e90314501e0031588141c0c9440c140d66114014a441c4110b0400c941c4024000101001c00303824202da808055400c91805900700d0b4651703944e1071005940700d0514041c40032010b40400801c6c44079482050b089940301520304c10300f850500e50064805500781c0315405180010712110042c400c200500310307211041002480c10300000c81070207280030342d0322803544944c0c0c080c0c1d940003612340d212003040030040d030090200402da40c6141d07035500e1048550302c003800e504910a10804021250149061145103101d03461540205010b0a00d0401d2540d80351038891012401d00c2107035402000f4816074040c0724000e414102c404168141381c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 833312131 1250 833310881 833310923
    0x30c3c0c05100501061e051e091306050f010e03031c1e09110909010b030604061b0512010e07020312090102130b030f0a020a030e0f010605210a020d02120a 68
    0x40c000b28402030909103001080800d17031003403c2140d60345039001c0b034000a4440313420550b19441000c82c0807450065500284a04425010141c10004006ea80b4802460b581503c11386c00c40d21b66002e82079000b810980c0035455540304066a80f04010043c04480c60060000d01c19400000d404541103400354444668940208507031140f0b00c0e1096080f581031054040300d0342c0b8941550903240001f1301500c047c1c0300041507002c00b50080002060302906613001030909060207005081d804148142c1c1d00e00900383c0a401e0b601c2082218401c00030020b10721a164244140310501c3c0034080d1400c001c43c4800d11290904080b51800309000c4d100c03000005944151315121802095440d40c0450901202232080000500803a50002e51165500d0001659040d48171300c140e00416100c4060b441d1446012400c20301d40c1c00540c840000d680b01140c034614a2080d6980c40617000e5000482d1a00b19046010801d006060144040b4100341c0700414114002d004450814903164141100b9500001802060059103a03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 833313381 1250 833312131 833312143
    0x8132d170a111c081e160207080d091a04030c140301051308070b060301110f0d0e06040201021504111c1401020f04050d170a02031306030c3c0c05 64
    0x600000646031885100500c04030f1210000e4000303043c0424400040c225000d00e149200d008a62500c1000c1c850030f141c840c041c05510801004409840342c0399000c0713969900007580f907010340d040d9a0750182c868104010700d001440000290130364030724280404400100e14881c0d14024048220351403140e40a548105801d40d800030745184542407011078a000412401c0045035840e9410804180d030715101c890109005102c08410b40c032003414085854030300603a007000144041d0320b41c250305200707280301000d4158803282c0964000b800341e07100c040014000c140300000181d1090041c110442e580030780c60080b900381d4100104e540020390700800b1110820107a07811490412401e80d00842c1415288448001d452040c0d01490740b054100340121804c00082241020344441007a00ca140c80d00c2070110069030301d802600d140d0300089481c51001c100103101348030b048410f9840c3d1756952546030030300707a48213030b580c00c41d690301c40110381a000c2402101c400410300d40140c02c0c031995410600d00c0a802c00c581403074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 833314631 1250 833313381 833313407
    0x90d1e240b09070903020d02030a06060b09010e030c010c2319020108090c0a1206020f070506180303040c0303120f110a020d030e070608071215030308132d170a 70
    0x1000310240551035038413404940540e641911350005902090002030310342213911130000c01c07042c103010011500400c814068407150b142a240c040c5159000d0040545a043d00304d070780c0740000c0200b820380e0080f40c0d400e80e01c007059064400e031050030300464281142c1080c5c480d403403000008902d907143e607045503403007181c15620690b02c0003c5c2801840d01c40000d00700344e10510858120b5100609050140241541140c19040d8002101c0780c0d0754200b450401d072601f07003c40310011f640020310f060400600d4040100c03441603a00803102c4401030b0440c6c3e2f050340c074440c00c0521540c04c0fa0750341c1903540e000c036000c0c401e00400604a46d0203d89504250788000d1908013819990300030903013000d41c07852500400203441c4040e200d0904041c1c5840ea600c04044074075060182040c0c0e0607504181e4554110044650b0000949001307035241795450307485040c4c094809244010050902c107443c8034048040e94030b1012084080e92111210700500ca90b5222448640340e00c1c1c41022540c000065460403494001d20313400c0706a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 833315881 1250 833314631 833314639
    0x606070525090b0a0501142101030212070b16030908160f0503071a07030c15020a140f070f050705040c05030604050709031502280203070b0c090d1e240b 67
    0x520020004140f040c04c2500c18581840803500120003e00610303c1030700c44041c800b03032030840000301850000c10101802e01c4142d001e101031210201818401198031020744005411712449c01c1410011344818816222081d02003020300307000400c240c002071115188441070a82503540445c01d001c1844444070791507102d117100c0da0149004004465841000104941c000350300f0644441280c101501c0941442c02d00810404101c03000142402041d806803010340540e540350003a09110900c80c44c0c0d2403040d0b1929550494040c081400003403600e4401540051081d400d9616059807040494191418103100d070020490210801029040c80e2090a070700c1042d920344540420710b07603120342e0303162104489800909a0001a505410f40207086002200c0700703041c0940b2500040c11100030345a420107041240c8403442c201c0444d004103481c60a40d440301130000c1181c00c41581a541d0b003030b0440788400310451081c228504c54400701e4031032802d181041d9080d003103910201c0103a8602030304403000350540d1446 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 833317131 1250 833315881 833315891
    0x120c090f090318051c0615061205010501050a3002340206030c03090c03240609040506071d060309010e160e0f091608160e01031703060607052509 64
    0x403e43c0c5c3c00320300711a05110b86003a141c0034a03082c1030420186c403d1001ca010000003000c00000d041d58446900205818a107030b041125980300c00045520b0321840742c1e440300268261940005007050000213030800e90600304039000b90005600c0030016038118003100100043c2c003030000740340200c40e584440e103060390181d002da100e20007070385c00140c0c3c030302000e0241401c1c2d1902100091103030104110b9080c000702e004088922500410140c800c0c00196801751141c64030404002c00e4441c24042d10300c0707001e42d82c068060181e0b5560000c0071560030f4140065040d0039545400b8001841e102c1d040107502881e051000450003850640400385001b14020b00c40c10004840741040104060a440c000d8101005200300707015030b20f5040041d071500041079994103108191410000c2e20301400500e6080c0c1c100ba03000100e0760700d40d81e1504034110703030001d12000e0f28000d0030020f01010001a5002103900003c001c00403414403005032101e525003070850700310315607810360050030b0070101f0481d1511400421a00c982070207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 833318381 1250 833317131 833317139
    0xb09041409190302070e01031211010203060109230415082b080c2809060c0f0213090b0405010605040f090249020f031501120c090f090318 61
    0x3558280d50000d1a07402c280041c0e140040520a0080e0401803840c110024055612420840185c0240341c40348400b08840d244140b09183c0c06000380c0e40303da20142c60350340300545021000712000300d0050340c0d002648a07801003c2c0303003580c40f840f40c64030014044c07203860111800c041d200751902e20904041c0c0160540781410502d11140034800010842c0c00307145c10307189500c03040e01040e000c0c0507625890402c4c00202504482c61418032202c0d0030009010758609100d40c0d5910b4080d9980e50741220085c004110401c0102c2c09030900743c541000410ba110382c009400c990f0354503210000c0c1025903084955944610b02004a803402d1301442083c0d04c8102c0c810080c80042ea07001480b200040748143c00f810114000c062005807640d42d01402400f0141c0245074405655075145a02c1c00054400700d01c0341c82044080012800c00003107480118000a00100f0755034200070401c01c85e0598801300322a8140c2a001c0403d90348120b000c3c0e00080c440148001c00c4202c014034020b8516010340c0914520040c140600300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 833319631 1250 833318381 833318383
    0x40b0103060b1c02040302041409010c11210409090f0302010c03060e060d0204140a0b13090503090d0f080a08011701050712090206041a21060d110612010b09041409 72
    0x40518114500c03503c020000e00540001034025540301079403061404600e4158918115065481810090020003d11482010a54506581d03945604181e802000b29010401d1018020900040d02c10300b8a41007955849191095501d5403600325142c2051a118101f0190240246103030b60902e4241031001341c0c181103801c4000070005040c2c9101c2c8004503610000d42d2581d034000750320103003440c061555130300d0000620030213000d24210060042c00003150b4500081114801c413460203034850060343c6059000010040d016803020001c0d0740c0342c4000388182000841c0c09004008107111600c54041e99850110301c001e450b10f802039080c40300e034140000c10110560080fa02c01d0101d4954500181020060002c50304070300072600300c10714031201030890312042c404030781c041d1582e84d8400b010403d58540c1c201004038003400030794255400c6003034100891b0020b102041140412180a0030036420b00306540c681c0800c811003a400010f0f462030000e901080c07030525000e003100300c1c500185035050a06140e41d0807 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 833320881 1250 833319631 833319637
    0x20c1f020c0f0105152823010e0a031403040e010609090e010b0a150c0605010b070506060a030302152509050f011106041b0509090619060501020319140d0b040b0103060b 74
    0x29441b40d00000340406084004080e40034440d4122280c0100c0d0b580c44030800c007803540c03003000c41440010074a0380c1d01e5084c0d8810322540045940142140c50068590f58980b03403c2c80c1443d0180d80140814000070483c9031090b00c1c03840c020007041d130f2500758240c0303845078500446c1c0719007000a40c40d034141442c44420340c0760040e682044808880a81e2681c1c541500101c44800c44440300520031801c0c1800010107410f48406450034601403020340300a500c2d04000c100a00700c19120050141e084102460b69091000000342e074401c10701d0761503c841c400c0c8940e000f528514240304800100e0040304050045080c507e03800b54494100303081601010030511401c5540d010700070001491200550054a18265000d0142006010140c2958040d0801074592621500e0031585415100c0f161440080b2400d4030380100f500b101c03810b030060343c9003007804900c41e96180300e0640c075a4144103441103030b400354445190040800c1c04e00c82e00c00088201d044403c2109842103003081504141c03c1c101c0070f204000d101011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 833322131 1250 833320881 833320921
    0x1b1a0a0e011119060f0203090a080711131d0d14070f061e0e031314030c030601080a0506240d11090406240612020c1f020c0f0105 57
    0x9000c00a000486000302c00d0000030009000f2544150300c4516034100c00381045105000c244071030750a40e04c10108034041100d40d025258008094480030403001c2c4000d00020b8000e11001402080013804aa00308082c5400e040c0629910045503c020414480c545407241e44030018207046d41d0f45000048c100e0b06103c00344094142c000904400304100c000c2d0f04c0030200d038081e01c28000325809603002090312034580090a01c403400d008400b03000140200864003605403441d09800c955081c800f44240c44240e1b00e112503090305c1407100c004403598007003114a000f004124010044c141c03203440d01c5805c1690181c482c41340328110030722003046041c00b99074070101d0305000d0345c8c0049803009604090f90b4089da40d2402c0b5030410b515009000900c0307580e030011a1403885e8001004650b11240b9600801041d8034420a0002600c104520440c542342d0740007072a8102c103600072039888000403402617540e80d409084204003a80c0c0022840c00c650b100380071580b0107150342d4000f0046440d204403201007042610803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 833323381 1250 833322131 833322137
    0x180e060408190c0203120912070e1302040e061005030c0103021e0f1201080d030e0c010206041b0902040806101203020d210f060303020601090b280506071b1a0a 70
    0x1250040d80c0d210f40384046002c1c0e0001c04039003200403488402185980600ca241703004025240c11980d9032000000c10a040703800490b8801d1855488066040c601d42c400d400881e40a034a8440c8038401100806c040d500661019040800311450b1108162501001c00c004a041c580107000d401c100d0215a00003000f00f856241c40a039503082c1d408030011503407046800054100f2444400410407000005000b0401841e6850800144019504481c1d8414009240c0c07401a4450340016002440407200d040449030102d2442d86440e8440880c0340aa80241d004401d50354402010001c01d561514940d10050819030b0b0203003452461038030002c0d21340c200104804d040c40001c0c134441001400084426000318214501080300e0b130600c10803000a000c0d14401a40184039250000c00c003400148205010984010302240301c2c500d0714040003c101503800d000d0991040011070006007074481f44003c1005070302c20200c203030412446112844013000c00350400c0c89116148680a2450420b62086811146240c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 833324631 1250 833323381 833323417
    0x6020304060e030d0b010e01050c060601030e0c030d0804021e0d0809060d060b03060a0603330815040b07081b0c0c0a080106090b0915091f180e060408 66
    0x2080c524003034211012601542c0c440010202c4509060364494545170100340c3c0c1d0001410110740c01140c01c0d02075441940d0702034100e00040b44c040d40c02070b03100d08950700070941642d8514402000003424481c0c038828a101040300b94081004504d4041201c078500b0b401114071003a0704044c0e402080f081307602004000d1110000152141c582c0d80d642c0161030000c0f000d5482170001c1901c807400c0301d0050f00241e80e1705004604800011400c41e000e40100007195002007000b002c1c800d1080d10107113480003500c8044240c4500d00b171003c1613001d414800c503080841714001a40c0242400d14145a0907a0f00811240c2009503070000d001d89007010006086140c401c100d4031689400090880c070342026118403905d5480704a482001602c4081900030400301c550b0300c04204440e03494002480f03070b005401c5601400052401c0092400e503d4040501500142c0b880d2948521010000c071113591001b16810440c00c07810240010000784519003e007402d004400e00c0a086a41041daa9881145c0101596084100119 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 833325881 1250 833324631 833324633
    0xc020108070306150e040e060411010c0201030618020903070b09100507061409060711010b0d02041d0d05071401020a09140f2206061b0314090303070606090b0a050d06020304 76
    0xc3d42094002e801000f5014030142001d42014001c071000408076030265081c541d80b0001c040f40820007910580d000540c2100d4642010011281c00000c808101d060555841011450200d40c1106c220f008002c480d006070380c0c13007050f810145001e9059000e1140d089080240381d0b580c0d1202840107070760340d855041058031107010349800006845e100c0340002c11244601d0800c40b03a5000001c446014100a8480000c0300d00c2201d001c03030a1351146031703010340c005000000300801801c00340c0c448019650884101081002841c0301a07040115516601c40084e8000c5005801e000344c401001c02a11510b000841c0b40844610000c1d0030401c0e0791040b500d5081904900c89031540307540e803c2112780034000b071094828407005041c0c012071403d0280403524140c43c0c118040303030b040d01030907074860600c0740e0031401c0c0e85452042d80e084604401461222810801c08d20465401c0d4504102510125204040103e269401c0c149110111045810702c544100030740d0100b00401e4451201d5085003980040001d6603036515 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 833327131 1250 833325881 833325887
    0x6040525050409060e0d020c09220206030403021513020306010905090c040902041e050a060909030230120f09061303180f0f09061d060d15021b0c100c02010807 70
    0x4070003140c0c5c1c40303004207a40e81c50801c1c0d011232500c114050460340815a51503c140d0f1131100b48140c141c3e00d100000401c401805807038101d01959109120b0310444000024401c160740ca044010340d000000010104a050210305d01031102c03e0240280e4082000130b031601506242d956011502c0c168002ca640c0c045583c15515075030001030301c046010025019151a41844a00812048501044140c5810400301b259056801103407001c4c0c4e0168000c0100d00c2c004101c1010b10800c8000d51100300000480d4003031001d40380f130007400241c030b40d420020300b0514004a00b8070070340200400ca0040c0342c0000b000c2000d01d94000d009003400da505454842c4554044081010741ea2106800c18a41d4814001d00001e80c440c05103000b00a541c90500240f00f166601c0e07600784620695811180c1031000303001d00141c0e0b2414101002c121940c09000b503c01c00812816800080313034040000200034022a9000c0c050241040101c000418400d41d40e00090103103035203009103c0908404000e0401c100b180200d00c100b44 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 833328381 1250 833327131 833327141
    0x60108040212030f0c0c041103071103040306060b03061305040302030a0f18030f12020c0a0509090c100e03012a050306010c120206070906110a020f031504050604052505040906 77
    0x1d0848100c81e9960401101903155800045d030b0900741c1c0c882c00300c0029250800340680400110320344c0c0450f046440303109007680d200c1600200d500382031009000000100320700d030041f000188900c01030700d50b41313061906c1804030303240c898004040719500700010320001a90000485522000710302d0a141c2e01d001040c411201c2142041044810b0f004404001c001c0c42044c10540b843e06100d03001007518100c2203901640c0796401d0880c071aa10126a144c20000750a001910300d50110590081d2aa000181c00000704008556079080001503c01c03114100c2c2402c091281107024a00343c0d42d540c1340d001803c0c04c50028180a022800d08001012000c141c290b4091251081ea469200d000c415800300080380080d40e640044440e1030005100000015989005040040e80340390701002505692402e9002e10514650000f41c10750544509600c1000c0740200e4100140581d200740040c1801d0b06041c108107103090b04501010710343c001c2c800f03003200c19420307680c00100c110380c2c003501c3c04a001c15450401c140241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 833329631 1250 833328381 833328409
    0x11280308032e05011b02090f420105210f0108010204030b060d05191b0b0c031e0f0d0e120306181f0306020a0818100504060612080a0806030a02090601080402 69
    0x401040038018480c3d208d4810600c5011421210000312a501154180703a080c2509c0001200da04620b8a198251900164440e20041810103c0c9080e1026400c080868440154207440c08010400c0c40502001c5004450041462000070f50615066450700c2e00204800f4101c54800e403200514007041003400e22080070400c0f10300c803010724481e1540c10f080e11840f466081c1e81d803018110b407001140800a01041c1c8113442c80c9000107504040c15000b00404000044446a210000034412139404a80c82c100a2402d1049180e001c1589206a03030b50610301a181041119801418001c0140303076215032080c0300c050300030903a101d001ca403503214081c10204480d018640b51000d4504021041c0885c0b60010142d11100c1d644200d965580c5080e82c2003540c0700c64141c202c1c503030440c069802d20640c2603003019401601410001a445942e004824454120520110f40a800200700c01c0030854002e1007140d07002c10150043d0413103600d241d0010b04007040040203a4144515440030405644822000c08092 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 833330881 1250 833329631 833329639
    0x12105010605032509030206030712020f04170304051c0f21020d1107140a080d0809150f01051e0a06090f05060711280308032e05011b02 60
    0x95840d184014219881200c138000100c140c00b01c1204883c0c29034600c00460700c0c44d80d6803100002d003190700b000020740c005080c01003000b000f2111000300748440d1006015044511843d5640d881c03030308240d407021482e0482241c00c5a04184402c00041d1a19200200980340026028290040e00d1801c0101440c40c500c010304000b032249150982d4410010481428103460307000c1350404100580704543c0d6031444040c121300c3d40c004840400c010300c0c1c003c03010003c611000b810814419224100213282003101003126000604080c00c0c002642401c0c010390f44140b1400003e8542031405452105010406203d003034014080201d801200f8901010040c0e85018018007080c100399407a20000c00c141400e0041003000102980001003e2030007008640784258408400c210788141c1600f00712511010401043c690b400654668401c070404c0c4004030007851194031081e88a0070010341c0c0122403001c5a02c40028889000390400c80c0c13800410302e0740d08680e42481d001260030004502d8a00100c1040002904 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 833332131 1250 833330881 833330891
    0x519050d0206130b0a0e1f0c030807140c100b09010311100c0f0b060907020f0a020d0807050f15061203072012030d150f0608130b070206060f0a140121 66
    0xd40e80d800350340307010700d4402243c0140c1c001844031150b10080703070754882c0100810029015180041d01034045240c2c007411a04000c221013001c920ce1111591088201000907001000184408082480703500e503160b100352071040c090346c11580c5a20101c03e440b0309880c03041001e10702eaa00918400d041040c8416400309030200700125a1500703180840d01610044e2040078650300007498a48000798030b5940c841300d14010151050315809020305c00d086480240c800e031104102c0500458010828806900d090b81d0041141c80b04040c116002684c001d400d451041c012058024000c03030380001600c0500e5007040c0302803000b100d030004070603411803041c00658005120000b25001c4d140044090017642c20480e105003c820605811101e000d0031900a803c000c0415480500005100f104815448005003500702c1014806441e0341d44100d10885501006034020b004018442c28060001029900c00351a00d01d080b508090507000c4e002115600c6c41d0400800454655800920000e41098200c2d10002040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 833333381 1250 833332131 833332147
    0x5040609021206010f0e0d020f180403020f03070b1503010914010204090b0409020607030c05010e011a18160507060908040603150b09150304050102070501060b03010519050d0206130b 80
    0x4081d400c0026140d0602801c0c50014643d540030399400c0030300c280f8940c0c4070601c14103640c04010304104a98001da800440e44082c2c10526104e1014004907651000e5134110f0b28900b0745402803420203410284180c42e0000e012500001c1d482000e40b81c2c00034011303005400d407284403d02103801802a04000341c502040690b900e401c0300419401002601c3e40c400040c09001342440511083d50300c80d03640290081c500301b0440021903c501c01446010380308400103c1d04001190245080d99150403407a00c070400300700e200d40740500d85003115400341003402c3c43da60440d10340101001c2c1ca5444000c42e210602c100021034003304034072079000780c1019a01690702e0f6250307078a6200003001808516101ca01000c1e07101da011410070b02800035540f08100007072400c40ca50301c05500800594101a10072580c66409002c00741c00240280038100180409500e003948a46c549401c0264480201164083e440002041031040751030352036801901d5034040d184a95030351f040ca20500d40041050784559855000860088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 833334631 1250 833333381 833333399
    0x804230d080106021615030c140427141602030405040221011a0f1b010516020d0c0f12050c100209010f0806030303071d18090f0f060c13050406 63
    0x541a1881c0c0d5007103810090002d121081d00307041c01c0c090f8805000704081600066440f9030080307a40309200703142658050010708040005074005401c0030bd445016280c02c00d000031a012100800c60300307101020f1004600c03072119245280030180210f42143c0c200d00001e0302c107900800442d0010280034008541ea4400742c01c03003814040390618400390190602d4000900910510b961182c21a41421541c0c03610001403040034143d800303810f158084a004e00e030b00b601030344000c1c400c05100d425140c0c0b00b0b003000d122428000703042000480c041c9090113148120707000440c503400d243c1c01c50780d41c2c000c24002400079456825203281c01440c65080f0036105614050700406c1840d0040d100024003030b200c1807030f858444042500c41c104200e8056806034003e100040c4914458085100052044140c03078907501900c4002c903000650342414480600c142005010b0b10703003010010b03001540b0548003e004621400e440090310340d42d0140c041143e2280100c0c24001d648450031041c03000b0303e0005c008114065503a2804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 833335881 1250 833334631 833334647
    0x618050108011a10030b010905100804020306250e03010e0601120512390d050a26060d1119030501050f07080601050d020f1812010c0804230d 62
    0x20019550030040700c0101c0001c800f1000100b00c4000713240307482103020f03510101c006016880000381000710142c0000b0301a201c54420045080b499903c6c284503180a0040c03500e450009403101000c980b08140d00800c100c0d072400d0956446041e881c2c0302d040501008006409000300014203526070142d90300001c7c154103640f0a003a1018460b406547d02c50315101c402098a00801510004100d9034841e4443d55460040422074110a011a00704244c0c0e1006805803070320400c456820007161000030140c1149070841484180b41c03244402ea0446c5880c051803041810a0241c000c034000e408143d001401c0081442c1e21003205440a030035001d4861000d8080c0c8250349040c802541c455180401151064078078501181c031451041d2601c021a40342c5400440b01f59102d5035004800c141d0a010075184a04040d0080a06c8400020080c0d140314049082000407040c40c103003283d07168904014800d40c44e40103014668040d800a010340170024043c0345e00d9583c0c1100c1e101c0c825590081d003141c503095680280301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 833337131 1250 833335881 833335889
    0x20f030415020a0503070305042a05010e030a050307121e030203010303031a01090e070c05060a020901020c0d0c090203040c080f0109050c040b060f03070e060703231206090402030106180501 83
    0x96150080040700700404030b10500c244040015010170018000303500036008a6040f40c410400c808290203800c5086d200001d80c180c40114446414004002c2981e0220700080c1002040f0040c2100031990b40e030341d942c5d07481440c200500c0400c0202102c2a280c3c05041c00064102c40d44c45841d42625131000010700a5109001c111b0100b440c1c4a00400b80742060700321f601a245042c0c4407603c0441c10004511300c4444000c142e00200110000f120700060b030300f440014010b003c414000750725604003030300190401d0091000c0d07030301a000b80760404000c2503501c095041202d02020005030f4a45482c200540104d030309820000703d9100d0003c00500310740056100701204c500030001e035644001500100015135200b441e4696001d54280700c0c14103001c0301c04000b140c10003c0783c1044e444500003180442c02541100030709502041c01034080701c1e11648410002900c0301480b115940c9048840309850b02c02e0740c00a0034481c080c660b0f2071300080440d00c0942c4200c001c0c10b12866258000032440c00618050b00007402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 833338381 1250 833337131 833337143
    0xb04030308090d0e24220f15020d0c1505090624010203180f10020f0f010615050a0c02040501091a0a05030309191d09300a030609020f0304 61
    0x1001e828241e1188002c40740e0380500410314070080d080d50428110400080880d032018a17003c000400c0818000014030610300c40000d644600680b401011005926981e80103a840b03001c0c220540702003540c0496014203841c0103040415440442c0c2c00d0a018403404200003034085d52610091142840c1c0000744d8910515005541b110040340900003c0f55000309665024050380c810311140704074002c90500b445038000040d103581c8810f01d0000c0000c00d40d04015484101580160356825101c0100f0300c2450b04070061840240300c660f1401d180c4001510110060004001c0c01240101e111762003290307084402038005200b40840c0d61100641d1004003403580844031481091a0f517540e1038109a0001022114000c014508040000c1d080c803020030a203c0c0c10842445c040341000c03940e00345c001c403043c85062450781501c0043c5812044180350007100704040788000c0c0d8081103007040801c040c0300da1441198591100391101c04034074058026101503080941d06c0c078000b0030035500e2010450301851049010f00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 833339631 1250 833338381 833338393
    0x21e07080604230d02060c07020111030f1b0601030507050111031b03030a0c08100302090612010c020307020406140a0303140d0603050c0a05090f01030f110d06060602010506220f02040b0403030809 86
    0x82c50b51942d501d1800c04d0b00002d40c0203100010321725202c0c170b40035105a60040c100030080500f00e081850450340a0f40400c000023030003096100308169212231b200b5001252500a040650564450990b2010300348101e07410040741b6981840044d10610a50307070100282c0307a80404950f402038401c0c0e242d81080354030007400345c5061260013000d44a160650b0051502c0480100a01d042d13800340701c0c0e0240000c00241d0041c0fa500741e0220011000d20031048000d000354081c41e1500700c144100f105842041d4001042031445600c001081d1b601e81c40d20401b12a810b00b003c6030350040004880c00780380642e1142215051a20300008103100300491010350a610441d40c030160720b921141004080901074600c0c141700b0042d2401440080d005840426480e80a05010b84048002e03d0000d00b001080120840740280c07140010040c6a409008090b04004101c40d100c80d81408a41c541c13207070302120002000e09646841c1c4210b02c501681c0d0480d4082c24400f105580d9580c0c4a007005048803905031014070042c8129 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 833340881 1250 833339631 833339693
    0x1c111201091509050a02060a0905040b04090803060d05190c15021f020d090c180c0305010501020a0f0c0509090706090f03080a05181e13020a021e07080604 68
    0x18440c15404a0b880030310302070a4603005241c4001011043c108a900d403182145d2240941e4801000d407011041d00e584060040f42408144000d039002d80c520030303004e6030074900081e00055810003602c2d48160280c0b40c049200015081540c9040010424810700c519110f0f4035006018540c0d0f044029074020302c060288049201008070fa5070380c0e541044810342da00c82c10750000101019001800b44012a84012950003d10349550130036054990050018074844003604854011901a00001d050a03060070841980740c00000303500c2d40454140104040e0200d0000020403080300d00d403001a010151000501e480d141d2216035407003646004a0b000b24142410029241c2107113080042034903400648241021078a101c2a95643c0280019000000d030708148000242c80b420100d0120803850200702000d00640d005101c000421041850340090040111044180d000103c00a82c02e61000720114640c019070002c070309140c05a0402c480c20b001e0f08040c44148801e423120b041c0c2c800b225018500d040e00c82 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 833342131 1250 833340881 833340883
    0x3060b091513110f0d0c030b0f04200d0213080c030a08070302030c01090602040504110702090105060a020f011b08130f0b0612030d020304120804201c1112 68
    0x401c44841016200ca442960a9402c08607400030156040324408201010100200c0899801020445031800004150004040141d00801d0184125800d0401010843c00301160310a4100102a401aa214101c003c40d00b4081c500a280700c0d0403020686840e00401c0340c00d4001b0b544401040384181c03401000110b6000740c0400c82d021039240080081190402c66034070320406402111041e000d6000502582c0c500c05020700034150254860b850040e5680d0030201000112404000c544450420500c066001621950b40c0181515421585140c9801110300e08a00e0050b582c05602030a5080441400c040504c062413a203001d04141c54522150340c0e010784a0169a40200029122544840e00c041c0400c0c400c1c03890581020014050790680007a191800f89140d0110b110400b090346d0010821050001a65a14440340000d2038065441d00341600e4807401c422074600c01a181c1601a0b141c10000e65403800a054481d1140d403249095020300d013000c0e00d40390300c21070004d40103c202246c04501000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 833343381 1250 833342131 833342149
    0x31c1409070e01060e062223010801140a030203120306041d0a02131808120609070c0b070302160614090610170f150a0606031104060e19060903060b 65
    0x2220340358400311030781303090f20450b8000d03258015250029010071107000940c5640e4070b0b004400c40c02c60b1586405c6403034000c1d00c414201d869203014004c8401d401c0342c540c0503030b4004007003070445442d80800300914201c1c000003007400500e41e0000b54035120b000142c042031004100030394414a0220740400054102c035907000721110917140e158444d1b800c10340e0304100510b000054080c4a0b800b0510004264408003404654010034007819a6004030100d282c41d00100510480da51250050320000c1c0d05051100010b400082c4600c401004241c4c0e030400201040e101c1c1c1d06452200301200001108001c0c41c0c1001d070010003900451045141d0f9190000341083e4000400364000d0740000c0e8011803241c5000101e15240c10300039038440c0140202a90004242c1c820410021980ca0000c04c0003102c0c1058080c4204440e02036101200341402c0200c0c0841c0c0445a00c01d40d07080f14007a0034019500e61100002a1542245000040068400c60300100d11664043c002c0c2d01a0791146000b00404d588140130412424 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 833344631 1250 833343381 833343389
    0xb06040b0301030803040609122a050c131b0507020319031202090d08130e1806010b0a020c0a0801051f0302060702040e0f010c08061003051605030603031c140907 71
    0x100c200010030000f0b1100d0b0040d070740180256400910741401e5954011210742606ea80703000910b80740704024145100a030740000e2090041c0d140c11021240f9650181c41d120400c0d0103d00c255503a800301080c0002d9034018082550607001110601040030310003811940010200ba40a40301d4858083c0c0c0d80c0c0344a00ba02e48074140c040e102c242c0888520741181000c0d40c00810415000810070b1004000266040041c0c1082414000f15007000c43c242090a010410000d00b141c00120b0740a5181c40113800200b129030558105070015959020114811303440c00b90503124080c0c00036480301000404040652009028006010b2900200340c81d200340c071710b10a10700c1d000c0070f988050104001001442c1c2988580a19080b0b0001c0e10700c1114002000d40c00c41d8800c11010000c6285002082340d076281c400031200006086060030482801e019100007444056600040c3c280711000000c070349566030030825334440144141100c40c0303242030201c024000d0075205440d078091000c5003000c16913414010903484241d13 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 833345881 1250 833344631 833344649
    0xf0109050a121b110a0801060905090105070206042406030803090703210203120a060f080d08241011100e0709020702060a030506180114010f020f0a02091e01180b0604 73
    0x4100341da03c41508903510020095440701700c110300000e21441c04e00900d030051914850000303843ca8100361880c25607000514040840d0800801c0000140403041c3e0480d079101040303201c92440c2c5c2104034910091940750806000f8032004000c105141a001510b01c0c250f910a55038998080c0b054595400161250719405015030000e100035650010b00100e240c0d1304c030005650118086948030031103680f2022a801c40c20f203030341048c40c0c00f40b00d0b43d4200038480d4108920400d010f484020800300060f1480107002c02c47c3c130501c8940b40300540941701d800c0071060400c050f01503855662901c8442c100030071061640d0311245c007484800042c045464400e403800c10340c01820f03080c581b000c1e5090440c000d00c40149240c4e4402d040040c0e00034210004400d060103841800c45407103904400e4800035020520b010581011503120310500c08030b002021500c0825143d06076180c00450b240c0007a450042c283c51403a01e0241040e6000000fa42c0d01d00883c041e2400583c00c00400c15003a020b01806164899802480703c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 833347131 1250 833345881 833345927
    0x3041a1501082a0705010b010f1706010201060b0307021617031902070306090309081510090e01230115092312010501091d0312070c03020f0109050a12 66
    0x41540602c2c01190b0041951101201d14103110104250a403841003650900d40804103030b610422100f4491140d410500742001c58120740c412600600c2c0c092100311103080c100191010810a034001d401410203000b010489e940c0300d2602c0c050080d034411034150000ca410a2000c400903a2200400300d0b0440c1c14101009176207440c103925000b1410400280901d01140b155480000c082604d910407160300b01c1c4240c2e1281092031804100d1071601102390344002090900405004040c40600f005104481a440703010840d41028a540b60051803044800f24045d203900881c40d04040bc1c03e00d14038141d61900403d601100c5204000302da40500f0350003802ca103104880070700e20010b2045000c08500e980f00504100d0660300302d401040c29640280e0000d06010b03128082100052030041c3e080c034800c10140c0065081c0000d41c2d243c503403d4580517001c10705003d400340a02051600c207000007850b002c070b00002400340c0251031404503510750421a081ea840300d035400b00c0290b068031403a200042814001c1c06519 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 833348381 1250 833347131 833347171
    0x3121c05010b030c0c0f0619050609150f040f1821050306011d0d1505060102031602130e03120403030b06070308071101020d06080a060b0108070c0b040503091503041a 73
    0x159100170300441c068801c0582d01403507000d04104040c400c0307a4601c0b48862031440a8191410344030007803c890302c0340700c40e00304100811814802040c1400000c441c00901c907112400031600030001c3c840903103290343c1407001e0b0400344d000c00064107045600c2001c211103808030207000760340480c162910003c009030082012559540c0310f407828025903807400d81101540e6a04400085100c40151021580e00101500c4860b969800c0d10a69a2103202070010318500704075940e82c1d40c035110240034000e109030903030300521184004503407141641c6486101200da80c1c1a80003a4010026000c4401314000b9040588565450a00f0300c1a079095503030645800d480c6880313074101074841141d410029a1a5903090214031841c1041c1d0080c00018641d03800907244091003030406034291601c240e001c83c14480b0303030010300404a0b03008000100c00e6030000340c1c0e002c603501d840c80d110b4110b10070145101d41c070036180102d21a9624910380154081c0341300e03061100d132801071010140314030a0b080354a60360364203020400c41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 833349631 1250 833348381 833348401
    0x4210509031b2404170609060108070b120c09030708100c03140406051528090603032708061005130e19032006041b050307060c1103121c05010b03 64
    0x303e40012104014141500c440701c03802040c040901464030350340041e043c0b0066030024032a440c098a000c401400a050905d54011000e100b2040901c10b941c8079100011030001c03034039043e1340390100010181c0700190f43d43d54a0b50341e42e0458021a0746454500900207040754000d2150410903010040d0704210350396940c4440c00240401031020350710500d040c1d42d0f682180d1303409407981c0040c080e250701c0045011240340e810f00c0341c1e100c030f800c00203005142410900100341c01c141c950042900c6074012401500d4460302400403001981d0000d502c9100700c90601100840400c0c0e90b10a5800c1a110031900c50b1b04806803000344c4850306a45403a0307400c002c0b03c0300103038110115451403140c003904040000004080b0035940c0c03c014442803103080d0f00038205200410100042d00ca405110801c3c10144190400c00000d03110078991040308148410608804204902c0e0700e07910031701c110b0080903201440420400d200385540103088040c4140e03a420780140d15682a8800c542c1a52907015809003190f451001d50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 833350881 1250 833349631 833349679
    0x412030207020f2205091006120503120603030d0e030a0e011e0302030705040b07060f0c0203120c0901090e070305040201090801020c070b180d03020c10080f0601030504210509031b 79
    0x6800304144820300c48044a1315001d00d901a80e8848010004201d07040260400c903845504002148918011900003103900081a502c6144290b40c20780d09948900b0002440c521500f005008424180f410311800c5890210240090003280d884001c00c600c1403100444581c1d0000b41c140340564800803828014030303c658003a40e44002c0c2130070811f14090702e1303140c40c6140d40c210081c21901292101444c0e914034919009140340e18080d400118242040c140507150400c400401207840f01e1008940100207a00c20312240004003407420407048581402c0000034003405080b00c091703001c24008040029284014800c946a0075001d41c0030b001082d00f03207042500030780e1000100303006020f2141c00041017540e481280340747c0140300360018030340905030307005200000d03082040301d40612000c402005070031504004880c0d07003d40240b900003019990b620344801601d6405500c02103c640c801a06030071983c20100038003c0038822800c65110681110049521110300000e00c1d03040ba003c1d0040d60112a450100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 833352131 1250 833350881 833350909
    0xb0f060303090a09020c190519050a08031806010506130902091527090f0105010f021e030c070b0301150f0c0506190c1106130f050f060412030207020f 66
    0x2078070b20748140e00b00051088040390f00040903c0381d0024903092000c0c0d0401c000101103105600050f600704040e10b50315211003501004185045000310302e141000401d200702601240c0c040c2102c5d849003020101031201802c04250b0908522414001150910308582035440c281038060904040754100328205010307400c1114001c0d0001d2003903449d07410310400d081c050b00400c82c60340f21042d1304c000d5200118904101001e01c1c14000c5a414080c0a45a209444c150741981c40a08000e0218616100c0480c0b42c03803220700800d56607100100c1c0d07005207100084000d000f81d920040880c0e5500c0c0d140c2143c5c014502c030070320416142c0c1030800c006803202070040c440380604800c941406943c0c00444d03215075003030041c21503d68a0030b80d220011180504041d1203040340c42081d03454a0325079040c0da80c44035540e03640c3c050101c90304e002601c3e6602d000c01c05141c1003245600d6004040d510130b440070407a42d541e01c01095400b03c40200c00e00030f40244040c4070744240d4803425001425540700e8a0705000380601c000300040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 833353381 1250 833352131 833352133
    0x30b03030c0f06100f060c0201051b0a032001050f0609060604150c140a0201081810060b070b06030a080d0c050c1c020706020703081209070519090b0d0b0f0603 70
    0xc41500c0000007449150840481607000d007003545464001c0e04099070301c3d0781082001c40c111100c00e208547e4002c5152110960a0030401e64826004103800d0010101e81104980792080385000c00426600c146503c000903040701c02804220394100c000c0d800c0c0c0b40d04440000900b1003000004140d0b15103900b040303410142c0500f1140c503051b114090481d881c0d50a04d140000f094141c02a201000454040c034150500112302818040044e580000c0c0790001c01303040e103404200c0740280100d4418050104074500020b14108201150f510300030100c06800000c01030715400740c01c000141e2075007404078900600c268003981da01e14041e44403240c580107149034146401005024850102514801c0141880901640340d602074942d1480d1002454008550011411508040801c100066140e000d490070a21040042c40459a4209030513203010ba180e8440c662150010b021b00d20510f00d0f400200d000d840d01c1e02010b0140035035010900c4480106075070b00800320860f900000f9a00300e02d081030355400900c020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 833354631 1250 833353381 833353387
    0x1605100914040b010c12090e10081005090c060706051005060405060a030504210c051c051b0102090a1e0603050403050f0a11120d050f01031109040507050a141c12030b0303 75
    0x345800d1b51a00d6000700c00004541c03450814410000d124904a0b0304c280c4180000d4001c2d13051000d516110740010f05401c410340c0d00c502c0402c40010341400200910080540920703180d540b41c1c00d00402420040d548a03480506000d400720b802d0130070310212419144050000c0f46050000202100207000040050742c41d0700c0e038034020322a03060745090700b6000140d460742c919020902509206040a4030b1120013000da042e40461030b03c105400c44191000c40714041070741c031040c031414610319001e841481b03805a444244428041485d03228030050403d84d0510701d48104607280c550300190100e0b10180e034041c01041d810707c0700e0b201647e4400010800c0001c540b1f400d051a0180403d00c5150081082c6107000c11000031680007200d21b400d114480e44070080c40803844003541b46494520a15081802181c0690740080008051160400c0548024a00034051115035035680344840008034110382c1c0369101d080c080c40c0e0250b40c001c40c1c2c0052160719420003507030080c00d03003c2c1000307a00030829580102e0b0540814 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 833355881 1250 833354631 833354633
    0x3040c0504050a0b040c09050a06120e0303090d1404030506010e06030c040f020a030c020c060904020a140301030f030e03011e021c1e0624030b0607051605100914040b010c 75
    0x240150b6018800c0d0150104040d82510108030964800041c0c00041081c040383c03c2050f941c0e06c0c0183c40c101c942608020a1140b0501d2800000e840c0c86c01814071070707110020922418000008142c5600c4401d070707450075400e0350840c004650502c1644000307007203688a000103000c00038803501040c1e04038100500f124003000310315000c03400307a880441600d41040c3d03011903110040f130b8040c021900030700081c1c400780022064410004545000e00d180c12401580c0c080390201403d40105200c2c20780c110a0b61210341c0703039a0740c0c0c82c0c11203e426440904400242c252140c501c0c80f4101401901e00000b80403280c1402000380e40c009000941010b048441d10825412119501030310034445c2010103001c2603034100039001e10b411820140c403440d134090805100130f41500c0c0d003816003240740c00d041d41c0381c0c520700030601d01c1d100c070001200c500610b0400341c16030003405540d00101001d03a03a40c1040312000d540f00c40392021142c41c1507400914501c26800390a05c0c50140118030b24095021014078401410296909801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 833357131 1250 833355881 833355889
    0xe07120203072d09050a05030615040e0f0c03240a11090607110a0501050f030c160b07120c021204030f050a06060e180a0807120917160512030a0503040c05 68
    0x1c0c40c2c4440e0420350411000d18043c9a200e142107018242c140d485c500c0c9645807c0200b552000010001003030582819281901c1ea43c41750014000316102004440f00030225403415601e8018000241c0c0c403d00c24501d1100d00010300e40040142d000203005614580c1ea15100d43c42d0142020250200e24000100074101050f5030380c002030011103024500c0100c885000800b0b02115020075040b10741030103024010443d0030046c400c1100e40c0084e0b1000c2e40d545032918104020901800d1050040100022000304200690301c012603100d00312011100380300c2c0d0600264160f0b1505500501a04150300c10417041c00450401d41c01950300500c61011a01030140503150801103401a0300f100610508403814800820520a8400e00d0711a0240140c10004076690724881e80d845031003c001e0400d20310894880e22180100c141d080201400340700068000080c402c020740301c60b4180c011201140355860003044030704082071940c4140940100851520340b41c2c0c201960385810041c0100d6200800c3c003800b10300303030f29 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 833358381 1250 833357131 833357177
    0x40b0423090f0910020315011107080d0507080c03040b2701020705120c030a0302070302010906050f1e0c06431803050f0c0a270c020325020306010e0712020307 70
    0x101c2d100700c40551f14400c00180750600340c19006103a948070400c1030281c0301010034800c8a00c0c200303040450750340000c4d01d810007060090b203c402d50b0601004c0307000500c2c010740c0d6000301f00b00d40580311907152824262800e405001400039550f4010f0f48010004e000c1400c0190306a5005401c0c1d00840d02d5440499001070f02d015902181180140c111903000c00840d60000200d001a007440c2c2403140c00c02f00d983d900c41c03549020b44410b130300000c04803090000f040c4048004440c003c040302803d45146140a440b034803c1d0b000850b0350860440381042c241c212076109100e0141c0500d4401c04828044c50100307408442d00300c5a46030203c0810b510550001c0056410402903040c1068000606060413010b4200182900c29038005a800a07401003560b0f5031010784600c034540843e0038480000d4501010404a29500401c2109920052501d00c40c1ba0201c80c04a440e4400d5032007281200c540c0d0380c03983d801d000b0306030041d952900440e46100c2025010411500655400304240c505264411854240c11001c45 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 833359631 1250 833358381 833358391
    0x509010e1b040f41040f08040306090b010f0b07020105120603010b06030f070f050c030912121b0c01030902180403050d05010b0307020727020d060803040b0423090f09100203 76
    0x341065907209585006181801e4004c042001c0d01600055901500d011030030005200a201c0781c10000c41e40704100410003a200590f400880030440c03891b041c900114003140a000c0d40e0740c0941455070020301100c0071802c40303200ba6410303540d55040140303116012041c00000760140f6895520f400fa000c10f2521007078080c61048208080b000034904066401038014800200b104017002010070100160080000c12100010310507580c4448510145400c2c03814402031205030685400300003200d5190314180b00720102401c4400058910003404200190112240781c50002e400205000c0358000c03008071000703400d42c424000d045c113514040c05d9070182401c03902c0c00d8015041003800401408641ca504110b0071003c1d01034540000307103500130006c80c0752003c40d14011080d18160005894444481d640d0030000090013000101c03500c8544481c1d110300b95400078080d0b040042d010701d010300758140311072001d0f000c8564060070b408940d40f81d1101032110140001c08440c06403007117003811641c1c101c45100441c415 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 833360881 1250 833359631 833359661
    0xf040b0a0302091311010305011202012d0302040e090703020d0f0503070503030a09030e0a0e18100c030e060a1b0305040206070b04050106051002030c12250c090509010e1b040f 77
    0x3004c1c46291201c01070300c1480310b482c10513140c2001401031140301d0780d051040340d409003041c025160384403a0000301d8a8413034815003200c000001168240c9070301a0081e00c240d4201708a0024a542e80e00a00c550b034130110300c030280d0b0255031518a900401c80d0a95210041070054003603900e001c4d42500d4240c515442030350a203441a561b44c03480414140e0040403003200000480d03180c02210302d010007002201c0c1300942010505010007001d113500f50741c10001c0045c14a03c1038001d00246403640000744c001d01000040c000306026003400100d420190f880b0b400202c0c1d043c41c0364503095580c4120b0490042c04010000c9800142c00c101d1400482e040140d0144102d20030400410458140f9051201c1140014030210540d80240940e0b046018080340720805003002c1c030708040c1c40b060000e41c80c3d1043d0f0303503400480c52003d400d209a8024000407000e001305541844030184002c0d1160b00c0b42034200c603190503c03807010380c01800394900c0c0f81c0e0701e241500801890003007011a080b103203040400c04030340501002c0303021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 833362131 1250 833360881 833360911
    0x7170304030f0308240d022b0503040e0610090b18040e0a03030e0d021b0a0e09010e01061d060108150a23010f1e0302071a06031203060f040b0a030209 66
    0x700488240700d0b090b00102466040c2c3e03094545e100403d0b1020f0002c50005c0c4102d5842c286600003002482400c1040c503c0030481c0c2d0341000130f03410301c00c9d103d50003401014056800c102c00038030b50f0309018103214040a0580d41c0c040c000c41c82d2124901300e80d00710f80c075521902080d044103d129507485008000c0e1801d42007000d030403429014940941181e088242c00d0485412541c80305c03c200d5000700d6110380d01c08010310601d161500140c0060186142c5070402081d43d07400344d0920581c803a0540c0b100c004480c2403002000001d4580340070340c00d880c1d16107007150204601e010008400794820b003035041c0c2080f183d1181030701c4070841d640012444410354110a015110030a82044440d6482d00001407001007803d1085041480a200400340000d004000d84820b02c8105400010380c407940c1107030b03010354004101c01003d441d1454203000b840c409442c01880792181121610301d0f100d14004583c0144c2c0018000712151146905102c003400700340d12a1507109203036200001c05a1650200c8a100702107009090780 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 833363381 1250 833362131 833362141
    0xf0d0f050118051005010c08090418051c08010b031504060308221703070803040f1a0f070201052502011d03031e040b3d0501020706020f07170304030f0308 68
    0x2110f100510030348011043d044100501d0b40c100e030b0042c034030b03039000001e0740e50ba0400c50004c80c02400400c80c04010078038182413500c0c2886404030301000d0b482025034800d0810f0f5003008080b1945038081c090708441400c10404100c00b1045407500202c800805800071908030f59a480300d024503004052941e0a2469030713030b410290038280c808894040c0105182240d41c5540d0200c0c026524000c0c00380050400c2c0c00000400c05000940030307a2140c0f45d6200b0307041a01c00c0b03d44c4012006102055400c0e01341c610108008c650400e0060082501c01e10700c0303150f19201c0c0300d402c401d0601031500000c404c01c190355807000307100d28541c1610f401c071b4084140034000b1580c82c244078804c1181e504a17845015000c0c1c04007001d00c400980039482140c0c00150b10301e07402c00c120001040c1840e26501e134680ca00d8192516801407a20001c0f280360041c1259426020388280d1640c44005a841c0c070603502d00c605880e00001c0c011320038071202c0200d1031005580e100071681495120385d10950700c441e03100000d40c04105440c0c2005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 833364631 1250 833363381 833363429
    0x5010f06060507080d020c070e011e0501110d08070909060803030f06030703030c02010804060b040207033501030b0702070b0a090f0b04630506060f0d0f0501 69
    0x611080c40e090385000340f1901c40c844076000710f0101d00700d000d8000910420b050420004003001c3c02241c40801400c0d40d403482031040700d2000716801c1c81c0b2009030001c0010703107600030468070030040d4004c8050b284125a50703000711003e280003080c0e4020300940410110740c0d603066108440c0500030a1004660343d040007030000700c0144006040034030a03032009209000180d40300c1d528000060342802d2501041d141c40c5400c00140054084042e0401e00c0441d084007403503408802501c081c1d0260241da1000e80d83c141503410039074030154900000402040c01000000e41c6d101e0256400712a40c03042e1078206840e0140c04242d03a1000300170000040441105205e00d00742c0d2440d010080030350050240c5003900e0420000c050300c24144446590b8803402007054403481114065400c0c0455076413101e48040a070712003130052140b03542c1c2010300307849442110a0b0400c8062141c07070f0080303500401090826084043c038075007030fa20a54900302c00d1900c42d20751200b00b15070390140c1070113800801d0b1405581da075400210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 833365881 1250 833364631 833364641
    0x51603030f11040503120304121206051f08070e0d020111120c1509010603030906050904060e07170105100c150b03160303080a1103071d060d020c071409070c060902030a05010f 77
    0x201b511082003440000794041910741d0300d44546040c844c4810b6011400070b001801142c3c031940d0040489034410f9100c054201840c0340407525601e4055190702d480c0c80c101c42c8004894040d54000e40c04405076000f541c0501c0b8814044108002150034050f45100015070070f400008156104d50300c04140310303440d00d000054203544034514030020000d03146140c038001c042d01d01c588229400e10000081d8401310341c4640d000000540981c412b1180c00f0308100b140180506408466210300311781d840004203486c03524401c030112043c05540d031111100074680720108039941c0168a10003081ea5110750403045d40742400300f805c4c8509018a914151407960401600d8224004c00103a175103407504100440141c8218242d0b600f140345490001a1030395200029210030000259950b80000c01180c04401e04505030020140c044124003951422640d40441e28101007101130780d66803041c2e0010004907414441c0111003501030082c80045904c40c101d07000701307041614001e0151f0315651280d0380e1090340300440c050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 833367131 1250 833365881 833365903
    0x30301150305090303040f052505010f030603080909101a1c050403020a120c05100203011d040b06060f0702040203071815090b0705070510022b051603030f11040503 72
    0x140b000c0e15110314415107a1000410041006c00328041c448140682081044020507112000c43e807401d05058500080b004a880f42d07a0002c0d040552640201d4442d000e03440849030301407030040c00d000561040050840d001024107210940c02140001d00403c03010b40c0c4401500c40000c1c95689040c5103180c014110410400a40303140c2c2403c040c080040d50005200650380c1d00720f5046088500d061004440f150200301d006047c2d88220702680d0324080340e1794000c40c1264039030602d0b1060040b882945184c899401c0790007601e02780d800360008686003089002042080030b005590752422216500050481e00180c82e100c000a0340428450039407005039074044064a800400800e00c081d442a000b003822201d801001403122010624100f044000c11005010b08402840d01d01d4004101c0c0009640e0201003184108221815800c94400340d0701440103000b00025540e8a85001400980b42007050300c030060480801d6074070304a0440c0301c2d40d98800c0e41001508041110b50b107600c1e24013054a0700507241c40f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 833368381 1250 833367131 833367137
    0xc030b010b0f160512040e0f010801140c0705030d0501120312060b1b0c0a03151a01092d060c0203011a010c030c0f050706050d05071d06070f060e03030115 68
    0x4038101c0c03100c0c1c01809840d034461583c0c5501d0b440c0e88051400c03d0404841c425009581600410702281d1400d441102c01d1003004048031001d40e50b0b036150451402c0c0c0b001140034004408601d0003140141c0c2d00a4010180240142d0031613240084140361807080342c509070b00036400d900c4d505a60380109640171154542c41c203502c2c00180452801c00562028500c40c8020740781042c4209912182010414414140d40010040075080c0f495601e0400702013896441c1140310440d45080d20203001e4101250f191440d0100c103946200116042c032211200d021203150036800c01c070304042c003100d00094400e880c40d400380c101c5075501c0e40d0301c0321184140740c03c0d5084a00c04500103403070f441c100840c59901080c0303940190307010b00e0042c0c0d00c2d0f9900c0c20154814076029402500b107000d00341001c180b003908240213102400008504110301c0e500c4460881d244502a5488229119009080502494210082c1000324001e420b00c50281400d0b07511001202d42c10307100c2c46261f40010004020002c0c00d80440003500d91682 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 833369631 1250 833368381 833368387
    0x515250f15020a18140409020f0603011403100c08010e04050109050f1e01020304120305040f051005070905032e0f021c1b0e1e030f06061011060f07020a020307030c030b010b 76
    0x41c17942031900c3c6400800c0d50242d81d452548806541d118040c1000000010301141d99070350715502102c0301e00c020000d0b040e0103417003003c14050f5400d1040c404e038880d03221243c4d10385440340d0812040e0542c0c1003015106840543d00d40c805400400c8d401d02c02d0b002d1404c2918000c00c181c071008440704a00158003145503000e644180b041101048500c03144076407000c0c4600e00091265282d25184001001d660005019440b0342c16102642200a0f0701c4507000324500d03150540030540c1c034410107a13249030111070380034a401540c4000319124405180701001d0b104448000c0f036600500030021040b80c0050034840445002180c15840ea03900c10b100342129076404402c45070441c50040030203400c840421180d94002c8440c0342d41c10104415054411401130f1004003981c05030010f04401c26540d600c103a4155100f1482085a100050f006140b070004440900c0081d00d4640e0364114051540c850060111040d401084542c800580c1c0c01d100346030181d80b2580c23241000c00d055040c010aa07000507000011600703420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 833370881 1250 833369631 833369639
    0xc170604021206040902030a051501031a091b061912051f0303111009060b0a0906050d0b1305060106021b090c0415090515040515250f15020a18 63
    0x1d04890f5016030241c4020884406503c0030074038002e003260b0041d01c3d0380141a0107103000395803000007074100c038000c41030461600504281918040800d0318048429808215480c0500ca542c52103040c441c500100020b0816849040c10700d118003120359510000b5500f12044a01404584102a003098411500fa59007900d0520f623a40c00461130700014082c0702a81040302e4420000f0083c00c2981804148184a0714003070745013401c0a0500004c81070b20512801b40003190001c40344c0303e40c0040361401080c500032007d86460314010302c1c074040d000c1e0070721170405c254500208004010702d40c002c1c105c0341c4c01040d07041d00c00c07010b428040010045440c4215005024403841e1b148401c181c805076000c821800d005955440d50a80f0340320380c1030780808e410020b68103140c2d460322245030140044400c280c510b203412040186114020748030700e020070f5500c0381409004090030440d281c41080c200f03201d0314461000007000d4440c1901804d01c2006012041d070002445a201c951042c00180c070861720350515280f4a0034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 833372131 1250 833370881 833370907
    0x3120f09021c050604020112020d021317150c09040b030304030f0506010e040330060609080c0103020f2b1806060501080609071b020d080903150c0901030f09060c17060402 75
    0x185c4080c0c1081247c4104e0340c480d40341e40e81110130f8010b03840c000315900c282c08141c41c41d00345664401d802c50243d00310260a5500070220703540030502482d280c601100c0da2015030811040c0c0290088a800650b2847e6030348a6480400007000954021100e800713030503410f4580325240c0001600807143c01c20550061000007a04115040c0703408800e410840034580e0029212040b20310040c006200309420b145000909642021401084e5204041512040e0b51013100550a030311514074690b0403464104030080303050009002e0385c2c1d40449001c11a4200e40740c2c046042c0243c0d45960519550740c0410301c404810402e4912032180100401c1c202403c5501d007120005641c507000034422400d0064010b03007036200780c0c4c0658000703500550045c0b00050159050610101ca600140b185170700038490321540b25107035080a2910b901c243e05c000350fa02d00d051001c00044000d400b402028030100c0e42c8a0a540001510b203018101001c03e890381c0f05002003107030480c1c5546080024080b075001d0fa00c100700070803140e14 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 833373381 1250 833372131 833372143
    0xa0605040e070e0112021c03080612070b0304023606030c0d0201051b010e0a050709060801050c0a030c03020f03010b0706050a0c0c1407031a01170c0906040903120f09021c05 76
    0x2040ba0304a034440c41741d900225064203100060701c01603c403c1d202200405800251150150b03c05403241910312140400040c0d90304068050080c40c1c41d0240006001454046400d61003c246401d10400070b4a036020b40240d0741a4403211044089040c50400c101414100512209884110b4151003a194290006041d0740700b0901d00224011444003c03032046442500514842d441440071102540f010b0b040035602c81d86c40f80541d00380d96042000c00580c20780c0500680c0c5c080c405e607849040c40c01e44007a8050b001024450401801e0540074000304441542c508055402070031002155a5120001d2600c02c01f118001000e030201186400142070341d480d0721082041003264052403040805030720500f1130780f078545580c1c0014900c500848116007a0410343c20740504880300d0311039440c070081151106a80340c03031000e411145c00030060800141c0900d0302e0b40024544034004e00704106100c21503100304040d15a06000d031030186484807224011030514030601c41844d005203608075030304c01803a80c440381c80345 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 833374631 1250 833373381 833373389
    0x2030601090909050a050f100e0a0507050d050723010807080c04170703140a03140901050a030b041b051306170a05040212011a0a1d010b03070e090a0605040e070e01 72
    0x15540e00183c40820200308500b080090b00715040b10389481d1001c0c5250398800f1080e076054400350420382c080c170346010000352140c1c03155482405030075000d0614041c02601d08101c0d0f01901d03184255040040c04074100c090404500346415080c0423070411840002d000d8038409801c2c0e204202c402001c000302000d40000b45c43c00d0301c0722200201034168000122074079100c42e07a00007a00300d11035562400202c1000003440040f0758400d448102104505c1950303024039018a107812800710b039041059020040c440d52090b0340c4440000c5c40000c0c25410110020850202c0310030340c1c07011603000a00340114000c44070043c0018080e91803c11040307101c582c6000380c01d62000d05540c4100d51503d022070119900c100284000d500b4040003004490740a8828001c80444031342c1181c018000780360049156011212004015030344920b01032111b07460003800c1c14083d80010014801c0000d0f4008424543ea5030000141c001c002019000c14410b09240800044910f00b0860301e07030552050300c04004c034040080b0206c0c111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 833375881 1250 833374631 833374649
    0x409152c01150201021c060e0601020a080909131b081c09150c0b0a2c06060108060a081b0a140307060503070905060d14060f0f06030a0f0c050c100203060109 69
    0x6103150b0b400fa4068041c3d00c142204076070403003c5084030fa840c507a0081c012a41c03121000e401c283ca070000107a880707441713004028040510400c0a141c0905000a00c40c1e0004500c41d000150824a0707220200e901740483e06070301807206048810800300724200800c80d8a11040544001410700410b00a041e4179100e1043c0d0301c401c1c00500e4484a410b01a0b05c4409c01d05070495014142d070b14018000c1001002c0075505c11080346185448050b020038042102560303401c5c004020b10a0b41c4039503005440240c00204003030f0b44a8142180429002c0080c0040440345500112100401c07021204101994645401a03012001c0365070341c010255030002a01d1f411034005091030303a40c0e615044000c46069040341c1240e07402150001d2019190000b40c4d00c803101442800e00c3c9101d070754071070b0010020030220203010141e0101900030003001d240ba2031070046800268441000072603030401d103481d5054545880518000c520045103084140f1414401d004040c1c44400c2c046240d490440c7c00688100f550740940b20b01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 833377131 1250 833375881 833375909
    0x3020343201320040b190c0b0609060d080c033115050c0703030804110a05060a031d0a050c0907090b180d2f0904050d11030409152c01 59
    0x904103c0180543c0510401210541d40c0d54981d03442d51015845254409401920303008001452803084080040181d407062100c44162240c8042002104029001c40d9110205402c22400a1804401018038000b5072018585a035284400080c0c1300601a03002040302e41400000d40d5202c10594600741610409052000c07540d550040c100c80740d00614460f49184d20410350040281500590424480c6204d600303800416080d00c42072108240340d038840c07560000030034001803070100c1c026000503034040c03003400510b0b24090070070034002d25040300104260f6407500012910b20460810490440d40469281041409a843c0c00c003851198850b200b068842c10b103e9029a09042e500c82c43c2d51051242c0008003404a25188401a4010328403043ca028410641341100d009509020b41040d00c200d412001030640301041f000e003901c0f04005000440000d000c1000301050592603845086017000c42c518040e082107040c01d0412030f0380c0c4168622032903008844c0c06038840400c0019401419107101203d0042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 833378381 1250 833377131 833377151
    0x14270c0402071b0b030f130309061b0c030c0503010506100c0215280f0f020304030609111903050d03090f11030f030f07150603030203432013 62
    0x401c5030842c400205020f14503c4009041d4848102a5000c2c0c5076000140c4a19191076030079100b8403c0303413140200440c170190741c1001041e000e13400c002100c0343e44152400018142c0e0303642074050308054001700c41d143c3e0701000034001c0d42400d114180e4010b5042e074441d58450354411000d441d03c40c400341c1c003d01c40d02801c40348000042440c403c3c3c50101038809100d09100c0c504021250785500321408101c0050b012400320a07455205402410048442e81c002d140307403a0550300d0321005001001029502c2c80c0c15a980c4a04544562449520b805140780e8007420b51800e42c548a03051241c04480b00c010182041c0d1070318081802e40c0307004d8078480d03031003c1c8006d4100d01380d0005c281403940c0d80402c0c050074040801c0c08007891030081d005000142c0b00b000060ba0051480d0f80003401c54602c6d00015005074000d202030944443c030502e0020070341c03040884080415070518020781d490a4100190400d000f1a0480710041107a4140b80c2d43c2102c600003e90381d5030a1800b004a603a002210101e002042c2c0c46d211991 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 833379631 1250 833378381 833378393
    0x80901090302101d0307061d1507050601060215060907080a0905010213140301020f040b18100906080f0405031603031b1e0e030307060911030114270c040207 69
    0xe00030765010303203c0100088440c902074880a00c050380b40d000708018160390126031034081100000c4ea03a180e00e50030340d1010902e42e13106040441000898010b401041c4a01c1e44d0b5017130802602442e4407600c000d04007503040910007828201544030b001e81488000c000d04c40140d40c1c20300850b600015170700e0100ca00b543e07070812200141500440240855100042d1000040c5041d50007200380c844e945c91411503411000141401c0b131080801034440048140b105204119040e80101450807000c0051100300f0741140c001024460601141400300b0300004042180a8010402d80d40c008d2007079500e840b051030701b0f4590300d450f440b03115090250b082428088004050003944629070041000310b005c681002c0c55403010b49840c2007141c803002c040700842d46105403079101d100741440c1c00b580540070758200780907030b42c940c00900403015089500e400205000c5d55079490910808096480081c0981c50740c1c00c0ca10f00d0030280600c600d001d45102a246c8400025070240042c6000320b031032080e10700580c0c07540715082503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 833380881 1250 833379631 833379647
    0x70f14100e04020d1d070e06030715050d0e010605010906020a0c06080a060e0406021e0421033c020f03030f15061b19031e020309121005060307050d080901 68
    0x11803034546801740880006450040d144c0c80404007004a8080c5503c5850310307500040129110f0364964480c0d0350034049102143c040031b00020b854100702d418001041440015107610720340441050f03544040401c410341e8010220001461240043d000000d0140c5801d40d42c0c04040c014101403007007071804034007031071040ea0024000304000342e0540214201807034030502940c07101c200c805c00d42c12240840f10000c4c58203001c540456011070350700f595155050803c4001041e1465065041c400166291280300c800c0c0020584c1542d00132140c454014080941c4903001c1c04291588411075000303407131403003244100008503500b21500302c00d080b426076103e49681d245240707d00200c540100010408035a0601e00a900c080380d14410300c291000c08604504282141006410280009000d0101404809100d14401380740c1c6502e8415603141030070140120341e0259098198030038603030058504500300d0345103100e90b0350080c408030080d00840e0b1800c1c0000310400d00d01d080c054498034001401c001603070300645803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 833382131 1250 833380881 833380897
    0x21c021e030f0c060901110c0d140906040905040b091b0405060d050d020a0b090d1202071b0b0703120606082d040f140c0108180a050f070f14100e0402 66
    0x1c1c0a0380c1c3e07040d820005440b8602039a0340b40c201d60800c0142d600ca1482202542d09204e4618020500603c0e10881200c403202e40c070004003100e5008000140301503c035000100050848528041b6080c2042d1a00188540d40201080c545802104610001e40b40041c1300c0089a10200d40204a0752117642c0020ba01d42a0791000800c02d200701c14070030101a4002c10320740543c5004510043c0c45560b50203d180c0c41d8407e8a5070741c0000340255070031403d41500d640c003904009000c0d142000c48102c903009020f56102054106e00c076410303c00308140041560001d100310403a02000410f0005d6072401c1009008000003030311110740d9080440302421224000c0d030107100c0696010032091650b05081c00c00e120306120915040d90b04000c4081a102803aa00180c1d401400c20b041c0c6d01c60009665100d6502d0700c2400e05180e95980e8050660108042002040045c1c03406009801034170407980b0300041d65400700d0355503101e0007104488403034451f500d54400190a0081075142015007282c5602c0e00090001c0c840c0302d030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 833383381 1250 833382131 833382157
    0x1020309040e06010e0c07030c0f11040507030203150f0a0e0711030d022a070302040506060f0c0d0e010908070e070e031c0f03021305040c111b01021c021e03 69
    0x6060007190030001c1c506049540c51020380307005880b19050f1b118076100e0480060003040415807620005441600041c403401e003d144101e2160074048001401c0d143c05070b4501c030009070040280250150034048002c10304504582840b140e01c0b503040402c074249002d2050020403207101001444240c015030518403082262419a83d45407003911001c2c00070f4000c0307406140d0030002c0482e408408540d013805054888001e10080c4801461503003000080c06004010350381040043c4072403104101e0cc2c03c00341241d07164240141a280104e1000280803100c1c2c52485810041d56050400c45a200810300d0f07000c3e61003038006040710b0f90340c40c10242d41c00c00e034a201c00c58051141840b02131100031214402e0080d940c1c25504c4100d00c211400d812000c0c2d0280700e42d10b1030011040b40c810405071034250f001501c441c610307090a00da50780704e0301162030400c14140f0030403028044c0d4045105656a042c0301d40316205086c00e05200701c280306201d0080da03031841d5890000d41c1c0d08420b408000c0c8070320f0400c1074860002c400ca03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 833384631 1250 833383381 833383391
    0x801050618270703091209061b0303060503240c0f0304061a120d0f0f0e0d020301060509041a160c0b1e130c1406091504091b0806030a1e020102030904 66
    0x1a030004c0041807404025a14880d85840b00541680319945050441d00142c0e60840e161100740c0584584035004001141850fa5803400000e260301d00b4050800748003125030307200d07940300c1c840e05244404d0207009042044100f01041010806850081030b03c1c2c006800c200c00241c004504141343e50100c855000d220f80c046000013540e42c10100001d11050048826a299100070071028019100310714000f0354007000c03880d050002c00060405c1c00795440c071103000400105980e036458002c1100080180d8040c4c0e0310707501c085007800322810f1403006035420031020000d1058040c0700301401854070001c900000c288500c0035020401c46500e6001103009400005055415414100e00008000c4c003050000c0ba0410455140025810f101c40042060f01e00050b11282c40c1610310010813290b90304039900980085001d10012032130b0351040c841d880c440030010820014a071000a00500400002000745100382d02c1080030f01d00140640c03180e61aa40000e846245100c030311480140d0450060104440c0c000b4036003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 833385881 1250 833384631 833384641
    0x30a180f0b0705010c030e1c140301060305100803090d0b090a201314070c1b031a060607150b2701051f090e0c160f0201080105061827 59
    0x500402d40c55100310001c22601414041c264240e07021850f0400d0150010780700344489042014003112010400d20f007140c80243e040c00e03805100d402c20b80101c80000d940d0010007542c03110921018001d00700c40c0d03004604000c01040000ea0503c4444002060a450600414100802004803603d101c0d07115070382e10755100ca0b100709100342c4080e07140310500c10b0070040100810b1002510401c1c0800303150810340202c075a6800d0040d10300f0503020404544066151106101c280c840707000c440302443c0305000d0854442030248400e40315410140c45944203480c100714220008107503101c0c184020004900206203014030500107080d0420039100d200ca00558442101d10040c500c14030b003030507200112555240b0709a000742c4460b10f00c80e4400d030715020800f01042444504c4e088580181d11074481c4e28180d18000100a030812000b007081401c40b010400355a00004560308240e0540c013614007503c0d95410121084228912600b500c6441c03801030880c003202c400783c441c1b482802c004070704950f11404c85034109 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 833387131 1250 833385881 833385899
    0x120a0c031404110a050a0b0d090309083f0318010e07183204022707080f130209150603040f03121401092406030f1a03030a180f 56
    0x4052059440341004e11070114051404c1002441950315018400741032008614500f0f00500380c074501034040c400070703141c0080c40d9041000f6400703160000e01c002001c10141c5201d506100c1e106107000002e43c0e074a403400e0b010301070130050031ba9503c041101010f00511405c000b015004102560f03100f042c6004802010070007002401f007641450705031030020486c40112080c1c0a00c840100b0041c16000c0c0f003144c00110b401002e2035081e0381c02030300041268840030444002c1c0341d01428900c203881c802c894441b0800c42d01a410260840d40040d40380142c2d5000e1a080e1100750080d030010310000d207c1c803601404201b00a00c60303918110100d8025001990f681014140300036442c01241c000c42c002401d80c50483c40c1d4083c2030182c2c0c658401d4200380c0b4811642003212201c0608111034800d01021101c0390390041c8802002c0c7c1d10700c02060561030010b080002460700c0d509680210381c44065602501b1200d0b10035440010443d941c0240516082d501f901400105c811030354550b6001240e0049414000b060102c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 833388381 1250 833387131 833387153
    0xd08071a0108070f0b0408030403031101020408030307031b020d020d0c0501060506040609050901210210030912050415020307050d050901023901031e0f0207050109060e0f03120a0c031404 82
    0x50901c8103e180c0e903809035082c40344501d0080c41f006810902080002034080d11103146417a80050003d41055101c00c0c0c82c7e031854004580d040006a110804102d1000c15503540d04900c240fa0700c040d0010b4109104c02030350765600b07000ca02e010013003800d401206001d401e500ca2406414000d00c01640c4d2980c1d06001446084540102889040d2315400000d16035280201145003070340c24881c0180d001c42540030403900010b0601132105144e00c0d400702d100042c200d14100010141641c60b2a9225410300382c00e0a1240914441001594000c00400000c0743c000078055000c90004c1c94010780e901e00500040b4101042c4818441da074155104402900035814807023503101c0c546115076443d01500040044082d20001c007450b4121240460848014500b40d8120b5001071450301005468250b15a407003d0031200c2d000ba080d01c3d49a51805162810070302841400381c074450000003142098a4075815613800380780070f00009041580c03400f01c0c000450281d0002c0c02000d5403454006910300d401e0402c1c1000704 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 833389631 1250 833388381 833388389
    0x6040216051e032b0b0d062c0c10020118060203040b070e010e040e120403110901090902090106030506031606020c12011107020d081608180409020d08071a010807 71
    0x212895155499000401d03030b0300034188035645441c024a80c6030840007414509079541c04e025120010070140c1d44074410300c44c604a2049000150201e4000780f036641251044107101804540c8000014011034006101030207602c0459841031058070f040c10680c010451015840382001e2aa600c0384184292036000d10302c41d81c003821756940a5511030104803210200109820301165480c81d9014142c10305503c0a960f603c2140c0c1100d109201054400c01c0541043e03004544c842504c00c441e40c03290070103e5820380141083c0300244403000d000c0c0d001401ca0700c0140518030030123503104000b0700c040e50100003000740f4402d04180d20500030740f2400020f485144021106020f41b03400b20750025a608148070358160417400601d07040c10100a42c1c02c0014410306200d0540395854144585034411410302d180e440a01e12a010b403aa54400f212815080d181041191a1180703143c980c42c0f0300035854071240104115030048480d541d80025140c0380032003614840001025945031800803408907070000b4024103030303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 833390881 1250 833389631 833389663
    0x91c1a0403090603090206030c0d060e091605151903061829030d05090d1e050607090503060106032304050606010215101413050a0c03050117150604021605 68
    0x407640f61001036040d40d014400c02034000c1c10400c00606109050009015404040c00010880d281d84220030501c1c51025506c10f0b0f141d8100a6102001130800d8010388000c00060359100c0c803080b8030303418045a0340a0340300101281c10760910550310051103640241c0140c042d600000011060805540000300038860005410034698800900704040c6000580038421303000b0300400604440c64412075058210899403504070740004241c02c002444001000c0300401814034a219050302410000d28000c8081c246006105070360005001d66140824003d054802609010034018400d00c0c021071000d400c1200000c40c2c91000b0140020840c001c52003a0240d86e0903407c03115500258011408599010780c8c07418801169150104000c0180380ca00341281100100700b07141c03480a071000303041035030011200400308035503c0a0800100390144241405060217200003070018205040503540c455003864a803491810050000302c0558458040302c003c014010640990107841c3c1c54602c1c0d44000d030540340020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 833392131 1250 833390881 833390897
    0x305011e1a0907052109010c09061e081902120f01052e0207030b0a05090d0906172a040815070c08090301060306020a0e1008070203091c1a0403 63
    0x1d10305a08075000301c40040201800b10544034a01c00b541c03684d01c4103e0080c3d1110201c4070001400d0320550580d803040d80c4134070001c603414409800003000c10916400080500121034407100c9034810008104481040c2418804401d0315008035600d440401180107000803400013403035100c10700780300b11003134002c00c00003000580c50398851040040742170f81c22101c80c0400700140c41c411507282c0085420a80d80a881c01038502c400c8c2c40707481c1d504940000b142c9102c2e0f41d503190418000f04010812405480038114a0010301007810b107a4024000720400400030400c25a040214120b80e8488508400450112140e041d803003200403030f540510b0704103224800d0903014502641180d444940a15807150000b65148484440c00f585c6102080d0403c10030180c2642d6102c00110010700148001e00000f00d454681c1d0000410010421620700c021103640400c0020703a0301404125900041500c601c038904a1b1006007a03e6160300c0204c0701140700c1c4000d004980250348040080b030701080c071240210b019642d4141d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 833393381 1250 833392131 833392151
    0x10801020a080a021c09020609120f07050603040209151201020a0e0a0e011203140904020304061d070321050702060304081c0b090601030504030201020c1b01030e07140d03090305011e 80
    0x20480c085c0c102c540303603849032152841000d50b03020303030052000700e00c018111401c015030380020609041020030b04910540c058000424080070401a0034002d000c202c42c0e15146280c40e50101c1c09441c0b000e851608800da1021114495960b109051503401182c4002151500b5034028010001413240410740d01030421400d0100c0c0541d540016241a501403c401c0c00c00302e6201c1c0d804907200d5021046d04400d04009110000070b580d941c0c00250700880c041c91000c00c031340c0140d2401c152005072200d12140580d115090400018562424058003119a610602c072180d403151000e560603c91030304002d51000000040100700003d00028002d80750a000c1240650203080080e102140d055825680d8000404400a84258425040703182e00510a10000d410843c1c0c1c9100c0038680814000c015001c2685802c00500c40d50349480342044c0103c0460040c0003a61034000440505032a04080303e000704841c00c08241030500504420006682c420700030000f10502c881e000303102201100032100020b0903c02414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 833394631 1250 833393381 833393401
    0x170402042a03270209040215040807050f1206010e0702030909010b0d05010f0b0d1d0f1b030312010302061b0d051306050f0307120e0d0507020a0914160e0405010801020a08 75
    0x440c0c0541c10344203c500400f100c0d001c02003a000024003c03a48010140c18207200381241c2d0015000808100b801004c0160600040104c22000849081c2c0a800c0b0b0010280c0c21070000034405044441c150103000d56a00c88090880c01c4d0300c5590202d94000c03045000006d070440071840141481c0d52000d0742041966200d003152010702c04240300e03401c2410000e01170004002c4456000e18a40d5039012a04113403418182800341c1420044450441c168005242e41e250440c6240c0614101c94000c80196203048206820594081410b01020f4047c190108a0303207950100c0c0c020501710380310703150211940c110440034014a9035201e00f0118000d5066140c000503940d00690940c0c81c2180c1d82d80798a425075442120481d011070311014500349030f82d15103801c050411420b1121540c0c01c8a00d40e5250303030b91038a600610030141c00c40c1d07010050007403a224000c40c42a0070013120680000080e90880355411988000300c41c050f4000c4031056105207404c1c00007980d018151300a0007034121a403202411f690b0340090305 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 833395881 1250 833394631 833394671
    0x1b0c0806070807020312270105061519080a0914061605040f092f0a170115050307020309033c03090118080109110a0e010501170402042a03 61
    0xd14051703803017485800191050030884941c85050049610501c00503102e140384030003a0500000813a035540c1090114605100c05c079100d4120b4400c420525205580551042814955200b402000755102c003041054a050300412040758118400d821001110b22480307844d14025500140e01710328088495414600403400d441c103c0e0007400303050b41c60300c1c134014140d0082c0c2040c1c01c900224140130300e55807500b103d00705850a5000072444c0d02641b41c850b4400042d0400403180e508401c1901041c0c0104020513480b690405211038038a00603459881d01e00003a031545c0118402c4c2680740c0188818804001213410f1110300c008954480d002d08100001900410f03640103c2000130300c1c3d0410020b109155000b400c00d0326912040c00b0004064556800d02c442c00c441f401e07041140c11550f402c036402c00610b0024451005400c403131058800d0b0303514041c0082d04001016045ca100e05940100280c15540c0b103901601401c00352403c0307541d8a0301880024122600614002e0010900c0c03c044c2800780d110946003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 833397131 1250 833395881 833395891
    0x9031504110d050a0b0103060b1201060f060e18012903160806010512130201031b020d120e060415181e06020903030f0702040b0d030509101b0c08060708 67
    0x22841400324110140aa005400321050740d551080140d413600041d0200d00e002d000318010100050891003950030002d60b01000d444141642e81804814020200e100c5180b8003110b00c1030507e5042e800c49000850032910024044c0218800241d0000582d2942e0050f0421825110170f14031200103401c0c00e1100b100d00050720b0042080f00032102141000d03028260a64104105040403810031414070750158a40f40111541894003013184402011540c1500584110505010380419440f010f0100290390340d1a00700c2342c0c4200320402070243e2007000c4a6000521041c09841925030a25044c10401200858200c03018030241c03908042e02c180301200800c5d044281d502246e1448001a41a02e101e1140c00c03055058480d15030030480c0b1040383c2da0820082c00f5078210602441e45641c494010401100c041c4602c2d18010301030b00104e440000d6102c0125205c2c44030403244050243d80c0c1c0300084864003612011600700da41490249002c2c405480c0c88a0700300c480f034400301d070002d556030002110050f0060361 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 833398381 1250 833397131 833397143
    0x30204060f08240310230106090803030c070317070206151906031a0d0c15021203190905060c04050916020a03051806120405010f0b030322030212010209031504 70
    0x4201d1a0f003d1401020030a044004044410955589001d10112181c85a0314012214161100d409048402c25030900514075401d003081c3d0586401011500d0303200003031111a000a00149600c101401004540300005071465101800d2914010107542e4200c00d813140381000d80c0010342406140b130521994006403800190304180c1038604034050b4090b01080422250b40d80d41d03481e9607102e0381c41e0001c42045003402100312080c25460801302d403100c040b03910454800c54120381a541c091106c413104483e0462528000103442c0c031043c0c2425002001c0000c0010514050b200130f1043ca000070078080c0c000e907841121001c4064031401c124005514404003000096005142c4003800310b401540a40300e9503003070301c40780e512203098040000d020341d020015461401d02144280018400248941c1803540c4641108105081180c0006962400f825501d0524010305041c2028880b010410000c001c56018001f040b4403145640140c0c080e4020382c00c102d02921488420280780711080030440c3c0501d0f0400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 833399631 1250 833398381 833398411
    0xe0105091c031a0d0f210903030c08070c090501090c110604020607050a0f03020102030412030b0904020402031b0309071d070801030209040c1d01030204051b03010e1015030204060f08 80
    0x10030180d001e0b0188094884110781000c07104030158483d40c0740c0c51902c40c8149000441700010f89805900b103020f11103480700340d2481c030104091140e00140141b050341c0d0581401090040d46161030806e40c402c90714002c00d00c44403200005841c180700e400443c103883e507034a01840b041110306c5017115010490820502241d000303802060150800000a01655000d4420f84000075100d0311a20bd074480750040c1200141c2d400070400041c0000c0e41030b5440e01c0402c81c6004e114034140c1c0c8001500c030b00030103403010388959400004161110020840e044080e10180343d41500c9180401c6c00640300c00c5036108114500c5120040ea013002148a0155840b610141d1900360303080c1d00316028800b41ca00024000c07660210340c1140810040c01450410308030440030190302c1c6841d0b0440c414003056880240c0750300c0120380718120f950b4051b80c2c0764058a041d00c0459403040b490b903441c140011207440403907200c11030b40810300240904003036140c2c00602c01d031000c0f030301c0e12905030244000445100c10101d0b81c40241140c02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 833400881 1250 833399631 833399683
    0x9050118050f0607170a030501140f040506130e0319090506041203090b0319200739060306060804110904020310050108030703030e03131a0d050a0e010509 68
    0x40340082e5090000d02040d08000840c1c1c3c030100740780c0b80040320f102840000315012480c191f0500a460240010b1005101ca0a504002003070240203c0e4900d00e219984410000303c072611407003031600a103101500c1c18040f4103132140140341c4a40c0720685002c04491010310748a44a030140400d80304440010348410306e401d00d0035144420420124100300c04104c000c040014140d08880041c0d40504043e440524048545e506504d0840380c0c0000d41c203070904509407000d40d03030000369030580b820b01707800000309010841028107030361a41b10030703d40c0041e0f401403050740300b80c0c8402d004207880300307594460710b00f0800152101350546240c0e02c100c0303004080f802c600d04d00c606642030540358203800c5803000d0211001c16144664010560303100b40c0100d05603610100d441c0e018140d050084200d0f46102c44040c614040e0042d80c403a1a0002500903c1c4100311034401e4070410407070740011038020007a000e01c10022405d180050402918512900c00100e41c00d210208014220100e0700261601d2551300211101c691 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 833402131 1250 833400881 833400889
    0x30a080705030c06480c0f10020306011d06030a02180907031e050c250b0c03160e101d0a0308070c0b1e0f1c09030905011805 55
    0x5004881c0380c0014001c0903070040041040714000d2940030303040d415004000713800c84890f04881c40d1883d004009240084404602414004034190000b46410703920803103c1c0c1168540025004000042d01c0703020300d031045080803907000e1030154000341e03240702800043d400481d140d01c0c0c180392050f40c030a004002080551070281e0003004060350201e41110000540c0f40004c8294900715400d03070100e0f03201c40c1e42e0035050300745442211501c1c2074030004109a04204139200002d005108040c2140440d801842c101040300c00038403404950f000c0c46a018034034240c5100040c3d6041642c1c019000c407000c0c1f000074901800385000000201000e440c42d07003508203085085449a171560760750260003103050340d00d4000792100381c42c42c03015600404405c1e94400c0d42c1e141140b01090b060384103040e91a001d1002c003000d0007440e40b2031002c1e0385030100c0090312070440198220070762080c42800c6010b600e403240c0c0c06002142c9508083c2d001d6000e031311261450340d624401900c50b01101e2040c030441411190342030240d464 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 833403381 1250 833402131 833402137
    0x1416050307030e01050f0405160e04020d020411040f090b0618010c11100203040311040b060d0f1d0d020708010e030915161406090705010e1c020405071d040b030a08 72
    0x400ca1401041c1e0384100700c078050850f170043d44c03480e0b001d603050700c100424800100711811b040d80f441800b24006500c0c200301da1940c3c100241000b445054604a0942036550b2500701c00c489030030700070600341d4503550313008100201e00aa10828003040d041050660041c941041a502048540041d180e8101c408100454012039400012103540c0741c4102e80c410700e41c889070785c1190740c1c4946400440e80e031425070920056000040050030300c00d5044c000c41d06c066440d03680c00c2ea02418504000880c05220007422400a0403500c410107400f1202d00760011a55040004e01642c856503c0e020317100c419444203078050980d03404e9074034a0380307643c400c0100038264100003c5d07000d50085081c00780d9040c04907200061402c40700f03d000c02c0d54030b960316602c00d10b00d1142c01e10040ea04041c05000420fa45485c1c08006816a2407442107035208240380c48641401680420000007010340c000c00401c80c84c0340941015051181c01140200ca480c40c820303048110b0b080c144a010500800100140b000800c650344902d1640c2c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 833404631 1250 833403381 833403391
    0x180201031e1e1b09030f060605030a03030b12150c2803020403120e01020a031b1b06030b0105130b0304050f07060309021002031c0218060301080106050414160503 71
    0x48003040c0800c0d40000c510500c400342040b070800c0c2915078085514075003035036241e480d5403a18003484400c183c0b2041d00312210b8001c596100080c40b07444421800c0800c000c01030b60384619090b0040c2d141800c1059410345c0f0400d6003603800c9a40007a00313501007409036690301c040890110400010004a1102c038001ca010b4101d20201c02aa200c9280184401c280500203008240c004260081014010000030321040d00c1541c3c00c61400542007514400001e5584920704000707010304c03440714030317038580440b504c140516a1030704003207050005403e0320401450041a40314820009182a1510070b9640c4181d00700c6010307040700510711091a00740000d041080c0e00c003400407034080c4200b0024000c0c0c14400d00c900c0c8000d00150b10000384100c0680184049552020303240e900710342007004219440707001101c164041e0301c01100c006884003484180580b00300c075030312a10380e8426004400007c025005420820541e00300365030074000303c44080800441210b0684e000e040811800060880451164029517440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 833405881 1250 833404631 833404661
    0x1506090f0312030a0b0d0b070e0109080a03090f0902340b181b0102060f04081b0102130b0415140d02071109060102030301080a0305070501091407170118020103 70
    0x400007926041011070000e00340c0e000030080080040e40762144504810301030756045aa11381984c1c9141803500e00910880922400003500c0c02d25034800c000171800380c49940c003140c81d078008a05000d802c2c0006485108140420700501151000860003611582240c0c030001d01c114145e40140b000c9281e403030360500316040000c1c40700000071440341c0300e246000d000001000428994043d4041d424041e500b0300420210b030310318101d04042d907070002e00154851425000c00c9182d0b200da2030440f510344a1652804c1100c510005001e50310304066004019014890051280095889038011503138022031245106800080d80c9503100b5070700406100c030b503e1311010225403903c9895502d10341280c010103c1500e11054544220103e820f00303150645d00400e09000850856240402155945145540c01001c0290100792601040f00075040f40d040541d000ca1521241e454078103205903a64458405e241c00750300e004140e03601403001031103a9603440107080421000c486040c0c00540c0a0710108d0140d40308 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 833407131 1250 833405881 833405899
    0x90501030e15180c0603010513020705101505090f010321031b08010503011811040207112106070305040c330306060e06090904030e010512011509080105150609 70
    0x1595400c29180c0d03114900d191007040c10f5160310304049180441c0806124040c1e40200014880c9907601501c0c000c4010744540d0240e9501074170b140560a24503014200304109003006520140d8940c2c0700e883d50142c070000d8070303840d4807650780d6880c12401c44401c0c40f0107401c00c08100c82d403210084510040b00403000013420f001c03440002002c1e4241044080c4c21060f03000038803200040c0418074080c0070b00b42040c0001c94200d41011807648803000300320b09a10b104d91140d64001502c000f085040142c0740462100142401c6e080d00c1c03440641d000c200d54600074807205014420004001718080e20440d40107541150202c05050f0410450000c1161080100303480031072408040d611110100c00c86800c0581d480c0c4c0c0100d1110318154021708141d20002080e440303003034280084d030000d0300c0b42c480341c990140d010704e0403a00c8909200d0050316184a5a0394101101000c1400400c1d44105d6100e034000f90011a92094000c950395542242220030582c0d0504079035070340c0c030545000ea150101c0a098200c1c002800c040e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 833408381 1250 833407131 833407153
    0x420040209282117070c06030f110c0d02010c110a021009170d020705030727020405090907150801122a06021e0a02061c06030618120906090501030e 65
    0x204201800300c8511281140929a10030001e240d0650140704c1c03d00c2892a0a115482c2c0d03c404c201d00d00c40c0030300005c02d55254004080c50889070000c6680e012014003040d60780009210007505e4140901600c4c01560030080c1c81d94001d48100e418205406ca9400502208030f02c607401c11582c400b06c003210501f00706100601207139240924021504414a08004106400d16120083c0c2003c0180d0300c0241f10380c10101003084095140440b038400541c0700398402002c4203003113585000a01603504909c1d0403846c0342d030400c00324240000d016002d85119801c500d40242585c1c000703c0b2041c44c01d001741d01c0301c02c0c0d4501508000654000706180030f40c4d0101c1d1100c0078950b844603078103040103065100c440182d220742801c0b255420203104c8024544210806410102da054022881d94421803107c0005083d40d2001040040d80320340c4008007450b1701c101c09204080b200d00c2540901015241e0a5429811481d000181507002d09150340403500e142d16803004484c5030000540050000c0c510301200e83c000c1700000c007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 833409631 1250 833408381 833408399
    0xc0516060f0f1a0111060105010504031115310b1204050a02091e0f041205030a0b060a0807120510050402090a0801050106021c0305100923042004020928 67
    0x280150050468101c1d03802142800181100b003904040017030b54000794010710559034464100c500340d035005041c0b100b9000c1c120000ca4070084000c6a210351244001c00d20004003090300c5280c00869035265a00c0080d01c0d19010501c030500710030320500150590070008400b540007090355030b90348240104181c4100c010b4503008201010300441c3c901301000034642c285880170048150240c1c0100d00d00a0807412451f045c0c0d68012620004405031041c0718010001030300050713280e04605410b02b0040c2c407882e00d840f5110340140580c80e050310340c507001c920f403565880b03080643c034460b203440b4500300013541490701e10f44001c1c0b00003544034608890b00030b80b90150100c0c00013000d011300343c001c0596a00034088120901c0300c64804450007640c8000305401d02c024405034136045440c22054601101000848100f031b900d403d1038480d240709100c2308032442501000b06100e228800e8040d04a49100e9242400008008010407481101419640800210900394000100d44030808003099240d42c140790090700c482e862 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 833410881 1250 833409631 833409641
    0xb0a0303082206050118021303020108040816150612242307020c18010311040618060f0911040b031e040605151203092413090c0516060f0f 61
    0x243c1d0455184d900400c44118107000034020010030440440c00d26902c51a0b554910310381d848064100b00620300840d05000111b401c0f14000b4004040001c10f46c2c04c14604440c0450780e44a00c4640546445d200107803250346011942140c9500c50040006c645003003030024101003030804030f4140665922034030001502488040020402d010a4048091400300380c02407030091465425030085044030070000d2041451044581500c0d88104c1c4c0b03204449180001c1401464198025500f00600c0c0358458900ca8155000310706032161450800c0209403a00c00b05020f03075542c100c0e1485840300c1000b0800000c0000000f540d0440126415946040310150140210708c006540035102143e50301e040c012a80c10503800f2004116043d039050052101030b0403455144e00495030074500541c1c3c1c220702400d0112441459071520040c07003915644400002d8211a0110f010740074800e44140b40503070050500b80110261001440007180110303000c001982d881001d001007540c1d012495444038101800c40d8030034012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 833412131 1250 833410881 833410883
    0x2003100f33050406030f110303090d0605070e01020f0712060b04020c2a060a110c10021509150117010906091514070f0c021c05011e0b0a03030822 64
    0x81c074084031030340002904441c6016400244900e10b071403c10000a05512024004590000d4030a0a200710107004282036100d0b12640503441040d06113184100403c03136003d1801030070359640e41d07200350301c40000581e0746141d1040070030f60652081d40d04003c002c0d4410b500660304c1d4450a00030400c0d02d03421001c034060b80c100d6684820b15810250310401083c60160201400101052298004c8042e0700c0125000d8450504014200880b064102c05500300030001c1c4008000007408098003001e12034002501c035070041709100d48002c00140891284940000d4900c11060315844500180c0d00c1d00d000074403a2074820780642299500c5d0121840450990300c100321269000d450203401000f04a00b14604450303403000c40c000d50250603130030f01800551017401500002d00720b003015000200e0354000640f21003208400412018400d505075020480c043d01b0850410219060203414031070037101800940700d142448540050030036008001080c41010140d0f04101c08054007a00912044580c4612081c580d40c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 833413381 1250 833412131 833412191
    0xc060d020309061003020a0501050306011107080c0f0910050909100e0a0c0b0a14090312180102060108240411040903031a01020a0b0a0203100b030907032003100f 71
    0x40040310300d010310903c1c1d03101d2620300045070441e0560f400aa001c1956028050400070003000003501a4000d2900c0d000310ba402d48111001c01d580c4469440e030782d0100ea40c180d40540e15400103514682041d030480d80c095459004484042c6007442c1c207224024000a0115216104400368501004241d10417140b00d5000b00c006486403c00a04210300c4000300e59000368901c00040000e0382900c0c0c0d010440301d100e0001d0500706030b6120040c000081c6001e4186011116203035000404480c0c0a650400e60080d1b03002c2a025290180e9842d50b2013500d6842800c9402440c03040850709e40099111602611b5101d0302c5412224280f034514004241226046c010850100750707500700300750308000c0414010031110b100344000c22000f40c3c6961981c80c40c410140c100300041c1e4020000c601d05081159400c1c002c0c00065010f2601e07031a1045446075a00e8141c413003942d40d201c50302d0b85040d0316541c2c22104001d03448061700601030807100902200c0240840c6100300380751565071048407040d1740c41c43c02e0850001100304d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 833414631 1250 833413381 833413387
    0xb0d23160809100507090803040e0604060506040513020306010912080a081f090e030c0105040305120907030b04030e0109050a08010c020f0604050d080c07061103041a0408090d050c060d02 82
    0xd105030031a0048840c0c50140711120702007150344000061141d5000740e0412000c00c8640300c0c484156441d0580380c000349010300010802041842800310010b124010448046c4680e070340c3c0b03c0902185102e1809050303080380d00079885511300300c1c0c01c0d0001c540100040c5041e0b14519650f00e904070754096240300480b8810b000080c4403080507070050b00315800c43ca10001c003a80c4030209200a21030600c20f4454488466221800341440300414415220f03581400340090040340380c140707030081241c6e201c00703501c01f0f030064400042680298001605020303203900c15203101943d11076480590b80c1c0d03000300b0314a60400030380010101b07492703d45034603c400034003201001080140e0322080203030a01050005440c80c1e41d001030f0401000c681c0008007550300100741e0074146115103e10312140c102e841030000c007070140b9080c481c44c903048007403039002103106d1801600040b0341c0444558090200150588000e4840d010a0040c21809d16204507041551031051045582d0000482c0100d01e15800c4048c0300d0002076804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 833415881 1250 833414631 833414641
    0x501090b030c0405091e01020717030103050d020118020906130e0606040c0201093504060c1e0b180a060e01060f0506121f080102181005130b0d23 64
    0x40040c2e841c250002c680602151034504035955940001c405441c0150034804540f04010100f94125618942c1001c030085003c141140d0740d65803544288822100703841610349612a840c4107214041d0003244c00440128050441d03005c1100f190000380001b0381c002c2a0f403460109010181c49003110307401c4020058100307031800400308000c85116008110a590421100c0000199002ca002c446000c541085903401d00c19040f08224485038003820b65103401c0005070120300300e50130820350074800d44911624550080748c1c41c0d0f00c4c00d810340c0162009003103815203000704a910201e00e61100c1000b180d40100d5040b40401d03200c80301039448000d112840e69651b01d40c14488c043d10351504401404060b10f41703618080c01210f01c0c16240200411600e4000c58400041d215100390030040c00041214000a41d22503810f081004800d40303000c02c0040c45242582040400b40740118169000002c0480b00b2041041c40c22024408a40c8040c4404600554881c1c98500c11200081e21981d940040b690b4a90b0354505 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 833417131 1250 833415881 833415883
    0x408040e071220070f0606031a1f270e01020403030504080c0907050307030911060a1701050103060f0303030e03130810140c16020d0204020a110610082107060501090b03 74
    0x400d000041000690501401036007a01c04c8501040e401a41d5611344181e0741018801080e04e500300428188100e04200c1055000380a00d900642d4000810360541000051b1120079514901c00c141003041440b005110741000a41034001c46009180c0216142e101100c5040c00c90740684c000704c010031b50100d0140540d10b4104003005951501380c9101580d030500e045e000e4460700004054004041e1180c070b52404200010085080b6160081e00081d200d088ec440c010305800c00508140d030f080c141c044000582036200f0301a0604642e0b0107850040001d007151011000742500d8505081c3ca8841000103d0072021045030b40d40040c80041d0152003241c009040e9001500c16031600c8080880300e0f0f04c103002c0405807140490f0807030302046802001c024040e00c04034048260031400a58801c8c408140310303074a00d40101c256a08424100f0a031510359407a1400400d40c0031b400c0c01103805640c000403c00c08003074040a2000c0725010340e140801d007455095600d08064481c01d030800c80009484100c1c6802c1414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 833418381 1250 833417131 833417141
    0x106080f071a18030d12200f0a090e070c0c1a040b0901030b030a060209012a03210e01020909011409040201140903030d05041202070f050402030408040e0712 69
    0x1001030050701146103000080c26509540d450b200500300c50019040d0344280040c00c0010a1800141c280d54110f20b100201078420302c1400c0158083d50f04100c0c0760080c0d62030700700d070801058880741307806820319003094035001d02a00120202c030280072101202164100002e0401c2e403003900e21f03990703403140b6886c00d142c02c4a03141d0495001c0120001480100c4000030850816502920000c605503500c0e4000f40f00104d01038404489259098041c54507040b0a12a1a8004103845c910a0300d40801640075114154080c000180c0344030001d100a00d40040068400e0400b4400030389888a40300c0c44070707243c902c5002110300c0c500b540030081e90b0001c2c040c91385080182400f401442c0740507200040c2c0c540ca401203200040000c00003810072002c050417030a00d600ca401038949440016046035107030a40e10b0303078403c0240010303101030310705031090916807002c03620024462054860b008480c4a07140d181a003484040c0d00050400c403403528040c4004100800c40818680c86070040b6682c1c2501c8038801c3c1c1480c0121b1b2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 833419631 1250 833418381 833418403
    0x90803100f0f09020a21051b121303021507080405010c08040201120c09091109040b0f01050a0f020c0603070512070915080c04120f15050f060d03180602010608 70
    0x1201d00300400182480103642c60449254a00242e42c5e44004402111546900c3c04000410b40d101400c05074010301940c0b02c540b240b085261203201c000800030b14880c09008140c0358200c4034090300002210b140b2902d1400c4880c0d403090044405460321220f09200786403084881070000b40c0030a0070007080c4942400380d1082188141022100d0b0f0426800007801c2002c0d121340d80d1a100d846000b075144540c40340f030340c400080c54000020840c54803c0d403015540303580000b00c0e80e44600d0a000d071514075868070704810490000305842e000e15210380c0950503a40c292040e0048815800b034103a070811151901001140708120981e5044d0355512100c1c0c05d08005200034201e80c040101c400c0c0c052000d0313258000c41d40340b0302403142011905507031101d1410755184503682106c0018888211110100803801c0291031029221b082400d104003030481d4840e04481c000c40b6907007047c08010000c200a81440f15419850364020714100c3c001300cac0d1410144180010304d61010005039904d6600300a1a40188040160b907 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 833420881 1250 833419631 833419649
    0x90618030f030a2607052a030a020f2808070605040b0a1d280c030302060907090506100e04020c060106020f190b0c090105070b040b010501030e0d08040318030609080310 74
    0x14003900c8901604102c8000d0002c002c0c402c1c009487d444601030b4400000700c8003e42c1150600300100310805e151a0f40000ca95a00984204000c9140041c03011990714480780b0f10440342c0003a0140f2140011640e5511801510760786402c01141010031114007071030384654081c004686403810000f61400440d01104101410241074180c0658504400300310b600151544a032a00502c50600d036004410b031b0a10341e8020800411050000101a00420014858114a0142d1b08801e6649288405a42c0c040b02c80c241c1c4400746d48600343d05280101c16541d21070102400050900b8101d140385480d000c4281c012034051307030000f83c441144103020810000d0a002c43c03c6200510f540c03a981d02e4040010207804200d800b0808a018205644075000340c81d500ca0300410b10302001c0c02d0500346800f40b05828010303640001d0a0074801c61103050002445090301d8455550f08000e80d640f5101214144d24032041c107052203004041c000080b40903070041d410024007800b48a640c03401c0000c1c240003690540d5001c4444 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 833422131 1250 833420881 833420927
    0x40c0b0c0618070b04150305161209061d071505071e0f05061f120312050a0209030703051015030308010b091906020105070e03070b090618030f030a 65
    0xa000010400c1c94000e0a030341c201c441e84103681d02042d4140390f41908a0035581c038000c80c002a4445e014188044039800c1a2010042501c4140800c1c602526140200e0301082c00c0070003110030301c03403260702100c0c240340948d00004103105102c14151207403100329490700d400e030701c0f401051058050100782110300c04400d040c15890842c0990380c459405450700d030381591000d0f2209401c401d20089070902c0310629402000c1e01c0951400c2c2c1c4184030307048400c1c1800d0ba41000c0c000300102d03003408030900c10440e064140e241c8040c0d120140c0094005444010304808615800b0320050255403800c01914010354400d038060454601a80078a100300d80300984d1801076406010020404641c01100c075506444d00c4203055603440c900b03503000c45d00c1080c4200c5030100d40c90351100005215641076011030700641d80c41d602e03d955084c0480800d640d803102409201c1c40030800304400341107840c0c243e00406030110a40400c9105455950000c0e0034641281c2c1510f04c039400000c1c1c2c140e4042c1c2c0c024581304c0c031400021005a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 833423381 1250 833422131 833422147
    0x90619020f0705011713050a030c05011803091e03020406090c02012003060d0f050a1a0f0f07050d090501020c150a060f03020f0d021009090f0e0d030b01050c01090b040c0b 75
    0x4441d4046050f0b064001c401003001c506c0d80ca01c00c0c803119944540180446100f0079140c50024882c242e950010b43d40795103400502c1c04080c0c00c801e05121000d07010341d60b980d003150030107450341c003a407480d840303064141e031084600000107031154080c0e400109411080000c0da8018076501a0940e4142094081d8810403240604401c0d03403140162500300e001a16603203200412803a149049129154005e4010301c0b44509803010464000d456a002400303a030303103280c2030344c55040e0203609903903003a1941340701c10641000140007a0321440203050390070322209020582c006191111822640300d408a48141d410460614809003150b01c001d81c3c21004c07189040010f18900a48040881894040213100344188580030202d40c1e110124903414940041030341d40c3c05400590050300c254007d102d140d801904003031800317550300340600c10070514050580c0a011920444c540c110001c1040b00d00702410b0110900014071290424840c141c00b051041e095141107061074107145c0d80244950340109a00801000101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 833424631 1250 833423381 833423387
    0x1512010e012d05070c06020d150602010903020d0f0c0c14010305100b0a0c1515050102011b0215071e09080705151209030904020d05060907032a0203090619020f070501 73
    0x100c40b5608015000600b501c2d0711a04845810792a0301c0507280c035001054181c0c001d0050783c000e0140344020b10866940c0c0713581b00c805a003a01c11760b0801802582207501202541d038045c044032a82007002d46041e80844149a94101705020b00d43c21501401420300d0900e001c40d601445410740003154907603121205481c10700b0319216403044065020401c0350101c01360003040201c01003c602c01c140c0d4401171044140c0031230440d400021078130139540150b0909170381c07050040900c4c4c6601554a2545c3c05013248505078102200324190140c0500308008060101079092a00301d04022040d40141c0d84092191349000240d07443c240c12a04280d110750b4010030369505519910045502444003507000740c105a4a8084030350071406041180c03178100f80005868604550a940b1003403081504031464459900d41d56070450840b000c4802c000c80c1202622100104100c3c3d50001d45200002407040300d2800c44603c1c04070f44180c01c130f42005000c040300c00605c0d01002e9014050044009600c03401003c200f85408002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 833425881 1250 833424631 833424701
    0x904080315060d0c02060403090504050c0423031603030f0503010e150f06040801060501120903051605010b100806041a150a09050414100f08151512010e01 68
    0x282544910000c10850b02c424050790b0725480b02e071004109110410780c0103521410101d5048001800360311000c00c1034902413040c180900030080c0c800341401d0910102e0380c0f02e132080b010b0070902100c20340e001c1181c9660030802d040c0044440b18042d0560b525524000c1c1a00c0b030f04031540710038400180300500101e5024290954003070001040c1d26641025900840c504030503ca81944c0c002400080c00700301001d054015904407402a40c1d110260500106280100c43c45104014005201040402408001800c0e90202c850048000080342402d0000180d80500c200d00035101140c001c1c030820403039280500c80c2d40b07000007411824800300e101c40c40000b2044984c0000c40e00e1100702c045028603072103105500c80005884007400070014001e8140f9400c180078812034201c84010442e90300802e89416240c0070200702e403080001044400030f8010200500f8000a01c0070301d45c900d407030081491680c2c41402d0014441200c13000010100d100c010107500707449420140c0651802c0300000300715100810845 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 833427131 1250 833425881 833425891
    0x4170601060512060d030c150506012d05090a080a1109070f091a040b16050c0a030c0509040f0f0b0901050709140603150d1a01050f061b030d181109040803 68
    0x2054138020007506e004d4661620015010785941c0c140c0808140444566114a0040c00240c03101e5141c0200341c04c88080b10110004595517035020000c4000e20580070b0340c0034104240004118414181d115111189003070078000c0b007a509451021099802d5052148056400400514150300b07009500d5002a00c4074125125200d454403c6c43e541d0024004050284e402030000e41c0c111541c2e8140120243d086c3e52100c18098a41e0b0207451402103051403c90502006c8030380c0a031060440d20310341410840201c10040050f2072000d5260b003c200055000291101001e01c00c0b2495603446c14803c03005421103000401c04010b20500410074441e00f041c200310740c0142a0201c41c004d0f82ca42d10140008001c40c0c04250490700718030500d54030401c108601d0409008810320414455035aa86ca078104149c8134501e10344a9000070040001c204605025030801d61500005411a413801304503060751012100078071015a06401001c44c0001044850b404d5109906403c0f54175542509064075280030320320012744 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 833428381 1250 833427131 833427139
    0x603020a0b1815160c0e0105040203101205010f060602010c0801051e0405040c050414070305091b061e0d150906030302031903060e100e1315020d0902060417060106051206 75
    0x19400488181401c21291200b40c8502000180c029924200c034651846008101b559594a40007042509245c82540e01c00c6a42c16142d00d07400380b900c0111192280e50160999280d5211500580350080900451000740f07801c1c1d00020781c12482035001006017070180c210301e109542c0c0d00f1182088030b40c5840b20360b010b01821200080c240d150b914003a1100745140d880203400904006600c0d526003481a412885520944c07070600c603e41d2002038003925000f041d02c20201c503560f400c00554403400c00c0c1c80030344075940c0210448403101e80402c0e6428080e42040036105d007480c2c1c4410301148150070181c0031400514161005101c544e0450360080c0d128055a1904061585510b03204032800e4801d400a50041402038441c107100c0c01c081a030a4080981405904820480e540c04540c81001000740c099983da005141c82102048035110040a907100141c1c8012160300c4040c1000941d40e0040240014001410004c4e612038a0b1002d030790030440141d000344140202400f0094001301003190305a4881c008a0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 833429631 1250 833428381 833428399
    0x330906011803021309030f020105012102030f060a0e070902041a07230321060a090507050903070906030507150504050f060d0f0905071401020a120516060603020a0b18 73
    0x4044003958021a8030103507004502e030440804280d155170211407554001e554031060402041c0c0d05900780d507030a20074005072414211106410b60040b0341c00242d1139100609595448194070700350741c40c005054913011491540c6070304503c1d003c0d20402c9000d000b02481102542031a251004030340003d0000b29500e0100540052190100207072000009082d0807007110060b901604410f81caa03582c0c1040b01404003401d140202c0c01203c404555200307200e482e0081655609504101c0800040c08000d42840d041c00020300c101c43c0303181d40034031841d0050582000001010351940c00c003249000c400f84d100c1030f45031034129500d00540b5030060454060701c0c000d0750410b00d0000c840c400700b0382070f100700381c0c40310103262030801d0600010145401c2b07060040d004200b210324681d201e860501c89070b51042101c0f40035902c4030382410001002003103101603001c22801d0503400c101c00d01848603420811b030107049903180d0b43d8a6040c0b085140808000000e840031080807400c02c10a240030244a82041c0c80700ea1190110b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 833430881 1250 833429631 833429657
    0x31c0e061e0304051011030f041407090e160b030112111f17010504020a0e0904020d02090403050307030c09030305160c1e030b0f06030a031110020333090601 69
    0xc080203204036007900140e8034501030614076103941408034000c006a060294648500100700b0641c0c1c0a0902c56943e180c031910350350381c0e01200d400d600420886502400200140130721485c070495000004100c050105026001015400e400864120341410b00080c0f0040c40000d05a802c030107403103640a40f001d090707181620006880c2c16210540c0d0a000c042660020156a45c0100d0a40b281e4818921074015039803680c0802c0164001c500f50100000c4032030111030450f1516880c4070303400900192074404800c1054000c120b03c85012142a4003180002040c0031040350305114a1078042d5462502091440c190781d40204203214511782d0382c0400c04241014801d000004450380020080d00103040c448050b14103190102580b244416104660703020300240f590310a0b4688180300da500203010f08250110740e1384c155506000c0204811103881744901203003071200c051000f50700900300c040e002c5010042140341c6420100304100144074141c00900b00000e20b032a4a10361941007842400d000c0700d0f016132 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 833432131 1250 833430881 833430907
    0x21513140f12180306040b1b13030506091006060c030f3e0102030c07080f0415030f0b010219110d06060b071b03050601050906041d0705031c0e06 64
    0x104003001c5400d400b03000c000742e805401d4000200b081100340c102a00741c3c04102810152260b50854000d4a845c2d003581c0011440f100400141c00e000b050001541e0800000d00b610342242e804903003088841d98019070a22460f030f40c0422013452140d044110510555050140050500000308401814088840d040b402c0c524040c0c151200740381900a25416900b6210048081c0192103102c0d02064841c44860840e4508060003120721580c074462810b494400956140f1040e035100c0074480c10030480a00c00482d841040c4140000717800c8142c0c0c0c000c02c00100326500c03801100e40c0c0310011415540300480d1080c1c143c542090703e000c09038100d000d07000a1505130f000320303c2c03043d0f944100402c424a070641c0170504041103c040e250303407405aa0040f21031140594902c080c08110702003d41185d211100411403482e100c081c01d9800749000d800030076101c40301414103581a03d149a00c03205600000c0d000e0100e804c1c02c0000d501d00c0160301c6d100c54040080f26802400b40044030100714020b09000070b442c034174054 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 833433381 1250 833432131 833432143
    0xc07091508190c09180c08030f040b0c010b0306070302030a06120b0403030903030b100302071109010819020616050a0b0a05060627030303010e0712090c06180e100602151314 76
    0x41c5499003485400b690178000040840190b0048441c90304a6001041010000003038030310b00c1b800303406110703c0d2508003c11004c0c00c1e04082c001d40107543d201c1c4603210203500e09000c510702031081518096228207204560f81e00f519515009900c0d18541c8602a00120b00c40c1c400c032a0300942c26090004154090341001c130040c04440201e1074000c008845025403041d07150f8001c0040d90b00410241d000e41c2d0030341040220ba401c003031040003050b52015076800c14502c8010680e0101a100030180b43c0380050401e512401c1041c0c0d50402d071110b42004074000300b4010000141c40d40101c0e08a42001a85811400240c0a002d041d40301241c034840781850302031212070404084010480141161788969407101d00f0762903140e049a05c840000c410b0070a03640688003d00440d00074941c8524400b0b0074a0401c60200c03040301d81c2000c03c4125441032980029502e668000c10ba0042000c6452100721605180b4041c0c5040000c55943c06520f055008000c054200d01c4c000e0f10000e80d2100104564003054001145080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 833434631 1250 833433381 833433389
    0x12040b0a14090d090504060602060402121f02091903020a090207083f0106020a03052508090312040506400311040e100c05040b0c07091508190c 63
    0x201d0342000d000c2468030020b40340144038200d550708500b10f80c8503c1448180c4680f84590009680041c0114005141840014651510943c00c80d003a040c8a058600300b00162204c0c0312440a6002559100e2070a00300c0d0400403c0d90810f01c5503146c1d52941d4041400d00c00385101d8100142e601180006c100100402112040e800c240807074140000d5a1035141f0f14020501020b081c3c02d0506002102d4080303081ca0014101c2d1240e4001e0140010b458505485c0e590098452003807030184e000601704514418a21608024040c1403c0d40d241c0d8241018140761900d102c0d04698200c0b010300c4100603580e80c6000701c0e6581e901204078020f02c40903051464041500304107544a501a50340c00030041c800031803070182c080307a000b00c80ca041c1400b014401e000c21141c5000d0300c01032036044240b400e10304112a800840780b0a00500d081440d00f5914001c00e840740d0000da1b020304039500212802c0000c070007203009111342000c107060f21170052440c22139441d035282a0b042c800144d10b0001a034000a0295142d5454024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 833435881 1250 833434631 833434661
    0xd0e04152301020607020d0c020f030a0309030501060b09030715030b091302041413020f130213080705033013090506030d020607021207060609110703030605040212040b0a 75
    0x415126200c82248920307425121425018440e009200741d03200140d118050b0385582c0240003100c03401030301215252008030341660400245516100c843e2001c01c80e00c80050b00030350729818503509528200d400c0d59090303440701c1e0300284140481d80351541c0c045100b8088030000e10705601d010310a644144d0192250000c21613201c100c1e0b000b08005032007901401070890344200c404001078900483c4010040c1000d031104220008180740e820014103052008181e070800c0100458170864207480520140d904c4401c207090b0f5001c0e16801004045003c0001c0c10160400720003901c120ba03249010f0307000004483d81001c0000307005102e10440341503001c1c11034840801c00701a120210340c0300d10907400505829600c4900078412500c2010019102103008c2c0d0268620b0b9004c3c101310800e001100e03550f60003038441036840350b50740d410000350701d540c038411448002c00e803174001c948840c52410060308481c403662006020302d0041111881c2c003c0d01502c06036100b41d00864180340e544130703040c00c0300007810840f4100d200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 833437131 1250 833435881 833435921
    0x10b0409080706050606040e0c0304030212130f050d03020d050d0e0709020a0f08090601260604210302070b0a05040302011e151e06270e0103030306090e0d0e04 70
    0x3800701032030040c9032090054009004507101d80041c80190b20541c4580c1f04d000c2c46010100310304032103d100654005010b0b01c111904500d010002d9003040d4404041c503044010801740401808445c56440c0c001050102c030302500000f49920007940740d1040d00000340403c500080e840d414041a80e201514150a61046410582c0c0340c00120b002588610b0511020494600030011114420444d5901c0780c06c01c180905407613482d080c4c01c29100c0d0946c0200c209503c40500c84032030400703401c011492140780140b001504d03003e0170b28095218001000240400c050040060401040c9a40e135481d402001510000509565905049004080000201c00c07125402e6035183e000fa00960883c04200b0b500280c1e000403503542e045201c60f102d50040f161000100c03404002c1000038001e5440c00342000e070400d01c0c100b00210004c2c1030080f0060641104694048000040c41030581c0340c8600c002905944000b08895040c0c1110180d42e400b000c0100070810120a40f2550b00741c85542203608605000c24000351 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 833438381 1250 833437131 833437133
    0x209090a1b0906080d0c06050705071a10061b030c0f140606090c1e0f0405090103150513051f27021f050304060f0b06070f1b05130e010b0409 62
    0x142140705803090754086410b00d880403030f02e503a000c900c50107584019102c21003c200c0c01e80c0d0b0180030341402000201401030034402600424004809201c031b80030315207809010b500c0c0884c2d03001511000c9401c50350402c40103000c140c26641100f441d03201d1003605420b180454288901e040383c4113501c00e4100601030221040786807542000018014025101100d031a152a0f5580c20b1002c15400345250f191030010209082e840c1e141201001440c03100171229940d450151200c0200d0000d0308281d0088921001513082c4820702c01d0280f14058201d0301c0f401c810380389540e054445941ea01c05c40281e80c4800703080d18114082e00d80c250703402072460300226596142c002d034240041c81b500c0240f00304140e010f0b0b9030105804118415407960494040a9134503600c1c1152200d0304d98000514401d8840301d0360707503980d0085444503a900c9019000f154800e03074910b00518101c0c508450300c0e0207002424595044c0d00310b402e0219507070307110a080441d0003154000a0b9800796040d554054a0100c109903001460003805030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 833439631 1250 833438381 833438423
    0x1204050c060c101d03070b0a09050307120f1412090f060703060e06030a0308010611030c03033d0b0901020703021002030403030f1701060528110c04050c070209090a 72
    0x60400d80410042150403004e440d1400440305803084035a00340c0081000e00d0000740e140c035080d40c11641d0702c07800103181f10055603800e19690046005480301050464500c4005610002c455589010383c6000f00c4100010400502140505226501c20485180000740c1261042020010308d03440001240d03100d040c00c1c10054010300040c007a0010400702103000550a0900041150003982c1c036540e241d119030310b080d030120303400341c80050010024003082181405044040014601030304d441003a4000100c84002c015860183d034502c0c00780c8074180c6100302a82515501c030300f47c00321007034526007a640f0700d090f0004074103048850708000c1d8007108192080c440c0c44d900001030030070759200c1d440300586c1201ca00d50035252002c102c07600c0c1714613128220043c4400d83c80340028002c03146e4010884079240d103034100f640c06401502c00301d600008145601c01e17010b40008112541c91140306a8080103030b414511140c00c1c40e80701305400a4003031103a0b0000304020ba6000c0100c0095580c11010590012034010607071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 833440881 1250 833439631 833439643
    0xb04020415030b15030c21070e010305031801020d02100c0c0503030a0f11041202060a11100905330903040e07020307020102010b0f030a121b050705040f111204050c060c 74
    0x90281d00b990700b46601303542c100094000c54424000300000c010300442075505918102000b02c07c4030b03030b01070380c08005128200322a81d41e02843c4107030091034550015030b00e1440c9204400a1440c115400050720300412a004a82035040d5001e420000c21103581030481502c0d42d0181c0000141540300c000108420810540d0040106a400c0842480385080030701824002c2d00440c02044115000103480364010315000c0c0082035203011030f007003903600c644002c4000d5092665541c0c0c80d03488161502203072010008140101410100398900c150300c40301d045886990444006800a038040c0e00f04808640060720800c00d44000b084c4001e4484007610304540020749a40040200300d001d9800e0040c0d0540925250594041c036540244c0104580a840d482d55640d410419802c80c0506c00307880300b10300142030000b1007103202900800044c0184c916210038041282e4108000c1c81c03195180103600c2e102d8082ca50100c609440c8100702c4e00b810f80d11141003a03400c004030601090303480800069000a035220114071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 833442131 1250 833440881 833440891
    0x150412120519080103110402040803040e13020402040e0912130b0f16080a110a0b070302130504060602160b0c0a1b0b0403150c03060b0306060c0114010801150602010908070b04020415030b 82
    0x794500d0282c042c400c0c1f105a000314001c1c1c14250f0002d020a209000c49000316a502ca2000c0244c842114100d40106081380c0c040d03084082e580324641c0c05c1041e26003040042c81020501c7c02001440c200040d1031840c0c0b4001c0c603008116250000103002124101510162049500400442c600e02001850300d40c0d09a8000c01c04180881c0a6005160700c44030049410120150491011451561000401c6000794486103a070342e04042074110200342c945a9101c0d042c00b07045036400601400c0400d40a800d50b80c509a88403410024040200118680002c52a0030440b0343c032100302c49503084950340344000200140c200d5002d2480c04580003090250015541f802c0c1407114a00b085a80510320040301902c0310740c01407000d602030800200d1030500b020340081428104840000600c0780c103621081071510300a9101c480030340e441d18402c4503609581b01081008080303e000070000401e0680d6a0380c0d2902810344041c0894400b9030000d410344d100c2c0e80003940c0a290161401160740d0b100d1500680d1204c0541d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 833443381 1250 833442131 833442143
    0x10f02100e1e030c03070303022b0c030b0d051b0a090c0509101b0201050d0e1207030f110a03030507051204050706081003080414121b150412120519080103 68
    0x4580810080b0200441c4d90300300d4010091450400c10780c8003a0081d601c2103441941c00d411040c0791703070000b0207140b595000d402082007010444000610000741070b1400f04038440c1c410000c210140c0002800025080100768002c14040001d100c054000b52a90902d60300080342141088551080203500c20000c21003000200c0701400280d946000845401e0035800c00f90408070700c41c4004502540c0210b0103003806440d805004034103605000701141c00d003000b941e840c2c20080e03004105807007055040780d00600c01b0240d9117014144151001865680e0b400d51404c080c05040c1d40302d0210b03400600c100211840010403c21816041c1841d10380607950380d0301d92241c10f001a48010101d80c40306102d0300e10400300c076002a41542020b0501e44402c484990512205030301c024540d00024a03154140802d8140c80c207884001d50559081c401402601c0891480c281010359041005010403002003641d02d40e080d802500082e440c4840e20000d40d40c5225000040003005110518901415840808641030300d1280c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 833444631 1250 833443381 833443423
    0x30d030c1205090303190b06070303060302040e0d210b12030a0909050c0d15030605010e0f130b1f170f011401120f0507050607081801020f0705010f02100e 68
    0x248014120342c8240c030951000e0f041000800c801c01d5030280d549124600030680042c114184c1d0001403904d0b400010b040300031030348400c070801c19407034a0310500102c500d000c00508242a000e103001001d80302e010703e185414000c0900e800070500b0065101d891304601c0134000300c20b80000460400e82d242c00c422640d4000400f12840030034400698040d46005014200d070660400000c8400c038400741c0344c0001034003e40a1a1140000030610030f00516009010034581c14040b410207040d5560840001080c01c000001403101d900001a420801150300410148d500d04881140c50724054045195a00090441d010740381740c09030030740012640c00c4441d00707914000c00484c0c1c000400c0b98202c2d00244103484801e182061000e0110b9441800f100144d8840d60503900441e441e079000940a4004078404d0f40c805901192082103076240642071146908240010002d40380d00710701a40d51000380380107017810480b00d841c2c10200c03035000700f142514205070850b09100c0c10060074082139460340072802c10017142c0210 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 833445881 1250 833444631 833444657
    0x712081f03031b0203031e0703120b03100207020d020907120c020f06011509230f0f0915010e040906090b0705040f060813020301090506070801210f060b030d030c 71
    0x403244404981c2e050701e550910000000c01e890503c5190710b004d0307030103000400c529201c1ea4002d6030400190381c4000c1007552106201d040043c00180c548100c2003171145840034020580e500040c9544034901228400b5a41300c141d0b01c00b00300100f159010003504a0071b544d0600850700d03080500c1a11850808204001015889900b01c1e5280c80211041180c3d0b0030840050007414a0b04d182e180501c0f1690a1a1207110b565064103004226400044950034985044030b011500c0c02864000d6048001c5903c0c05801041c0e400190042c3c40242107440912030aa410721047c2e4050002004942002031081108041a00b800e2000d41180c3e9001c90b40c0455410005560134040d4096400795400c000d4030511081c10402c040d01d510310042d100c83da43c41410144200107a03401d02030401401c0c403c401400e16810000c0c00602201d0f8181c200311110f410040104103c0440c00e00c122090940114410002903d02e0a2440040101440307558150003188604801103405800c292051031669850019503408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 833447131 1250 833445881 833445931
    0x60501060e060702060d09110d140d0302091c062c01060b0c1002030402030712032c130f0f021908060907090509040312050106030608010b04020906071205071208 71
    0x8003a0001c5d800700702800700030703c030f0304107a8420315001d8420001c5500d1011000d00003010751011080485080180a041ca8100314007070241a00013001e504040d03040140751b000154900d4035075000301031000102940b10050041c40e4200d0456243c4a0059a081c4640d200c8089000c142c5a00302c10203a40c24071600040d424914001c527600001000044c0a5009009000b407001c0e520250080e40e2602c501c50002c6a02810702c00701083c0b0601c2500d9034202000c000c00d0343e45440802094009d481e0003860b4080340940c40711260032907030700004100040c4c12042654044000d0805020801c181c80c40450700d556442101c030b6103c0b1000440f9203076540c1d25070f00d0340c00b084500361044030b084001804800081265003041006280c000d03119003000103026101510070000ca402c02d920100010f42c0321602082245400c0c450540d03141c03010785e070a602c3c1c00400004210244501a001046000512100180e0301c2c4508152802075900c8403a03140101500007005101c41d400307903940d40124a001c2515085194 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 833448381 1250 833447131 833447137
    0x9010318030507150e07060c02091e010b0a0924021005041110030b1206160503091c0521010e0705090d030e01030f0204080d02191109070c060207060501060e06 70
    0x140c5655042e2038503e455444903504900c00300b0224103130ba00c950b40c19040c50028031244002d03117450380d40d0030408101ea00420508290103400340d220450001d000d620b20100b00180341d410354011400060b0f079140d420f041120074032101e6000c0c11785410120700702e10b29503220032001e80b004880da82c2164466062503c005080381c9068400800f0a025050714a055042200c0109540c0285042c00074002225002190070500350101241003500140104105d6107a40780b000b4044861600d070150451074070301a001e80d242d0b4600381a440300c074000d81341d1700000c07803007034049883c0c0202c075145450414030651038045d01803400b8081c0d920100b002800284181d442002910501c81e402441000044220f49081d2140e4071424411410140c44400c02180260079000074030050005038010240c007601c4020081c1400704c040e12003c1c455640b4402c120101e20510142141507108075101249501c40308810340381c4511881c0f0090600740041000000e21644c1d6002d641252403546848840c3d606800400c0201c0c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 833449631 1250 833448381 833448383
    0x3110f0403020f040204030206130f0812070602090319121d01170604021b060a050901020a08070e010c0b0c03191b03020306060706090c1404050f072d030209010318 72
    0x26000d0100300054540040f0840c6002c002900040c0f9154480c0c022600303e030b000b10540b002058605008000e46d2210344140f00c000c01c0c00c10094210480e603199100324920801001809498004c90414103c0e5020701140150000740c01c01501d43c400b0500c1c200404669001d0820081103040fa40d003c04072126244c00b181a038016943d01440a4100d400c6110031040900744903005a42805091450310143d0000345130b201202d4010001480c100c8401801c0e10f60040c458041640148403c1e421582c01c80002e607000491400c1c540c0e000c4c440103004860b8050710442c081c000c5135491301805004d24940005501408203204000c003032424000002043e5000c924040c594407807900906008244643c0c040d50f00541c000b4455854811561100c10580303a20000c01c0d40c910001a00c10070886085115950724140107035028099450700b41075090418400034210424040b90040310f9901c0c035010046440600f04019054502c2050b100008000750445001507020900e000701c4500348c079859000c01c901d02c3e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 833450881 1250 833449631 833449657
    0xe07060c110a0b040303030e070512070e1f03120522030317010501120f18060b090a0e10090302150a051005061312030513080c1c0b2d090304060311 65
    0x240c45d42e0380443c01800c40c840400c00c1d50042681c003144551303664071064440d9810350001d20b8000c0c00c09841c0d0400d950007800c1e400c0340710b296000809900240925840440e508001002c105007900201520544652580c2900c1c24001903e4154800c10307042f69a0300b52030003592a0b612420102e442c448018030280109070104d050540c5180b01119660844001c003072050002254a8000c5102c81d4500b20044204036060303070b01c601d0080003504245000c40c1c6d018a90303c0090003c6501020a151074500300f5a80240176034a5a0544050500030041c4a010300c0f242c0505d80010714082440318010017040c2d03031a01a030040070034006020f1800c030080d920103c1c6102500402c2618080c0141c0c444000d004049090280c180401c1054104540040005020312009004101e82d01c81c108442c5001210315244000005601d00002c501c0161101da80210a03a1108000307402059002e0380206281d91107681d4014420100b012040b00400034004640303564900344030001903208403481c13a004080c659056 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 833452131 1250 833450881 833450887
    0x1c0504050c06030901060305120a180b0919030b0a0c3506190308181012050c0c0d0e18040b19020d0212070f0e0310020d0e07060c110a0b 60
    0x42407400b20300454000ca411800061450b5a995039142001044251407040c00000b103030f038504464100e1030f01502c0c80c203580f078503003102c605000c1ea0558a000c0c50402a000310845040c00e5004201d1080520145412201460a0346440c690300406050410a08000980a8211700700e1001d01c2118040b48049030350780d9003011440100410b000484028441c0d58059a9000381104442280c4032601c05580509840350365a00700c05440b080403800300b004a802140320110004480e0750180f2140c0c0004001c0101107035503110541c16031383c640a10203c00c5203c0c02080c6a081c169034008440c1e11640500383c071803c450301d000181041c0e00c51070444003d001c0d04c0b102c40000c0e03a490700581e409070000c0803400c401410b00130700000801c2260000340c980741a150740d44040c400203a030032186000007110b81c1c1c0f0342001442c840c080802d403103e0400d8030500d1030640208140303c46130803980140415a10110850303645079a5114000d04083c250141a0f8640c404016000c9241c1000241342050360144c40403a85 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 833453237 1106 833452131 833452153
    0x1115070b090a1a0a09050d05130518010521070f05010809060903040504020705070b0304030302040303110703050a021c0b100f08061b0a050403171c050405 68
    0x25203540306118010002e003d0780895038503550340b07601c00a640c1e120070304130801070910f900c4010b03c14003816403040c21080d400b9024110a240c03941405591a640c1c030248020341303040c01c8103003600b0f0b9443c100500c940d0030b149880380701503d8402e410a04580345078900380c0c14a00f50b41c10001c8500a59903042010303691000c89980c22a8916002d01003c0c00e000701c45a569209901c901e0340180c2d0082140011302000b40140001008080e2213150f49140c1032400034001e5005001c21000b00b001100002c609050000d070308800d07130790300c8402070420100e15002c0114042155000c5618071441c80030030400544035080c828000c03100803004001b41e500b00390303403800820a0b40d0060350300d982c00310003004003041c0b030140e880541c11440c6003400d41d1010084402c0b20140725540004d00046000303140c181c03011100000400640701d14440b4a88184020014001030783c006580c045c2c00c660101c42005 = true := by decide +kernel

theorem cover : BRFrame.Cov 833273381 833453237 := by
  have h0 := BRFrame.cov_init 833273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 833273381 ≤ n) (h2 : n < 833453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
