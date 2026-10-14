-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0081
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:44:00.745378+00:00
-- url     : https://prove2.me/submissions/6e79a4ae-8167-41b3-b9d2-bab501e5bd1a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 14388496 ≤ n < 14568352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 14389746 1250 14388496 14388503
    0x16060504050106090612030f020105011505180a0f17190f1106030f0703050702070305030a050d0212040501020403020a17101109090a06080705010e030a020103020306060706020708090108060418 85
    0x9a6000c00e091180941000003d8111003a08104070b550310007009000c0c0582440450108590a448580b55401881514101e0b0141040480003041a400c1180c0c00d41c07000b07ca80110f640a8040401c064440c940788030003900000013070201480c20301c0003104e01c07074002903d1401503604c0200111680d48214407003950315030f4000140440c01c0d4040c0340509001c0041c130181038004102000f003040c503942c940d00c000d000d46550b443c2009a82c6400d00201d0715406c4502001d0f01b107600802550026030f21600c0106818a0343c0880103007001030707140800d80c03010390070781e0305035200d81d000b080034010341c501098010020f1014249a02c0c44100c1c1784021500c0d480c0140b040e04034a40e440481082c0c034072040c0100c5444640041c880b1240d4601010081c00420306405030800900ca0f1180105131035006160409a0000040003052502040d81c01100a544010034403a084101071044c84002813050001d050f1b910300c05c2c21520b0700c40c0c0c01c400c001402c00600400642c811820074000409070040c40305a0464541c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 14390996 1250 14389746 14389751
    0x50402130902070303020a080105040b0901030803091002030c0903060c04030c0504021803030d0501061112040311010903020a14030111070f0f03030e0a0f140706051902070306050403050d111606 85
    0x29800a402904081a40024103082c000501041019416801070030600d42940710300e585640ca900c02e200440752440941c82d0040704840040c4003080140c0c024560010000d002c0341c00590070640c41400340e802c20759004440c100c1c041603050151800784425640420004425030510745191241301d142c01491244901031a8009030550308642180c0c0c146c141d0910103001c682e50b80302d0348158400241740034802c3d440001d240326070360b0211110118074002c1013511008075a00309070440c3c40d480d003102d444501640c14818200707c0000182c030b0301c0c0c0040c030050048019100f907410104c4107150035610846040c400c0075000700004800250040004540d00e5041000304aa103c00f51409500900d90100004201e2180e402c031300007000213a4032a000007174422000c0c3c80400c0100c102099a58005000c0c81c40030503000c3c80300558820b00d032581d40a070792995104891036650740e500c80e0421a003080d501500082c200140740b55040c4d02c540211520000440350f01490000300e156142450108640014001038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 14392246 1250 14390996 14391007
    0x30907150201022106040c0207080a0303050a0b030708100b0609010f030b010c140304080c030c090610020a060207060c020d0c0c060f050c0105010e0103020102160608150d0c060203090406080c0a050402 88
    0x1071003507050302d504030f00744910322a00c1d14580d40b0205012070700f141c3d101c0c0300e1414041480d10662002c1602411a0010300060500040640e03003500030302001042901040ea542c3c0c0d01040680c2c0812000c0000c00896015161403006058442e065a036844500c1e4010b0200b0440c030401030740d0048043c079402c085454000340d24a03000700125210404d0010280441100607013400440f071001c8001c2045400c2c03002180e2000c0c5440007810740b01c40031000280d501000910000320340c1e0510030020160000c1603c195400c1b0354132541c1e01402c98203c0042560415640d030202034906404008a100551050a0510008c4003d6586401c028414041c440030042c1c0003008040e030074007920603a0070201840d0001d001d41c1d80c503044c01c1c106105091000340d0042c40b401ca440c80c0180c0d03607110514240d5502d136451442c1c568070b903108800c81d00910074040b82c10480c0040b0000102e01102040030203462107078003440d9182b8400301044203440d800c0d0040406500502a48400b903030311000c1403400c503182500c0250315036 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 14393496 1250 14392246 14392289
    0xc03050d02030c090306100602101e09020303071505060f010c0b010b0a0e27010f0e04020409030e060d052a0d0e1608030702040609020f0304150b0a0303020f010501080102030907 78
    0x180104c1079125003500c100c1c003c3c010341000181e90301d070030b45035039600b1980410100080c0e80262500c2140c84041442d580010802d560090381144035003078009401c49141915076503d0204c101884003848103140d540b2401e214480ca051030800f114013009281c002c460051300d88842c03004250612030388035012400200840458040c00110510081c020000c51200281c501a80c0c04c9100c5180000c0e00ca2000c44008101c2e101d020020300e00f5a124509003004136610b660902c00241041c1038160103215101800e08030039901c6c840203040340032030200003044a080c800c040320406e00b80150705025040040c0c020445406030081550b8a1039a803a8010a6484c070035819141007280c2004105a00c064a404c04504c2c840b0000041000324409d95007008191398404800c8124064681c5440b070b030890400208020801c4210840e011441440c400a0040005000600d40344900d03803049002d40c00c11207001d4000c500a2040e2401401060020352030b501e4180100341d141d4031036009800310039a0380600320707050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 14394746 1250 14393496 14393521
    0x204030218060324040b1305100e0304090e0d020706020c0607110609100206011514030a09060e010501090b01080c09030606010c0507030510020c1006050f0d020d05010609020a0f0c03050d0203 84
    0x80865000021800342c00311070380000805404c172070035148803070b80c0700202e15004810340f04044130f103030407502138503504841c43d4843c0041c0081451101c0c241c482444080341d40003241c4208041d0a001c5d40080800c00d0742104080e0618045a001005641260003c0d40150310350300103d80b00b041d4883c0d0f10300da0103c0060001421030082d150b405410400040d0307102c2c042c07138001034a50305881034264220308241600d141161342120104440001400504c045544803510382c120345182ea129441c046010b100c0120418211482684503422540d107450189071917580184d074258010940181c01880c02803c2c0010079a10280608068100541c0341245010b220f410300408001c0c0d43d100d000d4825409075110b40002a4005803d4241e1230b018413410b5a1280080d40310700011690040c080c1c8061450000400450004840c02aa000003004030741e0790000b2000c1c4038a0001e880b02c4400180c807248107410052442060000c000f051040301042103020035081030a544055140b00c002680c0c1e9911034040001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 14395996 1250 14394746 14394763
    0x2010603080705070617161b020301090308070905010809030403030e01200601030201170702060a0216050a0f0309050303030106050301090507030b31021204020d08070b01060804021302040302180603 87
    0x20789980403509604015011407400e04403041d9640c2c0752440800540c03e220944004d50b4030346c40c0312134402c0244100c60b002d001d40c025a44092210b006600d00103801003825244103010841c006952082080340f2141c02168003400b9240c00e181c864514500704191554074802c41c0005001d11801c1103c0b8031960f07100741e4104203c12060004540205401300c0c10642e9036800b80002c074041860315802c0020030b50f48a0042e4800d03021035008110544440c816038009520403044905901800f4841d100414002c0080500d014460481e00c10807440a040080c000c0040343c0200c0c0c400c0e00208010000745030b2101c01d5906607942400001115126840150004c15490a59540049500760300e184404000c1e101c5815500001c2000800d01d40c0640c036900481c4503001040520700203100104000d4205109102c802d80d1040d03a02c03500d80285e9444112840d2402d03840840041c3d0500e00300300460402c1c40b28a5680403d40100b50308160a41d4002668480068480555600000c1c000b40d5169810040e042e03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 14397246 1250 14395996 14396003
    0xa0203090f0621060a0506090612040305090a03140f01020403020303030a0b040204050405010b07060c0e010f0e04060f0e01030611040b040302011d13020c01050f060a0e09030d051302040506150d090302010603 91
    0x18403d1103c0380c5800c00072103007250594428004c802c0001002c0c1001c0302202c402c100c0c000d240b0751504902840240303a0306405081541009030a0103107041a4903814085806140a000e08002903c0c806122514040c861000400240d006000410041e1400001c5da600148004004141c0c0306450003c41e00070300581e131080e80d01508007400041e8a5442c08001c01060313000b11020b00480c1240481a5030709104a01080e00084091410040543c481c845100000c60001c10100d03003295501000c000903040c6410806e40070181c040100100103062143c02010a540a501c40c101803501c4404281c601a620000e4107121910030071002041c1003408079101400024205042040c2e002c40a03002500b00110f1542d00b9071a040c00b0402d03c100c4121014442c4000401d5102c02034208502e40c041e014000c0c001c0c2e03031984010b000402060600340245842296000c01c20700c0c00c1c401600401c810790740c0190005000d503501004180c2604490002c4491580d85c11b1004510740e955490304031300502003070348060f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 14398496 1250 14397246 14397277
    0x50a020c0a030303060815060303030c072111060a09080d0506010c0605040b0612070506030a090c0e010e100915030201030c0e0904060203180304080a020f0a03082109030a0203090f06 80
    0xb200301900f60b0711603c00c2d290b40a0440d4000d41d50f668041c44004400d60348954540d0040c07002690503c1c444004202c102d200340924142441000003242c0c0c1d010300c4c60505c0c00401d21402800c075044800f00070365a800001d0201c1801010002d483e2100789210b01d138440540540c5074400910581d00440d580142541c3c4030408000506c0c0500300011100415030f40f561003030f1407203c909825220300280050a540004000030700e10380310399a00708000d200c50b8400b1269801488800144019642c007a1030081c447c00340112100e140c4901d00c190500c14540008024510300300940301c4803011008444142c13139080c00c00144082007614250707801c07008520b900d40d100350b04008110030021580c001e036005989610702d281e603220748840080e44900803801102c115a10540000025113403c1a07082c040e468040c000150003078581d11210b28540c410300c802c0c04200c0b081a03040d54021340548030321794083c0000c0c02450505031100e50007074031707442040211803081102a034414019510b4004440c1c40300c0028031031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 14399746 1250 14398496 14398499
    0x619030513080c010e070b04060210020706060806040506070e090906040f0503040801060b0c0c030a02010c0b190207080a090501020601050d03030f0e061e090a080d05090a05030a03090c050d12050a020c0a 89
    0xf62406056082e01c0010740f401034020000e090031a0905603000d40c0ea80b03401410201c2c1044082c1c03402908481d20949101d5181c1d10002034014092000d240614007400c09080d1900e0311220181000079003004150240040071308124440c40d01180300c40c3c0081c0d110203403a0040050b814a2032031400341e5048032015520f414400035040c0203402c011b000002e46082a0303221211500101501c502803548068003043e4214450000941d04629065212900900310003201150029000c00c0380c0003580d08881404c1c0002d60114010b0b0020151001820248014200c5605240200b010310181e62401401d01d51940100541036965801481500501c0c03001c548641c07a102c0158441c803410541c81c070300d4103010070022480883c80450018659600900001c0c60f10150010312002410020b00d2501d103070040e08640b000040040c402890f03007034009e03a004640b240c072500341643d4a02591780030707910401003005500c00250001c00700b00108402404e02580390050b03001c05908004030601120342c85034100a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 14400996 1250 14399746 14399767
    0xc030309080a0e0307050603040c05060a090e070804031205070e010513050d030906180602030f0d09020d0b0a1401030f080c0a0819030c030203060a14010306090504060204060806061903051308 84
    0x80c4003c100301c0c1201100c1c1c0e015074503828804944404d413000741c4110b00d17281060060b41044001050007001c1c40c0742034aca5080d80e0f150b80100c4588140e43c1c0000254215017030009241e40111a82a240c04601d010031450400c00c4d0050100e08100c60b031141485030214804445a1a807401c80d0020072000d03043c0000c1d4080c0d407800505007074103406041e0103e20920f0b02c48e2403100042d44c5040581e04107400071480c1035400c8654401c19000385005c03e0350580c1703407841000141ca0301d66650000c140b007480b000b04581000182c0405544200c00764070449501d6100400114640420007140c0310380003981d4994484c801d245050a00c4031000d005000c054000400800191014107071103c01035260f60104603111283c50120164071081d2616a40a01d0784401800001241e180b000f62011050400140c1300e5510489002600c801712001d803049540404d040100c0da4110251a9010400b11a00b40c901030041950203041e0302c1d01d40928042580d1000011041103d072138030b22100c280c2000e84142c41d90038980d0b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 14402246 1250 14400996 14401007
    0xb030318090606220602011b020c01080c0c150711031809060604030c060503040201031a090402010f0912050115090603020a030b090c13090c1401050d0b030a021807081e0105010c030309080a 83
    0x5c00d9900640c079103a40711070b003411182c0700050a08219800b50100c0140d0304c004640c00340010309812507a800c10001044200e2080000c2d400b000c00e80c500c8080340d40740903400540328502917030318004250420008120b2134201e42031004141031040795840c1c0640c070b0b0000454094060780c1c00080040401c2a404210203030400b0140d03200368400d99090140c86003c0320451011501803550721340000c14500400e00560060409203800300a510340304100503580d03000110301c1804450705444c981d54031803201102e003044107152409001c0311801400064a140d000c00d0780041a07201c054a01a01a400f180c07000f80e05014583c0c0305000103003c0001c140b603107150200104548002214004414000041c02c45030030111154901c0050311000d080401c0508680003a080c0c2007906a81801607081c588010707030b01c207000741c14500d1400c0307405215450f0002000c0d0403414040c000c104550030444a01e04001c502500c0541500c10030310b4800100b84940c42c080d8040d204442000b4059880800c44c01e2030554840c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 14403496 1250 14402246 14402249
    0x30109031211070804060809151005011106090703080a03020415080609070806010f030c090b0331080a0e0316080303060a0e060a0621050406020a030b03031809060622 73
    0xc00c01040034a209089051243c40b840f070006000d22024007007005154010303290b503540f040e01d04041c0d6003054403542d000e0f420400c048800328058a0802e0342440207581c4055030410321345032000100003500700038400550300c0e1004d10000380b505000066048546100b03405407001081043c0031720701403100101014003486421103025001e40c03500e03000101242e102e0135401d80900303010703101c2c52641d000d001400c4028002104101c014040c40305ea00003a0340603000004e52040c0d40034020301c4100c030707010300c88080290800501c403201e01d0050415600841e003803404031381074801103081100642145101081c24034075800d40740c00c3c03149090840090622008002988295000c8908800d01921150100c080b5030702541d08a8004561005c140880c900481081c0c0948407400550038011800340001c000b0744134116011182c054000c1514400b0540500402e446000120003840c00d1080c07c0b1a403068100140442510440a400c0072811a031901b100702c9400d030070b001c0503070820290b8103100b05030300d41070a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 14404746 1250 14403496 14403527
    0xa080c030307030c0f0e090a0b0a14030d0c0507150314040c05040e03130506130302210105060904120305180102070602040e0612120a031d0109030905010f02070618030203010903 78
    0x8052100380118071802032041040006c1c1c43d0040c1c00c1c2154414080c401c00010310001101e542c40c00c400d070465075040069001011001e180403c030203402e44c107160070140100b00c00d030117102d002205140092404908081030f00c42c01e40c4240c1c44100e590204a02400220350800c40c1d82c01b0210502040c02000c0b05107a060b980d056a083c0042107180311240d65074491468080001c0040c03100503c00d42c603000c4001d1000c5400c06c516106055201d4000440c1c80c02c0b081941000c6040d040c903000d03810300c004e00a0590000d001c4030069880d01d40b0703131036050010700300140b8841015682d0001607070620100311a0365540e04058000c540740e03141031401100030b50040c0201c1e50002508000aa46441c5c000d4001c10389899090140011a1a45082044680205038208141511a01404003075454500b905841160711400400c0d03990050502030810320300b64100d80d0401c03000500100c0d8154000400200312620b600d088140d10342c0a0a038070081600d6074200a52550070840321209040d4050541443e0920 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 14405996 1250 14404746 14404751
    0x509040905030c070b04150e040605041d06090a170304021f020d080604020906040501080a0204090908070b1503030315120a050706090617040308070302070507030302010608011103040f02090403020a080c03030703 93
    0xc81e1030000c2c810780141e00c2040d40c0d030412101f910800900c209160722034050081c002045454649000505030740e62900301c0004115820940303003c03140c013000344d43d4200000070003500e500314445d01c61f41035500c10003c1320b425809000000c102192116075252000403003551442114181414009403200046610480001e01d1500803078418a010b108480b040034004110a00e464501401524000b03001049a40150f50074400010050094014016200d100300390990341c0e103e040c6406542e403c006050401c0308024103480c0c0421b034400004503034110469001841a6880810004c0c9001300d1040ba8449140589061001000380c002030304402da070380d6074840016040c1c03030380022200e4100e00f24404059503020004100031034010f8070000d4000106240c09460a256500c0f0241713030000b1a0f0003100180c1d50b035941080b8200c020b02c50091800340030340c1203a10394109901c1c3c2c5010840451000b038820000c00c00454105802080707801000e80e8405c1e0080d03181c04441103000d07100c0d0011240302010a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 14407246 1250 14405996 14405999
    0x806132102030c07091505150c01020d060f120f0b0a060b071401050601080c040303032c0f1009050307060209010201140a0b010e0d120c02060d020705060103060e0601030b0403030506010509040905030c07 89
    0x782e40c012500715550a1b000d00d64500d1811042185404070055a04000c1d4000c01440c815541c00b03000401c0070422400000c00d1282c80d00c4181c01c6149140da0001c1c0c2c4001d101d05a441c0080d000040d40d0740c030541c0004544986846203103440000b0306640d8800f60a508000811000b0004021200c1c441c0405035402009140e03210401950100790031213241060300d808000034030010340280c1c041e1042c28240c03000754080030110002003903050301c0540c15180550040d00e600c04101c5c0b04111607000035070072180030700006d9100d9988503034a0140b01b5000f0020f5030003054004081e4403d510294401c0d102805140f03841c10403a844038020321500702040d00184400316824014107003102c440c21b046a200c410045a4041030800b2100384141107801c90740040200040f852512031400540002805000075090a5140d8a401d400722005c4002c139030f4903500018010000304042001003a031241e090304002c5200ea491000484140c442d156100d54040d00e0080c10005024000004d80b10216040e8115203005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 14408496 1250 14407246 14407259
    0x3070504020309120d06030804030503130803041406030a11030f0403021005070c0b04020a0b030a020c0f0c0109121103070608060f0102011b05070606031a0403090605040806132102030c07 82
    0x34441103d2103005a4060241c0643c100c40e444001d001e500500c01d0001442c0e6203940e500c2c001030b0f005d51b0094501e5400429000e4108e880302c50514010412480218501413902e00041d800d1811011918440c040101c00075840302200d401c0966020440d240c111b5036440e14200c925184041510b06400601c2030106100e1140388501ca0103000744025210300310300d400103590f58030030840d005108a81107d4101800034400302004099409510802c002503150803001e000c00d8070b0300e0082c0814410302da202401440d07a41e604290b607039003507917442c0f00110040c44a03402e0005100300c01200780d50701845041070010703282d5448245940181811105020015001ca00490903514258005040d200350304002402c0603008030014504988603490104880741d981d140c44071000001e20b200500f4000c1d44080008240d800103950303003d46000d040250500307040684550384c0b014002c2c80d25040c409141c181d04c4c18801580300c52200c5080580c036000c69104a600002d499810150880c0420321a556011522 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 14409746 1250 14408496 14408501
    0xd020703020906060c0109020310061403060c0f09030316050a1101080405070509130b01080105070807050708030c03102d080a02090c0918010b040f140102030702010e03070b0d06030203070504 84
    0x49075002040c0101545410040100ca6840b56803407034002d6680b0b03c0080016202804403642e10587c2000000d107079840c080100025294442003148240c000c2d000f040180314020081e034107a80680080c00d5265451310300401e24500c10104d0a10050071000d00782003c0110020703440c0b2880384240600d91148481d800150b41000c403d80e40201903410990062040b410b00340f040a51091600c460078240791807548403080c100130203800980550351900100003202d600801401d8000c1d221307240051508000391502009804040c06101603010300001003405130070301c1803400e000f4101c5803007011061080082c1010030f0b4a0901c41464181030300502c000b0341c482000ca9164900c85d00035001c03041642d80c3c0b89010007160300c0088180c0c0d200303a1441c1256180c41001d03007414040c0c0f0b800105a685e46084c5143c548005410394081c02c5081680400c501959a0100c2680e008580c20309100241d40d40c00c82c000f074100001078010280084000c90300c0c8148491070381026007228026000c0c0d071003068540061005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 14410996 1250 14409746 14409749
    0x16090b0405070c060c0207050402040e040501050603060f01090b0f06030a0c11071202061c0504050a0506150109031203110d0c0908010c08010e0405030702030a0b090c01031a041e050403030e0d0207 86
    0x1081c1c4248003e008140250090501d2042d54415108003035100c0c80014100d800c25004044020100c2003000208142440303035540154080b80244039a103001008002c1040f01401554070780c580340d103d0940380d515110401c2e444036200411098070303843c003a10f401004080c01500340001880455038a000000089454000d585806100352101a055000e2028a600440001a01d1102d03002c1404a400080c407680d40110f2040c005803080c0b10345070922600d4040301502030006c81c02e2083d0014640d0b030700b0400080859030f120004202c40122407000fa002440c8030784040c0300d0319000080c000400c00141d80181148000390700c1c0d00c400b4544032a070345800ca450650510b00030641c084010700c6110326501c101a80701d4441c0d412030703140400b647c1c04641016134004d0102c503041400000c0c024494000c2c0000c640b005c10070310b01042902c400340091948640b5828215015554400f0b040b401c0c4003060240c0d000c02c00c81720350240200d060900d001070080070300340000d4005010760382c0d103408043e102084410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 14412246 1250 14410996 14411011
    0x105030304210602070b0603060c040f030201140702090f01060f053c0c06040201090e0709140103090614010303020d08250306031209081204080303040605090703020316090b0405 78
    0x608190629201d007400800b00240740840b519503080c00800600580002c04410b840b8101400f41ca007002010715207090b0000d001001500d8041c04180b0485070307104240f10840b502403a00300300035585007241403418464400c010f500089084100303ca0300c048243c2d0319040307404903a2003a6504091000403152405441007590350002038004c6c0c40340307038488420110b0b40b2800f1069503480c0700c003018144580c41c1c0e10202e40150346421074005c00c0705641e0050b01d0180101007043e80c052551600030700041041c9002d000741449180c1e5403a800000e64880d03400030051a034004800c00c00c0024210700e00c4c0000382c4c00d00c0102c1c014890001907418291041c3d074118000d4131480203240383d900c05001140381c10740e8047c0c0300d04100341d601c40d40000804d002209030170300c06160307440c0c0c800f032a0300300030103a0300301140301e210f0b101d01810411040088107030000440340e000383c000c1c20018083e15600006401e02c0300f00e0740080c1d0f01d0700c1891001401e04024020b1803040304c0f140b02d400c1044612071011310040c1e8100b2510b05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 14413496 1250 14412246 14412253
    0x90b0102190203030c06010f051f08060d170a050d0b0301020a0801030f08190507030f1409010302030405100608100b01020a020609041a0604140103050a0921020106030501020f120f010503 82
    0xc1070414403944810584610050949040c44100f400d15860070200340c3c0461404580c40d00100454282007080d10724282c5400310310203054040180180280c1c4028007514060001d841c0a0000e21510a000203000e917000707203c1998031101228014100d4011000706000b851038440c1c8031905140520840d003040030181c545000e00d80c03854070307092140c09030380c0c20545040a041120034050800c1070085480c18240c0d0721050f40303ea60f503040c01848100c0a0030645c00380488010035070003107060304098903c0311100746400f5070389030f6441c45c2c264148241514961203a605020300441c100202003081e03543c0d0552010100b000e075281a004907550940700310080d400040410500030b0900f860380104003004075841050851120f004045507a542c0980e12952684481c2c070340c01d080303540c4c0c14041c0d240c000742040001e1007246a180c8400202c0c4407825150702c40103030b0708602009114001c0d00902c1c011608940215158203002070034504643c40300400c2c41e00540c030500001e801045440d0001d041c1d400240c006c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 14414746 1250 14413496 14413513
    0x220b04180201030b0f03120318030301090614030d02060a0b19080102030f0c120a050402120f030309100b031207020d1502040302040c03141f0503071d160c151116020109090b0102 78
    0x47c6100d50002e80f94400e00042c1c02c0421320204410001503000f0a54502c001903030615014180414608c0501c10a2003038001229001c00a9070004900c1d40142d200c003400540c9040240000348580c0340074840c0791071000e4148000031901010340c0230750711800c058031683e605070317480d030780052a207201d010701c4012400110008640000026404942e0140c4050414004942c207000450b182800c0030040030b4042d0320000c00c10140050038082c61500e00382000060041d4005840025151031105603100301c00480401d8be90107560f500207540640c0c0da04403201003081c28600c414680654002e010981c0298203101e08100058840d00c940c8840c2c84000703200540785d40f85c10801d00d0540074403408165181910200100d19568184003c10051060900d1707505508081414103a480b0001094081d500c0103444928040b190498441c14145030b0001d00c0000d03080042c0360000062909003150915035002081700900c1c0100000405030b0f40d0b0003629444041a550403901d0203441d408030300f003030058204814 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 14415996 1250 14414746 14414773
    0x203041505030a110720010903030801120305070803010e0604060506030601020a030c0c090c02010209090a09020603161701060c0203070801050601050906070204060305010207030807090b0405220b04180201030b0f03 94
    0x35582281c010700740130850303103041040440300390426041030300c407903082007210800307042031140950f544802828095850780c84e5407406440030005100c0c109050303500048141c100745c0b0038001c0b1a00103900c111425241e58442003402c180b090226910b60045140c109c002c1818603207582900c1c07090005a0080030003141564041b166504100000c903002041d07698081381d07030111400362a0106200c0e070b0005807948180820054802c6010341400d4106280191003805621420112640040c00340c0010010b048811307401c40c0c607074200490360384d4904407440c000714416502c0f101e18280d0034002c804590200340c803800014200c82003541c40b94003080c0c04100c140081d04080020340300c400d000401c00900e0a035607882e2207003641d001e41e0084000480e000c0402c507545411048070380181c12520448c0d0300b02070500010500d440e52224010b24000e002c08c8102c0c0f00d0100320f0b0010780c680303003016000340440100301504110202d0000c2040303000c2414401c0010013801c05402800884a00500415031480481c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 14417246 1250 14415996 14416007
    0x3071e0204090b07030b04050a02040f060804050715050307030e071412010e030301090e0f01090b070507051609050108150903040b070213060b040905060d03091a070b010e01080d02030415 82
    0x84080760441c2c0c0311404080407410a440d024404c0400c0e8601150110007001084100e80c0020304809101d84140014851902034080f01c20a90b07280c0e05040d42135840c0c904080d454103d803680100748001c81c1440b41c0c04c4056200b8043c6020310401d8a040c0300302c45012040680350400d900941100f145400c0000f0b10740c1c507102c240001500b20900c000913030980c4261040b81103034026007151000c5c580fa60850300f00e5807010414100712a5510008219469040d601c40035001d01c0a4240010400d01041e1241072040500c100c44c0343e21201100002c40b507507105003c0018001c244182c4100380900084032180d04102001d0a00c2840740b0005545040d007004203050107a081143c0681c5c20a204080e0000104054443c3c10041c00c01c211034141c9541c5442c0c2c101c0e003503500080c8001c0c00f400c068840d260002c1d801406102c1030750004030710a0100314101015943c24000d10b040500708084c01400000d007820000d040380d041e201040c4c01c5d1f030b11294002c14180e95178401c07407003203e010b001d00c0c0180d00b86091091 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 14418496 1250 14417246 14417303
    0xa081c0c0509040b030c0102061b0c0f030304030207060c0503070204050402060d0e0114090106050d080705250e010906061706030f0a06050609070804080301030803070e10030e070e01120f060908070c080706020307 93
    0x8072452400c152f40d215025242280014400c8136580c0004180001e1640420900004080920304080110840c0e962281c40c1e01400a000b170181d915200070400b15540d0300140d4800d0803164004010810201c0c00980c00b800d0310b054489451251040850384d03250040c0a9003080e58805012160140c2ca10342d14801035520640c2e06842c41e00400a40d0a6450701544907650110b81c0c0034801c10000b07052400c100c0d69040103912111001d45032020130413003d44c0154104452100000d051003240d03880d0408641050301c50103001c08207000e8903044a00308000d0340d00c000d00500c0141c0b0188243e035179a40017501c00000c280c034090603001060004000041c00341c8002c60f4000040c1c5460715038800341070080741d241c44000c0848000300f80c4a4500e01c4007010108045c0c001020740c03615102e00c651500e5801402c00c01904005007007242102210b1081c0a0580c0012592642c442196980c0780240d04141780752a11034040c0d00c15034003035442c001541500c000291828107400c500314800300004190881c5040c90003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 14419746 1250 14418496 14418541
    0x301050a0e060d0b0c0a090915090b0d060c0302120604050601020a0206071a01060809060703090c090b06070206040b03010f060f020601050f0111060a0f0b03010603050a081c0c0509040b030c010206 86
    0xe0303d841400a8410080c082c0144203081c02d264840c00c07101005452030065420507601d080c0b915a4000001055600394021209011800118011100007240403100c028202030702075030030003e080b151582e0681c01002c05480c280c02c0c01c03d09803140000c00082d2102038859038010383c000850b05001d490310000030000c09210b0301c420110708450880100180e0403d9000e2400b0401650811003807000c14020320340e0202c0d5500d01003000c4840c694882d80004042d010702c1010aa85080e031081c26212202103810698008142d20307151652030748400099842401144900100ca0f00d0024100d8040c2c0c414000320041a0050086a03003400d09012164105010075410000c024005801c90302c810300150303008140710000414542d211a00e2907042d100d0308901c240c06030f031600604001080b4003007107002202c0c0d4004440d550b03910101544034001005180f003544254a411885c41e40d07070b03800c04020700c002103040d203081c044d0700018030826807112041014640540c22403070000d24800130b4045605241507a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 14420996 1250 14419746 14419759
    0xb0115030608120406271e050414071d1e0f030a150b18070801090e03040e0117031b030702040f02033601090606080c15040611030912060403080c0301050a0e06 70
    0x180318003a142c00f5415602034004504540c0390000c1f001e83c201a20006010140c0e070500030300905865440903400000c01e2482008092245003080c010300c3d0a03a9102582c008028031600140004000341d1240c540d500d0505c2120040041045400c01060000c261034003c009022041c8087c0316442c040c2100e15401030b440048180a10040503020741280c1c040c0d0f001c0d1751001020340c107001119003110300000040e20603500600c4100000b007801030001d0f054030310011042d030280c03000a2101e442c5000700880ca4105c1e1307a1181d1001031075000003000d40b50711402101e0501584001540da8000c902c41681c0316500062038242840020800c0b941998006190f007400050920100c1d9086003140c1003070b04126480c0c5d44601e420020307846c040149006a5804440407010800d1412005007144140e11416050048c1c4416480c07400e20309106403000c010000d48070f003040d620024045601ca0100b10f0f01140400c200c40007096403407030300004ada4180c503005003007003180c81e050800381d411151008152590014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 14422246 1250 14420996 14421047
    0x2030304080d09060203070e040e01020405100c05070b03130507050103020a0e0103020307120e0a03121109010c03020703060f0204080f0106030b0a090c030203010c020c010f0206090601060c0303090b0115030608120406 95
    0x60662000310320800c019a15141c04a008c1d1040005031502d100800166a00501003404250b81e56004c0701207048039400e0200b9040d607245465030600009a000410700c0704c0200c00c0051a500c0300591880c6948901c040c0e461035a03c0f40015822400344011800002d2030350107890190394040da00464000c940b0f800c1602200b14407010f0703001070328085003d001e0941c000401203810580c203c40f20132141c981c002d2040c00540110600911180070b4068000d0421201c0d408a44c00e250090203060003554104400384a501407015445019500c07601c6906013a103c0c01480a0403100188295020344e42d10201c80f50490b2902000b000180000d243e094681c10b81c0940d00200682d0240310f44614519070b81c020b040e003580100c0001d4002c00440303648100f9500310300c040201004001c40c2143c15107030242081c41410201d402c0840c010513003144010900caa6900010034201d1100c007035204600003c2e035083c020241c03503000f07464540210341e031070641103101440700b03100f0180940d00500c07400003018401c82500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 14423496 1250 14422246 14422253
    0x20a0602180d03030e010b0d0b13021503041112030c060c030703060b04081c091d1302040203040303090203070506040605030a09110d080406080a0c0206041506050406060512010e0702030304080d09 86
    0x42c620442240841e5171a4203243e409002070068003042da20440700e0748204c040360f440301180d0040040c44e00d030000803e006414210340c2e800b5801c810b1008009041a282d280925101405500150000c1d00ca041c1c1c080501006a030004101c1e009800401c010344400d8a40c10021031064201500d20014140c83d00310100b03500040c02c0c090300003450302000501c4242840700c0711055140180708902d0070003060a209002d101e43c1b4040302460107881c421840c40c81c1c0d42d10006d0084d0b05615507c001d510074000014002410784c103411800000b8000c6050b1400c0a81d00e9040010912941c40f65602080083c40007914001d0690f201c10703c1d40340202c5d01a00c0988110001803d9545050000c550000001c13070103201d000d501c102000e500c09010b0008001859101c1800380d0b40d001300038001010518080700320707200c00344140c101600a120162050003540e132282d8000c0d00c00e812403112840e81840600001a815801c5007a0b0340c05031109401440c50341d00c880e299007403039910a00280c01140c0e207504085001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 14424746 1250 14423496 14423509
    0x6120204051b160b06010201060602030a0513050604090b030c0103270f060606170601050403110915040e0706022404080c01021e040611070302060a05070c03050706020f07090c020a060218 82
    0x3110350343c5080c500d01503124500241c4456014191030b04680c0b4210302400300700d070000704481455906041940e1901611071001c03603450150740001d500210082000641c00c00f0507048540c203580200c003501c252105160044041320b4400d034032140819100038514100c4517075000343d032175424024014090821748540b074040035620f4a40c00b090000d0f8600209400000904c0300c142e4000109103403081c606840d5803107846503814100d405900c13a080e03000104922400b1008002c6800d28040c00610001c805400394540361050741c030a60b8058000d81c648091442c4001140841c0f564a05801901d9a11149c50340c1da4070760000700c8a02000d6608000c07464142d0226a001120800b44100c41943d036401c19000074601c1ca00141e800d007031541300800500c0165103c00a0703403a047c0051406507103582042c10515003110641c0d001510340d00031a180807802036804074600307810380d00304004c95035925901c10402040792104a1804016004960518002000c85d0001d000300f0310401c94000c11901c5400000383c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 14425996 1250 14424746 14424757
    0x20d020d1b0b0a05040b09130603030201020306030709050c030109180f050a03090e04240207060603050703060605030706020c010c08090916030501090b01050301030213020705060703140a06120204051b 88
    0x3145440140ca1240307070003039040d215025211000896043c402c500101501c14004c50144625844010032110b0341a122005c4107a10f08881040900149a5034100a03000f0340c029991907000e80540b0300702180169050007500d0155403c400080d140d44e2806a11100626500341c0c401c0f0002140080403002c519100080c0c07503a20300843c06400c0c040c41524001c0d14001c940d503c00180c4100c03420801002c291204041c901010300140010441355144490000a1040540042140e0b10307100d00482480b00c00104001542d1065100b04a101d460340100341d0780d4101441480010303441403628130003a51040210b01c0d10f6500c251034017404c00300d5036000181210b0007160400c20340003048c44071007000c513807501030107006002e02e080422100280100003440b40c0300c1400080c3c0145129070f580b90700d9000c140d0403a07000d80d41020507a940e48c202108010043d0204591a11341038840c90003185200250784198411241d00260380005213100e070b03084c00040e000082c42c90381c64001d006c090710a0310360784000a04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 14427246 1250 14425996 14426003
    0x4180605061903080319090503090d050705040c0504050316050a032004060b0702010e060a0c0b0c070606080f070e011214070f180f0507020a02060708040801091101080a0c0813020d020d 81
    0xf51a1b180c00c041040780e18641c1a4919850341c103114440011400102c11124071041c10f9403501d41d103403817078108a450940e20354803540d040792410b240905402ea01c50007070004d90707c085003a500c4240e20404401d00324516400340550042814070304100140c0035843c48400d1014801c244071520030750000080403038400303a000f42040d000009031501150382c031418281100904950140c240040b44070003e241031b6585000030521011480440c0300b0010302c030151b54105038003240c203208094a4408907521000e640c4440e0006205007980031400c0030541300c855050f02d5850203003280c7c459480d00e8030503407042070441c9214140105440403c00d02420404803010307024464002840f12514030754802200c03600400950158581410311a00d207501040f0312107a1358048a01d41d0b00c9001c40d0809105030310480e4003d520312b41c40e11010200300310b1000302e002c0041c1c03800d0303d5280c40c41e540c2030f0700c1d0741c00da4808000000020310440300080541140032000c2c0100c030700240c040c00d0050100e0380442c40c1a264620b054 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 14428496 1250 14427246 14427263
    0x3080d09021311030c090102030f03010303030b0a060306061e0e09040506061212030403050c151003030807021606050a020c130905070f120308130b040b040b010504180605061903 78
    0x10025410041c8011942c641c1c2d030041084804590600410030b4000681104d03c4400006000f000c135a208000b541c52454840208540e00e503075901d0040c0041c1401c400090262122400c0090194082d02c03d02045401945502c010f11980c3e420015225915400e0b07c01803042a007100c0e94251954a00719200d40c1c03003070b0020b12144c1407007020001c00c040e84c100c8100103503100c00c061030050005003041d03d4129526040c09034031410028055800e240c0047c03180302c6203c0404042003821890900d0040480c0c0c001e4841031003d4481000480e128424075500e988030700a0000100117651017800140660744103441500c03151400507000400360b5071090001c050b800d84804200c0c00b485000d01c1840c000b40440141d1341507840c03402e5000c0054100705440502800040b000262010b2100000084150b6110006e00306e50b00d85072904a1000c0e4003a901079031042c00d09000881c16042500c030b08c50307a21001178100c2c0c40755003940c0d459401408004040c4c541146800750700211402e40762481c1c2c0c0185200780c000713 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 14429746 1250 14428496 14428511
    0x91509030201140c0703090b09010903020d080a080c0903060f06150a03020711030a030215040501140108060f0a05060d02040905161203140906030a020702030109050d03020406080907032a03080d 85
    0x3c41001e07103000740280d8900441040000000390b00003007820104d03031900b021981c50307a42c0c1c0c00040c0e6015a00750700294104804a0174503040051040090482003015203599005444442c0103481500819030020b8040d030141d00170070764000c04005000e6203c0402450001002e540010781121600300e000c503140406e80101d005c20400416181c4040c00550550007002945c005880c000c1d80c540c483c1e010110740c038038038002080500800703400c07022143c8201b101d0101c183d65980c5403a59120b80c21581e84600070340d18004500700c0301d02c502400e030291500070080c0080150355020800100b10f400e0040340c1c503110380d4902c00c17203101c0080c0d4034600070240c60020240400c0e1a04000e400000565052001d0050400200445941da031040d00c0d045008018010b8a96866202090040511040140c42481048060240c13036615800500503180c05550b285e600340c0300c1d0000d642e030780c84550000030460a001a02ca461800b0402c00c529240b41444c101030b11120341c0c0e901d54010b180e02606840401540b100c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 14430996 1250 14429746 14429771
    0x20f1002010e060105060a170a020705030a05041701140c0c03090405090601050316050603070c1b0e090c060f030604051b04090203010f12020d030509010905090a0e0d0512010504091509030201 84
    0x2600424007954040c0c50b0031060480141030001c010030f001d02e511608804121b092270340d90b061b200c9480e80441140e40c0c0e4030b54000050680e0704944140c011658240e42500c401c80d03018029082d0508c0900155041c41c2c81e281c012124035000750b403546c41c081c40140071502e036075515409107a0140c010103014066950501042c942031440248004002c0c441c005000c00580d1198000c496000c203052801c08203260091501108105018048040c4ac07100320001161080c0600b2040d8022000301e0100c2d01c514038070740203003c210b00030002d40c54841c030401e100048460506401442d8480300c0104c9a000c00d28414101c0f1046070405d400060005a0110051056400840c2040060000703019000c400e80d03034903800900585044440181007242c08140805140d0050300d44c4d1020b0b00b002072010400d841d04003501c1009000b1030640c83c3c81da00c038014104030360741d00070001c0345c498000060040714aa0700303000c18000070f8940e0540851b018003451000c0d038184074251041d82111761081d400411541072519 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 14432246 1250 14430996 14431003
    0xa0501080606010c050d080c040b0a02060718030206090d020a030203030403051501060809032d1605071a18030a020402070602090103060e070207181503050303010e010b03040f0b04020f1002010e 85
    0x40c1190f040c0310709802248045800080e1103003a0602c03078a451000c9540788101f01c09903005c1c0e6440040b180c6004030720444043d4011440038881d80c0d142e6204006604881911000e4903801c0c8806504100c0c1000303d030721103040040b00021040c0c0090f01f0031010a6495000c240b40d1b0b880748e48142c81300e4012805400c0324002ca403002c03030b00504541c070f0200101d01304441d1803602e9104013514045900076482c43e850041c1c840e000107860389034040c0d402030303101c0360310b82d0f40210200b580d4581100c29000d00d140200d01c00c0c40d401542e9a01991021500c1d06003001c1c0c2d00c80c046900101c40956516108802440d0b00507912400208640c0d413080c40c000da110010f8000140c15920b190300b020011f058003504204030b26500044840481d44816036080c3e0040c03558403200028460141212001500307610301009100d000002076040350001c00348030790103a9031030031441841c0c002600c00401e84280300034140007050030541c03115005800101480003802882c0c00189a041141c1490b0001d0707515018030300e80540061 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 14433496 1250 14432246 14432251
    0x504030b06040c140705011517010609060b0301031e05030a050d0c08010303020606060a0e09070810060503040503040b0319061401030b0312070f030504030c0305100507020307050703120c0602030a05010806 90
    0x182c909100c0c4561007080540350b40102c04403038400c6200800d0100501c102504800e01c128101c40c6d0361090540c82e801019a06880460200015801c22400048419031889034104075250030904070304690035aa2060800c00501d80c105600c001c02401100101340144014180050315131100ca80c0c0d0303440844840162611040a40f09005564004201084e000300b14190320200c115100b80c0c3e55a5030880554107000d4400003c4c0e0040780c00703030412407007e801240071383c05113078080c40e081d280d00d40e02c1c40101c883d40300403100101250400c5c0001c000c042800e0340134581001c508a950040d1003507890a5030201c07076060f0f100c14040c1401d0070702c40ca100d50705441144091b88040e40a014118448a8405c0300742c41010401800d412007910084245445001514041d40d440445003100c0e60f070301e08001b69500851950411407901c0c0c01e003c1501d0b10700010440d15002d902501034007921740303140c031065546800344264900344211000e419000956074402184107803482e80b00040c0ca541400740d0301c0e1400800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 14434746 1250 14433496 14433499
    0x105070507020109080f06070e12071509050a060c03030911100207090e0d0504120f0b0f042102150a1107060905070b0705071512050a0b0f090c0406121b0504030b06 72
    0x406c40007628040b01045c1540c2c41201400c0c0318220385d13100800719a45850a0020100303900416402141820b00c0b580c05980500c40e80d600c0d803448584600410014a895110f00c0b808100c402d0625000a406038001e10223440c0102e01007403480781101c5c04501b0503450f903400540160040b0b1414043d044032442201444bc188000508003520b9800d0042d000784200d001c0d0b29918030300360401608106800d0040000389a201e02d090a0a003056500070a04000655003100c7c0051440345520b680c0c40085211342c0000941d90042451000140c00c0f140d4030140034003c114910b490300184080c054403040100a61b41c4503002c0050707031858074101541401301541043e200da00e400c0054101103200000d050043d25080302446008203080c1c0c10644140c0c16a0003d04c2529003080c0030010b0381d00c00e617448054103507429502c054082c8410000c02510810071134260003a050f062000f03026151254103264cc019041003400161020f01400c0a544609042c0c12a0002800020f080c001c00c8201c144060300601d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 14435996 1250 14434746 14434753
    0x11812110606030c040b12070609030c08030708030a090201020c030d3603020613050d2004050f01060c03050f1201050307080a020604031106090a0b04060f0203070f0308060102030408010507050702010908 89
    0x4081000075150030f200c00090784120344071001240947d6449456042c20080d00c8100c0d40116130f55000035020600502c4156010604c1910000e0180c1c80401128100c0d03504c415580d10b1130f911142800d00500118170240e0452040d03220700ca100d900d042049000340591f070340700d03d48107005c0c00142c4419210385000d201c0540000303280007040000207901d07090550307604948841e1161762040340b07506100c1c4142c0c820340e4020350390f46048090000003c40844250038400c110401a0103000503c81958030a440241c080e0582500420a440c4101541700000b4824a0102e150140d01448102c09400200741001c520344408010819440d04004940041070403901030802454140c000442c140170780d01c0050480e107448040305038642c0c0c070a021201c01c4000109160360250301d601900e0700f55005402100089940e00c2c3c0d0282c1c1190000041da40303031580c042d800e032500c2c03440c0b43d50490340c0807805030000f410741c0300c180030216590b142030054900c14019503a502d600c0d11141e00004200200c25840a69a0341 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 14437246 1250 14435996 14436001
    0x309030d1701121401090c09050f06090a0c051c0605040507080405060c03180d030906060609080c0d021909050912120f100909050303010906090606050d050601020118121106 76
    0x859a000c42d0441d20b802e0450020400541064034801c500b00151040c1c2c0e52800b1440e0007004804030910b001d0f00c200300300030080d071795030341000c6046000c083c0c48156102802e240000d00030704403908484203518a5103405070500c1008004503d40d0001880080c150b41e45411090109041601c500c0358011402e18140d6000e00707150b22030580314072014145a06880c1d00000086043d44001e010b181d41901c0325084502525007003000a00404005400301c403040d09201c00020080e04ca45812010795801c1da000c3c24142003040108410b102d00c4d180c080f030b080f01c50007811a49400d50200081c0c014018980c0118107840c00c060f4550070804203610050707203000203001350b04c06200ca003100c182d806030b20a218040140c590301100840b07022240c1c05580701d64207024018040004c00b0028504941800c03006015283d15109150151030b854000c200001d035051240100e0401190001908082c0600000407014541d8860b42c241c0d4650010503559240180c001e00091030740031030350602840c400e0028013550b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 14438496 1250 14437246 14437277
    0x8040302040f020306130b030114040302060403080610090605070f0206070510050a0207080a08100902040b0904061d0c0a0c0c06050a1106041115120106020601031e0201090306180c0303020309030d 86
    0x221805008411280d41f00347c0c0034101c3e18254000d031445881c12740c200c3d1180c0303464a8020340d900790450301140011019004180e59041c280006048015540c0302c1601c10b50400004130b0b01c0b50080d030030650300944025100e00260f00ca210090050900400240100c5800100791034113458000c4d00c840c115070310401c407143c0411511000d40da409125403030700107078030341744c0d150030300c0c00c25a05c1d801c01640e813480020005a40d42c0c07600c0003003a044500340e6040c080c06683c0d18001036080c42e0f0101040c0d07041c01c0203000420240380d030001000d001d20141400c082c440855102c2500480182d0030900110310b001405590682c3c002c00f000100140c0000107041c24070b010740e910065a03440b445d80d903028450510080c64480303200003c5d52604007002112018035030751034100079a107160030300c0f0076584425a0050301d902041107483c05450160180c46c2c00c0c407100c0c95039946400610020b440948917202d40c41c10304001550860b1000010350003940203585403030b00ba00405007054820800602823103460b0700ca23420f04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 14439746 1250 14438496 14438509
    0x5070e1b03040f0204050a0c09050105030108030403030f11030a02010c0318050c0108060301180507060e01020313050603070903020301090c05090603070812070206160b04231009020f0d08040302040f020306 90
    0x80c0e031001030308607459403203c0c501040c4000d40b0540080d400b500b80b100300030f0341107855800048000c0c443d540d8420926552001034465110a006050240c1c1040105001103402000703050307140c14003403038032080304034041c480c1d10304540102e2031001c01030f5110b51035038600c990b0502800445040d56000b40c0c03c801811382d0749503625184181c0031414846000c4c005502e5036400c1d841001c1d072030303100c00148192020f90302c2d11980301c074100e0084401140079203110030015413000007543e41400900407072942250510003086507a0700b0013030142c010405950000b02c01030320300303025009549129158050000381400100300b581344000700b056009503c643d104014040d00010105884c0481c0e582d060740c2d5054900100d000c1e4800c10b007092440000c210340c4801003003810604c440c4628014942048040004902d00d14a4640600c0003076a44e80304451450302e4652642c051450b4a100805034000c1c5411000407440c0031450311002d60325050045400c10035403c00f4001d801100f01c0808046296107084c40c00550f4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 14440996 1250 14439746 14439781
    0x1030609120f020a02010807090f0906030c0e090a0b1005060406050d0b040c02030f090f09010312180e0106050a090312030e07050306010602030403080d1e090203010f0e030a0f12050405070305070e 86
    0x10400010046208e540c01410b003000a02150b9030080080c0340c98082c2c00014005900c02105d11034046d42e00065038002c6144040d00400c8060b01a0050149941710012655805051096031880255000845075a5400100010070040c4c03562512000c0c0c2c04c1071241203e11003100c483c0101c1c01e00c02c81b0f0031101e501000300d409141c0600d403042d88030700c040008194140c0c0300136641d9420a591030008020710480c200d1051118a00c0d58406019041e40905811a82d049216080b508110640140240b500a0029101c0c240861902c0e0602a5032519030450714524404244042540e4800032041458140300170320181005a009144951401b4402580d9205070f00c0068940c0401081c1001c01407072541105c0c0802000d2005074440e407078194005401030007181000ca20941ca040c007000c41c1d42c201030181842085140024506100d10103805664040c62800c07810704005050042d0142914644119400345015100503c0d601742146000c500c1c00189400400002e01c1c4041003064000f07038042041c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 14442246 1250 14440996 14440999
    0x818060a0f150605030f0709140103020a0201020c1b0109080304080c01050304031206080c0a1d0106050d0f09050c03060c1204030309080403050613050c0409050312060d0b01030609120f020a02 84
    0x6050851440700d00000c04004086a10340e070842c0d0000a51542c0c41000b0310300501e44070300c0202503621100c0c816941080c1c0c1e803080344004100845113030802c1d8025400740420b481d15000252401050030f000c6801d002094000c98440003400010880341e507480201070010340b10f480700440c5000e04115074207959190034000d450400800000040815100702d40d49424070031300840504c007054030380c1c0304207445008440401e030080501070b90014000c03204590442d40341c8071041285140340d0a00d0011606907200014691103180c41d40100d03060300700540f00344d40940d4040c0e0042c04814403d5400c060030000c0c003503c0c3d200c0349070050000101c1031420b043c446410941c1410001403455840ca8500d03454069940060300a020b880f0410102200c0e480e521051140b049042d40c1416a05400300000c4070701610002d4010b07401441040da410301d01800b0a0382111008050480c44047d60350344554428007600704907040c03915041142c040009a030848412408142895031900c603c0d030500030340c0d400c060103019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 14443496 1250 14442246 14442251
    0xd0b180c090f040c0305030304051b0103090201050a0807140c0615010c0c0b09010903080a02010218030d1b05010902091303030507020a02130c110105010b04030b0a06050a030807060605061204030818060a 89
    0x2010031813a544103100440c0c0c8030b07040d2910b9140c0342c14a81e80390703a070384140302442a00040d0469070561080c4149228994140c40346410800400c3c000c542c00507000741a90305028000b0b464907080c07004e40c0c0242c400d90540c03400502c45440e103600d6610054191602440c1801540105400002c5d500103e07481501c041202507a00c4513200001241c2411841e440a030080b400022858801641074008007003491000007002c024a001c6024141c3d80c01300e802030038000505c41c8005003250903046c10008401400360001080c0750806d600000e40c0040107a640c14800e002c800706c290105030705800740d16440f102071300103096011078680110b1809036651419510f031658841d0310710401c03402034201c0c40507041c22000800040d0303160703003020340c02e50b000b0302050350700c21400300c001081c025503030003200b09650000d800050028596941d407074003030b0401002180d8150300e83d10041441e0b04c586001d4840c2924402442c907503402c01d410b021300600f201078600400040810075210101000007070054000707070180d000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 14444746 1250 14443496 14443501
    0x105030307140a0602030f06100207081b01020304090203010f0f08060702030702060a020a0c060203090a09060b070204020c0307060507230903060601080a0603080d05070f0503090a020d0f020d0b180c090f 89
    0x10904103c3d00303020003881580b01005004241c40ea4040a1b0b12410083d100300c0019000480c0c166525111440364458680c4400600f00321070340003040784c2c00382603018011a42010b0700e580240b4141d030026044038111100703100701004a24000543c1400070130305007000e04010b007007031b03580251644501c0001a016a078001801d81046200b084000701c51900b0811580707500c7c1c1c48010013500c0b82d02c000380c8944104185880071415016600c501000c441341d440b5468605582c590031b010280d0031100e0590120b00041c400710740490264041c1c83d1007602d450b076542c4480202c041248480b514811000043d0985c1401400103139240020300f0790700f0100900380020540d40741d0b00d00c0d03005050143c1004003280004100d030111004c6580100b8054482500d60b000100d800c540300716030074041120881c648e0f5000c3c4000d180942400340000c00c8441c002d03100c050150400b500403840d42c1e1480c010848104100a0030052804d4603204026075408101020340030116000c0e00190034030030060404035051111801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 14445996 1250 14444746 14444783
    0x40b0f090a030b04060905010c020c090610022a010306090b0612090f0304080303060306060f0102150a1401060507020a050301021c050c0d2306010203070b040b07020708071502150105030307 83
    0x4041c0c00550340300c10300745032074038007403a114001c0c1c103072804112010f40c00c040d604807510f800072443d90903c0401030308004040d59040308101c03111005e18540415802443ea040d00c412081d5091040042010152801c0c40c2e600d92000404480c841c1d84901180cd107000000405940c5480444060700d0b1400190001c1d0348440385807c1c00c04089044090382480005800070308400080090b51181f08100c0644980f0b50707480d0144820850a201c0690058010341c4e0a002c40e100c001000a03000011071200203142002000c0520720004c0030b8001d1404030300d020441008510305042104050901600254104000b41d00c0b07a2607a00076540e402d6034129100d50008a0007481c040035105401442601440103194030b185c07401800c0000400351640504240c005405940000700b06e407020b03540141480d0184e6110340301d02840d64000340000b011070050950000d103c1c0340c1008907001401510320409040d0344200f1019180954000e802003001040c1c4004220320b030b0300032043e202d0098001200000c65040c0c40c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 14447246 1250 14445996 14446009
    0x714070317160306050d0c0b1305040c08091e1b010c150203010513020403150902030f060c0c07090b0307030201030c02030f070b0a0e0303090a03030b0a030b16080c040b0f09 76
    0x899521400c20001e0401c481076042944506004080351002c20909899105000000c80b66490192045c400c420307040000805100040071400c20300207281104039265070002e400d4400180300d0b1400200b04406010140c07805106101d0300c0070704500e540302d090f10261f61890b250b8000450300340d101441003807880102c0e40108603144517a5440700c0c4032400354803510b15250083d0400e00031140038000e051860b522111581c800c6400f5a03402c0707204620007511441c00d080242081c0402240c050250701d010600103442041517900231180ca640941d11603d8201501b4904000d03030f030003003079498200b5080081c3ea40300414110290b036028600464810590070041c1e1441c031850071150b2280c98001010f105010749620214010f10110303405004020b00045803580d60300007551041c1550b0040d001c1d5000003402a84400001e80b8003906564046070f50b1348603409100c90868101d481300e1446100341e03140b00c1d4020380d155803040809240c2380c101820020500e0b0300d070180c4028a4200d0718001008001c030340d503a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 14448496 1250 14447246 14447267
    0x2090906041a190f09030f02030c060c0306060d05090c0405060a050a090c03061e060806010305011809020109120302060a0b0a0b030106030507020102070609080c120c0a080315030319090504020307140703 89
    0x8503410701208090318414070085c58600000d070000340c0c64000ca960006d10100c103c0c1c00000c3c0030001440c41d5207902442070032941c009050140d00640810154400040600880f4400e13818000942070b07084180051005454008105a01c1180c12030b41c00c6c8081c2e581d602030f0b6000d49800c110000792210400205038000e1050f070f0014184a8040c11000401c00b2030501070340c0a0364078503550401c030b5860720310041d81030300c1c800c1c024001180c083d02055803140740290b0042039502d00501d0100e02c526900c841207000500034140c10341c0113030801d200300100d021071801408400301c0240e07101d102061a01504444900060040707008140e00c645c00304400a100750192400603030003040c00c0029480d1842d041c0107a5020721100002c42c000c0303030301203c480ba04a506a40003c1c41c080040c265034106581c441140740e0000706080c1003009946060340c0c40d174800304054680d0550a140b01c0c0c2c21000c2c01203010303060050a80c0183c2c4514010410048201d034040a60f078004400d007510700d9190140c41c40c0175038203003140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 14449746 1250 14448496 14448541
    0x30b1504060c0606270e0102030f0c070303060b0301060c020901050d11090a1103010b040305010e0111040614120405010603031103071e030509150307111903140408070b03010302090906041a 83
    0x8179812544820500d4090340c40d80308407600c108850304482c44058240e00044a030071811402c01000105804154401060032610030700c2d0000304603407118850103e41c0c200303800601c0042c881589071021030500240903405001d0803140c0940400561740d030812100440000e090088016001003418201203800040400012103003240d101d41e1154540007140e001480143d509600b401030702000d04006100c0c0b40c040303c90700c0727407007500e0702d410070f00c0c1aa904007110944540c20b02d4100031641480c6038281c0d4503801036200358008500c061070f508004114104144008031150010490b101c001440c410f4685615207203080c48428007041420290f880c0d01030341d031501c0e4201c005a10413036804001c582c002d40c420072454030394840582d90240c0a5558031800d1a18030020b1818040440c0401e00800e01c181c8902d80c101c80c05440c2c02d0b25100081e080081759448501e501c8000702c014000c501c0c0034503a16a0028040d1b001b4241131074652104608220b4801d98820303a04042000f241c00c608401050381c074080c11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 14450996 1250 14449746 14449769
    0x60905010308041427060901140a03230613020f0303040f0e0408070b070c020a150c1407050604030503030417090618040e07081c020304060503010608072102030601030b1504060c0606 80
    0x100705170b08440750303807040745c009110f56580c0300046040d41d10f5031040011341700e01400c900c104600759500c00c1041d040d01100c619000c40d132140e180c00d44030400c00440d0311982c50300d12600c4c00d0b10810300c14012402d440805042c4260402e210502c890a2124500c900712403900e181071449849a0900740818800c0d4903018144580403c02c000c4200c0d0480600b488452080c0e480404159039000b419408481c020001000180e042440c90086403c5410301c202000d0b005060368010f595903070020380700e980103900894440c3c001204000500802c000881c4e842128181b02e5440c02021038000303a018070400d1400301d8040184d08010030305488030340c00180c1c004848803c03a44501c0c0c03240099969103070440703070600030070b0382c441080c00c1c00c0761002c0262070031074040b5103441d42144d00b0003c0640340c8403030048c152003c10a0704480310010141700000e8070400e0a60300720041e505c3c02c01c2400101900d451340c180720301600078a94580d1001035901d00700d80880f510707881c00c00701489252070204003411483d48034813100103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 14452246 1250 14450996 14451049
    0x7050906090406030f110102030a0c02191d180106050a0603090f0602030108011505031b100c05010504110f040b06030a09060e030a020f0d03050402010c02010503040201051e09040609050103080414 86
    0x1050b0700b00c0818203030184201b00e4070401e01c0401241c0c1c0c0d2040c511908002130b0398003040360040c20194038000d220019200300703060203619494004400e40e000e14a00301495000c00c28030540c40419051603810a090b2402880068100404030b403040c01c0511a007020950303680404401e11000d0300788070f1515940130a003076648e5650380c0d40c1e0b14080d003804010b01c0300c142010900090a4540000c460a0841081003081c0030202c9007020004411a502a55801d0010300031651000410038400ca52080b881602e24080340700596081c042c140f0b4148030824025440c1001100701c03659041c0070b4a603c01000711010883c040c02c1d01e460300180c08039200c04c24082c800403c0c01940a03801141c040b0702d0f142c50008032040151222412819591f054802902164100c109180554030500007142c0c05801814003514108201188803101c0480d50005074101c0c07808a8000300501d02401180700800980c4c90a20503035055840303c3d20988950301c90584600f051860401d110f4550400d03590303001c101502080101d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 14453496 1250 14452246 14452253
    0xd15050703020a02070b04050f120f0607120507020303071e020c1806100c0804050103020703051204060c0212070503040902030414070605041d010303020c0d02030309100c05010f020307080705090609040603 90
    0x303403c03280340007000d0b00404074003042640c20501a80c1c00ca400040900390504940002d00002003628911404e0301d00440b40c4a4083d1075080009a01920301940c0301c10b54605500134242c00c0750805070501045400c100203000055900c81c440300349240e116200c42800380c5400105908d096103880205800484283c0c0140113003001420451040c0001c0d501c50044c80301e1740504403071241400300003c1c0140e4090209010300d500c6a0701070140c0d1880707420b00303901d0190f0301110b031001c06000300d500302c885940301e841d8042c520394140702c408007010300d50105a041882e141d0b1110748074003642c05400e14842d8048000b41c14031524090f000300d400c1848058989564440703400605562190150060384180d41c002d4440c1020780c0e101103412250194090000d0b40b80311010002c5030b003e41d0300e092340c0c5880140000d002c5070341c41d410840c06800c1241ca510b01088950b181c0582507070380d03c1610a42151041c0200700304640c01480255000b01d003460000e5549800100040083c0118145107801034075008012041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 14454746 1250 14453496 14453501
    0x8041b050a060315080a08120403020a06020304050309150a09030615090504050615030d080601030903140f041e0302010804020d03090801020d02071b0807090902030a0b0c130e070504050d15050703 86
    0x103801d2044c95012000d48840000d1350380d401d91035000305442c0003003203c2c030b601c1303600d074450543c2061203441590717560f03011303916130509980003030318107690325000060600b255240c01c0794140b5440d1203080810f400c26030f04000c060021010b82c8805041c154803070b241c2c03d060010844a40020f402008400c1116007003604000703a840c40300b02c40c01c03451205940444812450b0000c2c02002d244019511952503907221030044002e001341c0402102800401416000d00315030502c050401d8810685040f5242d03441c04448818580b141ca10744081038910000600260f64041c1505034441c3e01600c2c49112001d803880d04031036080180c1d200c200e541d4800b29224101c0c10f807540007885514007031042c10b03059504081184003030301c00074400c00000d0380c416070f003c0002e020f8640100e048a03000406441d8105c0107a12122074000045a500c0e40000000421003010b000d1586400c001e802074001d80b080920b04000c2c082d0291040e4010503104440907070400e0700700f0440c00302e01d24554041715000d00c4281840710000c2d01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 14455996 1250 14454746 14454761
    0x6070507061d0d11040b0d1203060501050c06060405060d060e07140103021206011b080706090b010f03030203040e060607050109030804020108180c06091903080c100204050108041b050a0603 83
    0x2481c056a10040030b07000712507800101c0c82c0104182e81c4698555114020385a100d020325401035162660115141e5030451700e80310490040751944064403074408020200c4141d03400c4541889810710003004040070000b0340c19400903040e60002810785404d800510900390140c0000c2c02c0794107056200c000b942000c54808112059500d1030846482c500d00194164000c0f0303200000d2031402a40080d00e1903105990080990014144445450106881c0c2c40b005610400d0165107264a0302c06240c200310040030f00d140144204c1c007401900c01e0031954021b40302c5c400c178412448450050000b0460303555640c02103c01d038a61100003008545024540940003150441c1c00b0b07408a00e4480000303580c10120688100e01101c07070400342560081c00c408120b29070f000100b125400042124240e500f490141e21800d02841c02803c101d81c6882a0616072881c0c03a10f807140c942c03d01c900600082089076080010290484d031f1242d071442d1000d01040402500101d981d0085a124190f008002101c2d5015408101b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 14457246 1250 14455996 14456009
    0x80403080d09030f0804080d0c1e0e0f0103021207270306090203010509010213210b09070807090c0c020909010b060d091406011d04050114070e090601020607140d090206070507 77
    0x1244c1c4d040c3c03050640d1143c00481c2c020b81081c10400a10b90f40c52444c0d8000d955481007420f000480b658001243e00c1101c00800d807610200b4810003c0b0211490301441d1012040800d28055252141207000c1c86030380000941482e050101ca10440f5903c540408280984404491440c00d140ba55034240f80001c0c00c0880c5003640207500c3c100100f085982c040c001c46a50f0310785907610071016498044540e02d070303a50091380f55a410b05030400c2c5000143ca0b8044036801041c5010043c0b141c682403540f01403c1040715409a074402307180000c03031890b40f60061035006215070102c489203217035138030a1120fa000d011481042540b108001031400b003024883e03480303881454040c6805110050018188c29a0f4035028040c0038002000001e2025142c2580507000398400d20400002c45c00000740d800c2950f03aa41c040d00c000b0301150340b880000803e4200108501d601140901c000c0006043c2200054160350045001c1e03044060002189100c1100a4215030b4032f090b07016000385c0e51401d50703003803140c0c40b4503c1e030181c1c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 14458496 1250 14457246 14457257
    0x1020d02090f1905060c010f020c010501051203030405070605030402040906140717191509060b0304030324050418020a1202030c03070b0d05070c05060906010e0112030c060207080403080d0903 84
    0x78445400e0000c900e0324001c03c0b80079000c007001d090104211240c0c06c80160f610310b964861140c030740c15062500140c13000302d00703c0001250650615080003601722004070f05440d941d205004110200e000020076804a13081c3d820801c1e41c0e5259400410701a110b0307200d000d00380340c1c04c00755111080910b0300c0009114405a95450441a801011800e10759005607990071030807100108952030700c0095802a0102c854008640c00001c0c0d5075a1028107507003482e441b42c03001e1413010003007005040d014000c0c80014803a401c14001c2218003a044108290b00034020180286e9036440303040c031110b500c0c41d0009207060f00100550603407642e540d0340880845880004a000b4025580b8078034060400003000f2003662146008503041852001d007400040c100103200004024542021201080c403d20549009040090181000b0f42c1055881c5a90a00603400446401c45500c00703080401d9011501490031544148050390340c00d4141081130460140750005814050009249004070140c0d83c80a00c09510070b8444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 14459746 1250 14458496 14458519
    0x303190b0604030302060105130902090c030a0f05060d0b0711010e0705030106060503240d0605090a0b2a030a0b040e0304080105060a030f06020903070902130501080f060a03140307020301020d0209 86
    0x1400558042e6200050159204a005001d00d00c0c00801e03040c944540c246000498030240c0e00012003421061302c105801010000911070359510f40e0046180c01c40070039406000504141000c1011a1b01e030a0000c0c0922801c000420f115910401d500700200c1c107a00024003a41c0350b0b088249895941030300c500740c8698600500021054000c03015203215440d1005100034110f0300d04044050315482e602125800207080c030f10440080e0941c031030079000d808050000c0501c04034078034050301403540250900c030f10040250007800f081c0c00d19100e103403650000180c00c65140c1e110400340c903001d0320001e1030603a4814100681c040500f01d0000c060000c82c0c00e540d009000740c1d101d410601010301f855020191201140c8407220003c200190004d003114034001e0100e030b041c9039403010300c0c404903008021035083c803901c050030820a960340203c0300c6030408000420f66203181030100010b043d603002440001c00d07052448800310070b00401841502d00882d000380082d56998101101c0200941c0401901c6104104640c0d0713 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 14460996 1250 14459746 14459749
    0x6060801080601060813030c0215040303110106050a06030c0909110705150606070305070516090f0b030712030c050703120206010306060e040c0303030b04090f0b01031205030c070209180303190b 85
    0x702c01e0f04036509a152100940c640803180c0d0b4440d03000300401e40034060041950700041c1c513150710160500020454440c0c03100c1c2180b4004003c0740e40081c400b041c582c1081c50a20095940c106410102c032124200000c1c038070102941600e0269056020030451481e040340c49803038ac540d4000514480d07100b0426a8401c0701c214000c0e4901400030b0b594250050002c1c0030303650000303006030b00070048140124110b8003d50401d1041c40c0036240c0079007025040f640c03200e001e499010018060b66800100481c05440e015003810442d900c0e408441d4000b0341088807145c24002405418080c10020310b82040c224406040d0014020707648020a203c121002c600c2c000c0001115203070049442e010350b9100d500111001c0c910b86046003c1c24a203c020355019a5074600400001c40da0303403021a9040c481c0f404000c0d135600d941440b101d00c40100080741c0c00e000040080002612820302101d401c0b0750304495160700c907140c2c003a01e80440081440100c00c14400003085c8101c400c1c1543c00011000c194103400e001003680c150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 14462246 1250 14460996 14461003
    0x301170604030806010507020105040801020c010603051209150702040e10020306030607090303020606010c031b050a020a0509040201080c070303020f0324060405061b100c0c0c0504020f070b0601020f0f010606080108 94
    0x141d001d030014000c00f010a007658852402071034131500500d0842e080640742c0095608a0b88804030108071a95100005c00c104070040c8040300c0710408030401c0e207080c0b401c00d8021400300da426201c0070024084c006180e0085507600e0b80440281d1074584102c0700c035180108504002580150307201c41c80b80c45108001500c45110b48a11000e0b2a459809040640c681c640155503501c02c4102c22024880440741003058500300d16469014140248000d200c8110a40148520521281c000324000c0399108100300150740c210b0315117604403c0c190009a56808603090881c028011400c0c1622092400030601219240c21100c81000b6040e903141907800c141901c0420102d03119501c9240d81004080c8428546c802d0b5401100c0303099090710060355002d04130048041e0403034901103800b0010800c80d01d000001d0082c461101b40181809607011031400440380b5490641c1d016000700200000400b000149159100307002101c4c03840185d03000c4410039504400c125020b040c41340510700014201c040001211078000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 14463496 1250 14462246 14462251
    0x207061518060b0f0711031018021e150d0e0303041104140609060d0f1703010602060f09070909030c02090a020901020c040b09011712040608070e0303070b0c09130204090203011706 79
    0x5407629043e05039a03525244106074210079410b00549080c041d1100705d500641c03c092641c140701c01003c201da48100722040d00940182f0482d0030b0091100c0d070341ca8230f40d010010160101100340f9625104554000005020000299246404007000b0700c020054030600c4070f001038004450a100b07604200d120b8080001044a00300d84c410041c1e0302040241c144007600003030a03400f03401180020091500d4081036502c1003207001c001d001000004101165042c021503800030000c0c5200c00c05402c4c0b9402d070303603502d110a00030704c42143c0d81c1e1000300040501401014040302d40c09440d103030991030403210100081d00800709042c003500410410141ca454244208404110001d16043c01c69003005164607107842030481a000d0f910800d0b4089052a05840291000380070030341d41c0c211a03140c58000140703074122a91041d8003036402884008005000042007a80c004d04a40c01c3d00d40b500c0c20000002d48040310211805450740c800100800c10940ea50001c506036859606a649460300c40d042c40c590f188000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 14464746 1250 14463496 14463517
    0x603020711090604060b0c0c0a080a080a120209040c0c0327030b06010e0607080409061202060d05070302130f0302042d0e0a08030106020a0c05060f09040207061518060b 74
    0x100500d421514004052540243c0301400c0065601d0f02e0700000d4809501c00d55010000342c2c41595482402d19000d103544000d001044090420b403032003030303503000c8031401b690b003580c0d003440b0800600f220891440d5040e00c003810300c020001c1c0f2045003901b4024012500038003040e400124116a100034144012200501030004074451780c941510710380768040c0340300c0003802c21410400c92041c0040c45982d80d0001c1d20109000e501d440382e80c1c515000206086030250b07070158803049d481c1c41d40180035036900015039808a110311404903556440000c08c030024400e01f0500300034803003a000040344d000041a403481c142d03842550200a100c0300020011516601000840d803001820203548814400341c3c5c0000004510400481c1c9404240d07035a07074812600260840b00c01030707001805801c280312903d45c0003002040141d4000380750481080c0d14900920030f070504039001c0e54001440004011305540003980010400c00010307001c5403201c4030355141c200801c1000701141d01f000808103019401000b1200f10105 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 14465996 1250 14464746 14464763
    0x20607020c0a0b0906040803030c03010e06010201090b151207080a0b01090204030f030f03141e0f070203040519090c0e1201020a0c0618050f03030a0e0604020321070804060207050a06030207 83
    0x10f810700c20801075000d0070500d9044a424040020855400c1000c0c0d4019604c0b102c0c140d4a075810720400e840d503aa0020400340c11a8100300041c0c010807941d4401581080b81e0002c1d01842d0b002c081c000c114015146503c2c0c40052148100000c1c03103110110301c3e040031502c01c0f1180c1c07240381d13a102c1c80b0030142c1c0141d002c00381c000c0040d1407041000a003d400741c1c020514190901160158810b000e0050014040307801008101d003000540082c0b021031003456520545044c1c00300c0c914201090025039034001d0740200e5000720000b5252240701d41c0c051003103c0c020000c6002c10f101003a51910000c00407454074105a00901601c030501001071010700031b80d59080c46695130901405410388400028084900740f070b001008441c071a01d0040751040c414a0300c03503111400215030705d04180b0f4185007100c180c2d8082c80041d4001109010043e90049414114101701c056002c4400e000880040e4140c89980c200400302c000000e4000f8200c1c0c2c022032501f0841b6400c4900e6502d1650315081035090340b142800060046d00d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 14467246 1250 14465996 14465999
    0x203060a05100905040305090f0301051e060102010b04020d0c090f1239030c1a0d0c0216060206040201022109010c03090504060305010204091a010504060c0f060912020607020c0a 78
    0x150030791006a0014280780c1941050395180300d00c3c3c04613030040c1e4080d00094000600e841190604040d03003460428150000c100c039240858405074a200d920000420046040f004140d0f03c1e03200350032902d08180001d10465071a900c540c8c014004040415101000c1880010006560020307113048008440011040900c02031181d551071a0311b000c414803501c08a030224000d1300501d82d10020449440184003c00a501800d604000c1d00f1076000b0750009014501070f200690707000100c4020b40d0b0a0140d01040030441c1c00c400d5105900b0045039907074080841180d0400010010b070300150086c003a60007a004d50304a80b40c62040c205012503114040355000c0e0081045180d035510640303280e00303c14080d01d03002c8003041d00e41c40014150746040c0d2098495070340101d000d1107406484c1c03192100600d004d0000c628010944000030745540901c0c407600d814032480c44003540a20002c41000c025641d4084c0c1c0410040350301d498008274428146074860018801d01d000544024000501e40e52244001443c044066 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 14468496 1250 14467246 14467261
    0x302031203090106031a070e1002031602030102040306140103060f0b010f110c10120e01020a020c0904080d05070906020d090503120904090602040f1706060105040b030915040b1e04020306 82
    0x1e50020308104401d650340e90001001c10310020a40122040e491152020307802c0039000108000014403605103e080c0c44591301e98200d400200300c0d00950100e44075a03080c8004da000007802070203240d1002d4038290501c131200c44804070300d040d0b0038141c0b8890a801c001090b031155140d400c03200c010746e00501203082c7c0e14880c81c003036000304104c4040c40c1250301142c002e0100180403030b10f0340003a451290701042090045200d111b042c1c0c041c400301e002000c002107060203410000290341d030a28428031fa029642020106082c02480c200301e408103681400d06000c07a0920320001000c800d614400c5000500400076072a11681c07103554040304440c0006c009098103420503c4050060b8441d081003a80035031365880d44400a186070010f0f00041c4010f04448007110b04c0c004d0b040b40c84c1c00003801c008007035030080810003406a81100555061318140c640e10390704c2c0d50b1038104d000e24008020400c8000c0210340340c104810000c01e80881071180e20f4050b04c0c0210301010b007180b1038000c102660001d5041d00010001445c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 14469746 1250 14468496 14468533
    0x1002091804060915020a020c01020309060301060305071103130608060405060a141804060603020306070801060f080c0c0114011a040807031203060302100210060e01081b0402091008010f0f030203 85
    0x40342c051480041c00b5021a42e03084505040e0658051145402040c41d4041036010700a04200381402e0001d10301e0320441c80006000c030300c4140510018107030b03a8800b0805a03031044038000200c880d040210307a981c40d8403003082c0b200d030b0f0400d11810303000880c00c40004681c0c4c145805264060440075017901070507420100c01c0f144020901c124550000d411240c0203200030381072028130b03005e50b0107010700141543c114014142080030060002042c0710198004102c110780c0401d4241c40e0116518040425488900780d2310420721440610f207d1030360800c0e08441541c5520714420b4100d800c05a44107a01010b5244051214025403051564503049504204003081e0a645c4d026007034403061600099047d160b50001c0e090305c0f511900a03005030300c07100411861740b1852237110060016a901085250f01d070640eaa941c4400c4e04503a1130030400301d1000c01101d52515011785254610007040040000c0c80c0b8400100311440910441e00307101e110103400a4003100030f1088401b070342d4001d07001d0186541c0aa441082 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 14470996 1250 14469746 14469751
    0x506010203160b0a0506060c0d1b02090f06010306050a06050703051305030613050f03090a0b07150507030906060515040501050f0d020406080a05070206090c010c0302070503010e0a0510020918 84
    0x550200300600038120985074640803040c2c0c4103a0f07a2050a0810003042c070111640248904d001c0d1404120000c58000e0024400e6458180c81ca84441e4919a072407410300b480440d604002c3d080800c2105104100208181e007a2041000307980030031000341e13a0070803c405010141f0820f004035604025190220b0301c035100815000d07200310307000340d566699031020901d405000c41c1d0312a4040320011100d410024240051070002c0d18003c01141018105030015440307105910405c04208800500700c1b0400039016401d4402840c183d030204850300c2c1001003d07024014864003110240d00c0e10b4800f044078988820000c041000342ca0078241418104401560640d0200600910140003406540000070a50000f0005400300707503108449030500c80014010303914050704034025504840100080f030400060401a40602441c2c50341c881a81405c040c0e0405e0400c5e04401d825508041d00b0300089a00060441010340c401c1e42110324038080840c4c510224050540c1c150342c05220214035180c00d40c20b038299643c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 14472246 1250 14470996 14470999
    0x1081b0d0612211409090702010b03010603200604030b0604050405030c01180308090f0c010f170c0403140f03040311120604060608070b0f0913091202030c010605060a120506 76
    0x784a64903204a20000401003508448100e48103201c141c800a4007408090360700031a007010507542244003482d4949004418049010701004070000d8103052007504101082103016008210268032410f01d03140302001e0000c20902c0d440c2060b0980d0b10b904110081702c04a03904209082c810781c851400300005841c0151042c0c44030f100900c0015001c3d4028850300e600c8006002c400f40c102c158a01d409030181000400f0031141c0d800008440010843c049900320342003c0c00d281c4040d41d2816143c0940b070a090721003a40350301c0a8040100002c4060700d00c020010b981c021580c00011800750303c29243e4491241400c03410300e0b001400200b0005000d14505400f42a00504031110b5a04011080f8070741501220285d0390b00f516803100b00410074061086502829034040075030301d0600c01421810103846442001406000c0d0030100703080082080d40101c100d26800310104100300007198000f50f50350044079000300c2c070394a0000700140c246080b104a0780220301070789480103650400803881000b03040041c10907 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 14473496 1250 14472246 14472251
    0x5031803070203060f0106021c0509010c020a09020c070806060301020702010f0e03031209030304020a0608060109050d060908070f060501140a0605070c05060c0708011802010503040b040c090f090302060601081b0d 93
    0x10001070fa0103201c002d200b500003e0003d045036160010003071134488005c4521001854070307019080017580c0101264181d08003820401010700d030354404540080519400408024804200d141100201040f20400c4940704012500c2c1516070790101400c03485091030081c0801e50300c0310003030304030350007140900a03018004042c1d9040c05045000c0000004044070000201c0d01700004200443c0b4101e084440502200d1410503c0c0f0700d40580043d007440e03218014284142e19900c2072804100c0950854580581e01c90a21600d4010034030b031103000000c10400450f00c5a080000200f43d0201c100c00c0c01441090090a07003a049290480541d07882d40301000c01c0d80c5074400d00c0d06c0424152aa00020050030b1200380c004c01c05145000070031800c55044030360703a90343d0580740c1d01c1d240701503030340a0256500b007500100380400e540c440e80741010045046902480506003408030400e9001502d600915546002e502503a40d103648040045034000403c81c1c0107010f110a05041c0c000d0044440090002d100b0710f400b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 14474746 1250 14473496 14473507
    0x20c24060d05011e0b0111010e070b130f0801050415051006120e0616110102161212090308010905010e04020d0602310306061a0405040504020406091404050706050a05031803 76
    0x686160a01003410b02d0404e544a15450069581c40444e001e03030b40344010002c1151800e07040b2410303141d170b105100c4c244801c07c0108000d1110303510b12100c0d05c001d19102d1800305241e950340c004140681400c1f1010b69070018884121507010302c15000d1248180551074041001a041403c1900c86001c08000804215511000404c0041741000414001d58520600c64001080210000d00400800440c0712803070740140440e941c003504803902601c043d5070002011141c4030f101942200c14140d80d00324143c6042c24080c91509143c0c1110030b03941030300c0c0d804c0c005020903a01d51540c044860010b1300e00035001a40c54041d0000b00d06668098000340503100710078442c40001802c2a10203c0c400c0c40344088065541c1c10400802c54103200b4007000b003c2000740903d4080c1e072980e40b072049002e50300c2254011903c0301e000404561760359001e140500030700107003003018094103c4020b2450b041201c04440500c1000c101007551405101581c501d040c00d41c2d192841c42d5078082c86049000c021880382c00f0503110a212 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 14475996 1250 14474746 14474771
    0x1081003050114060405060a05010c08070f050304060810060801030201020607030e0c0a1403010606020d02030d020d0f02070501150501050301050609060d060b0a1e0c08190c02060d020c24060d0501 86
    0x56400d00c01074940c0f4061250074014100011200301a0640380f141c03c81c03490400c0140d81001e0202000381d080700c00b9540b101070134200400c010b48908002010f5000019011401c10b0704460301500800d240941c000d046500d8081c00d9400700320a01000e80541d10080005030b5480c0f182c1c1003c0d500c0080c010555500c0c00c0f5480214150030410b07000340881d560919001602c50409100e900c2c0101b030180300410400f114001e000e5241d20031009101040e0f600010003048616041d00807140011545404660710203403428858020714250b591170303001d030050f000c000945611400681c0d05944008080030303c3e103800c007820030625a0002d440009840e413209000941c05414031301800050003151070b002050300da00d03424110303028440c0c2071280500003440041008140f0032400d1791030a2012040c0d041d00045140c000b511440300f0341170001d522581c00552002d1241050b00502000c0c0c1c0175104030750000b02d103c1900e200181800b400c00200c5039031400000c40a290a5440c814254024400040d00903500030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 14477246 1250 14475996 14476001
    0x905061605030a020a14120301060f020312010e01050405070206010f090e01140a02031b07050309010e01030915060602070905010b0f0a050d060e04020f0402070507031212020310051903030c02010810030501 90
    0x51241c0142e002040e45000b0b000140c80700040441c1b003280900b50941104515101e58001030107000304000d12030059014841c000c200712186202c502308280e545603550051000284070900409006506200204003010300002c0c2082c161121000c011003182c0c01c200c8410001d0442d880c01c40115074884000c140c6005145810b180a5861100e015a580c54039058082e2440c054850092040804110810202d000441698002c40003403030420746240034270004901038100100050001d01d60551114141081c90b4040c0741250340c0d640a483c02981c4c1d0b104003104544091260082c40ea42c00c000c55841015000c000340008901c0c0d0400f1401c0840a0310207004907541074125010f542d003004148015403410841604400c2d10480e4203610b8404142d45107919801c4603c402040b1041c03000158980703502071000044103000f01c100464591070240851040305049104190142e0304c082140502a007840001c00203903a010b850310740b035001c8543d00445500070010302c0e5900c807000148010002036000e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 14478496 1250 14477246 14477257
    0x4090e0606010201060e0108070b07021206090a02010807020c0d0602030a060e01030302010603060609020307051204080408010f0f06050102070f06050d0b0a080c0306150a0303030509011503050d12020a090506160503 94
    0x104014021450301c0c80000e402c490240c0c004410b4004000300411480700001441810740d03181d020000d4581030030303101280c010741038038909c0c08d114003c2c0010841e00040c00503000e0b0b400c41c004d0707031260000d451b05401680c49104000107260043d440c01361400104040313800440d00520b035984000f500c240e0340c55002e007115100707030400c40050751520000c1051003414091140035102100045207141800b40000e03106100e54561040c10300700d41700005050202440c00d90b0010b00c00311000780155603144000e400101000748405010600d4041d0200f00d6502c00100c84081c0d41d08a450400520309004013a103075600100010b401c501d44610141303116490710740f441001402014002c03c0143d520001b0103050200042074142090202189000300c0d036a10605001241c1e01070400140e00e4446c110914050101a0f41d05803420b0000708001042100c005a00803003a0119903a0a2901b5a0140303100240d10800300b41c08000350300380800340514034102d0000c0004140740d0202030740f08801039480c182141c010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 14479746 1250 14478496 14478521
    0x30403061505030604030f021513120905061b150606090603040c05031207060b0103090809010309030203070602030c1309091a060102030c0109050d0306060c0b0a150b040906060f030203100611030409 87
    0x5011500703a10f660108082041049c1d000240c190502c0c01030044589107407d114050101e8039120480d241c0c0034000c402c0c04010b854043c3c0038503a00c140621003803e0018007940113420302d03c5165000300f03590f840b0006190050302c0c0140807601e030000000c100052500007810a03921180244800922a6420040030744100c440240b2540ca0b0030303840c1004000c88401c02c076030a06160400000c0c0c80001c01c0c080440749411005d080c001500c18140c24100d203103000e6400f00400d00c5100000b4001c001480002900d40c041208004407030098407071070044107a0700c02000088c010940c034054102840003c3e082c003940100c042c8100ea080c60038003800b0300e00752011848256099045070200d0b540301c562501845010382400c0c200300d030b000245075680f0901e40c0002030040800d40d64a030030903921500b80c10345460040002d0340741d4640380ca803101c200c0c800400c001e21588006c16100c00d103c4100034080d009a0344107440d505541c8102e03500d0030074103503034003041c4810200c0d540c0010000414130360f51621a00c0c445041e07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 14480996 1250 14479746 14479757
    0xc020a020108090a020a030303020f04080f071712030a05060f03100f0e070b03150303070206040602010204090f09080319020d06060201050612010608100b01020102040e0106080f060901060203040306150503060403 93
    0x56030001402694002d00080c940b40c00080d91440542c442c0c0b0b01365001c59915160069688007a401840d9480c0919040587d182c05600c48294400c00001001005d85400d580b812203125201c001203640c1d240c01201784040c00d0b106000050001296500c603a901c994003078102030a4504540c0001e0419012050408040f03940700910410528603100c0c903d40c40d52480010105541040c03005101ca0200501c500750690400b46841e1240c0c400f030007a01c0d4110b50181c2342c1034031584c6612004c3d010b50031034040c0f072404500e4514240e00c038401d40d00aa8211582002e40d540c07440c0c46041c10900c02c6549210b0541401d0340800244440100c54480d1306c00030b1003507900000d818102a0104840951034203128181071381800030501c05045c010031231981c12200c8507800944803201d400141d01a001d560700801044c41c5200001403082e81201e00d1074420050000d000480f90749030000c0040c4141c0a0040c1001030740140414000142103038007440150001c00401802103603183d0000e4503105040314110b0000300c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 14482246 1250 14480996 14481013
    0x40605010503011a130e120a02060a0204121209050a0801090203010e01020909010e04050f0607030c032004050d0f0b10060206070503090d12021b0f0d020604020f010809100c02 77
    0x4510520340904422002800324102040400242d0022a403409100340c0c00c5006025070070442d035020f4903603a034680701554200800b2581c090505d4000704040c5001d03006d4080081c001042a00c200c4099031010b4151084011303003510350400030007006094000b40303c0f40d140042034658410240030002d01c6040c0c00820b441c0075a03c185800e4440140c0012801d81c014000240140d942680242c159001101120842d0b40c540c200b0740d10307000d048000d00015000320020b000351180e058004844600064600b8090382c1da0000e50303440026800f0b641c11202a80520050015203400c0c408883d24502540c4080780e100101c2c6c82d00210301d401510500ea511413110020080d03243c05100c040d50200050a2107811480c12040e07050311000e407150b0410404c024001c6650b07120303005505807800c5804003450220b1841d410340c040b030780e105020224000b06124403c45155200d01c0010f8161080381c0c060f003540c0c10206a5001541c3e902d00c058040c0c42180100c95a501c1c1e00c95561081007814a80f95005100e003c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 14483496 1250 14482246 14482253
    0xe1306050a0603110301030b100e04030305071d030a0809010207030c080c03010c17010b090d080c0105011a0c10020d0207020316060306090603030507171b0a06050903030609180c090c0304 82
    0x1e0080350b20000600d0b0520303c030700301c01c201d0301c1c026241107d80141d00442683e8580001650b03080c1950000d1040d162200107001c1490b038164403503449060f05445009403c5500d064005040b402c0400d004e41c1036001041071000591040090f161810060045038002c50f03d07a61403d90032030709604031040c254000707000030180c3c0c6000d000700081c0d0055420411800f5083d50204010000f050140c5401c42000042c00c00c07450b112003082c54000d0b5003000c0030513104d41d0462222030103440c0a11600b400b424400b05a10580e03d150b008450800c0b0707940b00240181941e120801020b500308020040a03158240910340240c3c9042c48410000c01e52002c800000904222001d0108c51003500900b4109207410001e000094001c01101c0c1d0181d002014071007061090000d9000f544505c0102c1001c5210310710b0185000c9100050764003455205031001d10896030380700c07219035590108503070541c4d10400000100e680444900040c141c40700c1c200065903d481203c00c04500c10880995810703403e040000704100c1070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 14484746 1250 14483496 14483509
    0x7150501050603090709020f0702040e0f010e0c0609010804150207081308030403030806010c0c09061d060409111302190c060b010c110f03030c070603020703020708070503060a020a0e130605 83
    0x1405003100c0c158190700f0605a05540d07618175010712510107074000b484110350280703941038800d141c3d402001031004071503a900e0241c83754031401c0041c01641c2043c00e130881c4c0b2603001c01c1c2c0165240014008505225640300112411500a081074a0a91104810182c001000e00040c6042c3e4013850340c10340d075403100b42c2a0113400c00050340b00702c40c9034009110501c00603031705c184607640000f0709180209171078040f81000c422580e206c0d80702221040c80d0402c0020182800c0107568905411164502c0c4681d0b40e54003480190740b10303076000510000301c4540066240c500322036003103503036130301c3c07200041c03c14045146201e4a01052617005011030010004001001524029541852000e180000360007030184d54415050600c040140e100c0c50200e008191582c074100141c0300c0c0103041800326051140e070346070064000d40c4005026401402a4280800d00010020324003084843c00b43c0101075030b075a0030f616070b80250010405c86080120840d0641025034400398107940d0081d1025001654524200c2000807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 14485996 1250 14484746 14484749
    0x30e09040b07141905180a23040e0d0311070b070c0b0901021c02090f15070309050913030c1a041b091404021003020708030c0403060c0306050d020d03021207150501 72
    0x1001d404102c3e9080780b03004d40c40d502e4107980107810404e8603000b81d1b01d841e0140c80300d15000e0b6600103000d61000141c40380c007454074810b080345002001d1442d494034800d210035180c502c041e1040d60780c0030694440a4a10035032006100f45001100f45040081c16543ca500d010020b503191000507540f00008014800c2880700250044015802186082d1000e091018158034243c110305440c0c0c0d01081d4840f00e40c98048400c1684400103005c40c460000c42d01c0c0d034800f141c0090a080c0c0000d4004003020450b410142040c50040340064152552503005079000c56610520801c100d41741303144c284460300205900c802290069102e14070480c44685020321224403689241d21800a00341001c20122501b4035101515070025010349208070141d00102c400e50180c07041e288001c1504500004001e000940200a4804c0d030348502d8080c40015641d110480541c3c44600460368000c5104007032000601c0c0c00c007401e400040c401e0055820f00340c865420080c00b60000380e000c1d5007035821710640c10350059091150b41e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 14487246 1250 14485996 14486027
    0x2030702100b030d0f110304060203040e0a0b0a030b04020d0c0902120a0501050f09100e010605030406060504050106050f031305030307020a0c0509090304050607030201020f070c06081302010e0d030e09040b07 91
    0x101960b880000703070b901c4100150311814802d2016189482c1071149441001014510048030394440e5a480e00964a1707019104000c45588040042040e20085c1d000780c00d11384800500c122006411500c441158a0300540b0807640124152006800180702c51851070041442200041c0c84102c901d80303606c06c4140052000c94030364a8800148040e40da60000c9442540c410740340b40010740d440151010303c81c441c036003203034203103040f40c400000d90141e004005600c114802c90f41403003d036a86009200c00c0d50001e000f5000804c0040c401401c1040e04a40510b0b48080144c8110300e1810107510b4242c1954400e54003c40140c0100c1500401d100500794000b00404058443e0346c41498590350840e224003640c0031740d0f403055100050780020b040c0300350181c030b0112955400444d5184514a040745040c90303a4802c2c0400700d00d8440000745121005004c03896040e0b01a12001883d000301000c0120440c030030760088080c072150104141d04c40d218100694410b5100d691210039030700b4040e00c040c1c51030603c504181c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 14488496 1250 14487246 14487251
    0x30e01090321030213030b0403020708030703020c010e0d1505180a110f03070f140103051609030201051c110d05090d02120304020406170a170a0c0206090a03150203070210 75
    0x70800115140301d002d01c0100c00e400c500c0031106441000724082d106140c03d1184540c038500700402032008550800380210304c00c0d021903c895640c4c1311056186e00a0400182c056048540c00341141d501407403001c00400e40092a00f655001590f40700b90300a22002454081c07981e90b0800c000e00b640700c41d011160300c2b001e100010200080a641e5095109101035840d5008840894139541162000c02080700a00a00100300703402e503071a42c2d0701c4803003030019810f294000390802c40400c4c4804405041c03071503a00091b81d1540001070454005503815800042840c3c8030084c00c4818241070541840303100c000b4a405603c4c1544e5121129104007500c601405411320354100d02440b098031f5800154890401a17060002c07912030f80c4070b00004005190684c06031f03603081904000d00030300c500b001c0340c1000000c2c442c0282d104030094050024882e40228401c900120320440a2800580380403c080d15507442c1c0201502406d5843e03a44512102c0044003800003c079401000740684660140a940740c0c2140080c400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 14489746 1250 14488496 14488499
    0x210313170304051c0c030209010806071b0201082e08031c020301060f0809210a02010f060b07060509010b030109150c031e05040302070503061e09030306030a030503070203041a07030e0109 82
    0x80ca1541018a61480c000d41210100040210380800c6900440d0024102408d0790b0752040c2c1c07503445810444200000400079004811000000c502d1010050307010303034600b1220f94542500d0605043e101800c44204c003040c9490303584500740d0880030303006001c09002454031802110100304290030b12604117807003580103100501c07000b980b00c1d0402110709054904a012074032502d28850030003002c1d10f909210000107102e0f28408400741c100504031035800f60b00800c2102d55030ba181c3c3d000c49151740a80904d80404010350000314801d504400e81125000300001941003100000908607140180e049901d072048903414102880d4621540001c0e04a0307050600400e00c4030001010340c421051000350005a481b0041001c2c54130030801c09000c3d1001404440c03007030174230200401440f47c44410098510814000041459801000784c0b4081d0704050003c0031500c00c1075405650541006015804620042c4800103132140008891001a8044030442d03079209070b1814000e12031804901e0b004e0610400010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 14490996 1250 14489746 14489749
    0x114010807033f03060b07060204170606030d0c020103020c15010509101203030914010603030503060a0b0702150714060a0f060602010504050705060306010c060203010806010501110a05030921031317030405 90
    0xd02c2c14800a100520599200103c01c00760002c005036040807298032000300d55401000a6640104103491402c81c2840070420905181692490120341c4035826801c28200b030b40a050040b149810014414140941450300910a05241c04400818113a41c20980e100401990600300d84076900a003000126408160402c1c144460a240641004013056580c101600c18001a9605054100c20311002400a50703924180100300390000d4480c42c4c8101110b95000461018001c21100310550242a2000c41a5a80c0c0d030b6045c150800c2506444c0800c09190740c0e9007403841401198440c41300d42c10f000800d0041d0740b001c10119080d94022030290380c542428840820380002d000380446000716a22940d958803900102d840424401c1e008140500110000c15480d0000c0341c80c42c1600d80a90703e0300380707104140031066521040384030050300f00d410030003442c42030b41046102e01c1c0030041d4a48401c43c1c46000c041c80e181c915441544803e4184132101c600f4040c085082c034081c0700403083c4800a5042905140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 14492246 1250 14490996 14491073
    0x70b0106120f1401050a0909020a090209040605090703050f16120519020703030e1207030516020d02060f030405011104060f031a030d050705060606121503011401080703 74
    0x103036030030300c01c1203181e04566008a400c0004200700114050103141140602091062020300031284508032081e00480e9200c194820b010384543c0084c00f203c00c0600e4044080300079032000420765006900c504011079262102d4929074029a17032540c3c0016149003d4074810000b24015004203141c96260080c103403159400500100f920104420006664482c05204500002c0b251400401c0d24000b00d043c034241034040d03008202035000c407401d4036030100b82c4501c240302c217100e000001004180144494020001c0103514560401e10140c15426008030a40025405400c40203412815220020801c41000f60a001d00c2d41e119100c000c12a00307150078400040c1445402c84085420950350300da220565a408001090121901070203903038901025401c02411a48455010345140c400c95001c681c160030030070704a0707103446400b0195020540300c8100e0716411404080080354150340340c84072003a4003104d8030b03901d86c000c00c0b4100080a00c640765181c1640c43d031000d42c62844a80c5c000c064228018401d45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 14493496 1250 14492246 14492249
    0xf030109050910111c0c0c030c06020c03040306020405040b03070b0307031802060a020106030b15010203090409060915060602010f0e100c020703080d0c0908010c020a030f17090705040b010203070b01 87
    0x140d00892590385010116190402000c206034a0f0f82c00c20110b1510505154010102c5880b0585034004211500d44008180c41143c000c440006105080400210380300743c80029000d4400c0c48050700c0d140320100d03001d14540298109a501c0b0f90b000504011078a0144109008480190060180d541c0341408103032090000400100a140d1070b411030031030f007509104005801603801404651507403a0110020700a090b1400120340ba0080500842c0c405a0010f22490314004140d00451038484c005c3c0602025000414040701c405454040490010b11250440c2c010440300d003200254152903c80d0080c00d607000021100a05890402c0c14003500c0c00109072019100008000464008104142246006d1003540060910b400c042030401030f013299a044441824441d0741c40803d0151544c000718200c603100d4034580050307400000c00c240024080c5002500440d1542004c011141d4040440512200d04640203000e5070010340742030019103040d100380da0064000703100a608245e0780c2c3d541d185070750030103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 14494746 1250 14493496 14493509
    0x80106061d0f0a0b09030a08030c03040b01080a08041a0409021801020c0a0e01140109150201020c0105070f0503040308100f0e06090f010302180603120d050603100c1b020406170d09050301020f0301 86
    0x10000c5146c2c400b004042001ea44c840a096980c2c90701040d0948130380c0003540c2c211000b5842c0000000c030382000060303000f00c403500546078a240902d41032000522001040d07929115103c01e00c000604515548003400c07082c1045841e040410000000090400c0c1c503513030f183d9104102c513234402d004c40d41d42100c003241545e41c5550302140607094080141c81c2070003107901202d484c0c807000303515079905641900a44145010300c4002c0c007450b120310b503040d510442040c01403000202d00303000060200b8460304400c1d070440381c0c444000c182d041e1500d007208840f410a811001e9008002e0341400658202180c07004e50190031039860380045d50542c0d0000b07000e100050341c041150304091000c128183e800748000c4a001404040c0280d960380c2c20310b110409040b0480f02c00e0312a000f00408017864141500460707007041c4a0b82c2d24860405421a0090351908070f6450680e007103656000041b171035180410480c882c50305184014800c9140b50000105401ea003504031030f009900511040703001a02c1e03c02603d064445 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 14495996 1250 14494746 14494769
    0x100c0b090f1209040b0307060c060b03010b06030408030612060c040e0c03010f0b03100e04110f030d0219050f06040602040519050108010608181516030e07030809010504080106061d0f0a 81
    0x80b100f0004015148105511750305014a00c000100145c1210160078040d1255505100c04e541000805003214011a41c1d280c0008040002400052059000f5540020020841d2a01880cd5414645000f01c100d80d1454000d000003814803c0d200c0c0c1900d21a03004d01c00718109441c540c1882c203100d24000c04c510a00711244c1d004404a03800e42040302280c0050980d2016450b01450305007004c4604482c510004e6020700d04185007056503080218440114800030f400070461601d0720441d044404031402019515400342800c2e01c4100780c3e0600c10140a41c5c0540740241e1210b0500080105000f4009403000b004186044208a2a6041075200341107490324109400d007a40e5041c1c4141030b02c400c40442d040180550501c184810407003860583c014072841e00e030b00e01c0100d001c00082c1c0454050072210801a40000301c20400152010014611400c0616100341015030f031368005401d41d00c003600580701140d511140c1c52024481d00072003d0f280d0804492186000e11040080f9a400070103000c5c0640440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 14497246 1250 14495996 14496007
    0x706052706090918030c0703060c02031305091801090503030103030f02071d070c0503070c15090308030103021309050303070f02060f01030b0619050d030203030604060e010f0b0a030902100c0b090f12 87
    0x490001034002c2c5444c3c1401902d0365052600d500581305c1075980021911207180608041220b44000180c3d8601c60b45004230244c11800e04040002d80b4400030000700d0510000c005c0001c0300502070064a0300148140015500e0b541140341c090180703c1d807117004e042103602078078082115081d5a90400104680c5643c0850b05841d00300044441c11001800540a4400045c8080400046605071411180c40400740314021014400489000c0410311020701444018401800545002910800001d0910400207900300c280d03551681950030449205000c603503c01106a8020303018803041c0c0d4481e020010810702da40c110f0f0303546824058040d140d036000e81c0840400c54020101100340c04084d0000401416a50f0f40c0c030725000307603203600854401d401241400b03000140030b02c0d0700a48605071480d022071310320924100500002ca682000c41000105a22184500d000d030f21100c0d82c50404142039038605c9290400750802e0ba406107000b80200c9070070340c49080c0031200b20001040340f401c0c0c01100c1f006d0341da644 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 14498496 1250 14497246 14497261
    0x30a03020c070f03080304170301120213020909040506071421100b0c030c100c0503040803070c06060f050f0d0209070e130507020607120501050109140d0507060527060909 75
    0x100440d044503d011512039404010300c001d1102440c4143e03c80c10000c03145412406c81e0040d580028440d090380010644038200040c68a003440180224180c1d600504240511000038180c0f01c0585c0d090306c00f030300010284600243c0c0110b00920740002d501040e882c041000011061041040301a070500c4e20103940468840e400c0c20318104008c10001041030380b100704001c41c00351a0ba210400c40c0d01300d8072821101c004444018058001c00c0c40c219200c1c07130308540d0b0703d0b1500d200c144c1c0000d11610412a844a454001880394401d5034040c2040b21034010752981400188482d42c011600c4d117a1003920480445401a0384841c015039003e851440c0000c01c01c0849000f00c0c0d140702012400c91015800c1100700110150700140039480391200313a80c0d11409195282c4148100c440a025083c0021080001030141010614019012203800ba10744409460b203a08c9843c1071410b5a00280d00050000403422054480044943c4200404401400400b01454000341040c42000c0b4050301401501c40017401c036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 14499746 1250 14498496 14498503
    0x206010b0306060f0c0a0501151a03070e0307030c03060515041505010f0c060207110913050d2303040c060810060804020f030c0d050708120a080a0e010e01111902030309030a03020c 79
    0xc044500040f1003103d0340a21742035010705480030a27103030200d000200004040503814410140c443d03e4101c01031a41c2c880c40001c031a1181d0504206816102e018800000516140302d0380c8000d6016400c001110f08141803000143e828030010f42e4840ca007800d41c1171448424030740b0700f40225042424034041c04003024106440e442b50f5124060000c07071002c41c00800303112a007940b8500c2c0807000c031807a50ba95a01c05428048060300b405000e00940c0c00100c1100c2e030b190060030a03580034041c01c6400e444079008040244200c1d4801c540071583c102003e04104030480c2c11000c015081200170310f41c14403041c1050340041180c80c0041020b4404e50800e01e66400946081c48110a101000352803603103000c0702418420741d05c0142d8842c2a85500c99012080302d0480f6060a40701580c502340e940c070303070140c036402c010201811145407401120b55a500c503601500800340b00305042c502505041e542ca4190020004050151040100055420030010020344090200459880c80e00c181401038440007148141841d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 14500996 1250 14499746 14499757
    0x302030d0806010e0a121202060408031308040e0a0c0306050301060b0d05040f0501020a0c030219031b0204270201030b04180f0804030605010909050606010c03050901030e100f0b010f0206010b0306060f 88
    0x5c00c09482c001c04200d40040005480c00d407406a0340203001d1403154541241d50302030481d40948038000c14400300f00b8905c0c10440c003000d820301030b0702681c0c242a11184001f8605c0020340d40300380c0d000c0d030f10b0b0600600c640d0140509001010b04900800443e850304001180601c545c25545000a0341c40c4006010045400c20800b00250004021501ca0308401e00c003414451542c01c00358094441c4d000003540b2503c6d50040940b185602d9620481c0694608c0e00721640400b060000b26401526046401145181000f00c10201001c0742c6100e64480c0c414000075003200c05d58020f20340107a05000318201034254403610342c1c20141e848080b011820aa9040901c440d0003203410040c07111b1308150001680188681024101038040c505448094660100544030201c4240300100803810510000c0310310340c0a80e010b42c41002082c001d645440030107507080e108590302c00b880745201c555503142c140d030b695038001e9101c082a5043d000811540d41404052a4940801000148030f40700002c1c03039985000e949020b440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 14502246 1250 14500996 14500999
    0x90b06040f06030509060a020c07091107061a120f0601050607021c080d11090a050907030204030c0e040c080d050717040302060a030605090c0f0906160f0507060207060503010302030d0806010e 84
    0x21981c0d500c03600e004000e0070303060300c07001410f129603008109085064800c48a0044074040201700d41c40c98110280040c0c100702c9903003901e900090002c0004035940b0b000b6044455180100300c01a408180701300007440c444002c800c0176562207848210040c8800151007030546030110360403911001c41d171000070f000d0046015801e030714811181c00f10040100480241c2400307a203504013408054010b1000d1490740c01500d00103940a0b01d80d8600308000e040282c1410b40280072480e002d4906074890321003242080b400e5100307400980c203c208200a02200b00003071405003c0f944054111141d2848004001d400f6504028184c204d0b114116004411072100700d034025a4040c001c241c80310740400c03028002b00620301c0703000d0040400c07000203943d41e05803d04481c4910100d45445003095120028050507402110300300c031200c100085114086654201c20f240c0c6c240c891001030500e1810000001d00f4100c03a5401142030150510040c80180c0e008140807a6014140c0b0703003200550b6a000048032844554440c19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 14503496 1250 14502246 14502269
    0x6050421020607140f0a030b0f030a0809180106020d050a17090a02030d020606010903060b060c010212070f02010b100503040302010b09010603060317120c0f0705030d0204030506060904030801090b0604 88
    0x51922a8020030014403c00c0952034840741801c3d21a44016144255002c080c803070102000f890808901a0b485907140c40f201404c08000c1d000d42d80c0100c1e1508402440603a0544c4002c10b08280360300e850185002c01d145000e070114080c3d4900a0041d50b6807405c594548107010010400b80c0a039881100c10f01040c0401c4030900800c6d00b05040c00c80d4440040c0c0310183d000340102c118002245000240d41802880180d44109541c1c1c034513203e04d0b004101d40c0b11420361001d010001603010a400340050b12150140d13040892643c1045600905044800d0b825581035904050321f07000e042e40c078140c0c580540440f900304240c3d280d950b4903040f401000e541d29001c0d803003103070781c80040303042c07541a0f104c1c41c1600e105204086c943c0302c0b4414105c20902440d02d4181c104000c0e140099101100b01c40580349131030b00e40100c02d0a00810381d4031181150002000d40f60319641c0402c080041c00010010340f5088070040d1401146410144c074000c2c1881414020003201d191150300820080c2c40c0c5404940041c260746202 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 14504746 1250 14503496 14503553
    0x20c150a0902060a030b100c05030a050d0603080c01021308010506090406090204150b0c01060605030f060613090204030b0a050106030507020c0405060a0e04060504110901080316020d1b0e070c0302030304060504 92
    0xa401441c42d02050b07802140702e0308841f00003c0c003a21100d00c880e0b40040003941480e2006c1d00c100c1e4035920900d0038421554603940d0000004000c207010385581182e220025850b00840c61000349889021703400800b56a0414040c444180c617404000b9070800c1d080310000c100803101c0d0011070082c0908883d0543d412045020028080040002522885440340024841c030307503a420044506000c107840648166035840081a95494800010104203040010303000c1d40c181e131202214100c0c1c2290740309a9440340c082007081946540c3d4441d1030701500290404105a05004400964814480483c0d0380203035034820100300b19607111003602000340010035001d0120300d8286009409000141e8080311600e00f5507051421a161103410a4161084100114201304841c16902c07148002000d00780d03001075040c10070ba40030078001c0c152040c0c2d50000180740002c503481e041008005000c000c043ca8108070038003040d040000c0d0f01004407600940c110f00041015100c1d030030200070152104141c0c62010750303a0b852 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 14505996 1250 14504746 14504767
    0xc0b0a0b1507060605011107050f0907091d0403021212060d020307050a06021b03060103030c060515040203010303051209010b0d02060f0c0d0c030806010c0309062001020d0902040b04020c150a090206 87
    0x100003a05d400b82e940b00054544000c050790703909994081c1c964800c080342050354960a08486081d480b900900d0452001030b0744041189143c820300d04803201c034a450f0810072013896010041c000e1b48203283c2d07038070350710b0501c0d2280c014051354070203041c16104401c051030740025580c0c100080006000001d003c6989035681d160081c1d44c80104030a203440000988401c0840d0349004264141246d8154031540403c4603950b440000811009201c040c00c3c910381d4610503015100d61002c4d6020b54441c0c2c0b902580d90180440014099600400c01546a811311041200b281ca070700c40b004d2049681a40c05a44170800001a5850750040c00e4440d901d920035011b1003c200c03503100c0055201030b4062344640c00d071a1600c00045443c8090f16201a0214407419002c00140f8814004040c001e65618058101f290201d01442d00b03980c006416010b00d0340e00d560341c4000b0351409104240c482481100d045161041ea80030b25034441c1400402010b1003840b00001070080c0800b6005140c55a90040500b50384104000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 14507246 1250 14505996 14506001
    0x30b0d171e040f0608070912030c0b09010e07050607020303190314070207051008040f0210090807091b0c08160f0b061903060c11070b0a030c0c0b0a0b150706 69
    0x603401c0c090400038011241107800d52030200c40035201c003000f0311a1098240041a109036501424a80401051100004101504903003404546109541e03d001c5855141094002c4500c0a801d00d2102d924243c0f20449112000825500710380080d503c807511682240002030441c09014800410101449400380780b00398141c1c002400b81400700711882d003a8645681c01c0380c2c3c0380010702440340c1010f5001404110030307020f4240d180d4003606c21103600e24221300700d80c0490701d000c90b40303c602c0300400ea8000e01800001d10900c034202c083d207003500080002600407244d50710301081d00150700d030078810b5015461041c00f4180301200e501030800005515041c2a030702d440c0709080440311056035440002d001040ca989020700c00b995100001c1e01100c4e0915041d91100c1c2c0003040d42e0400201404a040d40722000f07081e007441408002c2840641c500d440e03840c0c1100140c281c8021000200400683c00c40e4000082d404412003504060720710800500c0c0c00442000c50f41d080700104101750525004200390f402c00c907a94 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 14508496 1250 14507246 14507257
    0x10204030c12050a0303050a020405120f0d0c0507030f060e0303090a020a060e0f1306120b0103140303090d050a14040b180a0503030d0504050312040c14060307080106030b0d17 77
    0xd5600d00ca8003603903602000e5803054603960090254001540c11030100c4d06c02e400032504040c442400501d081d5403000041e415915211340082e00c0e030082940030201000078025040804e030302d0f003464080d1a00b02e65030b2640f0b620b01404010100d202d0100614203000c0036a00609130f003920881129981d0400f85802c1d607039003400000403417154410442c0441c05e01d216181504020401421007528410030300d00308540b141c51140c1c0701103119580e1000055100103c1c04610b00036028070507246065066003003001100ac5041d07a8000160300c2001131140042c0c0010340e40300041d40360324100f502e6001728401261528040303945103004c00400301d000700e00385c2140c60044c05014020703400c104010300c0c500d00380301440752188211603050f003051003002c1c1d5501071a0450b80e40a445101600e2400c80142c1800156403001e650503282034a980f2018011510b500c40d494804000484003c1d0030340c6003210b4000d18010301401070008141d01e400340c00e4a50b4440920002c10507038803250b5440900401d01503400c83c1c4c3c202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 14509746 1250 14508496 14508503
    0x60e0601120c06020304150e01230c150103030c020d0611070b01170a050309041e05010801090203150c07030c020609040e0102091507020a030b071103070302030306010e09130209131401020403 84
    0x41400243c1a4000001c030707021503404c841594a56041c1c00416205401c0c3c000b0040d06004a4404100030481031410307001c45000c007580440e41f522170807001c0d1450451203200840c1c6802c007642c010700c08650040400e084607941126817001c0c181c920300e01140940190700074142c80220216030711080104101845050b5003843d40c0030030b030422a854400b55185d20400f00a000c50304108030781c03509414950803280009044a215070480d00144084e14201e079400d0303110a140d0313552440d40304114035051003030106001e0010300302515801c09900342c003c0d81c803402c0340040a01100c80c039644c04540314001502da903884000d008000109010444078081c0d40105000c0e4841e6003460861240c051556050b543c582e07802a140c44116810759541003003800000c0d2805003030107480150440f400f4010801095010722035030145469061003030001d44410a035008080c41103000004014011007091144c910b0142c044a13420100c0e101e84001c5c102031120510060f140300741d03990025001e000305400070000c4921 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 14510996 1250 14509746 14509763
    0xf0f0f03030b0301050f0105060d0204050604090f0501050d0b01050d02120a0605010302030d020307050a0605090a080a09090b0f090403200703050a050706110303011e090203041a0a02030601020c0409060e060112 92
    0xc2c001010b08031001101d102c106e410b49140103005034100000608040142140010715264803400010030075045035000d9004076490700000d050308510350107201d0040c4019200d5622508069543c40c40c07200c0140038150080046040070b105554616282e41c17041c01c41882511640301c050b0510701c001c0e14003400141e01034420199034054492000084401c82c680100203441030880c655161000707450042d0446c000c910400080c01c0110711400e00412078507146450703030501140303003080d082d040d501e501004500c540c0d09000c81c0403c6484224000f54403e5051034036040c0301c21800c41004545500a12110461140300d01c04010083c0002d18031048600420480d800c031551804e007103510b851002803020490700f041c001086030003031245510341c0c400410742101c010191964890000c0343c1003194142c3d5128038442400710010142e92049800110700394040d072640c5031060000c1d648034440d010b4240036030760f10201c4809010290f40031400c40d59182d420707907040b96509d80720f0007020341c2d40000a6030b180b903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 14512246 1250 14510996 14511011
    0x14010216111207060e0f0a0b03010e010e0604050615090d0602031008010e010507021c11030d0f0507020a0309151701060c02030d02070807050607060e060709090606030203010302090408070f0f0f0303 87
    0x180002d41d04040350003541d140c07105d01040d002070110f9600c0c0c601c10540c10401d8504042041541c03980514081c05400b1090a5150b2500c40203200c03240e005883d0601842c034001c1440300d92f8680030208044040c290320303000e030354045540c080307101420000c80181040340301005118500c4c1206080d08212080180207006884000c80d403e8201da0041e00c00d0800340e40103000c180040c10300d01450030000409420081c941c41400c860f00303030030356000b00c1d100c150ae182e5410584500c0c2c0464403903560003d596100802006000b5074009d40b000750240101514103042d8079081c400d003442074805c181860520105c420855941d01c03000361001c4c07240e010880c401d002c4c290400181520004101017144c40020040094502e000c0612007594420842940c0e400d40300d44032140b00340c40c100004c5008690713030765644050b913140c8055001144c500d07421042c1014010001000940d0780c038001150003c3d00500d01c03650328180344c60f000c164205c040c44c2c024081000c01a08000340080b00074a42e400c680280c5047c07000c103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 14513496 1250 14512246 14512279
    0x10606020606130c020f030309280302070308090607051e01061d04020d020609040905060103021002070b19051303060203010501030f060b0d0b0604050411030a0608070608041401021611 81
    0x4180440c0d41e16000007101e10b85211a07469034021321002291030041d5000c10f01512091411030340201e0b600c0d00c81d9030141e503250102c0903d8288600e000e56400c1420421141076540c02901c0d4013151201030500880400c1449555464800b01c681f4030340e00c04102d92010345250000781e000500e10b12604810351805400080480600d5003e070b030305d400034402c480c1c06550b0725400c201c18070070700c0c00c01660415004c0c040e80880751035070301c240c41c00749000300000c0003103625600c1040403080d081d498481c1150040030003040301c9100442511010901c00b50081d54041d80c0c010202e03201d00850216a51061b290b00000003400500e43c015030580d403003070340c061094005e104481e0041d22000d1040200110041044002d1003c2075803110284101c002c1503540b800c0e0751840058241c2d0824940d80c2d0b10308a0010a0241191541c45200000c06246019000700341c070303000000e05400303002800941443c2c80061042c0440c1000c4d4112170100b18180c46a154628071428038250750010221803500604440c01c2090a4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 14514746 1250 14513496 14513503
    0xa031a0622050901020f0304060f1113030609080d021201080708070f051011030c030d0b041803050703090f15030c08010b0313060b0a03060510090b090a0e100c05090301060602 77
    0x4884070764000030031014560107401071000034014032640d5803e2140d6001c0600440080d4003a81c01100d0200c0c4264103030400030229a60b51461103032408017000711084800b40c4000c00c50032070350030071000a0710f0011810913441d00d10481401481d02840010b504940014002c2101c0c180c4000c2001c41d00300c1038407003d4565a515007030040021445c011482000b59213410058510740c1030b403501c0e10381c0c242d564460809180d030304841d015660700d42001c03400410080c214840c00a903510212004e000b03407030400400c4043c2c0c22031445c01404000c2d00145000a244c0103040e400028071300e01ea031140403031755643c3c444450501e40200b100000b9003060a0141103510a040a905a03100000d00901e1030710350684071800910b01e024100c64454aa040280940c0da9a28001d8011030140b1000f090b50b180c80103424518007400c0d00100000ca103041d072800340a44803102c156511904540300046c81d000750b40102882c04900c240d40d4a0202c0c2004031149600f503026001e480f0140c0150b009200e41034888505985 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 14515996 1250 14514746 14514769
    0x8100b0702031e100603050105070f0e0604060c0f0f050105041106070309050108060d0c092a02061501030e0f0f07091103061003090c032001050403020609040c02010b0a031a06 77
    0x50641c0b082c29004000c14408440e96052401072048070b034510444464035060780c45c1c550060f02c060359580100402140c11541c480703295889461309012903154500080e42c0d5000b00d001f94420003c9211084080040c420020007202e60880c0340100340b64102e1400c180079050442e0204c45010483c104040e480c24807000f40d83c400c9916440f0081001d080ca4011541080004d01d41d51307208c4d1341c052018001c108041c03101c0d40070b00131264000c2000580c1001100d10b00c0030030f50004407812120b45003030000f164085400e0343c22402d5a2401e01d44031401ea40124040c1002400101c035134064a04000303080c502c00244081d44064040640e8120360703468903040200e84894050170007031001000000c5403441d060a007400008180e090001e5506525121000d490086401c115800c0010b101105002c000b0040000380d881c1c0e0910f445031605007160b001c0f610794014001007501403610f401c2c107014454001e410a1080c06409040c0c002c0c0349582e0f050ac2813001c07140c0070a8081107641c0001040035410034901c60078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 14517246 1250 14515996 14515999
    0x120e01050306040905070f06030e0f0304080304060819060b07020f03031303171b0a0606050406030c090519020a050901030609050c070201080705120103030c05060603070303091406040b0a08100b0702 87
    0x1800c1d5598001400040c00554508031900c0c020111b01184a03003246008202805580ea80001d0812000e544145021080802046554030a100820900c04000300b22426210145845412902d40343c0d0450001e10b80c903d8030792034260524502141c0c4005080141c01c0d002d0007103d0f00a101c070101000d00d03480e4480d0605800181900e02c40500200b80302118140300c00401c2c0c008140b42040041c0340179400c05400c0f44d04459600240c0318403040c06031130300905000c0e2408450400c4041d01e11307955002c80318864801ca040e41d5844100040300313941d10070a0110003181c1004295a10002124020000c0d840420018042480c010011403404034a104252040358000341c81803408120340c00665140310010030f501c0400c542001801e00b0404100c00c218002e500c03036120806c1552a5140450178400d0040006000b54803000081008c03070750001d48101160b06018441501c1068240811032501c0303550000500d42c1400948100b030558448003840c401c00703c2501194920b9210204003929200303150020317 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 14518496 1250 14517246 14517257
    0x412090302060a210204030f0201020646050a1d030702030703021908010608030d0c050a02100e010603020306040c05030c0d0812250f090504110f0d0b0616120e01 71
    0x304216402141e0718005002d07080020201d2150301380c148010b03a4030a82048403000c00c0c0200c0320045580400c0001e03007160045011010507004c130240d40c035110518801c01d01c515111516803102c0120000c020b6004a09066000d011038500745007403030f0140400310b0b002d240b040364551140c400300202105580819078014040c05c1810300d10340800c07040c0e140034407000d90401400d040024000e8024403071200100f0061001d95203c0100b54000c2c412100c1681310b10050003000c10030204010b03404918000d940301c0c06400001d10541c81781e540d07401041242c10094161040d4000e200901160640c2041183d030210304036039481c1c119005001c4407040e1507600070b0144500b48900c0b6403446010300000d6010000c0c0c507940c034050100c01244034107042050900d1000c42c3c80070700c0c074041590707005410340060300303042d91305000e50f200c0342c004510280301b4142c60100b50320001c0341c0030a002d24250030062090000400c3c0c00c0d02c403500b4066100300d000207078000322410009501b1855182e40251540d942851050310369 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 14519746 1250 14518496 14518507
    0x8090309011202180a170c060a0e010f1101020c03030603070501020c010207090b030c040c0305041101030b030d0c0614010b0d051b030f040303060305120d0509030301030209160507020a0b03041209030206 89
    0xa02d01941000006140d40504e40c03480c407016480d4400e021005001d411b801450040398506000d05124000001c54001c601c03c001a0b140c0941000c81d002c0026000c0c070b400b081c0c0d00c4415004036954044550582155400080c404242c4003002000e90b008000032019104202e81d03072030041e80d1310811070114501507000b0703260401c100c162591050442c00c001a040c0c50b825200e160000742101c50142000c00442d03030326020310080c40707103082034081240000c2c2400c114520281d000079940b00742907d00302040000107550602000041d80141e255504840300d950f0340e03541c6a03030710780140c0d4010800090440d032400b000500006241c901002d08801031800180c5540c03143e080d0030144840041003507082c541c807600300100103036040202c01c12071842010b0480e160f6140907100e80070390f42c01411200c2154428001440540c0c2e4401c1d03003d4124481c80710509020050490645050090f640041d51000d1004000a148902003004500c1a03114084c001100140141c4c03da84451840c04040d400c02e506019 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 14520996 1250 14519746 14519777
    0x80106080d1b050607090314060402012007050306010e1803040b040603020702010201020c060f0105180103050d0804020d0c030305070c05031c14130801020c010501050d030f030b062205010809030901 87
    0x52a440c1c2e0b0a801802000907601c4403490444280c40c0c150002d00c0382401003062042000c00c2048402c01d0130083c02c502e00302900000e14007207090015070740c29010004a15030398401003084000803c0b02131305941d01985d464034281880300701110004240c031810701000103a84c1020084600b030700d800b0030341142081e041c00d000301e000b5004081d00300d05665003008140b0240c034040013007a02c60803259000851035810102800041c60000311000c2040081c1030060000850200701903045048500c1d0401c03242e9620300000d0304810b05000060710050300c0780302c04414554001e00401030240030310700c07080780e103682d54041c559661150311880c0c0d41100c240c40c004024922544d0040342d100c074402052801c15400721898030035903001e540041901d81d4009484414020207015560042c2001c5407005090a00c43c1c801514803400180100105580c1b0003203a1419076072881903035100019043c0c1c65041c1d038044140980040091701406001c03c0c07090b00010f00342c0d240081101d503882810f0355014890100c005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 14522246 1250 14520996 14521007
    0x22080604080a030e100b0a05041a0402071b030b0402041401030302060612030903030d140105010302070206030a0903032d060806130b09030c0a0305040f060507170702030a02032401080106080d 84
    0x81d40d0b5070415840380041c00541c001041308071040d1181d4a80040c6100841e010445400038682c48135010f141082d40d586c02c40c0300071148002141c5c105880c0580e40b14030070324000707001c0607000c401c2d42140400c1060100500c61094040c4d84500e1080e10200201807043c44e1180490100744001401680320700300084150901e004c1c0c80b034003440300d40210f07030410351407000003810761308410710210440c0d580b4080450b00e00800c0c841d903801042c00b801c08500c1c01840750007140c000c2c3b00041840c00d03040e403550a00c90425100754001d2140b0395661060712800401168500400000d504050441a04080011440d0f000108806c1d00070170102d040c4d40401207190380c2c3e00d00d02e1040181181400d000c1400700304582002400100b410074403d680b03895640d070504a803a070301000150001c2041200034850240090b40c21211002e1030707e40d0003852601e5624038800285418107a18009426015074200c4020800d042a40c0000100491074070020781c2c0c0e00ca02581d0700300e580d030f8851461103600c10b10f080030f10b050190 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 14523496 1250 14522246 14522257
    0x60f040609050a1e060f02030106020307032607080603010b0a05030d030c030e0604050601030c12080702131d030d0b040207050706030b030708011b03050a020a090b1b0703082208060408 81
    0x91064414904403074813554010500c40140c1441e914070a0120810001103101c0c001500482110450442d418800c00950720300075070600074140540301f0400c14003400c01480150b458080303981103030424a0b024000404544052700d0703060096003815000758942c5020050750b0144c42014008000c4805080422401b6012403012503041c980e54481845041c1414424603101d64020700c0100440d514500c0c110590744000d501504010500098100000d00c000048558440e012a0800d614001243c0d1410045c407a05d054454080e02d61941c0c00c14501c004405003c1207100da0740104254074501c4280010780c4260303840280306400410040c40f9550203540001045034016003240d6015071108412421a92031521409103c1c000d400c90b5240164140250b65004a038041c3c154201940a5405400d50304540125107103403001154805120341c4001403001d815442e02c04a03000246c0d04d003001640e031b5018980b5000d070740740300e0141c0400385180c40041c0e008175030b550390041045980700d40f04c501c0e4a401c103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 14524746 1250 14523496 14523503
    0xc0203060402061b0f030a020606190b070309080d030902030106050301090308060402070c05060a08090105070f021e011e02030405060609060a06050d0b060307031d120a1b02041401030b09060f040609 87
    0x4134031a988003003208000384106132a01d04011035641110502c0a894070310002d101d24420619404664030080303500c21068200e6006620240d185d07078a83c0360590b100d00e8182c11074056845180743e1001d02950581000c2942030003a40200502910742c020b050980b005e502002d004604418049091030415600a124480c0a0070100710669180d0000030440d510640d2500300103001e4100348040441c1c280700c1c00d07030894040c0c00d0664400080d620040d40b15100201c00f800380c800c01e45030340f120080c800e4203d2006403101c040754414140320142a000203400551303003a0b070b00c1c2c8075000009a1605119010b103005420040c000c1001320b1071b194007182c0550010312040c142544800741541e041c0c48540155014802d691408903841030003e00e04020700340303104000300440d8804100b0520f060b00c100100c07026142c09107441e6903c024004040f01719500b005800035080f41c500500f40c07144c009100e035628103903442507402031941c4d15040ca04554820041d00c4034a6034000d003001060000781c151b03002900c0c5922 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 14525996 1250 14524746 14524777
    0x3030c020f0301060b0c060108061306090c030b090d020c0301090809060c0102040306091101030b01030507050a200303150909010b01140913060b19031401030209090a05010f02090a05010c020306040206 88
    0x10700c1000b10f07003940c0f200d07807008085c5540400d540003410f0080c4600c9014240201c0242424a03250b14110705509248101038009950f410f00802407044031046280a1900910f8030010380c101706145594401f00c540300200180a03002d4540101d1506001d921246030b001070071326003001034440410096a004528002071590b003000b00100140e8a40504059035004c0c456100000408600140940d9243d13020300341050320345001c0282d0300f0341080070364240c3d840c24542440407520403041061420034016200c81c0d0741c40301000f0440300c2036400900250303c12007901d051103107889202d040c2d801c5e148441031180c04510207501c08507620041001401002c040103003403040d41c219886585045a419400c443c041c400e001410041e4100195070030705c5181080d2a00704000c42124070328034284541804000c2c412200c5c0c10208280081c10808810740c0c07a00200200103000340350b10740d94020350040e002e042c01140c0100002440f98014290b0203141c5030050041c01d03903503844c1c0e801c106850744507002c190311a09 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 14527246 1250 14525996 14526019
    0x605090604022d0a03050109200307171503010c0203070804090203060a090e070503010606090807030803062209020102061008150601120c02010204030c0e010501050a0e030106050d1109010b0a050403030c02 90
    0x310803c2008916180080c86984d400032a030008080d01c41c1600060340ca282410b0810000100c3c4601d40244441000001502d0381c650a034100d0724502c110207511040a01201804812012080000810031003240200496115084142d0322402040405020761009020400c4039107800d400a5a00030002041c04c410b05032201c074008110f1310102c0c0c40c26580d5006134820300240c20700b481420060101420010012458004261756800705408028403524010000c20788507200d00102280611025983c05540c0c030030420100014844050142d00500c110008109001d041072541c00913101c40002500001d1085406110591405403e440c100030810303102e2000c1e20781912510480030701300e600160b910f600d5424070650765011604901403070003140d4010815683c01500312690a1800e081542c070b04506100001d0040009604c07180d0001d41c3c401c440c41c10001c08002e071041e5403808451070800c0d0f03601c60701c4501031401200b6104010480400062010901a02204003040d1008014881c0321 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 14528496 1250 14527246 14527297
    0x1305070e21010f050105060702040b0303070c0803120c030c0a110f0304081509010b010203220b040314060f0411010c06022122020f01081801050702030d060801060509060402 76
    0x9110000121400c5100c0c400e104076404400c0c001e50088842e004000d111550603e00020814418004c0007031055543d800c40820684003441500c01d070503007101c01e503604203559000c450345a920410403c0100002d40002400088000f000d0f24043c805800e501420101403120a0300c0d11107801d10040680d124240382d448012100700000c4c8060099680030348103410102d2511011810b000d44544103590404000d1b460590f40001a1a604408000c4440d0002c0e1407001c00000b031003945c0c010402c030400000c0c0100502c01407141c0c0000c007110b201c04807607141d6584190318030050000e0340e00400000c0300c002d60f040650321491110100c0d50003406c00524101c46c26510b1103081000d208400701018a0104100303078042e9800710f14413640c407502e201030817030155070303000807800070038900007a0500580302d010070782403001c08485d400001c000320000c00160030202e1000e9074ae90842d24038091480d0622401184200d8180034400c1180c4006d480304800e42c48000411010390401c02c01501500710a038040c0592 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 14529746 1250 14528496 14528509
    0xf0b03070e0415060f090825170c1003051e060f0a0e010501090b03010803091c05060403020a1403090303030402100c020306040b01030209010e090a03030c0302040b040f09050105040504021305070e 86
    0x168555410940c0d0010300c1c01e0b0000e8920a42c4035004403c1c010181020000002c0114208420420414111501072361040b0400328640807600400b80c000c1024001c01c1304040c0008107080c00d400d048500303a1b1a1550808101c0c26202d044650725002111041c040e50941f80c10300859401070801045219072103140700109494000ba40d110b4000d50380c89200420a65030807401a001030002d910080c0e01d1507040500c0503683c2d00c102c4241c01d00980c01d5040841c0f04020545e0480f040c5035100c01521800c3c1445c1c00c0080d03680941e08001da600011020118000301400812a0400840a009142982d50390303000c20400031b8801c0004414000b00c0a040c500590b03080c81020b10451180b0006804d95065005114510205821881c44410080103000c1440800141c41d486154145408901410180c000314042c1c046c0d41e0083c41c200300d000c14081018004c1049030011b545411074204a16a614070804c0160b42060380e000c0e401c600c01c0c0d082182c0b007084c103230411b513800001c1e82410940c031048400410007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 14530996 1250 14529746 14529761
    0x50712090b01050a1509031e02040204030308070207050604080703020105250c060305090115120c0b0a0e011202070809120106080303070305090606150405101206030609050d0302040f0b03070e04 85
    0x70028000c0c00140410b20b000b5009402a16a8180f039a02900e44d65002400c01c03400c0f400302410801a69500b071000202860b01031000f00c2c1d010b0410b5440316941c0c0b40181045c0c01c01d0325241c015008208010038a803c0000c15941201c1070503004112417071660300151881d078490f03584650f41c5031078064580c13560f401c07401410682c288070380403240c03400e40b4000004040f03030360140003042c941c0d04156015460748a94078250303007612b032404800c60556031946000c200c020b0080d0700a041c6e50340c0c0480c41d0725070150030098001d081002178070390450741c0844100c2d1408a10801030001d00b4103105001085603824014801c00286150400016015131903d80040c5076030001c6841c400000c3c0c980d4100250b0b24000d0040541216047c2c0700102c0c048640080c56a80380030714016940a0b016401c02c001540d889141d60f1401003c488104103c0b240c0c80c2c1c00c050010303184607130b01a1014421361042031382c464424400c0300c04035524083c10945241c2410440c40361548007070540401c020302003c001d2155940d070312454a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 14532246 1250 14530996 14531003
    0x302041104062d0806010e03060906063c0105040b03040c051206060102060712020403020d0b1611060103020d0c0815040203100b0102030712090e070203030709050a03050a030305071209 81
    0x240c072a4a8504014003a540103c5500c03d4992400c0c0a0911920300b91948200500d19081081407a40e0381c0c0c0040301d0705116400b4a84c2d051041d00700740040ca2201203202e5028020a413680e140c0e852048510a08140d0588035220300c1000203554500c1000c2c10a120651030041498180c1c9041c1e0355030405e030030a800590301521056007101041165280c020f00310361042c3c1c41e01002e00210700e44000083d44642c2d005045000340400d080303220290301480c4d8101d41c0616402862003d421584d401c11001c44e1400319000381110300000c000e5010a400b4454241c04000e0000c01000f13640c3c210760038040340c0e21101d0ad044070b03007000360480441c00000900c0703000a9920505c8441d040f03442e0a0040624050b0241010340b003192810300d100385079036800310403582c10307a4004084601d4103041003c00c07035a28045501c10450b504c03411040c042c803160f01000035406215282d0301c442d410b40e128401c00990140a10004003554842500400024020b42041358000f603281440d04014800e0b0118800790b841110085 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 14533496 1250 14532246 14532281
    0x40e04031106181c0509040902010315030302060603060a02030405060c070c09051503070e0702070e0606071707060c080106170a11030702070e01080106030b04140a081305010f020a0b0a0c0504030204 87
    0x25400d600c03c114400030f03241c03c041354032001000210701034054801c00d10040c0c011921110680d0559000385c00c0b004043c141681544051696410003c1d10b440c000d0b18a00e01c03074000c000105030540503a0003a02e0007281c0240103440c00d03482c0c110140f900790f40500c07411a500381c00043d0010300742c0e507184182031103a41403655654640f00150101410588103070001c0c2c5808035800117000f41309a0005800040c3d41c02c415601c00c2503101d0030f002800c1400341c120010a2118014a6034200701c1600c0041d040081c403521051044c41000d000c241c503c22000d000789000518003200700705080f1166039140c0c3d004101003400107050496409540c00c198803c07180c0b103015a0080c9001c1102d41d14030003040d4010042140200252800e55990002d1010041e00250100c4003400062104580030b0100d60300c01544801813a13507609915815227604943d91158502080c6010407041c3d03000c0c008218001c0090f0b021101c140b8580e82c3d054210300800010600100b0414140004001a01d85100340b03213270025001c074072 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 14534746 1250 14533496 14533531
    0x170c2e0318030905100801060e04020a0c050313061701030201080403050306061306020309120105150f13050106030f0506010507020906011d0a0b1306020d0f0f03020f03160f030e03040e04031106 85
    0x1404580d42984005c0001c100041c0c00421440c0e034000d59000c26100111000340c0e5030790144034115540090110054a10b0000142c2e0f80041245045070400301c500c03549800300820078601520540c40d0b17091001a0100da244000200001d201c2c1c001954000c000500c024103096000b65a00400b61498009101581c4000f8154103507240900e40520001030b8070009101c13038030b40301d4400c1c0010703400b070100b05005071400500014039a170f800c07041d00d2150403030304001c02080da91904000d0103094a440e40b81d1540c0d14050105a082d441582110748481e005031810801380c0b07482d001100c500c201c4012070071041c001e8514071a00c5642d000194401800400d852689694141c120b4609018155000b4010340d070190108070070583c2c1080c1300d60324403d039078140030018060200c410307400f070301c2419080105040c0000c00c000c0f20081900c2179501244030399603002103030189070300141c0c201d030000000b00ca110f500a10040012020260807240c2c014404d05d072a41d51442c1d8101c041e8501903091b28032800c1003541100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 14535996 1250 14534746 14534749
    0x610050304170d18150b030a120203070b0708070f090305060f0604020405060c01050406150e13060209060c16050103050105060d05090c0306160807080408040306021b0304170c2e0318030905 83
    0x212412001c07600d04104011006e4100090b5281020140108100382c84101c0c54050340c002d0058a030601d40080003800240380224004184d5401114414003150121910036051813081c076040e410b0720740c0a0014209034440302400201c000c0300500490340150200f00100e0b1544076a005000343c04041d03c00440c15041918001c81561080c0300181050b100e00c1038108010b134442c4407603d411008900304060074100504041d0081d120320600e0680100000804135254800010105e0043c0d4094421914994a0f000110140d6000f1f100d0b8540c00f4409104000540340203a12250300032038100f084816001400020030b0400030304030b550b084030545070403181001c160003000301580400c4070301e440e40e90f91405555401c824000c40c0805891640d0120b5002c0c5103940d070b8400e024400405000312529150355100c1e5042c0c00c1e0360264259030138040e0040180340ca04103003503120500300340303940c101c294400c4040a01340a600c03990103100030181c50b131501c40c4070302181f40c0807128103e00170743d00c8642c818200390 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 14537246 1250 14535996 14536013
    0xd120905090a0902100804060603021507060f05070806040c03020903060106051207050f070807060e0709020c011a03070515040b030f01050a081506040507050f03100603050610050304170d18 83
    0x2456060028104020000182d485d03058008101ca524100390180c0c0e00ca41c2040c00003005160002500501c80940d0719400904442c0581728140c4500020f00040903518141000da03001542c9140200d51040c2c04103404c2d180c9600424031500861400505200741c2d440060300d066030a9124401007000083c607086191000f0358402c0e0302c000c03039081582c0761801040680d41c03d0b00c19900c0141c500000450050104a070725004407408003502d9040342e00d01901c3e004078900035402180360342025841c1c00c42c1c11680702103241151150140c02806402401d192500340320a020800121001040f010400440e070201c000340038500070316070050b08100301c1d0f04110602c0031640a81d0051740c400d80c005419041018a001011540b01c48203503004911900d40340d1042d103850054195141c09202c0c007204022489000c07035000c10417601c06542c00d01c1141c07159401d00c494040c140501c2c00000d0420800540441c541e512008092a200342c109407034802e081a9040131240d28034004206009505500001d100c2c000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 14538496 1250 14537246 14537251
    0x2010e10020a090b030112030c0c05090406140603071809080f0708070201020712020618040b0d0302030d0606050a140903030403020d0b040302100204210602090907020d120c05030105010e0d12090509 87
    0x4c84e001741785506100074002c0003406401d0040c1001080e8140d0703010811020b000300003c1c40003034184891424680342c01405020b4a0b62414000b40d0440006540341c0380001d80c0900700c80a00d155103090b0100c1c580040c02404954034151181c13641041310314603003080540100344d0f8030300440100d600d90000d44002806e1903481c1e8041500205000e4800c40540d40d40d00032112420b80c0d0340303400c19801c1d4a0310003007009842d00a401550040342d500700742d07007419008001407030b60384150442040515201e82043c2d4682c05089010400501184104102c42e503903003004010105005003101d0805d9520750026400072814032040310469980400e1004051f010410a41c0c8241820002d40c00e003400d00246021161b040800d5100714408400c20800b40101503048801c3e020028080440078940000c019541c0d1030071500000000385100180ca00260403882150400302055880301e285910340401110412a1094076a500a0005110100240510322444c90a04440e110706078680d10384000c008003076000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 14539746 1250 14538496 14538509
    0x150403030e0105010501080c0901140d0f15030b06060a140f0a030b030601080d0e0109030204021305010f0c0c030609050f070f0503070801200a0903050708010506040b03010c080408090102010e10020a09 88
    0x620f0014003140e078000d242d19034002c528984540d200c10480004a540c4c20525010721002036001400403030310f401c540c209242700f03421660b0078041c81340e88045901d0440d1903444090305a00340000410014541500100085581ca2400c1c50060100e00301504c500c0d8000c50300c2442d240c600280031504a0307054001ca02800100f00e02400341980f420100544403100705440c8010011140c0e92564240e0150114001071a0013400454072100c030094501c1c03c428141c050340e030120300b032480c0d40c0004520400041c0c0040d5804000c0003440f514554402000d4480d0300d108540d50b002d900000108160204502001031100c0781000140b00e107008180f40c00c01005e604500010b03410128030550340c40c0b40b042c4081002e4003000c15182d0310b245041d0102c408040300d40004200d4010b0f02030002d0700c100c1c1504614051351046030704110f2481303400c041508981041041300045030144001a000c22441c0000d08010304060001250340b507900c8e000f1505008180e005000c00542c08501e906201c0c2d80541e03c030020700030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 14540996 1250 14539746 14539751
    0xc0a020901060c03020c01080c0c0a05150f01030c0b07030c020303030403020604060b010e030a1b050a0602070602010623130f0c0221071a0403090504020403030804020f0a060926150403030e01 84
    0x3c8030703140203490380300942069050080d2600481c640d000ea400131100c100c1005800da6030b00390030070702d0300781c1e01c2d903140500d00d880c14a82c0b8400714020110484116040341c0e40103101d4650145022052217550b00600b0040d0184840c801082016807014002548101d00c0b95010385814509490081e04483c90b0b5490541004140140024503850010300700290f5608048500540100a200851402a41c3d00203541080d401d110000300e003900024400d0540340260000e01240b91248044406c7c011110500203102c10b1040c0c2d240102c1c00c1004042944492002001c25500c01c4114040300ba5400001c000d001070344100c03540784007010605403441c14004002ca62030f00d03201c483c3d00c950b98010000d08606401014841c0828200360064040780001c3c40082c00954482d40e6a04010b0007504003150241d01a40320920729410603e401c1d003030704003542c3e4540c40e82c4541a062080c001400480400240e20304c5050034035009050100f040110212120b080e00c44000307152030701d0014195801c14030341981c0daa0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 14542246 1250 14540996 14541017
    0x1020a020309040b0307050d0c06020d03020304020105040504090219120218040c061d031005010509060f01080c0904020c010905010903110601030b060f13050106030606110a080a05070f080c0a02090106 88
    0x240d001c801c58481c228100c03000304d2049800d038002030414081d640541c0c0e01029100c054001c00c09140d01500c11070b902c40d0290782445403140c4040d02644801c6030002d001a2003088280480d1601d0791011000c140054441e444194401c10b10038800301d07083e00030301007140e00c0780c0845085242800905000128200b01500c041c2000d58a0f9406540d0600481d001d108240c4002d4141003a080501c214040000b82107402c450317003000c0b81030010842800366074040e031030900001c2e4560030401c607904111801170307451404a90300c20303560901c1500040c045652150b001c200310340052409001d800010380c095400003d5880c074916000c0c1c1030307540c022440c1041d0b8000c0c10040001c545c038460790b103511400075200e0540c240c4282d800504440820030302607036803034a410000300f5034030390551142c001d40b500b5441d9424a00502c00314a076a0b0810b18600601c0034104001c1d24010511580c0642000392185c400d8506194460b517070004280c101c51450bc0581d07114488000640c84c194207600e00402007828170310003a5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 14543496 1250 14542246 14542267
    0x3040e0c03070c080a05040303090506090d030f03060801020c10140103050c01030b01050705010c0c121d101b1a06090f0a09030905040c0504050907020c01050d0e15010e04050f0102 79
    0x2000385124a4590040005103820b8042c0300d01c100308a0b84030322a10380e1020200c074080d000b9041400709500081c2c00d440c01040e281440400c0f281303440401030104112448642e000c0380e0400d04644450101a100e0f00300003a010002d00103070560000f0b801c094410080498043c50031200300d4900050a07114940040000c0750f4042000c0300c501c2c00c20b1034007141144907000182c450307200c0c040d4020515840c0c1404c82c00120341c4424103184a0b4410201c003440700164000c00c940012940c01d01d1b003138a80441240303107040d1030a04200002c1402608011801c0c81607490185c4005030007540c2610400e10740c08291246440f0859141d50014045441c4003141c18003a042d02d400581c02450b81150300d60f190024024907001c2d045030780007000c0042c010320468014280040440c0c200348620740c02900040701117081a400480e0b00601c840307040c1e50301405e0200381100d000291032030f41e140e0840fa00541d601c0d07030181030203002d1080c06080c0030b0b0086038480c1400e290845c5060b4544a00400c1d60b4414000144076 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 14544746 1250 14543496 14543519
    0x7031703100308030405010b091302090a0e0c040e0a0605070f0e0102012009040f020c010b090a02071a0c04080106090b130606051c0b03010f05090d080402060405130b04050103050f0706020304 84
    0x650b5009000700351245e0752480c1040c014a24140001d41c043c842604106282e9a1080c00070f48503807003aa2618510788505200c4020b85182c9440040b19030450080c5402c0c504041c0d000407403000d44141118125005a11141c00f1a141075030300c200003a0840b825864010380042245039041c00a10081005182e10301c0c1400a8242e0b081c03013402400400504030303441c1e0341c0b035030040300400900120441da5507a80e080007070700904009031118013031014400042c180e544e103031080d24000740e0031080b5085034144d4032a058a9000000707000903420b01e014400881c17035200920440c07018100300007001484800410400030300e214114003000500c0d0510100340540b40d80807040e40c4482070030144d035030035455122003228060322240704010342561812121550310149504014018040380042d16000034040b01c003121143c80c1210041d40042d800c00040000d410081c1d5001912440755130300290310440940081d0a8070702c01e85c01590309511a20018051210505c500001425580001c6103090720b1304404004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 14545996 1250 14544746 14544749
    0x30f0e0105030a0f23060301061205030a0503060102030d060e06090c07120305090c0d0b040201090f06080105060a0327140c0d060f020f0406051c020a05070f0516080703170310 77
    0x40f51340b0b401e1a0503029020784c01006640b004840f1248568448001c1200c601c00c01311920b62181d03080040c0015001c030018401c00e03d068105000c4c600d0310701e1901c0300b07480c264070103040700707046200c03c10231200d2184151140c580a0704504905d00e90310306101e01000310b0f88001402500041504105080005a010100304006009401d001c80d8980e0740c56500c5040070001e0007907940000750000c40c1020404410642840b0b039100740c0b1409504d986035120030440c1000341c081c0c00003041c82d44005002614050029080c28900ca10300865a144a424416000021012501014004a6070003020803c4600009030b85041020080110990714000100c00c107510745030207402c40f50b40312540051010701d41c040365540300d410b0a185c0d80c0c42d0398541c80145554044007515a68800c1000c0440a40303200703000f103606c809110340c1c0b4a800c181c2075444030354081c2c00100e0100c07010712902500300035020f0f26500010007002000090f050403071030750030005080e80340301c119041f201004008220111001e11260300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 14547246 1250 14545996 14546011
    0x20c0c0d020f03010c021f090b010902072303030703050601262707060e010206100b0c0106030203010606030e0c030705100804140109080a020f06060616030509090403020109030f0e010503 82
    0x240d034440d0350010030741c520103541d00541c040d424400d02c010029000181c44051480b0310031030007141d80d80300c0301040403070701c81c14401006012a600104400c8040390054091140141d80e0090303840341102e103200c0a41b604c40c50b0440940c0020003000403168051280c654040c02c203080c01c11200d15954100b101010840c4200d641000744c0401240045800b028840b0503d60100440108880c03101c0000365252024484c600000d68044000040c82d407010031868040d1450703c0c04544254140221300780d0541000141030f09965a0705000009640c2c01d01813140100015200081c0304024a5001401c0030045220345000750302540c420007458aa64980c2c02c031580440c541543c6503159898401c0702020303a0140b080c419030a00a540060241c0034009001b100b21680031500d10801581c1d446032600300848460f0b07400344040c0041d140302850075005000c0b1034820320b407040c94220b201c400a0700800e401d0b1410380050b03542e0900c00040580007680c00c0503654840c00d10782000160b050008000e8840281b0b6070307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 14548496 1250 14547246 14547259
    0x20301050a0e0606100c05100618060e0601030e03090d0c140d05030403230a03020c090703051603020a050715140c04080c040207230d02060112020a0e04020d02090f04020310020c0c 79
    0x10030f05128060000700300c0e91140a23554016028a10340c1c000d4450f501071503103500c041148250120f903a620401f800c0344d055195615550b0380c1d45006600030915244561a24002007201340f4179569071203102e40c03a26201d407a1070800740b4200141170190f6226104050b01030341d0507003c0c41c0089540007003602c084a5100500050581950540018240805004040a10681560720b08041d0003042148003a0025140c0c6445031f5500d000850a0b10403c5d61514140355400a0641616201e03400404054010703040c80d91610f181c07582e614010080d0740b542400b85030b40d40c0f054000801c41040311150014030125016045c10304244009407109940c902da2840759a0001c0c607041000701ea407681c0320424041c039003c00340c0104015122070325440e886481070014000c810020a4100c0680c0050040640207481d1010705418111025404100608280d80c000c11806507103005076140d101036031043c500f40380204803e04007441403621b40000c04240801290040c03150801700407000502c8907540c441200c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 14549746 1250 14548496 14548519
    0x20f040311010302070f0507030b070e010f141317010e0a0803130c0902041202010e03010e03040501030519020304080c06060109050f0409020103110a0201020a0e0a05011e0504120c03020301050a0e0606 88
    0x6a00034452100024110f401ba56507100031300501044030800c032401600740b008075503031340f03c1d0803600d80308820070050100e00d410040d08041c42c8115402c02c0403885c544001032a12100385050005202a81c0c0540d030100501d0740c01c10210300080c01942080c54011000305205d1800d0b80d1109868000101011082c00c0c40708200e01c1480100710ba4500209581001155242e03140c1d02422188001e400c816404030b03450002c00801401e05100d524600c41d02d20740a1402c240c10f0038011406000c014207070145075468a540d902d91f8003018401180524807883d03030642d441a1002c00395060800060025060140c48035013000142c9400015100310345085600042081032480160010550703801c801e00020310109245840075015401854101e416072951490185204100b2403a100306000701c500180745600640c030600c01e0810b2402001000d4101182843d44610885060301480340c0c06645400089a04005505007031080c1a08981952800e00130781c0e54011050b6501c000281c511802054007008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 14550996 1250 14549746 14549749
    0x270105100c0605011206050907030b0109020a030209120c03070608090606040c03020d050117190807110d080309011a04020304030f11030f1209010e0a030806040504080702030d030e010e01020f040311 87
    0x451140d10002c10401540c6500f03c04070b40d0403181c031086500615110201c1d1f0300c10030001d8500c040704e50003064842d1582c2405c2e4000060b41203900c094040c3364091081518513507400b900c0c41000f48048000f44080c00c4008201441c0c9102d03640040c09018480c030034003280b984089031050340b0050907100401c0f620401e02044009200700141c6405541c90200040380c0da001404d151a840b42514048649109164a082c0f80d481c440420060111500304039060005035031494803410b5440007403641c3c0c600216030702e0b0400194005c541c1c9030126503440e260f5100f00a0560800345510300c1c207940450440c506940c000e40940c0312040c5402c140b140002d03986d004007108004440051206507232182d00d400350645c1d43d00854809586011241d402d04c001d902c110306000484125240c2c26607242074064503003a0034440101800b610544c0c00d40010030804000d61410003100d844116155070028202061007165821a00105102100d036401000aa002d040c044801c0d1030517030303400a03c0355001c10704880 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 14552246 1250 14550996 14551007
    0x30f330105071401090201090f062c030709020304050105100302010203070314040b07050109060c020a0201120209030a1403030403020c01020d09060809010608190515010b180102120d060527010510 86
    0x10001003010380d10485000c03180c00f06410000340d0303034401e0f01c418081540b641c040d910141014040c000c000340c2da151089074801d13090548181080030b41d0a040c0d500c1440080801c1c141544d5811503003110f9000001e10082200c00d00c41c2c80d0744600d4220300717108000d0850380001d4992040c51070150030007034820a00f030442c40d2000c1c1154001c0080035011565480b0b03d1030b225010f0408410305072010f5160001c10f03030f400c074000700300320304d0959050750384440780e94900010ba002500540e4909406104e154030000000f140460409281d0a190004507100d141a1038002d280800c1807040c6411900a440390300803a940201000040e1800360504580715501d5a01d050b00404480e0302004491140c25408924003160300249410980102d06841302c1c80f100d00300f607034003040c8203100c1c803402144208117101078003041050203622160148103032203080004000f42017941c1c00c10034800400b1a1b48480422191502c910340341f56000550242070b4403030351400c1d08501e0715801445601d024039461102d07511040c1c0b203803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 14553496 1250 14552246 14552257
    0x309050f031518060108030909010501051605010c03140603390604030309030b0c091804030201020706090b100801050c0d0509030c03030403030203070e01051c02160203030c03030f330105 82
    0x386842c0c0c10301d001c085600c82c4000c100e00e40007160240301d00104480801108481800c40b001d0804441646001c00440703980c0e0154080480381c0303070221000d0000480a024004000b5200e54000c5440072460341448440781c006040310344a80e000804504000d0f01c5a60b400c64032903510303100341c90360031466407040400c0d68030360504ca82d220740000303004010590045400e5050b20300946018155a03615124446684a20039280f03a01c90381c1c0c0b8500140f4810070310a0141d0062180c0f001504000d01995601c082e28154902103400c09070b0300302045010071683d9003000040484400a000a042540404a0910456001b01c0e40540c88000003421502c040080303c078000072050480380d070380c40e00d4180100290426507240300001c080c060701000c6980720344140c1e005400a05c40040300c1d184150703104002540f002084001002610301080050398090000d0144000743e10301a41e81d81c030703010345c00382e41030f840c010b001c582e82010030b9a640031450b0903107002401580441d90300c070441103440d2006841a0051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 14554746 1250 14553496 14553523
    0x15060706021207090f06020a020904061b0f02010507020d090b0307170403030501091107081b0c0301020c0c0a0905040f0b13021c02100302041503150302030102040e01140406030309050f03 82
    0x7a400103210340c1c040c0024480e01c0c0302d0356441c403005c1d05c07405104100c9400b440395030010ba214107800405843c00101258200f840f0781d100040708040c00380501d6483c0003003100c40d4040341121011504040e02801026070018a80c4050841c80f0031248010300103c0090140000850000c40000c1c99a801040c4540c494080d0490b901c040b8075140c0b0b001809000240205210315080001c502504094281030fa50078544c88841207082c07509200501a8446404840c4003c5100780c0708415401d4070203200030300b402c841203806441d06122000a02645035065404500361925007810000810021102440c9036503000118aa60b9105c00228401e0b1540c2048041d502180c00001004183c0c5a01041b940c60340c03084d00c0d0500b80e2400307207406500b00d000d14811590072050441d04404001c1c46a4802032031000c01c00b0901800540780e0700402c0c01c81c0c005401205408280c40c006210061641001000c4814201d509000d0a4110395001b0000da40b01d109da41d00074190b00049080030755052082080c0c1c4034a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 14555996 1250 14554746 14554751
    0xc0102030408070c0f030327050a06020a0308060d0309060c05030702090a050f0702060405070501030915020a020303060307080c030d050d090b09030a0f03062103091703030613020a0815060706 84
    0x41c20b061120a0f6404103c04454100e43c18034009001c1c00300c0d4403c2021640c054880d4500360380c0d8010750b24100480980700c81d2203100f4040c1e0202c0c0955407101c550018109560040c00e8040c40361801904000c00500800c0c800c100c07599204000990044030801078030301c2454808043e14040c94003900e03600940c24001c4d40040c05200308450320007503510181c0701e21300c941c40341c040302d4851410990b206c100c240e40140182e0001841442a03500981000d44214419807001d00906412590001281c00c50b1030f404005800c004140304407850100000c4000d4031000028125032402c02000a550381c032001d481c0010f00201081403404141c56a00c2041e02030f4000d004441d081c035009038115202c0c0c2c0000a80d0300401c0c00d0a10403104075200c7e100c0d001c191403140c40d0044511405450023406030f14116422020001040808500c0b243c00220310344070311032804001c54584c10114108094010f40ba485000254414803000250075448008240c2050203c00c0b1041001e018801154079481440d102404290 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 14557246 1250 14555996 14556001
    0x60103230f10150509041a060604050301020d140c0301080303040b15060c070306050703020c0a140307020a06030903020606091e040c05040221090c0303070305091804050c010801060801150c0203030c010203 90
    0xb45150071100080d00c0f15429000d4468490041140414042d500079108003420114201d440a000c4401c3c0d82020f401000103081950303407000070b030aa03408010844802a1580064416003c054402d990060407a000b17440c01e660520000365074038000280040e004400080200c0d000c070202c4250b5010b2110042c0c50195208182106d143d41d034460740c030045855034903000000780308520034420350790003003071400103001e204501d0b48600c140c00024004100c005d00081111500581e202c12020300108007070340b4049909031450074080e040c81d00041009002d00005400c0000c07050ac810070300402107101e41c10341982c0e034645041c19980840c250700701607080f0b0f20000b480ca550baa4940102074442907010005c4445a0740d4160340d0f5101c0a07410000c64160380305004403800640100b02400000ea006046403e881100d0509400500c409880c290b58a4124404960140d41e110061502404460520010030352604c0c0a40c900d80c40c12003848410824408001000c55905000b03c2d2100c64641000750b44a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 14558496 1250 14557246 14557273
    0x103030804050601060801060203040317040e090f0f030f0a0c050c0909010b15090a03080a12060603091506030302061602012003180c01020c040b030a0605190c02060103230f 76
    0x103580c15901510396110341800022454032540c607840c181c3d402540950708143ca1075032104021104528580303403021041c84081203402d5502c1110340300e07003415802002004201c00b103a03410407015100b025400e400800c10034034409400801c07150207042c0340c81d154440c1d180c40c0c02c006080441d040c1071254090002000c1c004840c80c15040040840310490741075407505004031000a00c0d01c5079640403034011681c1c41e403c20101e0401c102030441001c460a0001050320039a0ba4042101d02c541c22100c00b01e03030341d0440482400880c030070a084201c1540c40c00c1081c141161006561240c0040c050300000c6160316550714124402c0d045209074004004901103040e820302071004482d002101e00000b0325415070f03022900d58200240b10800d68038185c0280c050b040382c06003884083c040b90300b82c0e2a05445508005c0001802c4c1e4400c0e40d100c2c03200b00c81c1e40441c0c02c041e10014403d5555500700c00302103510241c018408116804130b042c0d180c0c2d2459840e03810901c5810202820503050044070b414031f0180683d0000ca1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 14559746 1250 14558496 14558507
    0x90301050703050106031401230111010c05040603060b030f0604020c0c030f0705011106150d020a0e07080604050c1309021303140304030b010609060206160201200c070503010c0f05070f0b010303 85
    0x5032480b40d181409079047c010031509a8800074070070003c855442d0418550041a405401d5450b080d06140040c00c04008142c00340c2519208940310000400006042002a525106e003001400d10400303441d2842c188500c0510004c0c0b00600400d11a603070000300100401c00400c11a283c2a402806070f85903195181419074646640d03114480c04a40e0350040403449042c08503d891041a0207001d41742d20124410500441902c0610100d80210410070013050b00340c08600c080b882289a0366038055189414000e110594001419801c121032040c8054a050b90040d007615040e00c02081c00184c0320b484041012081c0c01c800e034005800100002c91150001101000400a0700d005651000490340d0302d21b000c0390861543d10078200140c002401003025011840c01c0c03e28082d00e280b001164040003040e07c900707201e0f400b081d4041c407050002004d00ea0f40f0801d004e50310040100b24000c00480008600c0035004144e4012079000f0400001101000c000e882d10074803451304d0b00620b00c4201c0c1c0da140d141c007516 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 14560996 1250 14559746 14559749
    0xf0605060603070203030103060e1f021b0309060d09060204030f051509070e041203060b04090b01020f010b01020a080c0102120406050601020f0d1e020102040503030f07140d05090f03030903010507030501 89
    0x1416810500003030800e007071540c1100d000300300a074011480c5071300e10344444000f0300a51891000038003a9269581c4100c2d0403884a045065880000603a540c12224000188180411820300c0030703082400044815561141625111420354030042960215850700748001c0c40b0b42d8200501d244030f0030141c4000d010000a407401803c2550f40c914000e912a00c2084d9654450742c4179850100c2c01150003c0c000a00c00391302d410b0302c000603090116800d51648025581c80e01b19400580242e903680c0341d90845980d0403c800300e02100098002c01084441c0c1c00002d40b290140f4201030030804001402c1e01c8044070950450391141b184c2e00e005001c0341807514281000d01826a5450f00600c101c254213825401c011030039010071062500c0c0d0205a1a55060241006c1c100d14203030019954248000503680e02d05100070300010101200721690f810061800d450708240107842069254040200d4440c199003020851301d540307008540c05a13040005000007807842c40f42e441030b41c1d019401d20042c881003d4040c1c00050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 14562246 1250 14560996 14561003
    0x606080f010e010509010302040902010e0d06051b030903090d030c05010e060601090b0c0703030f030b0a03050303040524010504110403021003050a36031403090d02160302030309040b0613030f 84
    0x400a036a10b00d41c14482007420702500341d100700000c004100601e000d50003e848140306060802c409250100010b0156240c0e08050f190552920100054400c445d14658100900f1107002403d5013000c10400741d403401400e00f00c5001b41e18280003601414051030743d0b00c480607070160007880141900725101e51604c605951490101d4041e0b81d0205103015402d081d01d41170441680205080307455500c088803042412442482070581d56440108c40d91594183e05015500610046035281400d1604501e03201c10300c11521040d0b1049030328102e81c46842803120b41141c80c00c480100700d4070548001c10002d4400c030b13800294480404011400c0340c541507044a8401c0070030706030404c080c008072540da0389112030b80e00c070400c400200b41c501c8814004041c0c0e1103c0c211402494080240c12303110000000d103903c10f48051081d40c2c00003030301403800350341081004aa080d10300703045e100c050303d0765020036924010902d84903c00d035218581e025981d1604402d82d0010359000e40e4401c541d6550f414662492296010280c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 14563496 1250 14562246 14562271
    0xe250504060e0a06020a0f020a08030d0b19060801030807021813050c0402040b070b090a05030403031701050d030509040207052a0103050c0301060806060715110408061602030a03021606060608 84
    0x128191501c01200c00454106402406c090300c1566528100c0c1d03d04d103c012a8010049000450207102c104060035035100c002c600040c1ca500700000300180c4620111100c5c4041c80c08100c240240c1c2c1e0701000b607504480d804244d564035035900e40b000540c903180030055418449000402c00c4507144440d40107501c250300039400d1382e11101203507040c803083e03100e0303401403120031801041008000303080880c1030b40e4403c080c4030503039403d105c159603542d055070701982c0140c00103440781d42e1343d01c055098541180d0040c03134129015080200c01d564080c0603402050000b6102d5540030130711409001d13080c0700007900302450701e08101246140070350094bd802e03a50b5000c42d001914100026031070003550000c581c140c2d0380e242c90b1442642c0e15642000300c580c4c840c070340c21101c0348180590100c468805008502a01e650b8910359910385040c004a14900303400103088100701c600384040750650075004030845840326190719015039215079038485038605104d41040107100f2850b006000490039400941035006072030206a4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 14564746 1250 14563496 14563517
    0x20607030915020601031e06060305070308120f130201140c070f061205010b090d0215030c07021002031204080a02070512032208030a0302160f0b01150c0305040e25050406 75
    0x2240d81324024000104002050030030b1a000c8180e03451481f2010307106000c0818201e480e5986c20b030804c005940100c82440300402d180c0107552102e114541d12008403078090b036040c41e0000364012070b041c1c605130190501042205d501c2d500c20225044484c807589600461340ea03241c0c0da0400780084403044c4506000210120f124004844c190301405049a403030800803410101500d04028046000324401c990100000c0600c12045450001a501c82d00750050400e032642d9030f50040c0200500030300310000440d0020010103858640b68400150010780081c58240c075810000c070b003640b510009402c4694841c8cc01d413100000e0500000c000c0c50a0b50411b14628002d40b40b0703120001a0000746c1c015003806401c140300c134110301c0340b00354007506001183c0321441c082d541c01522000308260f40c2003c113a52501c1c01c3c0c801403040c003400000c141381da03400c00d15045c001804035443c02003850060740242d0318142c03d003002050701d0003689101100181e20b0b421114181c03813809000908903502920411011030703103900d00b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 14565996 1250 14564746 14564789
    0xa0807031d07030b130b0106020303091b090a09021507050303041e0203030d11040906090e01050c040f0b0702030106050907050c060601050403020108040602090a09020a09090b09042303070206070309 87
    0x10181084100c2500a0003400d046680b0740301a1000103168280d2540108031301008200c0c1c603541b660090009801456480c10b00d00011030038142e0010304040c0d825550004000380b0f446220000c0d80c0005040340014604000d48001205039610b20300035402104042803440c1408004002140a1440f9807030528426a50070000e0040c0307114900003039407503007082c86a210707254003076004209281004c0c44200d24054480301c501086944541013201e490fa5280240c16100b54248603258115400d88440e078101403806001c440b1020300c60152002900020030191b0441d2030942020025110090807070216103000e20340280340b50044041a52140310380404100c2c0c0d94058011101580d4060f91031074100c0d5600e850388e002940c88032040032b400030b082e400c0000e05496288058a1401c0d459502e00e5100b52800d1041001c2e100207140032840307201f00d0f07410b010004251084040c5042c440c8550000c1c0b0b08100507c80c9c2c190b0040d01006900540700050311410164403103007180542c1d806a44103841e0421954 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 14567246 1250 14565996 14566031
    0x806010e220b1903080705011808040302030d030e19030203120411100801030b0408160f05010f06080102090f040506010207090f021c0c17060a1a03010620030304020d080f0a080703 79
    0x40c9108111070f68207003400400c0f210801001c0140c0a82c0c0007140c0303000f607800d400c1c95222802009030b416980200c0c0910440c81d003401144150001c034501409009816a6055103071106584145021800903c990081500900a0341c01501903564010064540f0341400407a207010082003600c03420f9450882c8501900480c00c1c181600d030088861000e030356843d03543c0d0702142d00c020300e00d1140907020038a52000900f144540c05045220384004075034880107107007080a03100190400d00e51079006210100103501c50740c0f50140b4035002194003046d586c840d000143c0c09c103040703500021501d40c10109050307260101c42c1c00419121100d20903100111050200700130890310716500960028001e450004459040034418503000396004100440f00d41e0380f030801000c90341c1215031024115001000420509820080c40715403001a042c03984541e000307072126651a480020300c02403260028034200303000d001d400e20607034143e0300b91a002c41e96658940c1c0c1d805410108211038420009040009042c3c6004111 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 14568352 1106 14567246 14567269
    0x140c01020c1b01020d020a020603070e091614030c070f020a0504021201030c0e0606040e0903070609030e03010b0111030901080a0b03010603031106070503010b0a0806010e220b 77
    0x10b00e01403551101d03018400e4103642009980c01c650b1078011414480e01903048401c41d03543c0d038401d40305480c409542c150150300018040208000c14840e066007000f00d42d00c0d500d407003049030001a410f040310f21003101d0f6440c4000003801404005a000b030343d515042d602c010030640c611385d143d0b408181260801040100c013801284010000d0144083e500d4005d400d060000c500c16150880119106100d144149114880040000b9003444401d20940d21202d80c440014040180039080c0102300004400807107100354600b812064880d8043c0404003614042440a07608058042005449090006202108551712022840c115a4083c402c1c1070243d40709032541c08050681c400c40d60701e0a14000d00440503c80100018811300102000742d0b0072081176803030701402c5543c0e40801207500e40f0003032082e190820a00d01e4040c00070036150b9080201c2c501c41513020000c00d0040b00030041001c911 = true := by decide +kernel

theorem cover : BRFrame.Cov 14388496 14568352 := by
  have h0 := BRFrame.cov_init 14388496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14388496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 14388496 ≤ n) (h2 : n < 14568352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
