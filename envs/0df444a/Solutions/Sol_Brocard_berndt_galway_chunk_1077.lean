-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1077
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:08:16.624379+00:00
-- url     : https://prove2.me/submissions/01d904c4-9cec-4b91-b5ba-55527b2bd54d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 193525179 ≤ n < 193705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 193526429 1250 193525179 193525181
    0xa050604090503161103010915200d0f052805040507090903081015090e04030c0f050607080a060602120913060e040311060c030c03041a01140103050f0106051903 71
    0xc10ba0203002c2e252910100072140d45840d03105001031380e0100507a030402603203003810f2140c044029040800c00c20408417031001007024001c0f06500791300c990480c1301220b460451030b402a0440c101c1c84500440e40c40314000c6408140c07200a0003016039540f01e608002e00e1070b42c248a00007544503d4140c0441c40ba580d5051007800d0046980c051904581881128401c056210712035520075410085401505615002c0c29045880a00014400f14500324014400c0300c04009049901c14402d2130084000010707640c5003080703006002d0040716280d0007502442071103034110710b0302540804042403c004003403174480025a10701000348043d20140d80022544a5500c5c1c10000d03000d109100241401038542e542010301c803913142110203400040c250281e440c0303100c0d80480e0641c01000e52060090960716403009040c0c10307038000340003120b9061400c00e4041d034100a504086000b44820207070b2020082c0380030005000d80303000900e440c1c003034080400144034054000041d03070b1480d0102c81c4a08400b40c88003030140c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 193527679 1250 193526429 193526441
    0xc080304150915120b2806081b0f030a110a030e0114190c030207050717060903030c040501030e01090f0804061b05030a030908040e131a060a090b04060504091103060c0a080a050604 79
    0x1002961703200d02907401c500504603248007182d87e940d5600001c0d0f5120b10714018031003280d55038050700d40030400012101443d15400703180c1060065400051000b180420318056500c070101d2100800d4442c1d941803500c00c428465060140744c1501140468604001619031801100540c1c640960707a49800c00c0000d80309a064846041d48001144c480584580916102c0d00e105020300c9203d00c02c400003e19114404025030b0700814090621504103403c000042d80070700110012001c00799a02d03101c0714041035292b41d81300610317030003120081d56640c02c10400400851040178030011941c0c5611100000070800011a02d0058130b501d4000781030178181c94000c0c0f851046900c0001c41c0302c1841e0503c541c0103807986c98038241c0da01c0380710442520149910b440f0132044003183c0d940e600c081640380401c022032850700102041d284c01400041d00a4070307500001d0450326092000d40301e01c80200c1072880103007130402606801c903942c84d90035170030880c0c011002001e12000808110341246c50f03902094107500c80d0b8100c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 193528929 1250 193527679 193527709
    0xc0a111810062d1107030605091e1207030815030105040c15090501211e020a0f030501050d0f050f100603020f0d020d03030e01091403070501050a20070c080304150915120b 75
    0x34048d41c103050304c0f420b5440361910b4032041d40c0101d03038800345c402c604c001411100d15022203c4541c284446900c050b41c00000060103880b1892840500341029a028030440b442035228465070300d00d80d420030742c5d11100410081c01240900c000c110082c06560380148042d01074400e444800c0c080412030340000340140000c10b52044040e507103e101800311400d940c0140414440310340d01e1407400c130301540d0210141d48081c4115904562407910150114940800000140d4020350840d18021000c0c80c2c101e18040b140018010090b07900d060500031440c0c011000140d2040403901d888601d412900000d02501001000500789070f914640c3d403d00e81400c1d048100c00d680c2054170b0031800c001c148500d40d184c3d441904e00326075079442e160014074080164801e054107204184940011241203414041c510340c82000c0544200c07416070b0001544840402c01031001d03015101011540c1011103102411848181c1c00c2210301c0d070b44c0c0300074403642d0329880469050060000c800100b03c3d81004c6020403d40f68941e450 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 193530179 1250 193528929 193528931
    0xc041a09041508010b041a01081819031b0503030126010507120f060303081b040e01030305040f080303090606060a0e15130b0c0a111810062d11070306 66
    0x70116071040d900000790b00300d410100090000380d8281040000b120342070a40700b0025410311350500340c194403680285a00c6150850045e07000104075240300e190420050026501d070000d010741c101016806140c20608110002010703c0359040e83d5900c68890005010305121501da105d50400d241c1101191801c4a929080c000c1116003400d6000500c00400c0c0118058042d041c81543e82c101a4a442036070112505a03603184425296101c0302c29019840302030b035810034282404045800c580c40581c0c01d00951280e1a000e0307032a807a04001254040c5603503c1808260414020002c0303618000c1000381e4044000c64015982d440110401d8484500d5540007d800001001d041040078501800410805406d0340850440c00c0e91110242d030076214006c0c040c2425005150464005100d180d191404000c000300b000203030781da00d56000501400101c4d0a221001400340080169940008c1402e0300024090402e20840180c1d0703007052181d041440c0c91500b00100c0c1060607503008000d0210102465100c40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 193531429 1250 193530179 193530191
    0x702070b0a1d0f01021b0406030602190f080103120f03020d18031418040902030c031b0a14011e02011d010204030506010501030903090312020a170c060601080c041a0904 74
    0x4402400c8806106200324200102c0003140114540072035504000d0710140c1c001c042c407071801240403500c034182c0e408094002d81c50300d401000040c0c00d800a807940905000c1500300701c0d0340c1ca031401000c44004004500034010301c2c1005201040c60070030320712048461070070040d0342c2a140c85001c400905c62140d99601d0030b8641400441c2030b01c182800c1d03c1e0105d00965516079013900300f0703181c21000d02c1041e00d0380ca801c01124920b509641030980020102c070b80018203440340e10201070702090820480f00c0c060089908944148942072902142d00c10107003040d901401404620540041c0694100c800c0b0340c08840740c00d2074820300c92803003500004241940c00b004601a89c2d001c1d00c10b40d0107900300d40000c070790074060131002003910b5200b44926510780340c2641d55810258a1901e5019461180451040450248900041c04100c070303c200c0e800840d11b000500313a03503128070b1800142841006008141044540c00601c07500b5800b12094405503140071a55810460010220348030b00e1203840b0300181c1040c1410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 193532679 1250 193531429 193531447
    0x80c15040e010b09213d09060207020306040807030809030a05090103090f021504050a090212040206070c0806130b0601080f060112060305060903030115080103050a060b0127050f03061e0702070b 85
    0x41a24121a107114000f08001e414012503510040e03c6c1d84406210841c0001031401020240c0d0400310000b40642001454640315401003410214125000e0301c00ea00c3c00691720b4100360f13024103515171103542034010f076003014041d1900400714401e4040490405454180e02c8003800340c00804080416402002e40d0101849a20b0281d0031750081d1107040d100707225003507000a04c91003a00845441c18039a407008000b554955080000503044154151f4803006c1241011031104c40c10080b01f401a50380c607400d105e520005281640e003414000745480d0400c003000d000d20001136100c4a9550b0840d00908156641c9848040e030f24004200c0e96001034071600c214402d0094111002c001141680d00702c242e05048a4074403031040d05d070001c080c0301c01050359202a01f000e011034055440103c2d80d0a0500d00156258405131001c810600200410020410b4201080003145082001842d00d03071415009020780346414400e100c080710456507103d82175040301002841e0603200f4001d59014000c40c08640307881c1c00f050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 193533929 1250 193532679 193532683
    0xa0e0a06030b01020f0601120b040c0f0b040504062304020f13090207020306010501230a11030a030b042706230405060109060f0302030d0e0118080c15040e010b0921 72
    0x1070b64190241c003511981d003984c4078011480030f040c0c0f50100c2c0d1003500706655666801061100030070542c1e10f6002c900e0041a681f65401c10f06004043d14204151224100001c00007103e85940c0148400c610f0b48040308481084030082c171000d403004403001a00e07658a40d0100c1524403800d81070101c04920f9040c04100b02d0750550240c10720030700981c200c68035aa00c0344015143c4072481c0c45562403800e2405002e060000040c3c0040940401d245080c0e0070100400c1e02c182e1075034000c07240d2000426220000440b90341818410560041c80d880c00c05041d0100706003c40d83c41c140f040d8409027116880d03801640c3e001c03400c04a0300030020041074883e00c29152030b091582d1030348070a021388548a41001c10000b200b811845c40c000c1640d030018080c0c45a1581c20f0000d40307a0070b10b04007645e414454201242d0402c507402c600322900401030315000e0030b0810243d03810004001413070800031540c1c0c0410f0001b0b00c9013031049207215054030641100e00b41e5910030480001c5140740381070040c40d002c40200208610800340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 193535179 1250 193533929 193533941
    0x50615041b1d040608150a0e0a0b0406091a0412020c0a09021b03040f03120905060f0c0705100302040617151201090f0c0e160503060d11060c39060a0e0a0603 69
    0x150186d0714041c0c0300d00c2c8100055030780920454a15900c03081c0468046a0464817040d00944101c00c0040c21441c5660b84000f50064150520b40800c40801000309000b12000d207c1e410344160700c05440c10326801c0d0000303039852480e40203240140c0d42c0400c04156100000306045120f001601c1201d44a80d5910b10184064080c1c1c001210401d20280141c0c80581c00b90340d00702c0030740304020900c40c00c02481c0c00034203860380c0104101d10058454032074000f8003903c5420103d05810020f95015035554200b4402400b01e041c0780c6d011403070340540101001207800d4100e40b00300c0311020850b0090f10140e1042800d82c054007a1110103801d817540c00e04990204420703580180201e8400788040401075568806a841c00c0c0c2c041100c15000c68000c00003e1140c4c5801f0826005041c8130740100c1d40000c044101250881d04a8105005654408510300420100310a810803a46114807115111617089210183e0410000b540041c0206408030f114040c1070301500c40a10003113009080a1901035032860001c024080d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 193536429 1250 193535179 193535203
    0x8060c0c0708030a0c0f021306030516050108150925020a0b0702031e210c071a090a1230050c0f07020f01030e0604050615041b1d040608 60
    0x4510a000544103001000380c0c0c255894986564440381940d490b6030002c0400f06c0c1c02281d110034640142d099800b282e11684016500801c000c10b42803112020700302d00300c1e02035084541400603041c01c201040c251070b214441020307025607020700561510214241620021b059441c1030340320000020b680c00f130313000820516850040000e8250303921030b100180e860340300710361119200c0c00100f00000a59015a4001d003107154900a8405490901d104000f1307068078191000408090002040320904c699103c00890000c00e4051541a906000440d1951080310441c014003140204081c80205405080d8017801d9126001009143d039900c0c0305002c0d000d00b42d107a4425480780c0381c000400e0600f1215410780d03482d40c100052107803604008c3c3c0c08214046040b003401a040584aa00c83c0740d060b9814070141d800b0394440e0008084509103102025038031440411040e0140d450305404890f410182516422a000302d814a4036080c680c81e400c0003e20114150b6090304035040c00000a02e5402c00034110700100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 193537679 1250 193536429 193536433
    0x30f0302100615020303041b080106060819020c061302041404030309051c050901080a020403140303040507090902090a05041115090f0a0b030106050d02041e150201270c08060c0c 78
    0x16440f4059008a50102410708005900c244002800030360240b04c020507130705180c0201144156180842804d4402d00d401032000640e9620921070080c115060b4410700c0f4000f46800e609200a1a40d440c0d40c9100c0101b40c02c298940e460000025504c55502000307a4106140a10030146811304016014010700f0804840603c01c02201081d00c1c200103c151044003410342d1440c4c5861610300c0115151103000e0708148100d83e01700800030014a08c80c00c2d8280010040340695100d10786030070401e0818026a21200507282002015070040e034510403400e60055008500103295200d40c1003045002e0b030388905640d08121551640601c05144101409a552049035250030084074034047c821282c082c0d2064140500d0244018080580245c0207010340003590803005042943d248064103075208800b5060070032007000324080c410050080c484084454182c0001d10a80440343c54510f60320004192050402c4071040003001001b41c1340409400505400045030034501380707640d40200c2c65006020600301d40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 193538929 1250 193537679 193537691
    0x80c040315022116140c0a050109030f0503010506030a0507110d1107050f090106030209060c070605070b01091515050d06030b0f070c0c0603050705071505010f0801060302060f0c07030f030210 84
    0x82000c0100350f034424094107020800d850302d4420107a90b07114800b20700d40031000080c00618140d4208201c0c41e5441c0c0d010303500200d802502410041d00c8080144142820050100700510094448900300e90700301128810014955039046011a03040301d1000b42601240540b400307440c0b01550141c11003400038010001c1e144010f584a040242c000c03e9a01d110b900443c41e42e00400030540207134041c001d1090043c0800b0b261503144103030242800c500e90003000202d0f0003c03901e441030150921090340501a200820001c15000f48101e9498110324410310920040c0315031117a034a1803003101520103e41041d1824012240ca9107004d424a01d0100c9004d2051040300d00000c0c0e40d80c0c4903c0d06030407640d80250004060030709225088000d050002e2828007404820406040050b202c041c16403411000380c070002910794101803101e070460343d00741d000da90a40e040c10020f0025903640310440352290540752a00b641d80c611f500500d410690b40798070141210000d4958007040c1600826444c1020038040801c00032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 193540179 1250 193538929 193538977
    0x3030f190c0c1202010b03061f09090f0605040305130b18010c031b05070317030601030e2113050315010e1f0501210536030a080c04031502 61
    0xc07a800400c50100291401c181500424003492440781460510710010406220110109203490000d407902015000d8407003d624804684038000c001a01d02e81005008882d8161243c5540891800003c0c3c6000c3c0e8504c04541014040c0c0c04503100e0b44841c0c1c06551055a0350400340700c16400181c0142c45007601c142c1d140031158400c2c2142c50700f040c0e1644078550403000360b20350100e4035005000c04403000e21070344034048003190900e031400b4400c00803504c2d82d44e50b9280480005003901c00000410010740e00c0403090111400d0f1000743c0c0e41e143c101c3d1200f81d5440350103120b00d03484041c1c1c80b64000758060052604d40e405501e0003904043c1070321000003030b00701c16032a49040480d0302740d00842e4640c110300ea941c0f01404558445c018041e980b40f120304043c003008211a0b9110203c071015039440c0000144a402a1465000e01c0342c051410407100444032000d080041d012500e0303102d80300c04041013181603000260030061000541c1d0145800174004c148100300b450030817001354860510401c01c0d0065001240b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 193541429 1250 193540179 193540181
    0x1a030601060e18060d0803040f150509010e06010602120f0403060f02040618050303160510052715150d0c0f050a05030109050a0305031003021207031208090a020f01050c03030f19 78
    0x4c0034401c0070700b4001d21300c0320645441003942c10180049034020b1015035410049002c41085400600562000151a040480255085549134000d00d496a0413182c01009480d40100e9088901e8895032081076946200f403c00c01404d01c6260002044940350610f2a44203110756405403040d01c0e40c81d11a440140e214554445030000507104081c0d1690003041310a540c0e00d0301580f00000c0340e204038219007510802c07115080541d40111fa80741c000b01d6001800d001103030a006846112122200c000d800d4440204070110110240200004091440c000340e242468079107040e1030482603040b00041e1046501ca20300742a04d00d04d2442024894641908013254503c0d040c0b14500150ba44100249822101079509441540008248940044002d0000805a2140f0300c90410004c013110140c100700d07055140421030040c071031105d0004c00480c4010010201000a6003151158045030b2140c450100100121094820f05508107124080031082c490449412611240601280300350785a04040311001d0b18 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 193542679 1250 193541429 193541431
    0x50a08010c03061e051009031514130f11060f0703020f010605040221070302090618040c020c0315190c050d060905130803060a0e0106020604031b0b01091a030601060e18 74
    0x31500f031302500010404c6113820801c2a80d1b41ca8039041110b4442d82d69115016809944480d180010b503d4140c02c2e99541480c1c20525400061812400480c0f0810785900c01d4080000400622450f45003028501c03940c0c403e825a9008840312041990300e429a01c0c0c020348a14600000243c90341c00c02101085500d054001c1d036450304c410b80e0900160601c581070085d445440641b2140905508000709032032601d4200052000c0d80040e110520f0010b04041404210b48603401c0c03030002c41d040152030702d010b9540031540019000c103c0556907001d03110782c3e8135407a1200c0101a410082e5142400001003070f600900600042c5c41d030f043d0204070441e6288032510903542c0864244a4540081e9250000600f03030300c02540d001600505040306031502c85002c42c481c80c01c02c2c1c00c2074015034403010400c4101644030200001d040e1401040341c14100156a070300c50030200600030315003030b2504c5040515a07030f844210202003d580040841c0c40f40d503940e0303e020300600c0c1104211409500034604003a01151122265 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 193543929 1250 193542679 193542719
    0x50c0f030705030709050a090213090b0d150f1a0f0306040305340501061e05060901031a041a010212030105031011040b040e01260c010e0406050a08010c0306 69
    0x10900d50359030300d00201c0700c50388028042001d00003251004030311511900002d0014180b000001680c40c411040007504040c0e081e8440004141040054021a03d038100c0072608154000c807002c407440590460300d4080c05403000c64920140c0b91050103171900440b407000c1507881e60192100d9130401c509005143e11943d04540150102d40308100704101c402c640d1001815204900b80808003540080f64181801d69549100f076510744e443d5141405075201c0c0f803890b040d045094110f1600700d103203804080340e52402049c0a0a05059690740001d24001c840c5505100341c1c00010820040300001000e4103040982400c04140144198080200441d00d21803c4a0607160002c0082c248080c0c2c0001840250003420360036001071005100025120b000300e4060400350000f00782801c050760400c1c105a200303001180c1c1811940104100b0181c0ca00e001013040403e001e420320700000030b581490080380c0542034641c81142c0110070540c2c0052291010b42c000d03000c00b5030558082c410190b49d40d00d002182c3c8207807040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 193545179 1250 193543929 193543957
    0x30f020a02012f0303040b060910030b0a090f1202010e010b04090308011403070e070507050d0e060306121608100e0c010807030e01270201091a0d0914031c050c 70
    0x3040c6421400b00c6180f03409424040d25001503040074003c4900b150000d6034111001c0c080340c8140526441e24050f401c0d0305ca042d1149106126155448001e18002c0150045102d941c1d113440c044103201228880d02800c6401c80032445000b0000b9400034000c01820036100c100d541780c0b240d040390500d4a0300500e01300700e800d0703540c0100e00d90070030654003050140300040c90340c54441c2003400030b0342c103081c0d0f4400b074480c43e260344847c0d48a40c00d03030802d14102131141409400304180c000c00050301e0b40d41e00041c0e0742c00c40d4065580018000d01421158940034100504030400c048902c0b0005040b540094036070024954800c0600c680c1503000021980c440124940e540071070000f400160b092446a8042000b8410307550000c502106c004c8070303003c03104614450380c020342c00c507a01c1c0130b41c15940c00c101c0080040c0040c40c441220742e18448468001d6005407655428102c1d12601d04405000320b5030301d03c601010914040d642d60305260100225801c2100f200c6070042418440040c0c0c160719924203030340d80319030403441c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 193546429 1250 193545179 193545197
    0xb040509030a030b04022115010203120a09020103060302040f0b01030b030a0506180c0d08040302030d0e0a1a0708030a06030b01090e03030a0f140f01170f030a0507081c0504030f020a0201 82
    0x4003d401a00011007010b4000303900340487d0751103150f0180b51030307403820912560071100d0a00c0200000c1c10010000f855055510030040d40600e00700920615078040081800010310700070bc0d00c01280030b03150941c00658414244046091481d8195110803050302d02601c0c10481c1003491414181c0394840500040d041d03400850008400c24211180c401600c603e00054800b0b07040c42e100050501d45207240140c420250110303080c4210304040184019144685c1400280c070425440000d18030040c03402403130040c1c1100c502d41000391301c90304103030348225510400e841d49030f1400e12134150040c145c5200c10f46600301e201000040e1541a41b00b4082d0480c03021014614540e030300b20b50714025007800821140c03030a50b1403a295404410381004203004035640d100401c225490402180e10400b698031240e5100d07003150501c1540c04200004980560105040050f01d4483d5424510785134068003c80182c5944581c11803050309100350321961103240300e510703400001e071030710316089958840d510f0380240441c24401e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 193547679 1250 193546429 193546447
    0x30209120c03031806040905040303050105040f020304050a1401021c02030a1d15060d12021c020706080109090c0f03030c0519020108060d11060703020c0a08030c030703050d060b120a0b04050903 85
    0x10189814908050100c5140c80c7c2d80310850b808407070013104e0980010f0b40d200d00501c240d26190051041a600349c101c2035045040c41d448540d00c4104d00c00c001428403038030450620314014203405454401d00352130351203413001c9800301c100406903000711140c0030068580840001c12010701d103144040781c00b9234801030541d0017a12074030b08403111014221650089003030f00f100d800030300c0000400f0388070b04059015004049072040c5008000641c0030813101550081c0c8824001664860846c80c1100c02e90b41c004100d440c8681884403000385950414128012507a2022080c90380014964150034854400c4410f900d6003281080c02c08201504024000360409010922601e0280030041e004c502541071030007406102d01c00510203500110701100540c0001e905c01c89076181040402000f08640000785140c080034a07010790701d0344509503008040c0200403580c0410084039902600180204030000395440c0d414690303584205a08603014407c050800342403000381e061901446001d180080001c5042071211 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 193548929 1250 193547679 193547707
    0x4060b180112060b07060605091603020304150c05030f0f07090302040e0f070603060806090102030705070320070b0d0e0106061b0f021f0807021b010819050106030209120c0303 77
    0x10000c14100084100010071035501403060341c0040c403841302c03032550341c5d00c5a141990031744401c0c0c3d20540c45849071030104401007070132000c002080c46c124680182d49507603624243d2480c1d08114640c140491510405e100101d40210080d4000e651402c040503095445091507104030008840e03000010307050300001c00041c24150130080b07403c0c40740000d175108a1080c0804524020311644007800003501d801c020008000c0511401d900810f013000294610310742810094039610460724020100301200304e44039601a402d20b0260b080d98100d2042d160701e51b40c0e038440c0b1001504a040700e170082524003120b00d5000c4105109490444070540c5400c41c091103088030300100c10aa010317082c4d80e181040d0148200503610420b00442c8030380e4004070003002d1980214000d05114008110200750350091040f4144120000c00e071358022102440e10440c0c1c2d9071100342210180030740d40310800ca083c1c1824008206950150041c115446003a1050450001441a060b136160741c82100150907400070040902c5045407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 193550179 1250 193548929 193548967
    0x3060103020d151401030603020d110d0611030708012103030e03090303030c0c010b2d0402040806090f0d02030f04140a1d04030f03091a040302010e01090c080c04060b 73
    0x105050060a1800e42e01c0054140d03140507101d0b0548218124041c0100e2000e01003100040d81e0178a0204a01c46c1550f0104180300c514080103031420141650526941d40c07468080c210499000c4000e1224140c0f081115002d0f03001070318041d02245803d40040f03142080c0c48050648441d141d007800e48188a41d4400794000e10300b80e800705003240401c002d01c103060b8504200a5011781c0b003c40c11941e44484414a01d0301b10340c8042c580d00e2145610600e8829111f201c081280f5810901d800010703885400600044c00901c01c07940b105125000310400c2110110f800316100341d600c20303000f050300c6a1b02c42080c03080b80c50744606580012001c805202c18041418403880034a07140e000982486030281c0c0742d0850740034003000801000880b20310340c8200003c01d94001414100d8034000c1c01c0900a030a072694441c90b80c070030101034108c035075060100040c041c98400d4000c25500d20b40c00c0001c2100c00c0c102d0802d8100d00f14240545240740c03103403911840683c1014860305c01203c0c1040725060810a012481316500d0a1f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 193551429 1250 193550179 193550191
    0x3080a050702090c070f35090909060c07140106030210080415050c070f020a030503040b0301170d17060a0b041401110c09040f03090305010f0606030b1008010501050a0c0606080303010e0a02041a03 86
    0x112500a0641000b02c031441c4681c00d882c7c40c0d1040d03160801d9138104284e4503002001010590020000d1210005250003900c02043c0d20138001d5400c0310303c8940d8140103000c07591010358895002c00d64a50034641103614680a1802070164035117124210700180e098031010344804280b444204100004141e1a21b0382042184c4000d284100780740d41e9444451450700140c00080c1c01c00740010040180620b1402132600385c0202c08045c0c41c00514800014003581e200c0c4420628500e40200003c4030f90390b03018615805040e188030019141c0d40c0310340d81121200e103140d11103408540311840c0a42000d200040c0401c1620009002c80696903855845100400c21454218107003c0c9200c000b00004000303010308081444026400100030f881c0c000c2c01415504102440e50180c12034082120540da030041000341561021f0804695401c1205011608c07031810100192441e45400740100d8503940100042d812251030030a03100c1140c640080b51000c034402c521503424403600c0802c1441d1114840c1010b0342d40b01d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 193552679 1250 193551429 193551473
    0x3012a0c080f04060e090a0e030a0305180d0201320a0b1c06050f0c0913020a11070308040305060f010f120212010c02010b1212030c030c0403080a050702090c070f 71
    0x510321103030014160010f810440110710105c00c02031403414030706078080d481a80c2c0c640520000b444241c0d281c0d124428240345604240d00c8000240c407075843c000c3c0c100e0786031400a084864900c150300c002402020b400303c00340100d401000e4140f03c0d844603403420f45d005100d81130317400e941600d5501110000b4145024019085102d0304691007454681c41005140e042c014075011a844c5411912030040a00003408001241414000c68003152201c0071102480681f04d0301c0140e0b614028402900d031189003102095071480340ad0000702c10454024003038001c40e4890022242103440e0507944142e000c500b4048c0b1001e041c074041041044500440081070309500103808580300700c1c92030300b601707013034507544109940540e444000c1c986460815042c90701905950344007908102640c0b00d2003038010322001e0241000c2d4840030020444030103590301102c00459109c0841c1d541c50307a0380b20011344240c005817426441425140300245503650210200c40382c45621602e055a000080d541c4e0171410000249500146 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 193553929 1250 193552679 193552687
    0x130b090c0d06080a0f021c08122206060e060a05150901030213150809010b030d030506060405040c112407050313020919050603010b010206160201230603012a0c08 71
    0x1181c2888004c0305580540c14140030790019005120b060f40c0b41c2c44035039802d03510344801d10003c01c0000060301d103071078042c0c01c0d00416601c8011102a6202c01c0e00b43c0c8c0915070008080c00c508010550b030005084070660900c0706d5003035607418100180300010388141074100070000500c101e280da000c0b00030804200d05040050418101c40529042c4421940224207400003460300303181c0b4160020b60703403944200c8481c000e0003181c031800046030b01d41c94a00304100501d600c42001c01d42550390007050346c010382400b0b4410006560070000003880c50500307445054030b900540d1010407110580420611202d07030890b0900c581d5807032340c6d0021603050384002c02c040320422446400000513524581301c14001d101011030030812150042880049501c0580510b1207a8500a82402d85d640c0118035241d00c58412600d40f440760361a00c1c402c0c1d000d040c030305a80203c841c0415440c1070102d54a4100513000c6d07401035000b00140040c40301443e0040c6210300c9405009152107101c1c40c0c209119850890f5014850700c001410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 193555179 1250 193553929 193553939
    0x2010e060f160c1701060302010e040b0d0807030201150e04050619150e0105042403030309050f01050901200310180e0303090615030706050306040c0507120e130b090c0d06 75
    0x91180b5002c0220340541808104000213003002c800c143d000340c50b10008200d081d00e19070010300400c4069880d68042c9481c0e507403c8005039034184048142d950800d9007950baa0340d4616000f07000f00700c44204108802d9000c80f02148100d440229a13110f168840c0081c8407a840700b5447e0340104a4003102000015103810a0326020190081350200520712030000ca007180d410701040000b03035407142024460801610108084c104c1001101c00116501070038005403040441c00c00c2401c01506800000c819800e040a0148910f13055000002d407080c0300180107642d140e0041c0c5401184410340781d0780f00000001c6400e0000c0380703c0001190b05082101000200c03446038406560441c1c0080b00c0c1c4112070f80280c8200210a2508001401600002c601500046007400400341040c04090201d500655541c8040200c40d402a011540c0e8280c201070840d5220750440801401000d101c20824007810b03c481e80d4811030034190003040810140146245150f41d252004a1081c4d0880c50610f24215252040011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 193556429 1250 193555179 193555207
    0x402041d0a0c05120a0f02030c150304030e04050402100f11071403060105031f0504110604141306050d0311030d02041e0f06050a08090f010f02071a0402010e060f 71
    0x191100802000d004a04180c1c20000460b110641c0901d005140002014004003070101780300c4402c0b0751000404118600b01e0000c41d150503924003145030003091508480e241a000b40c03000e18030991103030ba0740c0030181d4000707401c0c4400e69034250340c004c2d004802c0c00c07c004101070040b440f10100310b030b07145403131440d0130344a4060501c0d005040e403000320704d8440b4038800000c40c10700307100050140000380c00501d039220302c1c803020f100d80780d4101d40c20025456680020408001da05401000700d120020030050300c0d640c0720404801e004480c3d0446034400c41212051040d000024002c10342101e030002c00e03100030064140c5080d81c0e819101c80601103580820030a110241d9220f01c043c2000d07146c2403200ea1450100145c032031104900a400c004020003040c9401c11080e6400f50880c2c0c0c0300106031909258584407030960a20308003140f056140e180d401c1c00080081980c11f98058000355010380e400b014005058414444c0c050001d840190015444005100d0541040801000d0802480c1211442c05481500c480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 193557679 1250 193556429 193556471
    0xb031501170a0603022e11030c0a2906030309040c03020c100c170108030a050c0f0f011a0a0f050f060d0c050904050c03060a051302091507050d020601060215040204 72
    0x69080d5540d401c04d0003541000c410a00241c04490000d0000c0e00f01e800c000c1040e081034001c65000c0140101103085151001d2003502d10084004040b5080c26550340380ca9070102054040143c40c5880c0c115010901d450208034480c011a0090041c500e0807815409200203404032524200505030204150b80601038100b00310044030810000004804044100c01802011495a5a400b840c03200340103002e2a803000c0700b21009000141000356440d00c81496550030200d00d041e90003694001c0808080950340c0642125691811030411f410402101d08108148402a4062940144c0c6500c00c00d02c0b05040000461141c52002800541000b00522052042e10070300d1100b400090004256010582000d0040136003003094a40e4250952424070041a02d0000038854a8426860411441d40c625010750440e1303042000a4421414030700303c480046030030350040200301c40c0391181d1501980b0591021034000d040c0d504a038080c001da0706403098030000010000c2c0084e0b03402640c1c0d4404040d10f620751007540b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 193558929 1250 193557679 193557691
    0x4030212060702191104091109180706090b1206040e0613030206071b03080403120e03250201050403060905030910030f050708060d140f01020a0c050c0105040b03150117 74
    0x61500b4079080c20000e040000c07802c50140b03140c0010b141d400005c3c2c01191020305e514800c1e0342c00103080300ba509200900410344c11100703030080c075140140100a80d20030f00071104e0503a01390444a00c6986e480b81114501050700c11805440f105102191900088003019500264010310224a500e000d5400c00d045c0301c42075818101030b483c1c6144840030142c05000050780b140361410054035902002000c4525110711a80090070001660b0000b0101401008c4030310110b030444504115042e01c0b50001941d0343c0c404001c100300e90a01d8010b10f000003100702222800564181d4410b8140b80c556038944014000450023104c0c50b000c18000e8080f1600d40749503800c0d08115603035000c00d10740d2040b1140c004442024000d4030030095550100203c540340c42170500482580001d20414240740c20070154100b101140c000006540001900c10303d00341d100141c40d03c0c59025005132803070200d0349001555207202c0ea10540040140a2001a05090000c69802d105400604001a50b41c1c41800c40c08140c4004441c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 193560179 1250 193558929 193558933
    0x219020a03030f02090904030f02010e100c0206090109080406180504020a05040501030e0106051f0e120d021c0804030c050102070f2604180510030804030b0103060b0103180305030c04030212 83
    0x140c002032541c0341c000d080401018810031441d0501000c042111040c0061015060068890b00c801c0b2a80c400d6200310410f030300714070944000101907600c4001506451030361100520808000ca1200034042c8203070041e20b94814031086c40c4c90300d40182a200c160010400c16600750201d84006801d4446000610a000f0a81d0750296600e0504001504175510740502800130fa250610900254403010f25516280021001803604008015822260100b07580034103604076042444a05000b0030005101160071429002c0d42c0550b00400c56803008280c004140c840010450f001041c0402e0142101e20041409a0009840e284490311044007445100343d0440d000b2003404002c0d201030700c0e00251103021524190a070352801303103461009180d50749510490303a5655920340c08607013040420b502c0c6000940d0b0083c0c01a40700c3e0ba0b24208000c20b00c601348429a140c5043c68003900c00d5610070300c40c1ca000d115604001c094050002d0701c0c2214030341c00040c0b5040b41c0460400c00440075913100484401d240f40c0380d0300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 193561429 1250 193560179 193560193
    0xf0303131410141611100506040b03070b0a0212191b1a0103020109080d0e060306030a0203190201091d0a15050a0807030c0602010c0801180207150902010908120a12021902 75
    0x131030500c2092010480e281000034849180c0c540d540c1c041840106440d040748041069194200018014100318a5560f4144240c01001540e56101b101802d081c20282d000c1d40c1e00b108105450440c10710074812122110310b41316400c1183c0740d005042c80d070400701603603540c06004482d135511660340300c03520400c0c5421000c107080104115a8400d4a01003e48000000362200a0b0843c20240114400f02c10301441104c02000080240c7c40030441c08625640042c219a1301407582501d4907605851b42c1000d9000500840c1c01040614542440b0080c4204c40c1260400c0c9030350f801c001a00038002c2c21a904801c0a0200c07000031140e864044c0c0d0000707002120080c00c03c50f80b80d031600c14a02d070481c0e030140041d641403100084220381c0060a01e41154030b2103104040c0c0583c0c040c20035000b4800d5050080c042ca4800c00c0461401000385d0251000724400c0c0c81d00d5008544404419075248035809000480034010040321300e6842c45101c06a06808040502504246801e40e6403843c007031030f041240740164011303a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 193562679 1250 193561429 193561441
    0x120c0201051005120d0c2a03110904030f1809150f1a030402120102070609060203010e091b0f01110316171c05060d020d0501060501020f030313141014 66
    0x1214100042000f1074002c64440400300e45181c5072117607040103005102200005200f40108000c401c070340380b8000c1082a0482e502021010b00c915540e0105403054034004030401c415040404402c0d00583c3c02d521082140a0b5446c0304550b4043c014070116000c00b032600c0c001902c0031b6613020305100b04884210b020000d60400e120288085000c1d482010081c04020035031145c000d581d022660404d405880c2044c841c1001c0305042d01a105442004204518001900090281c42d901440c162846090500b2613500c4810242d503031409804181c04108403008892034081c9000021444001380604204000f90800c1c18840d04507041102c2c034075103602d20560f84204100a220441c08003e0011039903d040046900b88109881c3c035124100700e01c99501c0020549694505000c40c1980382d008115900c0200689400781c00f03400b0611440c1c0c094400c4500780d6000c1c1c107012013501e01c00c44420380101144c0e1042d85803c1801c2026007904411170040031960503401c02c0364090840b1010720140003511a040030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 193563929 1250 193562679 193562701
    0x210c140f0f07050d020105070305040b0301080c040c0833060403060515011b0210030212040f020405060607030c08030a060e04060b270708150a1d010b0319020a120c020105 75
    0x3061480100d40c2282e541440150f9540306180d0300c90740c080ca41140c48044a117029111441541c0110398184004000000c00e100001040380e01c0102c10b07102480ba0030b1645c0e60a660311081605c000c4410785c0080259416007580d4034005c110741446e03061508003d2008130206031250b000390000d94a554548042140c05100850800e401071801e00e80440d480c407201c004d6098924106400038440e0361551001130b034a6100380c0542d4090060000d010b0a6030601e0b291104419500b007408034000c0e82494009507640c5031040a54090603096114001414600d9942c2807059200502034100217580700f01c04a074a40d400e2901038407980c850440004d0703071500d800c10400c070704801301095000f41c200c8804d1141e101281c0c9202c43d810035000d0074582074a03102c1c0c590a954030410b5683d4103070082c825400c000b458403000c00721200d441134425014030035030741c070b520041d186c80c40200c1e100c6200841c0d2600d098401d460507402401c90f080d01d07160030f6000c0d40241003608250340c03590741da100051b911a0b0a0008242c20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 193565179 1250 193563929 193563943
    0xd0c111008100806040b1801060f1503051f05061b010507051c0606050d020a110f03070308151c0501110f090405060d0519080c0d091809210c140f 64
    0x207003c0040c00781d4913003a1354050407110018950030b1041c03815240c0c41c059800940258019041c52084c03e0283d5880d82550441014901e12260000c1d003050041105814045e07090140183c800001e1903070b0b0b030300745401c1c086c455004091901c0644000701c10b03808d260900780b041e6406070030310f5a6015a2180e0f500840481900d8034880b0f0300405240807401c010b469042812038089042c200400360710b03040d000c041a41c059a52521200450080c51561240d2100100003000c000e4420380755241c160312100c140a42c01080c202804d50011014161014055118800340070114425000850285075039040c1801c01d80040400c407004c1c000c0031941e2402441d2501585500c0001a2810b140100c203a844142d551200030041402e482c459941c0e903c00c2c40107181c2200d100d40f2052040b601c0603007414a00909180d039901c100150400d4039291980d0a400c54001c2c080341e02e400c48903010b00b20742c1d4100114440702485406600b0300070345130360040000301201c680c100040301d21300182c9503060f81102050f042c050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 193566429 1250 193565179 193565189
    0x1202070302270f0c070c031110080c03010302090c0d0e0106090506180402090c040302061c0e0703030c1101050d090606052416141005061c050d0c11100810 68
    0x200a80402d6451014500969004011074104480394072000e00001c0e86200d0502c018142503090a00441404200c4007001c3e120300c825a20560100103801c0c0494110302c0554041001200400041015180912506800419010142d03140140d00d00400c001c40303050400700811179445150810540c0c2c01b500c226544000706460240741070915841a10318003100500080c820165100816141002c0c00c054401550b4090f194547d50001289070348071060302c034020070300c1060501001880810010030114100c980c1511603069544840d42c80340c0c0903940003c2c2050412000380301d641c0c10010755021703034031000d0f0140b10300143d4241000b0600204040010040e0400034041c0d900d030511103c121304950440030440070f6455010000d20380700d200040d81700d00c0380c405445a0f50741c41c01d4841c4154041401203004503550202445001c070f401c022240d00c104c02408681101c843e40180c6070284c4500342c005440303510b0046542e03d582c2c1c0080d9110050144100c00525500e040000d50380040c03041c180540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 193567679 1250 193566429 193566469
    0x3020709061203031125060c020106030f03050a021504030302180103050702030a080a1107140d0201180f030e060301090222050f010c080c1509011401080c010507020d1202070302 78
    0x1030300340429034620280d00000241055070798040000c484260105641140000e041516078019514801c8041d81c07821141c01d0385c1f11407400c040601d05900510610003200e034002003110f01c220f22521b0a440b103811881180c070030f500800d12403610200134801403600c690f1280e14010384440c50038040c3c19540d107503030000d00e051502d041d0a0001098000080e101998001e1510040590300c415003d00501920503241310000000b107420810803481044898645109404032100501860710807400e8a180c1e08402e003840f1104110b50b00403503010480f0000480c02810100110f01e25940400c120b83d000341d00c101582c1d503020490b495030321340491141c902c2e40c601d400c072640d2003403c1a0011740c0c400380d03414175203040c4032011803d0750810980030141c0708801c05040035038191200030804521348400032a43d001c3c2079407070181c0c521400c070444103036075042c2d8014000400008261000540c0c0c0784e40102000da0780310010b0800c8800154000504540e01040e130303409084102d2451060000b1150917803c2c1000ca0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 193568929 1250 193567679 193567691
    0x7060b1009050d061e02120703020a1d210606031203010e0a0b1309060c14070c090e0a0b090a020901060503010608070c0602040b12041b030503030103200306100303020709 75
    0xc0d981c010304010640d94125030b00307003141030b940c50448003d0000d9036a158180d8405a03500514011690140a00c203821500100c075a0b179598004030100c0c8030300340108000c1040c50320810303e040c1d44900d42e01001383c3c0140c030200d1107072042202c0103058140303030640500c2035124030104600c078107041c040748500c50300b0328407046c1c1154102604c100d1165802008011440e648910344000c680e01c1e803070445450720344080108401c80003801c1a80c0030300050715052011038031140024003401c2c44a000c9072803580d0402c0321041c0c2030b07050402d00b1003d000480201d5486104905040000c500b40034141800740000c54024250940320f441800100b210590240302800010f000400c1101e4000900c80c0d4899440c2c030f00f14200c12843e15003c0005e020f10340001044000c0407500150344900c0304000c500441c01082e50b2610256426283c890141c020f0100814903003061004000040702482e10000d18030103035080e2283c0c911424082442c1041c21261103001d6501a241041890b405209080c040e110880081c026 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 193570179 1250 193568929 193568959
    0x20c010206060f030109120504090b060414100201110d060e06060705030706110403230606030f1f1112070305090102070c05010509040905100e1603050705120c04090807060b 76
    0x12244020b2200c0d000704181e4248500ca0390302076101030b451590107840c0701c40544081d04024510381041c040c00006c1403074a501c0c2c211602d0110103480882d10046034140710102e03d0401d10045031424803001e0155901c503000a03007110b8042018183e08074214400140c420300c1e0400419600901401060140d403080141c000866008411101d240703030011303000b02d0707441c400004260451045900207000300544070f80924212450070082ca4803906550203c86803511540300f01600c0d0399a44101114541c002401000c1d4480c00d2501409805200040000c6103c640c101c83d24050b03009060ba040380c0d01c000c80030031207480d401d0300c16680c002c5a602d00850610009541d0441c0c013520358060141030040104407010141d484c0d800803542c00b944141076a0b1131015948100c005000202c010703908900400c0c49481041904802c0581120780182c0205401c07443c0c201071088816003150f11b04998041d6010301d014545803405680c0d2130b107114030342081e9070342014284202190b40c003408030f6205a40104544d0703c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 193571429 1250 193570179 193570183
    0x1a0717030c03011509150c050f161401030b12060624030103060513060e070f05061213030203040e04030f110d090b0a0908010911010215010f0b07150216060c020c0102 73
    0x20645010001001310300c00c2d039100c181e9011103a0361108064030790002015008550000601c107809119401b1290001c1608034696210f07281c026004842500d08030007044801c544808008803402c040c14000307105c1ca0b00a000c992003e0007401040819448042070040c54106500d5a54112624078800155210030050b241c00030321062101418507500c40000c40c8034246010749140b0320035403000703007045003c9a140c681511044148101e1500f0351100307000050340c0c1003410803179950144004907918542d959100700c034400c1003118000d600310b01c014080420b20094620085005034000d4039450805680d03921300502e0301c2e03c80000500941c01040310b4164058226030010262141142c0740c640f0f40401d0070045400d4011540f00454075801c0c00c0c7d000061250990001b500d2041c01e13401e4402040c10020f000300c1161083c42111001070401d001001844003002c06454294894041c1450309100490b8100a0341c1000040007200c6c0740c000303103940c10005184100c0b040301d1203600150510026a4002039 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 193572679 1250 193571429 193571431
    0xc03090c030706090b070c05040e0c0f0f0a03140c0901030c08100603030c020f01261504090b0f0705040308040e0a060503010b22020d050f1f03021302131a0717030c03 73
    0x800548041030f0346c400c110070840f410000e41b0340a8420003101050a004540d10740044400d0341c06600d40d450309141e40c1c00c0c04005001c110302c000c3c00f100f10451230744c0e07074106030207034680d01c4203005004000300109242e031038042c014002e40c01014002c00d03540c10f21441604010411680390f030028070303098003000040d80262040c070a2680480b800000c45d0303500001600c00c0005240300c0d0310813480c4081a007401300c2a007000140134584001c10b51a500c2110424001241c07140f020150404080c240051b1030041c0d003808445d449091782c94454101076895541e0046038006030026041d2123652400c200c15180184244001000101c0003070140982d03100c007003040031100c00e1031950214131070442040c00780d9040d01194102d40c0c40380d03010009403404040e41700c0000030560b02010b23010081031081041d000c00a00388000d41c0d0300103011805840b44140c0b0740d00254006408502c4810001d440020708a4008914412000340a03e941c2d07920180c40c40c0c8104066290091028009010301c14410014503d405407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 193573929 1250 193572679 193572689
    0x90f05030c0d151e0603051b0d080a02030c01021917010605031305011107110114030c040e060f0d030f021501080601172a0f120c13140c03090c03070609 67
    0x105985a03032a6000f20280419004914480a40c020341e901044100d50010007228001c0b0207580c1c80c00c02c41850380310030b2010050000e80c4500d00b450104045242c1030000e100082141c01144e00d005000020340e42a0307005440f419180c00001c00c10054400d411490710300c401160307020440010341c10020041c0050101800e1035901c07030b0810b000310003040b01c00d60103200744085507400151500781a291840d94403890020030307400200825043c6070b2940d40001940d00400d818071085082909141042062a000a02039036008000e400004400d440784280c810041c0e000e696400211500705001a01d010203210550010000c003a0040021000c00703d140c3d41556001c3c0f5600040d421520001840d00d48440d1004601c4103036140d0001c2030820502d4106061038069600d60389a80c0c2070010444010608088010a900b2100c0d20074040d20304208291904070028000180ca026185ca06101151003214007009000e000400d1001e52101000702e410004002c5000745401401e100f0000d2101c0f80b28132032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 193575179 1250 193573929 193573943
    0x81e120c03010e06010507052a120d031b02120d09140a0b0601050a09030f020303040308030702030306040c03110304030806040e0109050f0105010e13060c200c01090605180904020a03050d090f05030c0d 88
    0x1000a0900032754002140b100c00605221029140c1820252210f240a010001081c6881562030710081c016044401c122129009002070541e5007060b904190b001021046008d5a900320380c200048100c90380b94200c8080d840246056601c0349071903029114083d25140c103001c414040008100d41c005030000640c0e07801a04120358452505c0800d10b10302841e00020108200401007140c030b00e6000024511036042158103200072440f9031010b404441c00250702c0d141e1000300704002800300f8080c3e9086038011001802c00076050003071080305800c50b205081e045a041d001100144030081090050728003502c429180c900050030082e0304c06510718030b0818020301003030b05c1d4a905e4410900902c1035415013004441c1d0a090091038401207615000102005804103040340d0010603103503c1281550801020350101c41c0d41700d000302d003c02022110080049034000c10400700800041c0701030080c1100c0d460f00751030b5261210b040c41c04940c003241c0390340c00c0b2601a5002c03440c0942d86903160002c3c20400307900988 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 193576429 1250 193575179 193575223
    0x512061512030409110c03160c050406140d17030c041404050105030606090a06030b011401020d0e0f010507020d05100912020c030c0d030314011806080703081e120c03010e0601050705 80
    0x2170104018040c0441000c054040030500f0029044d00c100483ea02610030880710340001e40710400c01041394114000c8011403c0c0b20309214405042191140c4646401240d922601d640940801e08140d8011103164030380c0400881c0802600c004022400d0030315104441c14445503040101103a40e8a000800387c1b132280f1421000319400250f070794484806550411000f1290750b0b103800801c0e81c13680080038814010f1244030005504544650240480c104000709100b40b2400e8000044800c1d4024180a90b40046034010500000b9000c1050700d1186260f1800401c03a00301e2410544040d00d40091400255080784446181c1c0d0303a00420842d0b4148006c962240c0b0400d00c50078104c0082481c20b081141840d98480080b904618200106011a00088042c4481c6440303900c1207032560341611001b09220024000c0004005041811911104131031020303505001e1401120405014150389a442081001005001100305001c1d4190b02020a080041c03500515070b6640750313118444030303001c0c1228441403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 193577679 1250 193576429 193576451
    0x60201090f111201020703081b0304120f090b040905010306060e090706050f070f050a0203071202090c2b020a080703060303050d0c020c03150610090b070602030604060512061512030409 81
    0x200c80c1243c0e03e03030400000c5443c2c055601d13018142000030703100882404040c02610b1842c000381343c112403140c1e40c840101500d501e000c210650703020800422032030500c107517484042000313500303607014200030007903100003280e139508d103003440e0b000c8801581100078590300d000c04110100000185010484002c3e1803e50342c0c42c070303040400018500510340c008111015196141060040c0000e00e002c1d41c5008400382c0ba011952003410703221a20391b00a00940282d001000900d144070b007403015001e90711001003011014151043c050800d2104d041210825590206d229018564003100f050307404021802c007004038074110b0710003400c80e000d42c910001ca804d4480c002800b40c144248420121904003604840450303c44484c40400d8000c1110454015503030301d17602611140c07080c0c4900040f80c008451040c9407006c2d03078680e903000e548001c12161b0480d80301c06000803c1e48402100400701c103880c0c1d01030840c1e03040c0f0b04d44100c41d400000f542c080c8200d2b00401c02496004e80441210107c40c114a00021020302c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 193578929 1250 193577679 193577689
    0xc1908040b04030302060a05010b04120204020906040f081e070b16060b040507050c0c1e0126040b1e04020604050607030c0215040e0f07120b120d110106060201090f11 73
    0x54000585145001c02c000040640005400d400b400c018103082c05560388036a001d07000e500a91081c40700d000700550080016040c16402814544000f034001890b01d03480f01036588000c07076640c0c070920b4903900c0007442100203155041130209540005025002c0749140030300301e2255005003401d504590004810080c10020554005a1004c8015109200d80d1600b0b07003018041c0d8200301655003490044942e0352015280181000800d40740d46900201900c2c103a20044600040100300001c3c5007554411b0f83d081c0c11200001644500d100d064001d04500d4031030300401041102160003840c81c0781843c24440107a82e0a030a07581a00c5040d202c168461009040484410a0500019400c60100060443c03000224001401524103617452142580c460310300100c000304044986000042090b00214100d0007a5086a4240b83c0c1c010500203200b0740d500d07541800c20003510820b601003070140d407a18406030700038000c84005140d0f50001b0070814050f80c80720310004044400043c640d00c14000c600c2119503030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 193580179 1250 193578929 193578937
    0x30e03031b100e01060b0403060e160905060a0801050f0406020a030f020412120c08071203023702030a080f091e0309090f1509150301091110050c1908 66
    0x2181c80d140010390035014098032809890294003403981407100103596000140611400c5914613010a45000d2841d00d172000103202c0c21b80e00d070206005903030304104652070b103140b04006040d5020000644d42485420000104055031185000340d0406c81004240d01003624142d900a811050159a4151141080b8010b00307030000c1034111244085001710b04600282800010a8447c5110412428100800381c5062900510090a003001001850b0005003440c4224000310403604001d401e007855500c1c000500100d031913074507004145102c190103401e0040c1400070340c1d941d4580041d528040210100a0007010005d1500d219411420b02154030f403074081140c00012a102c04600d01d040403910700c1c40c0d0b201e51103000001c0c4170710010004501340b400c41e0300e96140a0401c03820704c51800801c400c01e1240500300144040d200045c81d18448905403002e0041d090164862900b60300c805440c2820001c6102540d420702042140030700c0070042c0d100c00000c21b961220b15052a0600c01040c82c513250520b840303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 193581429 1250 193580179 193580197
    0x110301061512050928020a0302040204090e1e030d020c0f03120901050907050a2102040513030915050a1103040b0d060806060103110a0e060d06141302090d030e0303 72
    0x1601804a03600726440031414080146400d0309216648400695a54580380020360405000d1080307a9504240700e101803000d1550300c040d002c0e9240e2541c940000302260416440900040c0d00c80080c44e817045014008070005002e0401011000751905018135a24019402800c5030158001501c0b101d03040c1c2000f0704407500e07040104507560341d10f49d00018008a07800b0355002d0320310b600f424049410032601085400c150f401c00303800103101618007410306680c02140299000b045109102250141e150747c05858400c2906082c002d202d40c100c0c5c81e0041c1744440750740c8860300401441c1c2c1d4a18815038420116a030720000c0e454400b0703903402d02c4141c0f1404c40c400c95000420912001589406003c043c4e08000101c031105030958fc61642c40701c2c0150207449150b41200c1c42211704004031260305015800482003c0d00240866040075254a041c82c02c0703070041c2d005443c405540458425481c40c1c96013602d0448688500c0950030100403402040201041c200c00800744410071200808545040064920380700d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 193582679 1250 193581429 193581449
    0x60706140108010c120b090a0533010e0103090209130305040b071a0105030c0121060504150e07050c0a020f0d1506050102060a0e070e040305070203100209010306090606050711030106 80
    0x25035942d0300c05008103400654580400c40404400444005074030070a0101c2c41c0180800a040d40c800b4901801080c4c01445001c849403080c030451518500f0342048450752004148511044804500160070b809904d05914109070034141204010703100c03001c00c00d811528080d0b00244015462130159041e00858101d40d0b0b003000003144440a00c071540100008003821140b11000a0341c0350018143c66070080f012075404103040502142e802407a0344042020800501c0e000600c0d03a8481c40083c007600c51030002d023103602c5408101071006005802c0c0c1a500a45c89051440c41c1540350f620b115269050000040e100c5c1c4203100380341502da1581c1004c244c201e03500081e40f040c1000500503080c0241400d002c1c1d0b82c018410b0f0000a05116024030600409443c044001c5c44000c1c9420080300480c50001c000301e007004006e01282e00143c4041114980d131400401c40940c4904101c0001000c498150380b000c0c903014100b241c100b20309a04041150a0740b0313007041c09815100e8842c004280035249541c0400c0d001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 193583929 1250 193582679 193582681
    0x1b0a140f04051503011802090d0b04170a03020403210f0f0215090a140105090304270510090b0409080d0c0903122f06011e0305010c0f0e030a050c06070614 68
    0xa410f00000e50503144040c0c035550706a20b0501c02d08007240a40c00d51590021040300502d0082420802925449071081960300450004c0d409083d01c03903000314188002194000ca010f108201da2042020701c6c4603403007920080a070990007801000b09484404a00501000501113105d8902c00d10140c1c5000401c10444480750805152441e0b96802c08401940c03540001006651906011f020b01d50043c4240d80c01542072500300601d010003c0c6c1e0315150b122011501142359845400c1c0e5010382c5d84681d000d42c1c1c00c0c10f6058945802e0384181d4001144007803140345000b800f44002034807001540c000c159410800603801c4031022041d18540c229820142032900e0b103100d0081000d501440d440c140c0f0851a000000041244040c802c142241d0185403906402c035078010707ca00050f00d140e806526552903040c4c80e0171541c80d201d15003180e5000651000069145401c1d00c10590410710340220000140c00a00320303002207454264454000d101c28510441c2c0001c0c800d8180b244a4008900b0700040241d030b40b5031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 193585179 1250 193583929 193583959
    0xc05030a03110607090e01090b040207021c0209010b1215010509040f020a0201060e15060304080f030a0b01082a0c01020904050c09010305061816050705151b0a140f0405 74
    0x11800c0329070b20340e524510078400018640340c4102c1600b000c036428032606280e16400c1006130400345c0090f070aa540c2260382840418056a04c00801120001d0f50100240301003082d401400003800301604032445c101c0040000208038241941c2680d400910600d80489203011200100e8003440b600000340e50041c10521501552061707a030050080e034100d50020025030380c0c2d5100300c603800d036011160031040c105420804d01d4a07040c0f03040103551252042c80003500d0060305040d80d0b21a5001551105102c56a40300400c0c015600305121640101007101d50008a591206104003400314010384108a4200440d04034051a0700350180c64030940f00400c1444685066403061043e6000544400e00190805010807801d05140d05c500c4d048200322000380700c150b5076400c07200c5a400e44c1103008034100401044103001058041c080180e00800d12885403180f401c1c0151070349086610703203250320072903042041658140c64002d090190914000d0303050b203883d421601c411100d1b5010325809150408450000021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 193586429 1250 193585179 193585187
    0x90f0303140610020a06020306180f04120e1309031404062c090c070c050d06050a05160c0311071a07051501030b0103060e010b030d0f03050108010e0703030c0c05030a03 74
    0x38038010007411407031a070303403000104403c0020b80418007004d6040503c1410114190390000c581c455005805929501104041d4410500b07086414102e0001c50006210800160980d05e843c0300500d494031888544090002414001500746000002c80d03982c0718880415024540907030010840c4003407140c0300c55940138041e04140003642951840d0750700010040c06801c000d440420190780182198200d580c480702e0112481c0d001c540c0070743e15100151000649035403540e800d031140c18800d100114283c1070404a080a42c0c1c805040c1e050a621461445030f000b544c07281180c2c18a60b0149403c0c61000c00c0c401c0301070304104040d080025203444000f030480c3c1e0b80c4125002440828450002c43e80700303400d0310580410901003170100a04940321a0010000328801e60080c50300755000400000383c64034402e00091404900003117134030118404800b419002c2c3d4040c481c450043ca1914020b0004a140076002d68a410150000030203000440b001c03082840903001101c8007400020341140c0c070751001402c01034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 193587679 1250 193586429 193586441
    0xa031d0c0a1703250615051309050303070e130203070c0209090a030918020c01060609210f03030203042105030a060605090109060f030b060301030c1505040b090f04090f0303 76
    0x9809245210400210b800c6034003140702224450700b000d541031444207150210703c40c0c088440200603190031810800403c0d0148038400000400140c2d01d0001890001400492000302d8641a0a58a840a01c8021130b10110880f54001c03910300d090b003046807061000400b1300c008022403200c100d1020007000105a0041051011903001b121980c55517902c007141030340d0710211100002d00090040c1d001300001003468141e81c070403020f041805030800121011207802c4a41030b40c8241c0000c0e004c1c20041004c480b00729901480c04250742c0f01905240301e03589984030080103a901c020201a4000001030034440d07090300e40b8586802e502c100304000410404002c050307401c107844803050240340c20400900d850081c4111018802c041c2c40d50480303e89001000c0c0c0d030008801c8181c605040c2c0b5000d0800859642d034000714080c41c842d0706604d0b801e0b41058003168040c200941e81c1000c2c401e081000784240240d403400e031500c00c481100d80082c03a225541c00f040c0541049800101020f105021301000c164058200d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 193588929 1250 193587679 193587703
    0xc01090201020118050705040902120105041101120c0801140a0e01030b040317132301060909050111090a0e1905010e060909070515070503090a030f050118170a031d 72
    0x84c04881410f0340d911300800300200c0003d2550340003250801c15030616030403280d841c40c001000345845804810003942514012a01102e21100107580e40035250b0300803410406941ea02b050801440d401150080d01840040c0a4850500078404800d03500d9980c13403070150050407801e1440e200a5940745400300e4078040654084010070f846160210511408524445c4920517440c00e03003c03010b4440c4c07a00c6500e41d00000c086082c021403040c03c01007804090044400411456000041001d01828440c0c01c503400e0b050102c4174110b0402454440e80d0b07905003101c06466040f01c440e8182c1e12042d002c08011250204140b80060400000192103400703140d04078031451054450b00c0c5296294480c5a840d50710f107000e184d07480400760300e0700c6520720b00f01c0340548101c070b10880440e840e184d0760500180041100c0c0e80202d4606100140da802040400e026000610a030300400c808002520380e104001c8400500351400020008103c00c80054800d8004040c02020710740003080300c00c201003e04e5140c03d00b4140c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 193590179 1250 193588929 193588931
    0xc030a021b0a1203020c030d0e0a1203020601051903050a06050a0b090103120f09080a0b09100203010510050a050904050c032409040303020703170f040b010e070f0e150c010902010201 80
    0x1121009401003014006001c000800e10444503081c02c4a02c0c0000031080e40503800c610914000303c00300e850401c40740c8041100764664401015000007001407050040e001113404400c8001c01c070340003035000101141034071403c803a032002040390311101007200d01c426800986248203250700103082c00380e1684901c0c061084100c080c4100c000701010b1240c03c240a00c0001d048202401642e41000c0c03140d040c44103020170500d49100030a0f55924582e19002ca00395080c1c0b407040001080c007210400c01c0040c40c0401520321419821589840c0c0010052010b00c0380050a00c80009401c2004921a00840741d1401d40100104102d0800c20000325581e0000c0715140d0201048868034181c4085547e4107512200005100010315078030303960b048010b03400401c0214144a8406c00c0800130300015401039114001ca010010758601d06030030a2454181d0680c01040b8441c03c0c0c2040c003078441c0c0d004200074a40b001d1803c0154200e000b1a020400701c40d41840850030030b41010607000d40c3c00a041d00103503440da0003680 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 193591429 1250 193590179 193590193
    0x4092405060411070314161502040905060a03120509011115150111030f070501140702030721020c01030c2115090501050a0e07030f050903131a0406050d020f0c030a02 73
    0x4a074603040d03c0703100d03800380c085010805802600d44029001f49402030f005201c201401c010756035031810034595082c50403122a004a010f00c16100c01c0d1180b140d0088049400d1b281c81b82c9503884104490b55910345440411800282c1c10031943d015480c82c00a8404580807260b144006071a000d4182e2001c1d0707000b01c110600160f614480d98803400740d24015180b5400954540084255400c0c5550b01003203003200c1079500e40b030705c01421141740c0401910650094011316902c0c500d034601451064103503607540c60218a510010f81d1459030028860052000178280001c460400950035525180380b2160395030401c0b884891860014890b8100082d0303956000d119160340754903455000141ca00900880d50404620a01080440c80d054216074002c440c03402c1c00030f940021954100e007503c3c2c044401c14003e40c400200c9213500c1c940b0a04d06c50080008034600e40f091071007032030070102c179216501c41d0b40304200300828007520030906d41d412035452030300040809581c2c00403584c285440c1e4015001020250003404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 193592679 1250 193591429 193591451
    0x50a02280f060f2001020708040329070809010b030d0e030111090303250f1a070f120e0111071a0702070503070501030c030f14090129040924050604 65
    0x12070580140c0d000c54030b9042e407040c01c03128112081c0844090b0300c140542006000310700e5460a00c024801c81d40204040c3c3d40e941d0440c100b8400108030310360803002100035485101101c42a22007100d40144151900717640769100d600800c0d000d054460700076a498060541a00121500a06161095641500240020a00b002c400c550f00d014007041c558243d001042110b01007102042071403801c1440c0e21903204020b18503240c42461440690b000c0b21076415540c0188221805201c007035921440900c0c150300d0b60007241c8001072164400c0e01403961065100c90814168485c03e40040220103d40c03880c01d501c030122400c01202150101082d411030001320008524014070104d5203909580000e0001d000704e82c40d04d001100113114014003c41019942c50f10b102e2031902c28042c4802d94902c1303a4041e052800c040407150b08640c0030401281c421480081c04c0546024254050014500116070010b10010715081040b6403e14004403c112402000c406c1c11105001d076103c24003c240c2a0740401c042c403815 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 193593929 1250 193592679 193592699
    0x120d0503010510030e0c0d030908030f0904060e09150603070b120a05090f0c150f03040c0611010b1f0306031a0403080c090d060e210706050606070c12050a0228 70
    0x40045c0756059084643d4a003200e00f03000c000d00e141a0b01c02c1c0307880c6030499555007800b400c5401039500c40200c0e40e00012070320040d28007400303004090508481d40034901e04100420554074a61201e003482e640011400145059400303014541c002d041052025075560b40050702c0c0b24404d1011100004c01d80c0c581004942c0120000504031000c41417203004103000c1100204100e070800e1280c15100607140208142e2410440e403002460055104400800100f8101900500112034181d0340010580c517104200b2042c0d642c5424112401c40109143d1b108000d107103200318090005600f01078000c82303203515401c900c5a00503120a00c1103010740e030350f070300140c42d076007910102031144140b0310381c2c030480e104110f03030214190307602802038007054004943c0b41c140c0d480c130140321100c120501444000c801103040e00900056003d071a038011000c0b074103949048200e54440180c10319500036034444000c550010001c02078100400030500350028511401c8003035154201741c000e00c441c80141d09541d0402e400107205807035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 193595179 1250 193593929 193593941
    0x90503010f0225151e0c020607120c0c020d050307020604180b0d03080c031f090c0201110301050604180f050a09050c0f06090f0102071203050a0f020c030304090b120d050301051003 79
    0x4c01501d129601944001d90b4010b0a07580100c0e25143c01c560640400d51002031059052048039500600b00e68540b100307000d010100c603000c0c0c4070752050030000c0b00c000c030940c441003030103980d0f5040b980603412800c02c1c02d10350300d58003a000c8025080321001501080d8060101905c403800c40b0740b40e105100070721f068400d00c00b030131100c003400501003400a004203c1881c0141c001c1c650111103910f0450350200d81100441458001d5802140c80035559150709801660a02410310050005c508480c03941d4904004110503104034810f0780081d211221480181d16000e030018010003448040511036400d009201c2001040151303012603091003082600111030501c1501c0e03040507200107203041d00300900001800210100d24035003604501880030b000c160782c10b040614a01d6280281c1c0e4103621340c12000300c0641043d2030410142d065500c14081401c46940000840702920080d0001041c41e4041d2000310342c168103840220b03906e50148400b40044c032a03000b0702543c12541c00b20b419078520000c90f8829400c60b00d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 193596429 1250 193595179 193595183
    0x902100c0305040302060f0c060a020c0c0a0803070b22030f030609140105060f09060304050c03120f0a0f0c080a0201050906131709010e0d060b09010504110a0f090503010f0225 77
    0x8083c08100301518080c800740c03491002010811740741140c088841824200b080302c2050740781d5404205c101c080c800401c980103c110042d5180710f2070a090a80003640c900505500038902102140000d440b010f521815030410901241c4040d403440030b07440e000c1d11510b88480c07100002850400000303040c81d040e00400403103258081045819900301400e20009138403098030740b9180710040002a865488220056101b01d01510140c40007006410406090890f01c05040e084030000b400540341c1604550111100c1b45000e0a0010b911607403201c041d120400c0d19103014000c5040441e01507480c58042d08403501c525204e0341607500307a40e50f01d0b04814240001c100050031480d400040c1007484000d80c8020f015a00c4141044403d2100003000241d8401841404441883d10384044082e00d0418038001c9014007000c81d424480175600710f45144160240000301400c000f07829a150041d0b40c003907035400000d89405802801040790360b0b030904019611407042c00000a06100300307030307070303030040850b0503401d819 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 193597679 1250 193596429 193596437
    0x10908150106260a0905032703010b090402030303150102011404120906050f0406122012010902031312110f0115081516030209031e0f0705090c2101090902100c03 71
    0x1e04c81c400c80e04010004410200d4051004109442d41c2c0c1c0380300e9a040740da020045144c00d003211520780078182580c00c20303c5490b0060403540184030041e1740200689900032144440380011450040040b8054101e681403091048a00c0c0284401d110184d41016009106a114080e11070b98402040300c19116030400c0218101050006200581c07244840c03100c0d0340f03241c000218401205501c0b91100342413040d1040800100012440c80741c180c1c07c452a801013039900d50860651811280418034111094070003840b4050442d160610140207515025030040c40c04101d414003491912068001c10300d1001c01d883e04c0590344000203400000003425010620144142c00c101d03260600031b04051100b0501240905800303001c160b0380c2e62000c214a48115000c900480500d0701022507950800316a0b602c10b11003504910024829515100d0311036070031040c031164480d9601120440721000e010b41310b20b81036603801c0880000800ca0b07059000545a14021a40180b020a4504c015200c0e440702c104020049 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 193598929 1250 193597679 193597681
    0xd0804020a0b0a02100e031b03120103080c010207060f02041409011827150501210201081905040c06260105060304020a0306020c010501061101020c070e0601090815010626 75
    0x420302c020064400007202d03004480c924103540754040e05440d01417550846590021840c000404211440103004141c8880658540305c5a10400210f629050102508140e0009607103000260258100c41016810810803c2000f04241c40c0a02a510038410b801944010040c004400d14051803080d04036080340c001c102c0f5900790309410740094110505040e100000c015541254080d042010845040c0304150200c5015070786205c1b40119207040e000240e8140c2c2c1006880d5800b592075904000841e024207041d03840d07645a035095421011928480d0700e40034180000e102c2000b454208500941ea141e0f107030703600b1249018005440003498440514407030645a4010404d03030514800858100703001a003100242501d940300c0d6000e030303031101400c4880780e03658100400160354401c1e80c0a4107074000100030340c034005554409a94a81580c080d02c0395032100700c000726038942c4c01200402d00400d07440d0b042e14034171035026070b040012000074071a18001c038032914103480000709142040322036000350501011607 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 193600179 1250 193598929 193598939
    0x5010c02090a1104030602041e14040f1d03030406050109020c0d0305060a1d07031a0f0402130f1203120c08010314011103011e050303090a06080a0207061a01020d0804020a 75
    0x2001400b12200165103101001c00f121038030380100301950150030007603504c42c80c0c01c1010160020041c041a080210080c0074840702d001681d60325035800b0115808070742051025071100040080700d100d41c00c3c003c24400050300299020018511490080d4000c0100e40e0f62840c500c1d040c0c3c0702d06005401c49400141c1a0b95256002e40c1c000c94000c030001e024540c00645440c030790b0740500e91303011420704c1c4060000308102c0a6603043c0034600030b400304840c8000003c0d100e500031179010003890031124421a004503006001407171403a484401000e1b95940039032056036a00351072100c0b0901090070f60000b40d98a0700c032000241c0500903030b0035012940d50f940e0316aa2864560540160710f80a407104655201c9049001c8051210f000d18082d1012120407192184034061240c8140020f60295000b60070600000405a495000c0e117021a640d034141556145d403003c001c0002485003480007003445142841c0745031604012004401440c0c0280c0884901c80350703d04050f00c84e0303041214000d5000c1c0c0c01c02c0081c04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 193601429 1250 193600179 193600189
    0x20106050616170409050c12060d03140a050c121903090206070201050d02070c0807170109110f1c0305030601080c1201050609130e06060a0e071b0809030a11031605010c02 75
    0x420500035408075030030280c490b19030801baa1425101c0300c11280d0302241000b46004104140d6410080894154000c2c0040e6074016060061042c845401e1031000304e861034000d800303501103441040c800741c03d944c41c48480300001c0046070090003010b400080403000d8440c800780284101c0008940003000300b41001600d90045a155205981115003141c0038001c510018490140350409000101b003e09a1b0504100d01c170f030358a4940c408600c80c66030502000d800412030614020710082c1d01500d40343c00c3d88000001040003084048001c41410420451700c1c0c0a260703101c000707107010b104242c0e110000f075112500207109a006050448500310b180300010002442d2890040000701d10140034180140c80d0460030000710303590000601890740003401004142d29011a07150054940072030480c40c0e508040400800d0740350703030724401e064000350550054107106c000390035240f600030300404840c4070f03c06500c1c01d001c4107c1d04803d00e60091107103061382c009000d08117106000ba01d5040e500c5c07070003042c4c0c1502002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 193602679 1250 193601429 193601453
    0x603061d151302090411040b040b0d061508030703020c150a02060f07120204060206061503040b01120c09020a030c09050306070c1704150f02190206040308180406090b01020106050616 80
    0x400b034144580000300180c803100e00451050b0300440b800c002402c6850140004e803054681d10034821480d005003901c3c1542c07940071600410b81c20403000a80f1010402584002a01c0c0c1e811002d50b600c030100303e0008141e0f001a4103480201c0907103007082d8600103040e40c00c2560068402800250300242e000881c0384003080c251903840314640c40c140001441c4d00f19441c0c00c0307070f106400100050700300f8002c1040905003165a0005d44000e111590719500e4030382c0b200e225020040c0a0360101c40a12000132003400002e1450401812440c84119640c1d06500b101600400301c00a52002003403586030006800d02e0003090b001d11615082d100d140c00b406042d41c03080081d0002980b80e10406506001c0460380d04c040c40d01800c20346070309885000b4000d03805040039213440101c031145183d030080c1c00300c1e050040c0c40304000c1c2e404499110b00c1d00c40e25401c003031103418030307062040300c0c0550007a01c0c01d440003445e9000c90b0840107100c02d0130303002080350640303071001d003c014401c100c2070003582900c1c0f84100b0001110b4203002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 193603929 1250 193602679 193602691
    0xc060e10181a0903120304082508040e040308060109061416080406020d080f010f060c02040902030d0e180c1b1501090615030b0108040b07020a0b0a0603061d15 70
    0x60501c0c40e2110300000100c0ea21030000102c6140200e0f1410880c1000c04c0074100883d0401001030862800b0369500851748640c9090710104880d01700500d00146c071301c00540c5086d50b030040303d8944442d290000d099034094112400d4000070b8101001c42e03070303079405032062a080e1507060361031403d040018242c0c400c0940c0700800356205120310554040108140314003400246c806680605508882c0060048c0820409807005940f040b4400040140e004809443c40448020b81000c3e030b03031044207000103801004010f4020307400d40114400c500d000c40c6e01c000d41c50860141190708500c64000f40c07c288401260071940001c400b141044018414a012004020440198401c441d00d0162030715008208450a9000c504216110706080c03040c42078415490810050b1480c003048026a00e100080207500050310240032004d807034002c00c85143c03090081800c01d6421071200d10160500d00911401456030b03110a80d011807600b416854018aa40e080030000704061000b0300042c4414010b403104c0782c02c05065 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 193605179 1250 193603929 193603967
    0x20108071404050414011a1306030c050c03030414060a092409050f010b130b01050901030504050106050a0b09120f150a0f0603050d0f030519050c07020d0c030c060e10 73
    0x100040d0341c2c0c0d41707015440d052500f0004104042d450405580c0d03181e0042d24000340306200034000b010394452080040011500d56244c04242e03140e107500e0640d078610400e02240242c1c040001004103001e0b81c492032841c50000c4404071a02070783c0300e041c440d080358801b040040ca0b503c0102840100d402c18040000911012003100050000369a03a03110b140c40510340e11966030303035101c19540c28a071402440a040d41307200030030103022010038400028440e100344420141030540d218081010b000f003d52050000c0c12020b004c1032040390301c590307101803550802c0078024450700314405032090243d40854104100c00c1450020451145040c03148150315200914043c00b4503030756109402100f05900840c00154001c1c1e025124801d04807000400c42a54004000b080c941840c00b485070a1907840940d0181c000e00100001c0c05448440141a9a11492902940c011421042c100900208008850031030784110040c003002da980d56016191021081419a0302c461034030181c0600500465801c00b41140c40d80d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 193606429 1250 193605179 193605187
    0x803040902280207030b0a05040314030717150a080706020c0d0620030f100e010b07060f02031e091c050703020a021026131106130306021903090201080714 68
    0x1210711912440b101d0078000580c850042082403240e111425508109595018003140c94541c8018040e20005c100424401c9000130014212038818000c2d060049000c1c0c450081904001c0340c2c1d0103100690059007803046690b9900001c0c005400940f03581141c21680180244c55558000c00011080c4800d040d200f141d11000c1c400c0302c00900040508600d0f01c0b410341c86490b818030744054403036640001d06403600d00c44c0d0008140644c2d402c40078001d0450702cbe010b141d65601c010302e180c568043c018051074094054004002e00c50580342e070003039000003011134402e054200c0e07445050156940aa0354002020003995169241c00d46124a0040100034003d0040350001407280d804100d6810010742c408000800520480008285121080c0884c1030508020022400e02d1138241d23108040810004105421340441c0000c2a1071700001c2e601c1d4210444480000955a400d00e00041c1d44958042c83e5002804011800b015000b4460b05440c03d40603940c0401f0b559424100b13442c8140885110019010180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 193607679 1250 193606429 193606477
    0x5031203061503010605030703140424110c030702010f022404060605030a05010504020a05041109040e150a060306050705210c090d030507110604050618220e070902040803040902 78
    0x2100031030080c4206d5840300d56a1a01c1500201280c01401c51001c000c1c5011041c480842c1c09403000e100c20300b65a00c0040b0407400b85041e05001400c3c0c1d450358000324800071900c0c18000001101414080f8000e032214120506650300c02c03070300d8188258640c0000a030742d482140b500c202c004111540644510000140d0303030303182d600007403030030f8500c0c0e80403500c9a4540c03081104600305400190020402540c051110b18944504000310340990725007207010b2a5104444013900d002049401d5149141ca0900311036070a01807800d0015080501080d03a1081c00d200214007110f1003001119800c01c2d07140741070310300609041191503c441c00034088000d80794040c06007048607652490300d1303054a8420780711a80d44a000d807812404405150880c40d04c281004d000410254807100211460610301c2c0072a507080c1a044c900040d50138000d1a112202008500c031000030180c02580030351213441110003101c0906a9802c150070603440b4078010340c200da40041c081001214019005030403070320123110340d1040d00010a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 193608929 1250 193607679 193607719
    0xe090105100909050c0d0f2006040e0405070e0405060907080c0d06180605070c110427050f0d17060a03020a05011101330b12180f060403030f0c05040503120306 70
    0x2e0042600c1f001ca10024660400031903008031807000c0b00d82002c041c10303400d41da40080e03d107001e10b11821040e04628000a0304002081c0a001d010b8150640d04410f24201070a103580e41c0d03502100c0c92581446040d0004c15109000500703052002d000410124002c0f2080d41c030500034119a0400d10300d400002c2d4040000904680609480340740c0503614000c1c11451420b010300d0322190301564900a600e8102c0c40702048801c04a404d24552401b280c4c400030720304519001d4500b60062007500d07070318007402004c01ca225911070181841d28201d500c5d80720580d100c060801420344042c1c440254416583d480c108600d50090603013100c007040344800001e01d00031001e144080c0c803140070801c01d80b4886031710582e480a50001e1951028214140003e420304d00c9141218959120152900c0001040860080d40b503043c1008009240f0740d0f014150b42e10381c2068600a4007801008000f250f503141402400215244070308103580488500900405c0c00e621200342e84891a40090034140e009104481d208401900e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 193610179 1250 193608929 193608949
    0x3050702061201080c03070b0c0714060c031c06050f0108010303030f020c011a0405010f03080711120f0601060305090a020102071403010e0a0332030a050612070f0e090105100909050c 80
    0x1444d009010b41d59800d10806080001d03e82000141140c107025000c07061000050399010303034030700700da4410581004d03000280c5980100018090144000503240c42901400092400410403418051143c6504c1c1c808114102c0c0c24100b01c1400105210010000f1900c81d410180300c00003645401464050300c0300c03405003902c1001d0040c1d94401c08003141850203040500c41c09004000c440030b402c000c2070075699011a14498408060035800300c51300344640541d1000001c101840c0c03880201d420030b001104015403120741c00d10541011074603105c0000c41c81400403801d11801039059002d040040c0c1495603100c070280c005454181c1665807103480407810a420029202407502a45600b0b000b142c801d030814081000244480b080d4103800d85502c0e002240c0f16041d04e8015600c40380c0410141d44a030040b0701c01c42c2c001e0362020158411008000344c4031680302c01d004142d40034240b10812030750f200c03000d8900382e400640304002c2074079180e0000c00035418150f00086900348281d042d20200042100044c0099034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 193611429 1250 193610179 193610189
    0x105160320060627010311010e060a0806040b0f18090c0904030903060e0c0114160605101d040816051c05030108011b050405010c06060306140f0c04050d03050702061201 74
    0xb220b0b500740440382c50620a0350540a00c0341d0445645002400e110484103d010300c03005090280e5241c1d0900c00c3d0303002d002000b0401c407001d0401a1108150304004000200a54606009500d0010104c0d0a410144100b1188c1c80010f0140d04040031a00c2d010b0740e03508070080620030a0300504450034440d0b0350300554180118000d60301d8141d031034210304180d82200c1442d402441681c0c411424803501d030f60400c0d11054100c070a544107680761304641018240a448821004048514060800a13420556203001003034440d5004c50388014000e02612440221041c0d030054005001070007002c0d2503441e0800044215885401524110f080d010980001c90900131211f002088001c00180071040d400d01c00d845000907812022262221080800b030001d00c00e1740940f0b4104021807007180c0500540e6000b0100440c2d02c040100081c00c3c071120b24400404042e2400701c850021b500200380201106001d42c0d042d11f10003410015001d001d0365007941e080d484110701320781100c010305c0754001040c003015409009103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 193612679 1250 193611429 193611433
    0x70c060503040b07030507090b0705100e03180a0302060d150902070309050418020a0905130c03050109030f11030a050d0e030c01060503160e1b0405031002040f140105160320 76
    0x4241842e100f9990b22004103050b00b0140317043d080205169001100c2c8040720402080c035a911900c600340241040072560f10f0304403242c01c0151400e0080000401441541000302c41ea10316070184004002910420788006944450103000e04c40541c6100e40c014140c400ca500e14044115690b0311413481a030f0040c80c410f4010890a510070801c0c2d00749400351101d080d04501c4a061441001d50000e945c05660b0700842c0c0c1d03010303a601c0c0003801c5c1c400c1c0480b12a02d00c6070001074441c2169580d04c0c01501800a502048002034442007481020314050180c1d44803840280c0701071803c0c6496010111100d4000c0c080210080740c4072442000035100c1030005006c100e2601001080403410b28003814581100c400072404d081c10529001c1040240301081c1a800104da8422200114140d03c03003103c2034002c54000960600604400e490b10500c079900030002c40d40c424444a502c0b541c0e501d04000644103203409030303002c20350030041c415518007501d04c1580918401c0c1488400480c14020300d141502ca030042d0314401b5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 193613929 1250 193612679 193612681
    0x11041e050d03031a010804210306210507050909070b0a0512010801140c03060307030314041d070318080702040507030e01020c070302120604030e0105310302121501140303070c060503 80
    0x3124607940d050101013020b00f810585030405558007014035000c07500c01d0007181507580f20642403a11070740044009062000c0703200c010341340c01304000420f00b0540702c04480794842e40b000051582880c038000c521910304080940321603882c0648032125a405408030000f0000304200b040741405803400064040c0108500025078180554003208a4410103060422625014030800ca1195000100c1d84242e9a01d89003550380203080c00002e4103a8022500038060413294802490940c04001d000644515140c2c1d5050008401e444000440e8040509024011031000c000a80150815070400c03904191149030010b041b005552a0900326000005003017001d0b0055403040055241c40e180700d10401d4410809040a0b080c90355014000e00b04102c5058107102c4003003030031145800303130050b1214242004541917500c0300c05000c117060003012500089220f4a00004040b081d0040001c0d0032440300d403034000c020341d03a9003458009029110080002941b51008101b188002140c0b160080000d0801d900ca40e80c41e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 193615179 1250 193613929 193613951
    0x114012610060b092d0618130e1207020a0306020a0e10090f050901050a050d0312090f170c121308010207060606080f04030801031b03061401030303060911041e050d0303 74
    0x3450303100d20b00c1d4000c02841505c0d51442d5100020700503e0354400711200f03075541020074542021029240f80700ba6005801c0d55101b00440000c0d00490200380d61201510a0f07549040600b9240340581c8101942044000c0014000144568020500e036041420b09140c146024000117459542e901c4040c400210300241c2008000c040500301d0300600b000b252109400e40c10400480d040208a104242c852001c04100702d0a1500070514540e035140780070400c0c8600100d90801c4c6c03900d10182981222003800a0440049440700b1400313803410b00c925540500034048402c0c20b8070356190420801200c40707484039030307001944400910003403078054850340c00418614a0b040010b081c03900d0040404000061000402c000240d1003042141034030340c080c03604500e0517603c020340c0c003a00c011a040104050300d01180b207e800401305000c9030407644255020f003c0c50341c0300c008101c02c2e80d2040403140c002110030705c02031140301a80075a034003554241801c403a81c5c15940303200040b2550050f45d0142c0110f56a0600034407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 193616429 1250 193615179 193615189
    0x50402300c060a0c060f023c030f06010f050c01060806150f01020316060b0604090504060b01030b030a0305030603281b060c080d0b060c0309030114012610060b09 71
    0x21011048800ba400c010109101078410191080c00038001d82c0d83e5450700c102c808150b07059600302c60030780c8695102420801d0412101d002c50688010a1324446141c004148140b001113134440d0700c40c002624001d40b180e00042d0b901481400c264000e105061080210310202485910000c0000301e0040c074990518580d2080802313501c6817414001e011441c00c1e003c05903000811140003000c0b0407443c5d40c40c0390300c0b814803000130040200f08991061300000c00141d131600c290040750165001d48030030403216031010015021070300190260f0b44c164101145035030102c0c8c09500034580c0180080e0a90305001c050302501c020900803a1120300207070100991172414410703030032010780030102040b201440c0b850400c0406860347c10400380041204800180b15034999616800002c3c544002800e61900c95040b00c2e1007580782d41180d580c55000b5880c085107407440e6013040354064100c072003030131500b10f20911200c08107070340b204980402116845500d40c006005d03040c44c4500c400404400b001103846200c9801008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 193617679 1250 193616429 193616443
    0xc04090612051c12020d02030603010f05010e01090905010b03010c0f02070605030903190e0a030308180a0209040803100e1003170a020d03020a090801110d290405040230 74
    0x40e0350350944103420000820001d44041c01d0701d1011035444034010f500c0d9040b03600a61902100c81010f00104101d4042d01e07003a0069405040214000d00ca1414100804802c0340c1c07003445020408800341d0010031a00d010f5900c8000d055019400109104000c5030100f42522841d803080d0001410580340c020a00342e06004540140000f45070140c41d6003003a010761a03032802420180c88400405084040d480b41c020410100d0b4294058003441030b05a581c10b01500e819001c441c494020910301400b020481c00104882c00303500c3d4020320b85408d68a4a85845419400041c60300c0e0200300c8110340800c10083c4000c026106076190095220f505e401c40c0340c05031404030021001c1e11070300018000102070780d80124038543d21003400c0c640141c032002c0640040b80d2224491b4006206940b0340500c2c0c413805005103000b80b40700410068140b00c82045001c114420791110144c0c1c0c43d00701c3da92954440a45019048540c2040c0010400401d00c0400c2110444009805401c80030751183d00c0e25050f480c4005000d44 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 193618929 1250 193617679 193617689
    0x20d0c031106030403020a060507090314330420030a060b040b0103020306030a0f0204110a02011a010c0c0902070f0b090a12020601050d02090c16080d1b12020904090b0c040906 77
    0x700b41181441d17500a96503c0f01203000811482c0c07150006103000384075070030301d00086803c50b8103140c0081a4240c03c03511114184100400c0c0c10607515400440440c541c0160451403003220141c00790b07030340e949031542e0462413080d00c040040384912050b51241c1d010072414210500a0000003510701015040104468410a140741454014420014241e0700803030340c07c0c04950402e00c00d144810561000034006c02c442010403c4404021429601240d8154802220440400c0c0303c006e00740024001520a8169003c00508600b0707640030030b010101240d00a882c2c0c0c04d00c40c0c0340d03000c4113403d0342d0f4806c4418181103903a001d007540000e0403141805010520040c841d100b90001d000e05504240200352450030114019008401610100e04041c50040494229024881003042124503510308800c45038824101481c42908022000007189807008400e00f002c6c07200e880300a092024603050a001e0b400440b0995071040e69202c08402084603400150701c9001510a050341d40c600300502c0c1c00842d020354110b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 193620179 1250 193618929 193618939
    0x409060509010311120a0804060e1314130609020a030f06140f070f0216080607020d02010606211b110f07030b040b060a0b0c1c020c0a150c020d0c0311 66
    0x104040b03010301e004c041200c031040d03850180702507022001c80e140200500005101200004000824075404081c0040c5020100d030b240083ca0555407801091718000307000b5502c6510118081140681101a44030195104034008074100c80c0a4000a50710995644165000c0c0704058541042007002c0c411002494040d0149030741e103003010001c48281d0303d00141200f0500c56103040c2c11410500030000c1919042c94008821903064076510b07110340381c1034103683d4000944100c80d44480c8080c018010803042e5078607a0b0715400340300e5070741c08554900050990382480640d50349190300c1196020881190044030292034082007038040c00d02091600402000503816034000da403042c000590f54a440c030384c00a81004072640301d512740a0005150000b940e0003405d2080c0001020081c840e07000c41c0d110310360b078180010a107030480300007400c0e42c07100c070110030346035104086400034170003411001600344c52075066217801405200b86501040d0700e00b900ca08240c9015032241001c10800204242e6600b00910540b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 193621429 1250 193620179 193620181
    0xa0605090105151f1d060f0406080c03090a0308040212010c0903050f0708030906070602040824010f062c03190506010530153303031c0609110409060509 67
    0x202444044846a043d40101720b58800b4100c440048100e81003002d41008140c25503501c00050040c2d0564807502c207030f03008a400346000980002c4403e040d2813040e050b40d07001c0d1510b5000380d5000c071203d01000303008903401540310501900d20b050901c10034042c0b42150312090001429420445e281403c8804d00711150f40c401d00040c4490640030043e100341000580f1455200e446501d0028064015070704901c16612940c1d036118542c0800680f0865034410081a03100f5598031806100f03407540f0300d40036210125030908440054080303c00303d0740c18580c80085600248040314000a402c0650005201002c0c40301c41c807800c418480e060003154010300c001c0314451160050401450711003c80000310b104400007408000143e00c8061040740c10b4005400c0e0800358515050f2900303210760b0151f19058801400050403103200000301c189420f800b1200030011070401c040301c505c1082a005188141a0480c1c40c0c4600042500c03050207840c1003c00d0140050703860721304103a151400c80b4203982c0103a21881341c000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 193622679 1250 193621429 193621459
    0x510080d0e040504020d08160c09050f070e01030603021e01090b0405030a1506210605090d02030904022802010204061101050402011704050a0b011509240c03020a060509010515 77
    0x10091501d95054030089a103948900010300070301800003000d0720840c40021120260443e21180381d00c0203205900101c0200c0d181d030554011200708844001d0005040f4011a102e070b4085c9408100d440070501d000304141e9202e6021919440101d83c87c0300761601c2040100c1819030700400b0b05d001510141e410b040c240b03454500002d41e40e07a0400d07000361501c2943e074000c001400f90354005034040d01070b44c5140910402150315034110030411b100c041e10070724504404502660000320711000340885c250300540c100400442007100039409140c0284520300841007860b403100d220040ca01c4107503502c1c0c000685452800c5030241c4210250a00b04010364581020000141c0e0801e42e070320968401c1881e1020155154500f40e494a01e03c0359001c2d2180c05d50b41c000041041203c121121507038010f5494121075903841003040c05480100f0710320720360a400101e062030320a1007000c0c154000740c028411121002e8554441c00c0032282c0035104404a65154010000186000202c221018a00f55089124040d810b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 193623929 1250 193622679 193622687
    0x61302030402150f0f0c240f04140a05070905041e0314070305041205070312091d04020a1205030c0c0a08100506130216050606010e090406111303060510080d 69
    0x80381d4032044010101c4c0420720540120140d9003e13111003044103507145685180a591a80c400388001105102c1c0502d41c0711051502e4a42c900503809590b081e0f80940301d0750f944800109200b00c00459078440c1c0880000410410083c00703004208400f000211803c0c141003400028401c8a0504044130140480758002036210701d448034100170f9000b11580f500004d16085031580300d1540208802514414104240301d008a03903d801c0b2403007908410200e42d13540c2c070190303041c03a5144500c07041030b09403c00000320902c2c0c040d00d0980c000d1006090030307041610340c03000c803202040403802070703490b588042020b901c2800e04203c1981e0290040380d40c1d441162810204598450701c90401c0c40465880b0404034115449054046942004860742951148400054501c2001d0865400c0d6554401d9501260095001d8061001640000340c2480707207960b115160f407005000c00c0c20b00c00c080c0c5071003045100301202c2c0782f003049805948502000301d080d0905984142050340ba581028000c0c0d013041090884842d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 193625179 1250 193623929 193623949
    0x6170d030c05092e03050106050f0c030c060c030f071e110c032406040911150403080301091409010b03210c0607090e010812040303140c0a0803061302030402 69
    0x40d00c0c000c40c116405440c1140c9502800c0b00c00c0340c0250100403e0b64081e41603540c2d034044480d0108481c84440400001141600c07420310401c808144208084c81c40031101000500c540801d101c2124541219104110310703002c2d048444001d401000b00c01d0081e0400e0391500690000c2941c80c0401d403405069000000c100300711001c41060182c6000350f0110000d05108070440084000c054030b5485680c85040c00041000d0080351844100344d6001402c41c0c43c142c450460f100f504001110343d1841c516082c80f031400024074032035400712401d01000001907518801140a011400c0707020a112175000e424000105000e00800d409904160000a003910001000c0b50b500e109070305192052548000345075903500c1401001c00c1107014040c10852101d8001004c03204681322102003400c96a81c0b010000e480b010b281d0103904080d5010070080010910504083d46042403209110386482055100286001c500040480300140d001c130030088589130018000301c4480b11144107520710f151990003c0d1110b50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 193626429 1250 193625179 193625203
    0x80d0201110d02091305160f0315060305040302070902180f041a0603070c020409050f06010807150807110307030804061a03071a0702030601060822030e0d0312020a080a0617 76
    0x1501003041075155907141c0008001700c4440d80704000504212040f020194007088402d000300340c0159816100351302c01c1c0310344051081c3c04180b158045060141c01c030003a03c2c000c0d00690851240b0b500100c0e82c46801d01c01849000444005440a25609800e200c2c03501c2e603036008507100b11714003110b900e00f0401003200e11080318400c4ec0c06603682ea40d22102a505160080c20103500a894954050204040000e8a016688202c1c0c1114030030b80c1d8601213103584440c14086c504440b41410318410480c1d00031360885400001c1400c00d440003100403c541460754104500940c00200c1690500043c84030910620030015224080c030381c00510f000000c030f6a60646482413007007410341444004c1e00c0614480548841503802011b64842d07580d21000241030394070980d800c00c500c0088106104241c007052110320358056050300c43c0c400140c2036404005012900c0e413000d409200302c14080c52210b00c003520007030030b041c202a1103a0229040070f00d0110101c66458028000700340c4100484055800c4c00101c2290202e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 193627679 1250 193626429 193626431
    0xc0806030604060f0e0114010801050109050106020a03050306031c0206040605070912110409021518100e010f090f080706030e1207020d0f06060306270c0b0706020f03010b04080d0201110d 82
    0x5030b0051300c1c0e200a2200b00e928400551909007807950322510807140d01e0484904030028030003a6215502001240c038203106000150744003d09000000f0b000324051980138100409543c00300030764114440040e620070860000507081030302080200051031085c1900000985001d6000d40c5c24102650b450200c2c19201500900301c0503d0380f04190755581096078440d901031710110010a40c05042c47d1941c00c441c445070704040e4400b40842c980d041400c0a5407018440e561008007103000345d001568a44041d0707610b03900b0403c188a02262580380d18484200510324400108185440c094004045440302540061682c104086210904c0025400d480d400c80c0c04646035081c0700d010703180c20320841c001d2580050903030b41098400130501c09039a01c00002e51030070441c12100e003030114900b0300440d040d2000081c11200540780a00208980c0d101900c0160b11841005207010a071161488807900240d205075a040c84c0082c0601900ba014041400c003e00540002d01c5040304c0c0c0304078141140a0042842241 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 193628929 1250 193627679 193627691
    0xc120c04051f030e12030c07080f04080703020a090b0906090601050904050c03070f0e0a0303030b060c010e1501170a03030b130906060512060405100b210a0212030a021c0c02100809010c080603060406 87
    0xc41502000c482802c0540ad207216036440c0e40d2201e07070703403900d8035440164481c5001d44000200301103603008016001200903c00c440541e02d203002c0010111002e4065030420005019a800c2500c80b840b40c64090399540c42030644901c0c00650090410480a41400c104050581180241c0d120404014103695150034040f0310141002c0c0419158007800609490395800c1070300003040008045403140110901e00c3c118501c0f41c0c1c03100000901ca404620742d00800da8811100c50010034466803081e00d280318014000080600c900d2600c90544203505010717509199212030400803032400380010001d01076808082c29880c074081c1c40302038950f054903074001100794680d0413081d0a1b60700c041c6000c60f08200d2040709504002821450b541e50582041c0c124002e00c89049000c1001c400002540e00a26090b8010441d81050394180c242850995880d802481002c9070100e00503600c80440611912440d6074a11103490b10280b0f803070130b584100301030400b070142c1c003420302025842c04100146d201d0780250001c070f60 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 193630179 1250 193628929 193628933
    0xa1404090623090705060a021b03010204090906050906060315010924090e160f1e0902040e0702010510050a030305090a081c020708060c120c04051f030e12030c07 71
    0x25080100c001d1541c01d54400e0b105400c1944601c54500403490302084441d01610350381030250394800c0784080409680040b0400300c2ca004210741c007114240d000780016080c1075030b81401c50241c44200030300312001c6490307004200111344200840d03a4058001c070020800700000c01c00f044064071301801412255034940984540040807490603800c0b0301c0006a80d88006956007014500a200982c0340b40c8080c0560407a002056600a10150a0322520b00600c15606e1a00c40c4445000c01c0e00b151002400ca0050400519a20540b01500040c1101c030580d07002c910340303480003c4c02c41e1401030941c804004d0660040c0040c0d00c41502d442d061301e5141c10116900c207880e100046a0328807551080f002e41c442c801030114096082d421802a010b165000c079010a600c6400c2d07152034850488001c82c031001c050055040c038010560301e041d00007090b03509503890305031500080350b034089103c2d0940000440d0860300183c00c2e54144120402000f10b103024106084600d0741c044024030000c0e059588044002c649042 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 193631429 1250 193630179 193630181
    0x20c0307270618050108010c11030a050a09081002070203060a060b07170c0a060b010e01020f0d030b1807030218030a0309140103020405030712050f0f070510090509240a14040906 78
    0x2026065818154020303c90196400e005484240100003d6509201803080c0190040145180e090741c100080c60500498140c00c0307031607402980a0760200704098000103201d040902c5180380301e00580c000981c2d282d40c40d005142c505140600a50030591500e41c042212111181c2500d4040343c1c400703106140b45014a5005400d4018442000d07186d001d103003400420007146034808210284280c8032031104a0440e001641c454002d0054038106400440f03140326810710a6110504004d8010710ba00c00d04100707804903c2c41c160049404401107540090f403071051700381c8400155540d00b000c030700a1030f1800869030014015405440b41c1162117642c2c109161440c0c0c0a501500c019000280c2190601d5541c1c00344240c10061844c4180c569000e1040322500e03a860104006070000e010500601482e45094140003d41115044100c204070b02ea5030042103590b40c0d44600e90040d00c2c1e94249840780c441404002c101d00b504050914840e45644a00304454000362030f021114940440780041e4850b200d0070084 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 193632679 1250 193631429 193631441
    0x50d05070924030c05070305040905070c0b07090f09020906090108060f060c0109060e0312010315110d021305041b12020c060f0702070608010506030c0304240903020c030727 76
    0x15046502c4204050440e030207100c00d00c40c1011840d0390038488000b20710016501481451009400140308000070f002035201600540e80041e640c0c9020030390320b00345845200e40010145c0c2c008001844082040081c110105140005090542d00440c83c1c03481c1240000c0d00d520640440d20305201c40540002c010790b440d640070014500b0040c00507640d890107000100d00a00202c00200c031041e15108511180c041d000065641c0f01d03d561021025990a40d1504001c8004201d400c080e0300e52108503100d00e00b695200940303c070341c1203410050307241c0d15120221304c103101441e0401c5004070f20f0300c41040d84403401511014140c208905240b24100000e4101c00060302c01c2045148042c81217109014440020101c9075200300380c00e500743c401142e2101c000310381c0c0d01000e02c10681d00c0f075014008121030769480801135410910841d2080c007a15500c0101c1142542c1401000700c200d80d07118904414540c051024503141c80c4120064159941880c00c010402c0b01851845c04107801903128031503020030136030300c08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 193633929 1250 193632679 193632689
    0x90f1f030c0b0405010212120c0f070204060f03020f030a050d032004081509011b030e100507050d0f0e0a080703090e0a050a0c030504020f0105030703060f080609010b0a06050d050709 80
    0x300600790b0321603112148941c0684100c0740103104404064950540c080103440c10340c2c8281da00c08555440d01c60a00f80b50760481184810008400c110b003200580c1d882c41604010114540540f24580c07545c0108002905900d0701c180c02504007a80c00c0c00094400b1403a40d5050103181000104031840800c0344480f00d170024125a8000400503001c0341e00640050200104a2055890445540d458041e18207030740ca180050850941c0809200c2002c0d07000e600104180380c410001c03116001820255070b0150391050303d0000c0880c1001808007024a001e024001041c41440d009011207000d000c10141ea891120300b014021030b0300410510304051244107240300400e2030801c054041c5c01c09992480c024000ad0758520340300c92900c0d418411140c0603000d04d900c543d4000b030003c000c51600344015281944024140810107541d05000705005200c050454050008032000b02150b00d8103512007803c450300c0c1000303c0e2181042c0c41d010403c00d41d1080c00c840c0c004040f1a000304036511100d0003912001003c0d001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 193635179 1250 193633929 193633943
    0x110309030303151009080d03020f07050d03050601110d0e0f0a1a04060f080c120405010e07091b1827050901020901120506061b101d0606090f1f03 64
    0x740005400c3c200302c030b40d5000310202d41c00a1692003800b401d0352001028480d40030a41c001511591101d130095014180d0780041c040018500903d90f0740f06428500c500054002007907070f40c404d1224950303000121650800c0e8180050034586032185024125000d145501486011105081901510b0711901080140410034070a00c1d46e814824410500d074006000c0e140004500303207954035019100d1458180103581803200c40386000036000c054007184034020001e49540d92034401015000000f0411540204003856001450b040048201c48480c42c4c0340400b0390400052200e00c0500040c4100700e030081b194048170341c03260b410740c4600610048515022141d0020318150800c000110190001c14007204c09aa40c4070004202402c10350840384142c4005400c410305010176a0464131000c280703040280d210088035900c20a003160ad5040c0c40b00d468103202d40d060044003090440c3c6040003050340140c401c8501d07450500c0e1421110080b00c00082100c207030681145a0500d140c003910081001654018807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 193636429 1250 193635179 193635181
    0xb060d02031504140105010b040506070f020303190e040506031903030b270a0e060a0c020304030507030c050a090b090a020a0c0c0f0f050108010b070f050709050a060312030e0a03110309030303 84
    0x444110003000301c0f0207403040340781d0020a060048061007058107917540302a240303050600349802d000140c0c0192504030380c404003100401015a0701007015100c50b41c0500315203002c02a41440c01841603c40c4040c00340210b08000500413550303000704088500018a284204450b001800c045026103090244990407000c4400d411503d080c10884c1d45050001000d0328840d00c0d1580b0800804542e180c15030380c0780540194012807032481c51034000700c8441802e0b20440781099141d4541038201440780d4030440329589154420081d80c14041d141100400869100300018481540403d012500081a290b580c0b030340007940c00704250040c801481100d07044982e000e0340603288c201036081c400c1980520291508521800202503109084c064142c0d01c13903c0304641004240d50300c07048070802c8120112298010100701003400c0081d8420f451003101240000702d213092450400184000425090340101400c01c410661800d200040c104115981403421046849031041e01c0e508501440d650140c1c1404008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 193637679 1250 193636429 193636453
    0x4030b04060e030a0c2901080304090b030703120c02150a03050f0901090c0306050a020f0304060209090f06011d031002070804030b0c040f0918020a0b030915010506070b060d0203 78
    0x1424030603842103404009007081030980560328090b10100c3e8000441d104900d10019441c00c14280804040008580c00c8140000141440e071809800c0440c80340c2c400b050400c10100701d030159035000401030b0040d217521411600c5003150307214001c00000520800b019600c04544030300800030401951054002e4a40d030741214014003810041d510187d09550b5039000c540f51100600c41d8280d02680000e007000101e1139580c2c2d0f2005800b0051401d41120303400d000c102d1041001c0d05c021841030f80f04000069580c01d83c07400708280300c10060030a0241108070b0303040164698001c0c0c441425003020803040c1030040d134094002454002c4240c5294134032800800c09004020720203029000380d83c03080c0300070112550f40740000c42003130150344984100d5148542c01040310040603800800d660043c190003044901c02500403520b000816400180c0340c40c0004100040404140003414100206510901c030652401000030400d00a11601420003034500000c6405079403540e415903071480d170103000d0b140819420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 193638929 1250 193637679 193637693
    0xe0402030405061b0c0a150209030d0f0206090d0912060603050d182301051305190e070c03020d0e0402040f08070501080708060a0e0c07020d0501050603010608010204050d03030c0c080403 82
    0x261551050b022541345011400c140d040306880140480c20000d0070022281e89481a05501802d20114296400c10807016251401d01568207202d03084d0720b8403082c00c10364501c000d15000c0001e00c2c90307255410072036089100a0748041010103c07280d0a0304d482d225807035810202c0040c6200c0d80000c1592280c16000c12211b508000303c0c0b808001c241c112081502d5640c050300780e101071150319480000a12480600c0e1640c007032400380c040701102d481c9180c40c241d01c510129041074807480c1e00010604003088200f10702030b04002c646038230000c10315001c0200ca2031aa0042d5850030030700743c0b4400384901b640c0c0091450721150b05840c02404415901d501032544c4031201600d8240382d0281d41cec0010102c1d00040c100d40d010707800d11801034801504e4691198a05094007440f010701428408003444c04024240c056590302c816135041078042c400000b29406c0400030582116643e91280f09075900501003000256540c031041d001c0309403d411b01103040e504d01c0c901220000b4160320010250400071402009008107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 193640179 1250 193638929 193638931
    0x3030c07141806030601060804050f030a05090a0621020d020f1605121804020f07062901020a0b0f0a2d060603090b04171b06090c0109180506010e040203040506 70
    0x15581d1502c002040741c2c5010488000700c40316500340d44070340c0040112134401c580041d440340c01132040d1010445410b00207030455010003802c00003d00d010480504030714081c82e0801c0105000d04000010111503070341c82c0c40ba08002c03400d03000c1907580440c6100306109989c044030040724038030ad00d059403a006004200a00030318100b003a039640c811110200449840300084403004407025095104900c0700704204400396001c0e02c3c44070919142405080000351b51405149034030004a6181d01ea007403c5d4490050324191003203080742c1103500030005d40c000701c0ea03101d03a41600074042007041c40455661b0040c80003d46420128400e400840840075502c65881d04103429200d2030b5803400f0700c1610b56401c000c07410358103847c00161044c00a200407500107400d9040d181004000780d030b00d080c2001581d0580390411455000c1003a841d4100000300150210305200781000384109081040034a0304001103002c080324a07080c000801981c442c0452001d0780a540c5180031000020025582c03880c21f8a000382c6c51302e1b8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 193641429 1250 193640179 193640219
    0x1d130905060f0c121b0409090602071505070f0e0a050904030503011703032e0306020d140c0f0901110304120809011209110f0402041a04030209070f0e0603040203030c07 74
    0x32070316010a4029110380100c0318995903130790030311199450b50a01c0e1035989888402ca61100364007040000b07400340141c0103403018540030b1100180c80c1d042c903040c4135520450781400903082c0c41c80c21040000355500701040912103007107403900010300005040852401a02c503041aa88035440b1400c1100b099840302c02103040e50300e5410703400c2d0100d4001001c5a039074041603c1d206003ca0b6403241c0038100d401100c202c5054103801a029140740759490700c03100202c3e40854005084036450324a07013002d00100308642a04081c902650030715141c44420201050b0188103034441c10400000404043c8000400907907002d056000014110102d4510745a40c080d800300c030026000c00d80030301c14038108404d00d1240401983d040360f0501c062070000d030f0400c801d81030302d041801d0740107070f0a000209044030040c0d12050618202c6a500f640c541c19030042152002004002c41d041164112160030032641c4103400c0c2d1100d41c81039480948a40b03c500c00a0f00b103001e07008405500e445140d000080d034803050380c4c150560030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 193642679 1250 193641429 193641451
    0x409150b030f041a0408030a050405031c0f0c0203030c12130501050c0403120e0109090209060708040806010501031808070602090607021009170304140d0302030c1f0605101d13090506 80
    0x84e007803d04055603030030032134010b4503044050001070a40a9690070144d8414031807015680740c450480c8042018074010502c0f4020560707a0300d00802e1102661060006a0b83c10740029400d515007112503094a20030122070b10212a0480041100c80b141c00121045542e400002031080303162155500091740c00921080d41d10040c80f90b00741d01c1d0103000c2c0002040c183c8040e500c40703c20314205815000070794044080306800900803c411400b087c0e405d8040e00150404c5d41c040c149951414000406032201407115800301d01000408500065000c4100e032105540400c0140c3c0f65074044002440e14080c1040281d00081180b00c4003006540c003800e05025072f0030001003501d40d00c22001401d1348c0d0307000354040c8030407600e11111342400c1c0c1d02e004901b10043c14424070440346081e0380c42c008a03080070f95080d915003051903c0509034151410a010b4030015081c240c1da914894040810010700880e60400001111003d103000111940c848c0d00002d14031004410b4280400e030304610703107203984034030443c1e807000e0030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 193643929 1250 193642679 193642703
    0x203120703090b15100c050c030d0809070f0b0a12090606090504200319022e0912080f070606030803100806090304080d050307091d040212120409150b030f04 69
    0x16a580000e55980540c050038048260030020020391b455085c0d00070a8030340e4410307115140354594042000c810750780c005039200442030411407074135840c0c00110340160380c500c0010102484150b00040541e007440415280107550342022401c11300062400340c4002d4011420810045584609508028003070380c800c046289280b0040c5d51507508520003082c070240d042d000321b00c98464031100c968900800a0004040c1030300d40541d00400040042c0b1010f158000303911039130200c103100b5003111540009000c80184080840c1190b86c42d004c0c5803040032414142d50402003031070003d100c420fa0140c00a154003c509a589007030500c03480d44080740703070b1081d034202d03110300c4002990413000031007030f581110303e40001001641e00e454001e440750b0f000184400100705000b00001000a400b15040360b07200310110703031076540b404d0900601c200c91980c2042583c0b0350784140e40c05006140008100d4040340d60054000030b024038407441c0e4000e171045d030341c0c06040d44490100078000d00041c1201c4480c0034a100d09904072407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 193645179 1250 193643929 193643941
    0x3032205031045020111010203160908120403060c050903150105030c0a0807060e011b21020102030f070305090a14010605010801080a0804051306210c08010b0904020d030203120703090b 81
    0x100c54660030003402072148a483c01d250f0312100c4081421140c0f050408070502e404c4522081d00326001113695520000c420311810708403030703042200302d4050000403014145e09000c10700c10f8a102c0c452840000d005a03600c18111800364400c50640e066841c00600340e5688010b022880540c203502070040a1007401000150450343c500240c4c0001198800c3c8060014140360410543d801e00c140602c02e8140044001c81d228102050521600102e10a40250f0400c4e660a00e64160030148250103500303680c8100180702c95608282c1c0341036404032042ca00410781765039001c0500c0c103140400700020016800440515940101900442c080e580c2c02c1ea07030482503a13038490358030342d44240c44140a404241d007044140114280740000d403071401203110700801d020340c0d1002c52072009940140041020035529020008004a100b07500700100040c80c004d0088460110000320181c00280000344540e1800b90f01e241094000d1003600d0060001254220240c5413100c000360281c0a00e01c801c9950804100c00202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 193646429 1250 193645179 193645241
    0x2106040b1c150c09120609150606030c05070506040b101e050301050702160b0304030306150e030c060a0207120606080d0801030501060602030313030c0212011a01021902030322050310 80
    0x9000040f07a40d802d10b829141c10640c5102c03581d00e19080c0d40f003a45910005012846600e150542c50902c030a001884610b090030080890b20950190f4080001c2001080301090001a01940260704035400010b03d855010001c10940d450740e06c900709000440c6101d0903c503074803405032011500306a000303120540d12410120384618020b460901004a80e660601405404070043d6030321500c41d00b000541c2c0e40d115030035560200c0f111400400094030340c0e49119540d090a0002c2031070080180c4d64103003480c0c280c000c0652544141d01448903014010390000082c09220340045006003030326800e6518982901400500e034440c02d00081d64550301389540011b8403403001040300c0c45070b905034280d0007440d09140c2d0300301c90100307030418180d9021307414001071910f8450070b100c1d000c105800030300e0b2005045040000039061017090790154a0303820307030480b1742400760320080210b844051284017444000481d46d1520562004950002901071152880412182169034454544204803a2070900c1030400540004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 193647679 1250 193646429 193646441
    0x90402030d08090a02030102040e01091d0309010332160215060d050c040c02010b040605090c04050f0a0806070804150b0a0b0c0a080f040e0108032106040b1c15 70
    0x25015400703511500c50741e5201d20201c030380201900058900c51643e64000030300b03a8015810a400700350310600104211000c0340300720f0319a064080d241126511819401545030300807a880107040c186c503078401d0f2103c4402d00e4080c07000940d40341480488241c584560400700503044410a181123584112510303242e000143c0d0654111030034940e591309a1b00c40d81444081f0b02da03a181210b40d40f0070310381f0724003860b5214012500005070a9000190900c51a8104800d40741158482c1d4051105042808514841c00013182c2c103442c001c0d11070012980b0307c030000c18a55a565844850140255414089025801012603014038000d10b80c04007031090300c110300401c5880042c00c0e02d500400c84d42c020401c682446019040b0004814166085120a0303201c01c8150340c0040158208403000041c1801903100340013010b405015014011410480112815400f0004005890484414140018604c0d030f4468102e8000340c0800341c0300e4515030411030410507201c90301400845e4015140d11a0041e0404103104034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 193648929 1250 193647679 193647683
    0x3010c08040c06031104090e0f060132450f06090604020c0106121401090519050307021e03010b030d0c26030c040603060504022125021b0904 62
    0x601d100b602d8500164001d10f191140b4180074101404000350403881441810302840c2170350082c080c070800c00080039040410582181c0c2c80107000c012000720501c984100b446004038240e920200f000d100900041003825010100413042e0f050503d1446421170307107400580d52803041c403020321800001082c03800452408441000d0b0050b80704000440c245005c0c0c00781900714402420051901c43c0e4628681c3c2552a150000c1c610386e440075075000d08000d01c1548030440d808102c0003c00007828a030b0b545603120f45071f00e022101c1c03c660403404070085c04018001c483d45580e004050340310802e01e07a80d10180c086410075001e4840d5207003840301e1000d42400304403011810215920240109400da032048020502c90700500c81c140202d80c003002103500c00300c000398050610010a0f82d15a40f5019004082d80d119401c050301590060005c420001500468441c20300308485540029603a0100f42c0041c080707409480c54a02c000c1204991066500410f0300741070101c0003810050100d940300140404001c090700c1c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 193650179 1250 193648929 193648943
    0x12070c080d0504170c0c010905090103050c0d060e01020a17090a0c060c0507120807171201090903020c04060f050301060902040b0f0a2d030e06060307030210050409060e040203010c0804 81
    0x1001c1d00d00100e640b2590380144030b6614000d00503005044d00c042900207914004941c0d06c80301c2008a81d68200060304002d11048a8011807581542c1d5250303101c400c01c445803400780c66801e94520402140d50000e00700400000300031500c0303610598004110f2080400d420103800d04050100d85050302c00300b201200702e1307081015203050b070b0710307004080751013448000d401d503040d00600c030001c40c007100701071200d138071090007600c802d5104e00c90ba041c081c44c0300403102c031803201e5640200074000c6044c903400c0c40981103405801e40054095940c3c28240e050050403040603034000e10b0810046034045204440c81c06840c01640200207103910749030a502284641d0007450341c03101d41408042e400400c400c0040c046403100d1f15244448601c40e450300008800c000c200c0c0c91881140b00c0004203c250b041c0304502000401d80e00603d140d04003c404130307446400e5070201900403000c610007a580c203409103040b9001414250810044c6503500c0711003001040342a6030483c401d500b01020841c106214602890055400c404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 193651429 1250 193650179 193650187
    0xa020f060a090e010f062a080904020c0d020a050c0613091104030203060109050f0a06050108060904240f0b10080f060d0209090c03010e1c110703061112070c08 70
    0x42084000d4200c14511410451100300102d1180183d000e141d00a0444045c0011180e0600b035000d012004c0c1c042200340182101c504400348001051282c10329281c024812955400440000c20702070720445090070810301c100f07003402001950002c0da544d5054055019200c8080a0307600f048010300c01e000e007d0f44400100003040c042303001e045d40402c810124540d209858540c5c1da9012908003c0309900031281c0c42d94910400070100b001a22256000c807103104104407c904002c006400c00300b01400b8640141e01030f400141c1041800c0603400240080803080b4075450031710f15440800344c07015014589410781005840d0009060095802407842c8140c0c66549850350f807400c0d000c20003031008207925403201040d526900580c49030200e2900910390200036245400143d070515081d1109507503011282d41c0108400c200814022413170300301040851914030074a164450020b85007800c141c0010b02100c4c0340c60003201d02070000304020f00341d0164583d421031786503844180a840044404c0700142409000700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 193652679 1250 193651429 193651459
    0x31516092304020f12010303050315060f04030305030a0f06140111070f12060f11370c020102011d010207140a120516150501080f0c0a09051902030702010209010801080a02 75
    0x2802800302d8031040304a00d170901d182d0360400e085000f405e92054000c140d0001c28003c0c003142c40717000344d4450b0605548103845e140300c10040c82100d1240b031201604100d00070011506030b9945810464502803070400074040c0c41c0d05e0305111600c0d800c4840e255808510300c20a40807141c94081100c00407035101c1402c80c80717010325081c20a0b064032825207049541710703510004102e080d94039100d102158540c044505413502410100b41441d100401c9088240f41003010319606c01039922103454807550000d1412845c50016440140c0c054a040406440014500503c15100d50f1056000e401d549001d00e01030820100120f65094480324201c0c8080d007040c41c49440d030140e4500490083c0800c4101c0c1d001e85d205803115855000102c140030183d402a6512440100f1001c18108100c00603030a0000c013409a0401c04000214007102078401c0c60041c80d29540000d098200c01391440c80c1d40440c05600750364034981140000c0c000d6000181c4540440d66142c0040b454007400214941c11950280c050305000304e4103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 193653929 1250 193652679 193652681
    0xf070e010e031207050709020c0606100806100e060408030d090b0115080103032d030c02010501090c0507020f1804080a031107121202040510030209030d0806060403030c02031516092304 81
    0x212005d64544c800d0301c800003141005031000744003084101e1301500385420000e04119101000e0f81c050340821410205018407652924103184401c0100c1c201100290641c8001c910f880c0a2980020348500000c6044500704d10705070803500c021480b407200c00000d6030b00c601c58001841b0209a240300061912001400080d000c1d600c508610f803c1040064582d01141c080508900b080c49013600001c1d0f01c40d40d03400c0c40990240501400340001c14018410703028003441c010414042c51201a10a945a0500003060788540942014207481001d0807034007403400d410302c00010b6020b030801d038000030f00d400341ca403041c02c02400641312515401000c054040342c208000311240ca004148285516608000c0080c5540e600c10440c5903240c402e803000758440c590b1100700350800101e4030201050100700000c020503036071500c0413281a6581400d00418200403800401d287c000d902c0c650301c42c0e00b244082070090f000308401c1e15028201d01e560740c000c00c26403220080000035031f291103034010a000b14842c1300001d20785 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 193655179 1250 193653929 193653937
    0x9060c0f070c0f0b121501020d05090409080a08011509120b1b0c1506060306060a05180d06060503011b020d0e0d120f230403110111060f070e010e0312 66
    0x54004901c00d940314038492001425503070040e0130b01c1c2d9001401c00c0c4200b00c04105940d1000200d014040c0c144168400071f51202c0202c03840e0350801900003545100382d6200c2c0e000040082c0c00285464540070000d80151a1150a0188210410400000c10982c07032080e00801c0c1620b880c0480c0c03d441d8407280d5191410000c0180080c001845030741404000030b8001805803503001690310051100c03402d07003c0305041540c0041d040c1c50055508100300009519035404692900c000ca2070010b544526a110007200f200038846000e40c81200200d444003031254075006202580c8044008120350141900d11405040e404510a80540c1180c00711040890040b0070720b101500f0081c040481191603541d4100b0100c9000544001103a803140c0c1038554291f2200310b08a0a401500544444941300c504520050050b0300c40101800003d4010442c00d074858255124440401c0d022a203a60030320798203041040303604441c034a000031503a05041d01a51710070102c507402c0c09005006441550601c2c090a081680 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 193656429 1250 193655179 193655183
    0xc0c030706050a23060a0e0a39020105041707080c0a0c0302010306060c150b010e090901020d060b04080604080a0507080706050604110906090909161401080a050903370503040b09060c0f07 82
    0x260b2640c0c0c1279a002140d216a40454203004410b6171a42d40c0505140000e40c5007000010131a890b00081100255042240301840c0c172314206100d8890540c0c0c50003075507a215100c1e0003805401801003041c100310500e40c241c81078910036242407107015192030003100d02211040c005001c001c41c8252200458885510100c03002c401894000f0a6000240214001c5881980e441420f41c0d80010309038080c1c0b1052244c407000c3c01c0d10007002c0340b80c01c3c03501250325541c000141010708401c1001504280d0180120116401c041d849501340784c48003414208030000349400c81da00360045041c8890041c03c4d0300c54078212840f030500281101c0c1420314007801d10660480081145800d845540840702c034800041007918000c04038440d0039150100348200040080c2006000c1c0040b0070309260034400c0700880882910001e0460080301c241d60a094181c08211644500080c603409112200d01d200181e44030004601c41c40c05444509501c2d01d13007980c11030b50707000104d5101106c080c3c12322414041620080090030014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 193657679 1250 193656429 193656431
    0x5060d021e031b0310050610050a0207030f0317060f030a031206090e030403060e0114010311310e03070201020a0f080903150402030c010e090c0c030706050a23060a0e0a 74
    0x95004a403802204850f1030008402040f061100d600e010002c541c0c0f4204100410b0003181021004900d0342c1581050381810700c42d002c5001d0349014402c115100045407c80e540078200d08240c01c0150075014010040d5400d0b51b04000000c00600b0a8561a4040300c0040c0081200142c40c0e201210049213000700d842600ba00c42e040001e0f9510b80c0d010702c00c11000210302460355245540b800300300310b4144065400c101c0e41011145903140712040851411640c009641400318460f11000034034110250380e800c456104001c4051080c0341000302018071545d401c6004100c1c0d60401d401c03652b507038001d800c0000e006a001030b01d6480050081e004013020544144541d905100040e000030f410540700d810002c80701496802004158a0300700103002040e0342c00c1c02c08500c5c240c50b00c1c01007102910000c0403015550400034442c8890b03041007040340c80c8203410130300800807821314040d080050543d00c414000044809050b0303400f40c0e10058000303030040ca0700804a11391a8a0000d415a0329200140724001d01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 193658929 1250 193657679 193657729
    0x71103010c05270a080c0315040305030a1a090a0e010e0a0807030f020307120c11010e090601031a04020304060e071a030604180501021c0f060308040308030421021006060305060d02 79
    0x140c444c02c0c86800685941000351940303807005010705241a40299268401c90f10401c113000205e034000048a80200f03611402060005030001101d00001070300316899080803074034080028592050380425007900c01c01c4000d00100c21408071095484032003003409061002d003009000d002a004103c2c03100041058010740c2c2c241101c035100d24403456801d240e20004600d0003890305080090303003a0205041042420101a03206858020950a140041080e418156110006501a0080c04000c1d8885100030b2040d9524640303464000d000c0c00140d13003070546d50b114908000c6806680018594403a0360800308440c05c45c0e0b204000c0001821407030a00100c00f0308180c4d240000b1a400380014980c4141c1040c0b0065a0100b00c46400c007201c070281c48403400e6500e01304090001984007030440d01280d81042119499846504150405042100382580e040d00480010704070681c001ca88840b4100445074100700c1c8964804040c0c0940380129000c9070b200a44207040401403078940c10741032424059900c0ca80107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 193660179 1250 193658929 193659007
    0x10504111605010b10020a060f020301080a11040b061309060e060102250308040b0a0f11030a030203060a0503061305011a150313080c010b040608010207080307140c12071103010c05 79
    0x30b00843c5d55480d0300180c0150010000344002d600881686803a64101140303198506200030380c59142c000e0700100200c50010007246280d40750341104280c180000e2030a0b41d10355160100019032400da11a01080d541000d1000039190f0886282622075807040e0068080d00d20345031140b040303c0c80801c05242d5440d0424001002140c00344018002800380400701e1030b55a078441e030010744001d081900f40000c000d1560240d0f1071410b000320a642000140c0d02300036031203498940008080400a41000d40c05105080070800c0b41c0c86100030004d440d5025000070031881c065005085501d000c04580d458018080e0002e040d280c1d07801200940d8000301481c1030b0200211241d8600c0f029500c503002060b01b5030b44800501409141c47d00c2340c11300605208000b149400500c0d95002c0d01800020400c3c010f00c110b8018040d0030f881a4821610580d8042c02500d82d4480c3c042c8403001a6000741c0d1040c0d4840101c1541c010040c101442000003500ca01d449150406050308080360070000c1042e5240c035001140312501030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 193661429 1250 193660179 193660189
    0x30115061e0c051b010e0906060f0d02040504090609150e0d050a03090b150315010e06010503130b0f040b010503031c18020301050c0307030c0816030b120a03090806010504111605010b 80
    0xe504844c403683c10000449000602d0011314440051007034140a00380036803540e4840407101021101e110694980300b0581e0041e0007801150b210540050a1514072405c0243c254421000248180030011410981c000c19074219451059504800d50010800d214214020710242c2004061840d020496200310b0340c070f000d130b25141a2500e000402158001080602e028080509560718020f80c1e10b410798942a19210fa0400c041d040c28180100040829100e505000d5110409500800c02d0b8039107041001100840c2c09003142c003550703130b058801c0001c6594a0b010044034140c115901180358043d510700081d40050680c0310040305000c005114440c0141c1b42070240d0b9100340d004a10700c40e16441c00600180c1540d8803040c000040181003810800b818070213172404040c1401c141b60000d0300d03440e09008240d00f2256240c01c0001d512541e4045c804159001442c101910035070003d940280c0d0380d0310248800d0f00d001301e0721803030b50290078041c441030940c2da01c408211440c0194000700700c00f0504d0012072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 193662679 1250 193661429 193661443
    0x130206070c060219080306090606040f06020c01030c03060510181208180a080a0b10030b0c0304030f1b0f05030f0408060f10030b01050907020f01020d0b030115061e0c05 74
    0x31090748846608002c09901400b100c6160450100013145498040e610a1050b100041509214034081c0c008600d140c0c8800040d100985080803900491075110031000e50713105180d0200a00090400c11100240c52090081c0d070304032000500580c1041e00114000d50f4008003400200c241400c142c0d00014200c84108941e54105002e10902c6540310380035905842000c442d0480a03001d2685403c0c02c000a040016400c45c10740d0b00002e40001c107071120118114a0005a0b0024142c0c80c4400203100c2100c406200560040d032003520748401035440c6000564900b40c14051080c1000c0680c81711401041c2d02c1840c5ca44070744e10510a03245800d03030440e40080103410039041211181c1c445810415948a40b0202e01d4201c1340303108000491a2440e62020100c1405000d00380c000d4031342002243c0c0040c001c021014081e90000b000f5916400064040401007140c404034901c607608002c0b080f8241030445c0040303008d88000e942c50041c0d003e100b400d40704038510b0003101c240030408001e5045000c268140101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 193663929 1250 193662679 193662683
    0xa05030a181205120c032a0c03270102070806010909050106050306070e13052814070f14190c0212030409050a05090f0c01030b0d051005010602011103010b0901030513020607 76
    0x20b07036150070312004c1d20182c034400101070500458041042c0403520980c3c44203840c01c150f050010004a030030082400c0114052903900051910000c41e042c000c2e480241c0d12071340c403050300708041100e503810038004a07a91b000501c6015055080a0018048031200340c100040080c090f000220f00b90790790700f01291600c4e40445610000418002d902513981c58880c014500b007048240c0140701d0f9060220b407403180c1924100400c200c01440c251110f00181c40c5030081300d0b281366800031030052413030048009091581c69044450000350380c054050012200102920500c0c2d0140709607810011108505440c0e0a80c028810390f8468140001050f0281e800c02c01400a06400c3e9008102820001e124800f6510b000d00b52001d6a080700c2191139004a000075034980c0b03204240781c00304034408042c002c00d20340e15000700007a213240103491910307045042c183c00050484400c1d074001c03c6a002d2503004030095000078011030104000821a68441d98444d41115030414821080e50004800c21742c00512180d01c0a042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 193665179 1250 193663929 193663937
    0x60b060912030901080106022419021c050a02040303082a040f030201020106170c0d110a06020c0a0609050904060903020709020c0114010b090a05040216061812050a05030a1812 77
    0x1000407a580c400c5000f801081b460000f004100b01ca4003c81d10321243c0c40307809d945000760354400200000d25560f00d010f084090400c0866540541e1801c81d181307007454049a10a49040170041070342000c840c800caa00302ca03059600c040c1207450ba0506444c06a400c40000d05805400d0841703100b14016600003032004081100c641d6100e5407940c4006402d551165000d81e110303074000c940c007041150001c185e191001d18200e41284c0349030010301d40114044005c0c1c1100340c202074044400704955800040202c1c6040c021120420200c0e42d034242102d01880b2070195540040c40500458006a903039000f481300c252013401620115600c4849040882c1c01408413002603a44520000c54210f02031540c00d0702402100b021a4500741c0c1c0100895000340c0d00c0e20409000729030004a80103201510302c120480b40e503011505000700d2071040788003070503058051800c2d500380c10003900c00c00d1194002d008450b03030203180740c0f84c160940e940c0342060001071000d501c2d00c404c21039104d87d908000444444542602c8031181d00c1d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 193666429 1250 193665179 193665187
    0xd021201030314131202210c0f091b030907081204031a090618031606020c1605010c120c0b0703020c15010b0f0901051b03071104090c03060b06091203 66
    0x42c014600648000d000c060b00d20200090015002c070180d03003c0070f80e07120011440d44004030f4400b02d07800d00b0408010181015400d40b20614a0901068001c00d040d400c81c2d100418151203410060301c03c3e02541d00082800c9901040c001c403061803c00795a0210301c0206407443c0e195035044941c01c02d110b0341200460b00c0c6001405104100c8628a500c100d0303201d4800750031481ca0f14000c1a662440050000300b00c951201011200c0202c040080b114400d00c0c01d8204070200c00103191141c00381d04814034200c014040c2c00f240b01d051261080e456000c032541613480e8801401c094803003100c45c618030703101142008080c664000c080381009240c0d41c011310311940c0040e0355021a20030b40d8100900410000f1002c1c2400d00100504c50480040d40d484500e80c1141d40e98510000340180c40794401c0107000b20410031080014003401f1408806001414090308404c0c1140c0a9507040004840c00414000c000301100c200171b00c081980360f4003100784008040c26040c6084a41400941c405c40302c6880d448c410380c4001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 193667679 1250 193666429 193666433
    0xc0a02240a0903060e0c0a18020c03120117120d020711061611010f0207030b07020f16080601060318110609131d060105060708091507030f02070501091404020304080d02120103 77
    0xc0701740c1078280c500b600135110041201d00000d155111500c24036840c0c007014a80b80d0b00030300c0154101daa1300f03001e07501184d0351a42e0814940141000922882c0540b44030144d11a8042401003044040c100c041d5070340306d141c02d4203030303103101e00035008503c0c184c4030020032021101c0f803900c07910020326215041d445c1020044042e40b07080b1390300d101c0c1021068100220240b080300710a400085041c1583e1b80810030b81c542e941c421070101e10b084034051461804c1e200b04140c2c007410703030802007691050380d038824255666a0b03214a01907094480c201da0031102c4100d082d0000c03010409901e600c2130b2140c0001d02c2e4600c0c142c1c1540c00600385004800075501241e965510003007140d0324802302000c40301400c03405850a0f41c500000200a4050501d0161034500c0000301c81c88542e41c0c0c0c540401705503c0f00c403240c544480140c20000d19401002c1d8022001d446222400305036580602e501c40c1c112032030f882c2801003000b03618003808040e42010340101c40b000020300a010140c0c116002400c18607044140b000b07003540c958 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 193668929 1250 193667679 193667681
    0xc020322080709020715090b0f160503060613030b010b0d050105040612080a030612120e0415061812110913030f030905030702040609060501030b0103020c0a02240a090306 75
    0xa9608048540c01800081000c2030000ca611012101800801038440d9039500344183c0c0b1011520824125514100032242082015590280602c4081209590f00e42c2c581c13242103600c40400c905070021510600010300540f030100010300024100440c448217660f660794a50401c0c600030f820802c2d00140201c0c4c140c20817a0f89108a40c0103100890381881203d240c40c42c01e0100055412002e003120500140c2030030054043e4000310000c2455280c040c1e51144103051000c1031031416a18a0002010755080f68254600b41c010030301d80c103503015400c10015207442c800307840b081e04915625140d8140b82200060502c40d011500e05494012000c0782c50f40481e03035003001040c0a00610303800e25801d2515403030001c20b42c44883c0340d0300c000c0a400c00251a2100f03003083c03031640c001d1500c020761103401d10700c0100300c508040c0c01210482d48280c03000d0100c144c01c07400640a9000340c1d04407406036402100c50308054584814103448580c8036680070070742a0840d0072800b04030390101c076003034001c40c4119008004000c41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 193670179 1250 193668929 193668967
    0xe0c180f01050103090807051507082d09010b040609141e010e1305010f0c020d090e0a05060a0b04060c0b0a0603020607030f0201020c10050105030f160b030c07060c0203 74
    0x14141816545140c44610300301040300c1806080d0405a55080110802141008a0b201907402804030344004114401031414004220340c41ca00164085020a2500d1480307100010031004a0042400510740c8110301410000014010700d1780e5900c580d11a00162900d100e46805403500c0c3d03e001c2342040072612a50100c00c0f000d00800c58003c60b035840c05044040380300d02c09055131090440b09a840d280c480403a515580303c1e0760060f00b00e5103403034a0312142e000f455108102180301e0740c0985040406210041d1a00d03070151042c6041c490003c400140150207a501c0b071f40d40480010082d0b507c030340d15410035102c00c2e001a080304c40490380c103442a0b01400000c541440d440002c5c2032041c003545003075a010071001d02401034024180010034171506500c5000b034042d20f4070404000300b1039100514280c00781015020a100e000c5c080c0c002e0500043c0c811001180704e0074848081e004222080307180c018150900d61000340850620041842940c0000c1ca46000302d00340c0349560b500030b54944102902c1404881e40e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 193671429 1250 193670179 193670209
    0x80601050909121b0307020603010e0907150512060a03050a0c030c0b07020a05040c090902031003200102071208040503030a12180b0106050d090c03060509120a020705220e0c 76
    0x400f900f01d0018034940344046600c50b030707114000d000201c500341400074a0750040003002944860f0210010550003001482a8807404108040b41c0300260354041202c00340c50310780c810311300140d4100401e01100300402519500203401426040e506030381c0382c40359800c2450b800000c80703015035451010000c0c40650b2a038207018103000030b0450b1a000d491781c00104403503010710640d8010768071941c40718180c44c01088448010302c00490300355501d24001c018010014402d000c1100c05008000c1c610744505c42c50314001c107810f40d06070000c004040c1000d07504081c000841000b110a0740d0104404210b9842c148080c01c081025521981c03805e030100e000e00d4080c0e408145404000f15820750120000c10250500f01341102d030340381001681c400300366101a0140610040150002c40d85540c00801c0101590060b440b07405020152424104c240c030300610a031140c2d04000c00160712101c0c0c10b010501c2c0c0500c0c3c80c800303000f1541d4903042c40c0120344240030549040c13101d0100f03150032028403d030490130039050b03a00b1000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 193672679 1250 193671429 193671433
    0x907020d050a0c03020c0d080903011404080426030706020a110303040b0f06032e050705030c040315090f0b04030f021f0e0106080703050606011b120c02030c0406080601050909 77
    0x1000000c010200d0161054207020050941e43c504149402804038402d00d2101034210300c1750301c0060030310034103960010010500035881c1056040900205d02611405030781d01030b112926252034032004101592003003055001d9212a0445000c81c400d0410003007880d18030a1801584400c65140b0260030b528805c2c40041840c1c20810400000821003501c02c0d9001ea20320300d4100340c0340c0b1403a0110340740c01d0150003410600300d907240c0c3c1585414505040c0ea40e03c0d2034903980a00c003652741c46c0021502e82c0010f0300d0301902140e0a210510000348501c3c1c8221580c40203100001d4140001d44a89042c02c400c02d0080c2ca00e58402018002895840204050200d40c140000c0c0324010684039800080244040181601980d80721140c80716002074000500400700c2c081100d4550f81c803030800940f01c00c400c1d140c00b80458920200f40b88041c1d80c502015072840e0b0040004000c55400340010f40e55011030035822641405504d003c43c4855846200d01e10107000440004d01ca0340d814082480140300f40a4507000c203070707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 193673929 1250 193672679 193672693
    0xe010e060f0915280b0a0c241b08090606060d0e0316030225060f0e0111070909030e090906130602130605030402130b0a051c050f0c090702 61
    0xa034481c1d080c4544a420300303032620102c55480321041d1015640c502a0039038890290080380005501c583d5078030000380300e407460b0850095a00c00ea07a408034810b0089000100d40300c0940c81c00860f0b6440e0610107031107403141030813a00390107088252080b540152a000b943d00c500c03e04d100175443e0300102c00c4d075014070410010042070412070300190f540d00458400607901d6403188180102200d05206850300100c001e1040421a81c552a01944480f8600030512541c44070010360501c0c1d280780d800c000308892164481600c04525080112880e40e4466405418058001441800c41400300540f00090101c400700080050452400030104502e00640510034814541804284000464805e4101a81001558400c000d61030258041c0c0038410a80c14102010304000881c130ba002002148500e2003103482244032090004008126440185d03201e03000340781c00300f0500c500d0804241045141300c1000c00000c2183c201e0b41c0d180c1c0f40410249412901340c0040c070040119040ca40701503a04805030b40090481 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 193675179 1250 193673929 193673941
    0x50a03150b0102010c05180f0603090c18010524070c0807090f0203010e0112050a12032c0d0f051b0304060e0a0602060a02030a0615170a0b0303070f0302160f0e010e 72
    0x5002c1d0f0843c1540c14141f6094943d825541c0e049003080484001d050300da1a071520741d420300e03206c034440c5000e14000c0000303220007510502c04cc80741e40e050fa98014145866460f0800f60071801180740c0c151094400810040080030410035010000108604402808400e0810301d040003a20b200301480c00d8410300610041c0850f50302d407080141910f2039405110720b03d010310b0512030302d441c0c42c640010303241740c1c2207854543c41c0d203a0540182c0c81581d40e0000c070008244550600e242402c0100082a807641c10400030402c00500c5100d07030312040d90041c80c04505009000302000c950850100616980760b00020b0300304155030b0440c04022440d2130481300302085500c4d00a01035103452004115020f00c5500000140306c28180d58080e00103002900b003100244c5410060280008602c10304295200c10070000103801903039140030b9600103c00c00b60256080a81a94070038406140d6107408a055011303038807090304903982280f0240c000b00103100c41c19640a01c0c1c28001c00c107211040c2c01000b2000425020858 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 193676429 1250 193675179 193675187
    0xc030c02071805071403010b0c190506040b360709020408030a0305060409060204090c2019050114190b0a0e0121020a120c05040b28050a03150b0102010c 67
    0x2c401d040b50106860741d0f5240d007124413000d0144580b082440c0440081103601003500074008c40281803049521030180b032a00947c60072503c5000500e0740c0e128200080001d81c00b0400d0682240f45c01480e4041241c02401c0d041802118080915840c0717a10b9070880810a02080b044004003450320342189424200620f1544a101c1c409910082c151550013184c080e40380c5d940445c041e650415030454840d0b494841417005030140b400c01c0d400281e40200504c91818400031103d102409070401817035159541c010743c4890000022040c0c489542e90091021850301040c40700c0c4c4a034901a03d544d868010290050b4111920401120701030501e440c014080b2403500580c441c1034810f414030444481c02148801c240c084540e4a0083d00019000000030f00118200049414070784603041c800349198132281800216604880340a03030048402c0403464100c405030211001d456101d4501c81d0f070340c94a0300d020910070405640b0032103103900041c0c006410030849200700303640c0110920080c041c40310002e1000b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 193677679 1250 193676429 193676459
    0xb010206153d05031611032b0c03050105090108030307121109040e0c0414061e01180b030604050106050a0905040e0c1e120708060a09060914010c030c0207 68
    0x44003600d20000340b101849003000128018030501c00580311400d01e800040060700203480310b00804c0350200014051034000d1002d01880c82a1000550a110f5035103543d024868000d103400c4150b0948042603e80d0340020f0081240085103a2030114940d403501c02800b0a40d901603000c440070f0340092007401141a841206a4101c0240020124181d10141c0360054240b00345040310b43d000703180c013a024613583c0d03020806580304801240c0411402c005000c640a807080c0489006900803c000c10f400d00c2e24004034149120404185499001e10a900e5040e103503c2240ba000305010402c04000c00c030080c603090103224050800c40c5080d078182050004040c249001d24020303180310b00c1e04c481000106103c00c000c0351041090007003004141803007080005c01418000c0c0d0fa060701800e80070100380074883c8000750b0141100c20940040c015561440500300c010300c0080c2c400c0f00c1054880821401103450305826540f810101d00001076042c0304850081c2c22195440c000006540080e0340070024442454220 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 193678929 1250 193677679 193677709
    0x1050319051803130501020c030a050606190803070807120e03060402131b0c0c0806010f270207080910090f050603041511191b06020a020106051002010b01020615 71
    0x1207040d40340c84942401c09510304100c04a284004252006020041004102190001c0c2c09540c54400c9020a141d00c0c0c0002d403501034036651080e40860f40601340780404004901280c1261506e0a072244c0c0780c01d0070b5502000303040e5405000410b030003042c0545c2403020309002c03225040c400c81a000c0c010101c5d40b607800041029120703110b01407102e0301c00041504011040004420344040b00c02c425400a80100b0701404140c0381d2500c404004180040b000403d541a034001c0000706030420301d031104100d054011f2604e030101580b0f0181c4c07510103548403070003d010100c3c0f04048050f00c8000040030b0100c40c05610a003801041200380c8100080a801c5d01c602d01582d20540741c1130342e41e40d41c500b044145044241c108440113480d1104c004070110001c00170300300b01031505182e480701e40c0080031300f125000d0a02c0c1c01048105c0c0c007105820002502d070341c020001c18105000101d465643c801c00074800710b1b560020034015075103c00491009603818400594020044d590014045900101040408100c0145 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 193680179 1250 193678929 193678931
    0x20a0509040f02040c030c090b0c03031614030f010e06030d080610020106150203030105090c120106050c0c0405010b03011503060312050304020d08030103121b050c10090b0301090207020f01050319 86
    0x30a0a100d0b500c0095411140c010f4400c1c0840e810000d401001840040d00c0d610020799900c0011508250050841d03801e210302d0310046045031114440d003404020611442002d108007800003115960548029520820b07030010150404e43c54580310002540700100746a10980007070668a07400d0760480c0c2035540142064440d80c00c0510000c0c0b0a0b03005008540120011a442c041845902d0f43c6c004011030582d402512074249030380750036140d121640500c841008503480c0c4440140445807050000e0020040048201d9644d0703040040070500300ca50030f82003402007041c00801031003140c0740d000001410b071066141c20001c581c995102c408440500c3c50342e810420500102050566442c414509049074102c0115036a950356031500784014400c404884010880140307140848510032090301e2000b0390010007034880700c1164000c00c0329000b00f4141160511091200c081404480e079070185020708085c400050740c07000c0c9401045096606400e0640c10050704004020031001e491200403500514104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 193681429 1250 193680179 193680181
    0xb0d0b0601090509010806060f06182e0f020c1221090a08010e1612171b030c0106090605131503021002010b040b030706050703210e0a050d0903020a0509 67
    0x3004994480580e403205500c03003007510005c1401d6501080050058104075040700e01e52074007000740810350081708081425100c204030101482e09100b101990f0392150f0304502001d2482d030a20088401140885d04800900b8010140c100a9010400c6040c2c01e04c0860740001b0001e10070290983c1c5501d004526520346800c412885403500c4c0c148103032400c000c0c1c01003181000c40d4403a20194001c10041e480c0110314411030040d4004000202170308000e54642c1c60707040c40190401d844000741d02c40e440c002c00e24100410881340c88030000300c84091141c07102680103159118060304172103007900d17459080070442525218081041d581c0d1554a03a8103034106000118079403100000503c1c41d11910707400650048800021503a14540c198010b00800310100e9007000030381d91a005059861489001c1d140108108100d06000b080c060200041c0b2449a212b1010301845890100f1050750851800c10155a2000c81d040d0100300043c801c1c0c0c01c2950140c501019102d103160000340000d14144200303030050040c10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 193682679 1250 193681429 193681441
    0xd030e03090f041b080406111c0507090e0705040f081207030c03030e010510090c090e06040e0109050f0f10020703120f180813050316050f0a030b1e010503010b0d0b 72
    0x40c11040218400720507070060741c08640800b0301749001c01c850490300c1929003d003040040156400381e03503540050700d03110903e20b010780c4800401080083c00740d60611618650002e85034110b41429485941c07180c0d100c5031201c0c6001d12144015242d07800080307598010a18010b0183c02d540c0990750582c0e003618011050f00c0d03442c1016001009408000f024550800c420000c1e0840e0350003120045800032002000b10039401681190b02c42c5850040c60403003031a850208140c0d1031702e40c10214400c3d604500010b8101115542c01d850440c0302e02d446201c036080f0b00001d0508034002c0c000c0c604d407a100003030306516011072039900801c611001d2206a000325507a85100c40c0502059000a1804140d04030000598800e17041c420150740020000b8001c4410304203000c69142000301d1300c0d10984a403100800c6459080c18104880111120880e80c4c00240b4405d001002c03860545505018801350100c00304000712040c80694001c0050300b04e5030082e8106031110240361908a21004810f400030b0821001d62101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 193683929 1250 193682679 193682681
    0x9062205060f070e01030c020c12070b04170c0a030503070b1b1b060601020c01050706090602070f06020306150301031a090309060403030203031f1512180b04050d030e03090f04 77
    0x22202502920a12041040e504a62001240104800d480e0744520014480c0114290345c500c280000058100c820700f084c243c03c00e14100f41d0185181420f0720f00750f40d1a05074442d140d40003039000d1102c1c806441254003084006010b25125a08291600300c1c40600715180c29549224400340140603020800020780c21031300710702c00f0b84100070721401131a80c1ca12100340c1170b00c0140000313400e0140500940004c100c4030341c000120801d0440042c0c646030b061504c40d442c0d40d4000c0212100541d0202e400b08100310001e50440400d5081c00d1245030010786a0400605100c0781c0e120441130100e40180c00c00c01400410b201a0350281d003040303040c001e8007142c0d03a4003420506500604418a0f04800041008010513030088095032007521045407101031150116842e42c48030145120341500c3c100c1d16403200240c81c0c032581003140c0040300004049145502c420380c1e0f8140e081c069100340d600000c1c50b82803008003d028819810150309074542405488008001a5120311030b201e1500d102c0c1d0241981e0340607548070703 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 193685179 1250 193683929 193683991
    0x9130f0206190203070215090a0605090f10091a091305040203070803030c07170a0e060726070302150f07030e0a080c03040602070909110d150c20060906 67
    0x40b102800c02d800382e0350310020307549400c641c908034811072045400c0c0e0202480e05040d500011070081040042c10300c0c041d01502c4960000b041c050300001155042c2c1c240e62a034408034441034031269641d450032460310444da254820305481915400000700000d06503651020010b44609204180003d009d89a61000924001a40e0302c40c41c0680030100410042101101c05402c1541c01610751038000000c05140d18258410580c011002c81c0000c0c8001c802030034060f01400085216114581c40c1002200410400d000d40324501d0200000c001030b1401019411b1124140c05141016600d1681c2020303c001a103004c00108100c04043da0703200300c00311500003000341d0070203035400400d41540d42c6000c20165440c0da129000782005885103210008480c4420b101d900502d5411020200c0c0c0500203c003005400803c0c09020b5070150015501e1400c0d40046101e8081241c6060b11030342d0586038440310320440080b00101440d420b4228004100c1110004112035901103520350400010301343e040d446001c8070710 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 193686429 1250 193685179 193685197
    0x170c0a060e0105090f0708070b031008100b0a0603020319020c03040308030c0301030303060510051207032301180b090105060d0905030a09080606060c030a0e0303040503010c050d050609130f0206 85
    0x300701a04100355070419072119000303619080c1035500e800300c44a1101c0e5540c940d442411a50340c0b161400304660040364004d0360300a840c20351006441303541c07040020f15000140c5040103200d0b40c0e0740d407416003610706035554500902c07a80c02c3c29401c602d000003507403a05103014913141c5000b94000400124240d0180100c0f0091980141341c3c0f512411f02d00303d421100d03082400b045000c40d1400001042c1490103485488144941e603665034900b2006101010203248080d08010616499000f40194044881d003c2c5022103a11221070005600d40008a00540b10307130281c206c070b09840d10b40d021900d600e44002e2241528400d4484507607030409100c3c5400100b5060101038454003012800b809040d0340004080c040340c508030126891501c8801c1000250320a4a0820129a02c100103080005d070088000100d405001015a03007800c2c1c0d907401181c2912201503040000500001701070300c1f03d42d00c5210341a00040306403403c2c0014a01401c040b0007480d600f00002d007400440c1049075085681d080701700d50481c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 193687679 1250 193686429 193686431
    0x501231011070e0402090a09200a150201020d1d0c040209031e06090127030e01090306061409010f0501020307020114070629041401060f0210060609061b170c0a06 71
    0x29940300e2030f1030000101502c04030710480c83e000110707800032104e0003480c81c21500451180851a10700400303852400c420306d40250403070800800020110440a1440e41288030b540001d03941c1c03605221803004a9003035010040c80c0f1180400300151f44140000d84c2c0390201c800342c0300180d480c0d0480c0c000a14028941c0c0c030300391043c0c805120744425501c021030740301e0048000c2c8009106075140092443c00012142080d48881d0212903a0400400e210b20903542140b40107041031030805880f0384602050f15501d070480760155000c5000282541000152f01b4010241c61042c90710b01c0707040c180002d407a0310a44901a04008005e50720301e04504014080f2400b180d403100c1c003040703c0306108a6074144412071070218103102106082c01210740c1824043e01e030020900300b4094000781c0c2455002d88010780d1480001085205440543d5a100414400c60000d803000d174440c200040e1404400506c1454600350040070ba01031a031140b00002d441092240c000e985013000103440f00c0225480318030701240c20310701401e42 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 193688929 1250 193687679 193687693
    0xc0314070c150302030c0d0506010c05011b02071a030a0203060a15030902040501120b0a0f090501051807050613060e130c0906030b0a230612010305100501231011 71
    0x11824007010011540070b48102e01c900100048103600b03d0000700c400011016007044840200e0016a02095003d603050400281c110226103904d821128085000521041300101010325140c0401c60f0780c0050400c00030224611074883c05100301800094a443c54040c1c02001041440c3d5501702450041c1c05511050301c5111301c614002006458136000c181c0c01689400e0001c42c01c200d415940c00d050a4000142c2400c80e168280b1400051503400c100c00103050b5600300c0ca00008401b0b002d01c600445120403150113144e2860b42e02401e1007803942c429440350008200c0c4003004010610044110380d09070030400580891200480c0000030301c0e0390848c1d22581340451689104e600100540d058441d142c0e000c0001c08007c0043c84603082507402844420039071107003e400c0c00d60100008200740b0102400e803d0921031038a003101140b140a0b08211400d402031401860403070000d200c1e01f401404c2e2007007050424008402001410018028207902030820180100d00d01400b541015002d000d03000200d43c41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 193690179 1250 193688929 193688933
    0x6090c05060a090612020f12061306080c03010e010203040201021009030e04020c010f32100b04060804050607020703030c11010c1e0204060909080306060c0705030d0804060b01080c09010c031407 85
    0x80c0e03d9005034408203030b240c40c044800840c28402d0310348425a42c000e1918203010081d4031621040002e141e9548880f046882040c00c502c1c0e40582c500800c0ba01c0010120b00515001300350940b80f0b100703801c01440c1e2040c010807000d41c2e4000350038044503a48200018110100b42000c441c80308140b070645070080d0000800681044055010103e00c400001c403c2080102c1410b401c04a0024003a0742c410300503000d5051303612a5820b24070349130001001144144c48542d5140501e0298019078080e1021440010410040c01740504c40e0a5100da024806041c0c82d508540e4003512514403840040c141c01c2c600c42c0400c00d640d005002c0306040f070b40c1101c056071002c800c000594213509185401280502d040010010b0381c0111800340b40e103201c0d0b2214142e81142d8807082400a0b46e04183c0280f0b031240310b10383c0d00248944090204a80e4600f5581d0343c066180f03403a06181050398890400581002030103001c0200070101c0fa030a54403184c07424a8076480c40d00160600720f481200410300540380310340010311041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 193691429 1250 193690179 193690187
    0x80f070605070c110d12030b040612050a170f070311160906081009050706080c0706060305010903110c1e03030403050114010e01060f021209010908010203040b01030c0902090102030706090c05060a 86
    0x12118860006005810140420b022100300c984d05c0040c0140c401c00303410a5118000e8200f194201009803000480d140c1e11044d400e603546400384144c982d9041884454140000112802c400c20804d00b269807804844280001241c8a11b500160402c4000b40c01c0e13a01c03182091000707405d1031010b90301c1d01840780d449205d118004c04041c420b05500303108039207000340307031300242e024400080390408080c044291034250150740102d001090741c1044c3d1000c0044c080018164403500020f180100000115400503141c06030403001c4001c6030115550141d03040207440c0d03072650303468030103500480034582032215040c011a145000b1600010255405e000309502100e07600000503049866040407a0b005990302c0e40103031501100c2484e0a801a00980c6000310075640c488000c3c601c0304030601d07001c0c0c0800c3da64059039089810030b6070b080718040c44110041050000c10301c0d590000d4503c4000031032400c004800040d659105a0743c005080b5610340c0c80b080140220941820028076015006941d292045c41c0020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 193692679 1250 193691429 193691447
    0x305070c0504150e07030e06060d080702030a05060703050a2d0605060d1a0a05030712020d080301090b15030c0912030c03120f072a060608030a200303060d080f07060507 74
    0x41310745856000814040c40303030240000180029000c4c01440d155071041c0402101840d80a0340d40d40d100304103240060300d040040c1d04485000d040600002c0c100590000d06550b4007501e20581e4a04010510b00c0f84001498407200d2900305907041240c8a154072440030180a041c0e100c50341c41a03005c10440c12452558000b15010220407581c098001e88142c10800911580c0c05181e80503030128006000394480c200400764072a000801d0840c0005d501e581c4c0020a034400d0f005905200c3e29808000402c0c1000314044190884c031400903400c51408003c02c1d4014000c018510388200c41c640780c00c80f180041801111403060981c4141d071f40c1c0740580c52030110031032002e03102c0f5200d40e52400009201d0901c6080c0304480c041e030b644070204200d845030003d140c002c01032040c01d40b04280c0d601c5000841c0390081006100040d0305440d0346e02000c807041d10307031006001c0121a1680c039030020802c00565a8580003200b24980c1c1c050b108686800c1068100c001c02c0c020380600404092401082c00181c5400c01a40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 193693929 1250 193692679 193692689
    0x31603150f030c0b040b1905070804060905030f0601061b0317010603020a0801090603051005062817010b090a15080106060e040606051626030412030e030c0a0305070c050415 76
    0x10f030703400c0e0b81d6408015410b229034401d00c148a1030901c128059400d01a003014800061443c00e05e06000843e1180035155000c0d5025002107460900204014141803040003110f000c0c0502814496140640152285003a0b400301e13145911b0325008d890030503003d5121a400f11855419814039076031038410140003584040c0703484001c42c0d00500001645449406402c1c2520741c088080c209100b000f00c14034001c1d100240c0070035403060301c1000030300c42c200c9900b10012151b00702c00c0c2c00b10441c070b2a1440c0d515120f0034592180419034103003036400001d519030850940d0815002c41c00003d05240402000048440c0c40d08503c0c400c1d420710381c00240c050f610070b0000c58555001c030340c01c000040e607804040d1100e10031595850568907030340c42c012012420703030800643c0be45c20301c041105121202c82c03110040b99200300c400b2602058120440815540c0c544180048a68200000c518000038210038594035911448010200000001c160381040030101c000710003030a000c0c00a102c1001b5500072041404024064 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 193695179 1250 193693929 193693943
    0x301050a05060412170d090507141009030b060102120c010e0c0d050c0d0203070f0b0c0105090a080d090c050402030112030e190905090f0a050a03081b031603150f03 72
    0x4180c500d0030742d007283c0803640500500000c40340c65a440d2480390480c0c1a0f10503851034184001c6410302d9060144505451180000c2c000301818403140c0a0082e0030301242d240209050510032072601c0c0c0086191007600c0d04107915045035610000101c1c41e20205110318000c02074085002c0c00415015040345074803040144c02e51351130741250010300045811802c00540781c2c0c5d000070110320140c103203421035644c0d6500103000d86a0164954042d89203020b183e52004480890005006612010a00c20503410110103805401c42c00501d4841c45224014580b0440459945503080c0040202c011002e1008080281c0195241d41c1d44420b0002e41516103401500440c14070f0745512024034042d464841d100d80354880000d1241d041c03070400d10007010003d0402c4a18414903c4044100804001e420074492046001b81003440300761400521014001c0d101c03210015255040c110024040010380e94002914550054441da000000700c0150458a460502d45005184c020485150210300b00c4141d03401990 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 193696429 1250 193695179 193695199
    0x19090b071202071e030c05010e15060301051612091704030203010c0207180f02070f0c032009070324060f020c062107020a06060f150305091507020709020708030105 72
    0x1031402a0312031204000c01500181345204900c1c404001c00055440c000d1808001005072503551a003103551000d58030140380d001d00c80e1039107800c00b5101c4103940444298000d200c10300304184000d101d10705184000c0c06004650301070810203c80c551000390620342240b2400f011107580d40078041c4507401804240d0080d400d00c050754a030300d400041c0001c21222404150749048030802404c0005041c19034025900680805c03c90300410301205105018900914010421619610340311440c4001d0910150001090440c00c9055541d5070442980c002600d040104910916204030404812500f94520001d060440080307961548281e101d54214103a400720b0301c50500c50010011136000d4415404080e401d00c14040444914441c0e80d40d4000c07026004807400102d81c2d03070b2400184c034459048028012100c0f376082100724241c01605020031074500b002c004904004281507241d0f1a90003000c14060350710070114808502c2000303000020107640c081191900d15500d4064002e80c804e1041d1486010b04070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 193697679 1250 193696429 193696457
    0xc1006170a03090302060306010c06020417011b050703080c0702060705010c08010906050a051e060406020d1e0e10050d0c090302120d120c051b03120a1a04020319090b07 74
    0x24404141c15059180c02e40464a95800c010030b076400245070764100440c0e040c0e100c00040d001e0000e880600603e000c1c441c0032402000c109421174000c554600d5030003d40351803600075aa00481252007194151600d40e0880d038032000c0d4a070032071207a010000d4100000140b514180f05040d40020807486103541c4044841c1d980303034081420349002e40641503108625010420052400c84141c0403444450341504801e0103a58000034201d4102e0f511110260b0401140c0c028526030080a190011204548980c1205070560004007007106480b5030a018149850380d1110745801042621960701c4540b0042c082990096001802030182d403000324050302001c10046469140442d0352100001a680c0310208140c010000702c1c007038440b81840348207102003000700e440c0b42e05848018103219140c50004545c0d54140c508405902c00c0020444c52645141c9038005004014100c3c02d805000381c101d0703000d61607490f0000d5031010000c401101c0890240307030020000c2008501518148161119128609d0040f00b40d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 193698929 1250 193697679 193697683
    0xd060b0f0a05151b010e060403020f150612010b031002180d2409080409091101020d050414031f0905250302270c04090f1406090c0c100617 61
    0x1600030300782e100114500c1d1040b0f4000003400f810f0302c0006039903e050f8081c1c001064900b1126002059055508072800704000e04d034041050002800c5620b005209103880f44e414841c1e80140908100c4c450f401c0d1840a01040b0400d402a40710580002e050701d0f94419500d03810f000a501140743e840840700f9405254406251981502d01c003070f03412440b402200798400c40d0281d09021041d00c0400d68a40e650041c0011075010400351001d080083c43c0021403510b141014654a2a8402c1d4603046600000001e50b4840d0f203c001e5030111110103a054402074491000070303080042c1d07142040002c1703808116141000c0c040f41c10000000c0c1c0101c05850804411046004001c2d180e030300d02c2400405141020401824003040d0051021441031080301d502c620801244c031900000d1315a44031144000c1000d0000c000720780302e8200f070915090400c0080030924886420302c03038002030481c0d2150031000c00080c103c4400a00f103503200d0b54402c00303659000441c20112402000c1c0d0303003c2e030b15403812900d0f2205645d0b540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 193700179 1250 193698929 193698949
    0x1407080d090504050f070e0a0801092d0f02011202120a0204030b09030a09180b090a0b030c19031104060305030a0504140109210204290f01031104060e0402090d060b0f 73
    0x2e1701a0360541e032200c0c010744034034613501041c540081400c0d070001a4480c080c03051000280c07246034201410554000548011500321180380d9000284081c00e0b40050f80c40c0340201001079082c06c200e1845100d2080381002401800500101d42c4240c030100840310200f0f900130000c1d2881f6441a4031142c41d07903809a55a405010b8541001c0755600034140a440b005210801c85008806004121010b007d40450154202525400c0e8426114004450305207802e0101e24441e110948a1071014900c1d0640464150140c2c480500800542c000481d010348450304420050343d080b0b000ca9542c1c14207407178010b11a0b8000d11070304030880ea9000da0b400e040d40c8a50842800c81d00c8801e115481410200c8980c204608000000c0342c4c440c0da6400303031070a20140e030010000105c0c40c44c1c0102440703202000c2400a10040401424109890f00d1000c0c1c02d10005a400e0300c0640b0744519004c4000c89400010070005c5c829010410780c80002c1804100c10000703d60801320a10304161950425030071540180041005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 193701429 1250 193700179 193700191
    0x30b010b0c030a180f0e10170a0212011506091406070201090608190608010606030e0307030f0c030c02040504150c0201091e02010909050a02070203120909070503041407080d09050405 80
    0x2c0101c42c241512a441c150032101c40084d20014080d95246955100300701d80c2d0110342c1d021041d408000140d20072840080c0107200f5030442d06685500412241e4031900c90000003403151103120944c3c0705413942580201540342e108010045c07015100c00d005840090584515040c0020700b00d00980c660801c0c2d810746164940c182c44040605003040f0741502c091a00410001010080c580d55150711002401018001c00140703000140c8542004402020366a80c00c40000640d441040740300e0000b03520071700c224649255031400c08410051032504859020641034060750103801c08007404148171010f8010f4501010b014001c02a12001c03120507406c3e0b40b245c050207030001503203042c000d105102e071075290180795105141100c1c01d20340b00c100c0541201d1090701d158001c19400b041c1a411404d0400c0b015007054148113a0703074100b91600c00007440181004103e0000c1120110105040203e44807002082070040c03001e0390074454480884550342e040105a00002400040d40020b841c1003d228840c081c0f4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 193702679 1250 193701429 193701433
    0x1305060a09110d0317041b120c0e04021804030504060e030d020703030503060102010b03030c07060e0a30081b0d03090506220c06080106140414190504090804030b010b0c 74
    0x100e071079400c006050f46041c40641c103104008035009614944154103600c034a1082d0302e224400b03a441122600700724520b4200340511051801644081424001d6190403a04184a404000c0e44c580c408940303400341c800002800b00c6086002e1108164001c80500306807006a0f5440407000441300805565408000581c00580c00180c01030010078441c1d401194011810700010500c10112000300746140d00c9a100e0b030703101e500f100f0b1040c44095031003803000c3d0714000d00320784051049040c2503040717401040008a0050034032111104c110312008003d40c2d125019080110310f0345546c000d4403006100c9640e80551f029034010320400103011400f0748580c0303094030340080082919903140c0d0680c1030b0200500060388501c4040540700070018050302594400f605090340c034040154900240070b0500340004900310f107020024482401000c4858035820080e02c01150004c848030003145182c01c07180500c1c3c0ac211740050402c41c1000a00c81003800500489114140e660304c640c2c0c3c2c402d4810900c0c011002036825903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 193703929 1250 193702679 193702703
    0xd0f020414010807031b051c0504080f07030201061d0411150a0e0a08030a0f09050d02010e01030b15130305061806070f140a03061d091011121305060a09 67
    0x20b52144001030351211443c180041c0003094000110714100d40c1d4100c0c00009000028168009030105005404103c520b503014415802c2c50b40d1030115030300a0707031404c00d000f03980483c1802c24140f00750803620090a11411001c0044254080c110240c07404450a884003440c80184c0c56003400c0030056010010385c82c1140b00d0134130311300d4082101c01c00160b0702c0304c0754084041440481e5044040c40107205800171606d41c0f162140c821540540307021840e51015200c0d59030750041c8405030341c10a0004940b12400d2900041101030080022541581c00a4081c121007004c00d14003c11007200d10001c00340c074001d400300c0320543d4800c0030300314849484400c02e84013508000302203036915000b4086018191103e05100b8403a0700181c1d0304c100d00e500203c5c00c4900081e180c0b40100041c0800098510040d0401c40c1d09250f0380c44c1c21003c0540d41c290402d864440d680d910b00d400002c444025050f100c15501d140f258001c642081c002c2d003031444003040303000d8800d030040c0008501e0b50750503845206444c5602048401d10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 193705035 1106 193703929 193703969
    0x7111512070c020303030705030a0905010603030206060117130f1415060907050a0f05090103020702041103061503010f030209041505040f050607020d050403080912070603020d0f0204 80
    0x9008014030702c00050384000c412a84e00c40c05071300700699281c80e1030850400810102e500a0269440d0110100070143d0102d0514091030342642d9103107100e5480035240654580a5400319031120307010640768000740344050f8128941d40a02d9110070100000302865080c00b4070070f03020304081c0003c507003041110b28003c003905800428600d4030030b04040300800007401d0003a000d030000003481000700c1c003003000c2e80c803940441d00390a501800510000700c51004407071454000b5907200c0d02c18402031101074275188020098034129440849012110b901d1034090050501c0c000d4002d17169901d247c0d22009101e20240071b000c5c013840c840e50b1a603c219100c0d04095040c408040c010400319008040d100416640c00707003d56094940042c4007035a00c108980004501003030900480744a8041d103480055160b4050707015101e46102440f0901001441c840303001c0480c4690701030444034958440061030 = true := by decide +kernel

theorem cover : BRFrame.Cov 193525179 193705035 := by
  have h0 := BRFrame.cov_init 193525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 193525179 ≤ n) (h2 : n < 193705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
