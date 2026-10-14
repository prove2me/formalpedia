-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3690
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:23:54.461993+00:00
-- url     : https://prove2.me/submissions/cf552f3e-01bd-4fea-8eae-fe80b0f31042

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 663489208 ≤ n < 663669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 663490458 1250 663489208 663489247
    0xb0405090a020423010f140316033f0215090a020108040503040b030a0606020c030f0d0f2106051201090c050d0f060501090609062102040510120308310206 68
    0x308074044901d540c540c200c0b040340c40d910703005244916a4031f0403565468079001448010044010850f231205500303503501ea4034100c208018220100c1c450a605040c01400b036030180c41c4090100b4a004030503490180000d1500e28001d005102d4081d6801c14055903850100e80704600796020f09095000b0b80b2207203025451841260721010303890b9000300c144103d80c0a180c00000403512158225070001032024101902e441d0b5904621a00354417000c00480c0030387c01100a10600001030800c82800340c822500d00120300c1e08a24400a855078a4509000b9840c20742c16841e0400d91b03180080000300c50607a00c010a03001940079140c41003090710101010042508131940d5501d03880202170050f075960f092001c014040600903178803240d06182005c207244c030300c80204906100000d10051003001040e02840b00404014010511155096401240710310540c0b4888041c80e10a98400d030310381c0b0300040381d11462282c2d00c0c03040c0340780154801902e00815480221030402c03501121a580c1e0307000406c0380300740700e00c05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 663491708 1250 663490458 663490511
    0x30d20060c182b02130f140c090a180908071a010e0f22060212060f040c1b060204031a0a0b09070806100905030a0317090102040501020a03030b040603060218040b0405090a0204 77
    0x20100c0d050391a82203900104c02034155618220300b20b4072051801e00c4140600c840f27061308003507500c008200040d41c0c000c1c46c81c14a445040c00080d500e09a4580704070541c00550140c88100d880580300c20b181103805011801002030304403101c10703400c007412160300009000d42a58040060340540400000b002041d035181c05601c0301c411555115050040808110121822881040c10001050003070601d0b0050304901041c65540c10b030300d400d21803807151601140b1041654402c3d400e20002c000103c0c104004c605100304605c80030078500d00003089000b60303100341c540715005040000c1400324050700700290340e8000c0c03000c0b40c01080d54001035a00300c1d00004694032035941131007248240c0d800e060700561601024048940201c00c84da0303c04070300030f00341e100b00c2c4103190050f03204410f80e10100e40303c0d40c40603031603010040020492175903949514003a41c01034a9400320b15201c51840b042d41c5d14003840f62900c40366065409200500d00001019110480d440c0040d00480e102e900002c0700e12040540c1050b40380 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 663492958 1250 663491708 663491711
    0x30715090e130c0509060f040504140303090f1b0a0504020a0c060c050405030c0604080a020d030c050706030515031b0409060207170a0815030d20060c182b0213 70
    0x160044034810b162103800d10030f031840c4802e030f1804240c80c20a00f4041d0720414014001c00545c020007000c0c4001000028001d4400e02241c107002440140240001c0d8000e44050b001000c2134805129400d092001240181c1d80b040d0713041c0c5001290b1345402c6100310894200700d0300140c641c00b65020584021242c4607004010600c1c11010071180ea8014018200359003094084805404209090151038880d80c01005017a51041d51603000500e0111342c240c40c11032083c68002107900c1955916460700e011508030301b0209445101b000590701c03420641c03102c00c0c101180200b24140c00c10301c5000e04e01000c030414500030742d141c000e208180640741c3c04590025900103400005840c0040c903d0702e85420940d48200000d10356408190300d20303a03030a0000940003004000d03000900d44070605a0b80c40c404a03504a50306400004101d00360a014005a0710640c4030030000c5598181b19920380740f507140c2c0400c206200e440c220510303818150014281d1402d0b1082c03940401050a05400014082c941140c05019011b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 663494208 1250 663492958 663492961
    0x20d09020d08031b070203210f12041a0f190902090c0307090e01030809010c03030b0418060c0201060b0717160f05060703110715060f09090c060806030715090e 70
    0x2c030510095100c0d2000150301912000c8180e140c24103031103007642c0070754151b21070303000d83c0604450400031001e5017070801c00c25440d200c8a5602800e041c4c0041601011540d4200208000c0c00800280d6104d0780aa202105145103415402e0440071030016008401040510303519510342c0d860b5601440c1c070650002d1056046140003111055a9401150610001342c610040051262010242141a254013842c61070400316070000444222055200c161304060f103441c07201c40c0c0c07a111440b0324100c1044642c2c2071030300b4500906007941501c0d0b01c04142021603240440400c076030802d0005442ca19a0f201903010809410511000402e00032038410010941d481c5000388104000f034000c51400d28414001d558070303a0758284041c0d04403000000c108500c90420001d400010f0100012401c240210b0100058034075268003e052460001c0e80041c002039a546403c40240049103507200003c213082d00d410321262902c00c022039110030325031007410303c542c0c0c4525440b0f607003e0103070124501402c01e880d1440e009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 663495458 1250 663494208 663494213
    0x50c01060b190201060303230706050f1b0c0712050f0d20030306060315030a06060b0a120b01090e10080604111305040209180f03071118061003020d09020d 68
    0xb6070120890031409044044a16951401801000100c3e505600c0b0f01401c9a10014610062000001411524401000501c1c00a00c0d10302c50f050080e41c485002a081d4600049280c0c4280c89045081641690a1250b0100090f001481400340c0705076041c40300d26043c0c185483c81c9400c005c4900021640103071070031070340710590051841110300d1060f883c8003000f841c00d600350344d101e20007610351035000f90082000446c10000b02000919946001d0202d500480b030302e4076548121042900b01c1d0b0b040340000070701d020301164031008003003014460300c004114040a04002030060030b41c5120300c500c2020083c0018009810f400001c4005024402c00c0d1030180ca810b01d8050700c4a944100001d00c0b034002d6216685507506148078440c441d0360302070280300554813180318840c9540420f1040c182d803842121030300191000240040c1020911561003500c0584082c810001d0f1a0000030f142c07048182c03801c003048140e503201c5148228104030b0782001641c84801056003c0a001d007a24081c2d000820141100308 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 663496708 1250 663495458 663495479
    0x7050a0506130b0c04060905010f12050c041418040605190908091f081b041206020304060c020a050a0b221202160f23120307051b010206070e01050c0106 67
    0x880a100d14101c030426544c490580c1514015800b541c8001900e43c0020302040d40681d0741110a81143e0800300019a2609101d2041e52000c48650310310300001706042000944080400c81d203030740226440c101034007100c440104036610040c0060016a100d20124504413000e51844a001780da80c881403103646140c0c244078045510a9066500840512070300d0b5260a401e440c5110070f03040e050381d40010030340b91410502c90807510400c01c0c1c050350004010005003908009060480144035560258491a05017420301c1110071b4410101e0640d0041d0410000281c404958003d0703c543c00400d102041e16452071702512072850501c50f000c54405000c10034203110314003100e520b88481c95800c40701c8210f8003d40b4a1018000c0340b15419800e01a03013010b0010404411500b20064447e20050440001801c00205031410040400401d5040007803024140074050180016908100090b10345070380c81d80340001d40c0d40030001c007510304014881c80040d910303a1042048a8010308041d000384112a1203292211 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 663497958 1250 663496708 663496741
    0x310150515040305430b040e060f12070b0705030403020612090d020712063308010c050319091a09070611060126010e100c022a040207050a0506 63
    0x21207911808400c21aa008032041c5c0507689440301200c43c0214401c0d2420008500c900445100c200d40e61070b42c042042c0303d002c00600020540382460315a5402c01105002d00c1c440301d02045e80c050170110640c17985502001501c0710440c0d10035500c10795188140c0c1405401c50080341c0009502c4040004c3d03440128400e00385580c0102410f5042c0d03071200d5a6220180da0740ca199108041c544103280c002c45c8046030480d4404d2000c100e09040c800081092901d03800c40020041900f51001000f000c0148051135003440b92488070b203454144145141030511601329414075442050b1f000c02c0c0c5030000e030000c000c6143c0d02510311204419030241903090482e00c941e1030700d12034043d5600182401443e00c09821002513140d0480e1110508034a1031080d0040c08802000f10340d190800325034880d081c40c400034174104000140d0307108103036001500b403120501c002c0c2441c0340c00004100c1050310400c100a01800320400c2800102e017200c005940c2d180ca840c2c91810401d07001c0001e00340b8051982002001c81c030b04150032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 663499208 1250 663497958 663497963
    0x20411090418030e1203041203081006020c0f120114010306200906070206030417030c0d2a110a0209130c0e04030e091b0309011b0e03101505150403 65
    0xe0042e54014a844101503036850380103800a0350a054a0056052116064190340c01890550f8035050716112242c0311303841040c07822400588c80f50b0401080031b98501d1150068003051001e060f15040840006141d00c1d8a10341d03082c8105130035000700154410961051a15100070456a0000d60b56420420018600702c60416180000c5203d403d0001580c4401c50701404002040c40d03040003a16000e0140c0c0b600024400c69000080d03509000003101c0d03840140d480b41c00c14254080c0e55800701c4100405907100030302c0c5880308810710003200d209094050030b911034040491078100411024510480d1405100d06c201030340043c01d400500201c566000210341c40340707015411481034155194060809400d040710b02600040e42e0144211013032520343d000799080340e0b469400d880103205030320416100d41e100351180402a9958513080702c0540e80ea0000c44e048800d0341c00d25280c4a0807090109844017892698003042d15641c8071030800b4801c4010340c1402900e005482100100c99280341490241c0c45404103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 663500458 1250 663499208 663499211
    0x2070b091c02030f0403110406051f1209240b0618040c020c0901140609060307030902240708130816030b060d0809010503130639020c0114070204110904 67
    0xc41c5169000000b10360701d48031004d100350302d003518644078021007500c00150f881c1c3c0306880d003000003030580d06ca5050f010ac000c180c1a607000c990100810252261440c3c1c00c41d48400c1c0c0c100b81544011039100c5815101003030140000505505c03255000d10000c00150001030317400b41001c02d002504070140f240c003a02046080d03900300b007804600e10080e41d88001d1b82125030761180c6048011310502c04c146082000180019040c64286009040000c445800032a503030000207980315480c00a51800c0054416142050545156401c0c91000c015a080c451008080c00b8940c1c00201c880d48003406059140040107014140d1780e80154240344a1544036180c071003520100e4560b40426068501440c1c41ca150a91101c01c0d01e180a21000054806400080c00c008034a0004998100825103602400a0004c410f40c054505c4140c2e69454429020310f1803203110b0201040005440d0b40c035000510115410000d081c04490b043e402c404a681512821a0080d04941421000c5100059440140c40c002004580 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 663501708 1250 663500458 663500503
    0x9010810060e0c1902100204121b0b0d0b0f03061303110c0d060b0d021207060201060608040822170c01030c031802100903020909070e0f01062102070b09 67
    0x180c4820410083c1d80f920480e420420800c42e140d00710500a800030300040c019281741d00316940621041784c005a026409001c0450988420030030061074844060030783c4138414001d1410840c0c1c42d5000d009119440b10303c0307950761000f09515079031100c1882d030708803004046640310b182c10f0007040c0c92030201e030100310301003107030f00440880421002c558031400060140a00c5141c11071070311000c1c003610400746480d4021000101400c09602d60103080c81c0d04a040307500812200b46040402403c49142d98003410411000409010000c1c600c5000c5035503400405040c480c441c40d260f0500540540c190b40080791a84001081000e02c080205003040c00380307000d81f000c001c0703484994000e409860122003ca00c0c0606160003041c0107240113400c2000c48a83d519022000d2a1640e0105a0406003594110303940e5004d039008016010320302c00c140d81e0000d041b0780e0aa009514010000d011200e404200d040c0c1080c1040f04400e0242a590644281c0d40e0003200030b069600b0420b00640d241c40300500010070b02e800c0c450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 663502958 1250 663501708 663501719
    0xe04021b19110a061b0611070c050307120305040504050901060b1303030206010f150f02010e0a1505011d0c0307051603031b020105100501080402030c1f080f010b0d05040201030b0901081006 83
    0x401c04000c1320324944078400c40315a4841240350720751038218215442ea540348428801c0c40e643c039014000c80d91040c81c10900883c1000100351505049600c0782d14070050640c12080000ea101c82698121742c000e41c0d020039070f03071203011019000d04183e400200c5200008a98081001011000b00c4110303400394094412a988850707110b68901614020270301ea07204886600e1000350710034003100c00c420013540700021708003842859107820881c0c00b0b4030036100006400380b2440c11403a2441550300600c5503d044040501034044146211a8001d120f1954054040009407445000700100e60080e00346e286240c201d43c0c2d103854085c000700318410b8010343d8291800e20702580703580140710311402440038140b03d032103880c646001111911070042c801c0f60140134429082006440c2c800b10803500a10001c4a100c800c08544030007003900c0300c01020076885914000041140056540484222048041c004952641d581c0010f8014004840040e504008298000601014041030001c18012000750074001c981e07890 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 663504208 1250 663502958 663502969
    0x90b0a06140304020d02030316060b1002120a020a0c120303050a0905070515090603010e0601110d0c06181a01052d0904170f190507030e04021b1911 65
    0x901450300031404a0001d620352688280c00741d80d00510080c00022001c070143d0119041d0740001c801480344440c0000d4800c10401180950010564242d40c4404001000b0300700079910389401c0f02018075000000796583e1400e00c28000c1c6030046400c01d00c4c0c0840c0b140d84403180042d1041043c401e6001920b06000303d02c1d145604d028100c06a5007100040102c1c0b03041c00b080105042030340d04030040507902003000c9200381c2c8500003e18001d1032441c0c00300309a0b290800000d46810000c60302c805c1c0c20303044040e064a90303a40010604501d9508004006800e000300400d544082c50543d10192403504843c14841e16603c0c3c001304607043e581d056078400b00010214094092044000201c0a1070003443c4440c0c40d01420f00c0c0040035070041c0070b21416000041c40c0c0c816135a00f9480350445842c03464000038906140540148041040c0340103180152a280440c0c5005000a00e1685502c2c40307150005010b100b600030b803c000c0000098000180c4a02980c0d4032200c0354401d81d40d44088401c10816400d1220030310b0309 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 663505458 1250 663504208 663504229
    0x71806050a1403060604080f01091a040b1b0403081306180305031903180609020f0a0b0a0f030f11041a0403030f0e0d060e030901110606060906090a0b13090b 69
    0x1079480c0d01d91001004849034500c1e400c0184125040f0f542808002520441000034200d082d00d82c0000060b0005c103030800780100b400404ca1791160540c26802e0200091030300e0306275a440036200d400544800300240301034019105681c0301070840e102c00f189100d45901204900d0040360308545a80d90328200b110b040003003804003480051f015820034440c041100c88640072940d800c620f00c4c0340002d075807400b900699803202c071410802d4543e15603070903468045051a4402c0a403015088a24028051400c0d0044005100740300000080100040c0c04641ca82e0281d0040c0c011001125400d0203846903031245051150480c1c401e60320303800480354000e4021001c402c00c45041e240c041d6940307001d00c0b440710070940382501c0100d201038112a44440c0030700825943e10502d205e84c0d0040004c0d513030f144007080006011400c0802c03504016000f03c0c0c14007010360b4401c4101c841995013513441545030448180003500701001c59011074400c2d0800140540303c80b143c1007018094030020324081000c9401d070340611125602 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 663506708 1250 663505458 663505477
    0x2061009060605070f1e08040e0f130f0203120f0901180f0605131503050910050f061002070e0903190e0904020103020c0102090d11011101110301030209180607180605 73
    0x1042110704089001c44184054507070142c2094006c484412002c0c01d08420604070036503c89401050502a10b081045da00750400041d0701c1c400c485090408411042d03c031105001009d64601d5007405045440602180c0c3c11800d034191038076102c0e21812a090760b0b9910000d0404e001440030944000d000c02104545829a07601c005854001400c12100755410b91150a902008900d00d820016000740291035082c818905a6008141400c203880c8183c985100b031240b0b0030381582410104030b100f01e0300c0035600d54000d10498050400c40d50b03d0a00380e0502e0107035007000c030b240202d103030400c035040c0400802807003010306d81c24482d002c10307540c0e600c2154a0780c0c482040a0b44a1012000b0074090361080d00541a901d0000c00018079042c20400092030950700000100c0b000c4e0700098000c500c1e984c012a11056030303da90002403081da020300015503030603c01400300174411961600800c204c010180c800000d81024401200c1035420041d0001e400b01044c5000c0040c507488200000c40c62911a8003903c100030f1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 663507958 1250 663506708 663506717
    0x303030c040915090e031809090619020f03010e01081507080a050705042301030501080705370b130f08060a09150911130501061205041110020610090606 67
    0x741005500d00181c40e01d034412542d1400e00f064045a56031452080c86001002e0000840c0d44580306915580070101da211503921641d030344400c010200c0c2001c501a0b0b88074100185c3c8d1201c511020308071600038000d0618800e40d111011002150b171a188201082c1a5080e00045131b0702ca0f0300305101d0f12011541158440c0000b41702d40c010413414180f58020036000400781c24114102070311110060140e0540098000c00c0030410105184c803540c1600c940b9005d00300400c0908002810000403407103442454100c40c2032684039108031006520a6140185e00d1040c52004030252a070322051340c0565082190500e0800d00a50000a0101c148200140455580c071002d481c2a035500f402c2c00005064650044d6142030b002c240302103010156218104555200d50b29051410040b0402d02c0340300d202c110300000c907013450440180a41500040c803031010407200300d000f090769a43c47c5003002c0c0407159601c14a400803003901c1d0b012495078020030540e01c5505c8415110200340d42c0c40780701c035007074524134403a100118 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 663509208 1250 663507958 663507967
    0x30070506180f03180a0b120a0b0102031815070204060608091203010e160903170a0e0603040b4204150e06060f0f0d0e0d09031505040201111b0109050303030c 69
    0x140e030718000f914001d000074041412581d986c411404642d200480340d80c040d45028082084550580c4a50402e40d0303020300c0110b0504100e0001c1e0000341400c00c40c29403043d8502c4036a00748428501e011a224550301410621004d50b440f640500b80724425200d05145000d4480901e001c540f681d42681d0403241c800c441503685031110f2681a2405802c00c801c0800c1190304140817010501e0440115013444a030003206946803007070301d001000010300d08030a500c908400c0042c040880e09018400e504543e00c060040018061728640074041154142a20300000c40d420b04984510b4607a001200c45000c251010311240f4000c0b09441101107084c000d03a8102806000400d180b4280100502075921070440c0c0309103480406142003015400c03942030040101d4a6107101c0b4140c86040c0000f40103d20700d41040180c0c1070542c0d8071040d0007089581030f082415694400901903a220340c0e1111a15001c41c41954401c070350200c0c028800d148655182c50205040c214001741908000080760701c00d6401c0c080240c02c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 663510458 1250 663509208 663509227
    0x1b06070609020402072f0405010311060c0703050f010f0f0509060c030907050a0806013303020d020f03040b040c120f0f060608030c1c030605010230070506180f03 71
    0xa145107442660015401d000c00b5000610a000300d12608040f0050200d000281c011404010a0f0800d042ca000c1c606020040001841080c141c00c0812411103c007038442041070344441c50f240184e8400740031840b8400b100c1004540c19400411480c4140300144041c404084190056a10a40360403c3d15800700c0005200380e4181c1c009141c000003074209682c19031b590b46001544c42800c03a040b030b07421600000d0041103c0d0b11001ea211060300c00e421141106070001c265010844921035100c1000d058001411003900c00c0c00d54111611151021507140e143d041c642015004180708035821100346812603000704810804a060074192607010300412001c001d903540d12070340400e0030003007160040e440b00c2000c200c580042c00549031001900b0300404052040140d144803422500b02c0010038940303050030901284c0d0b40800c0000e0740d9498204a00b461190152000c1d02e400030742110030240c03203030100310b01c4200440449c05500030380702e0340c0c00602c8641e41000c20716203400111a011394554400c00c0707515103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 663511708 1250 663510458 663510461
    0x13050a0305060613060503030a020609061f030b04020415060f02300c0c03071205011b080c1c0507030c18051c06060b07060204061707120e0a0203030c070303021b060706 74
    0x12000c04511005c41c0302035440001c04c0c5980c01915a020140c0c02c0b04c002c00001c0b000070845164014105803a0141c0b0f11012441c1c1601c0345514080584103001440000d010b6440701d40085070304030882e1320000c00083d07684000900c443e034401e661800501442001e210001c40103100c2c0741600c129403205545500c3d010718100ca9584c02040d0002d018000e80da41e081c6143c2e03040c01403c0003421211341c48080b0080c1c0707140540c2181c1074005040108050741c4080440554002c01a9601c101d8800085550b04c07103520206502c0c80900d14514400c505040c00c2020b0640e058002d0400358035181c461b1003120905e0000300480d51710340d0140a0704421260500c4c070659401c078100340d584034021180003036601e844d500c50706d61550081d001510b400390006020000994451090010882035411682140c2020840200a584090152841261902e01d59a8400002e00c06040c4541d03000f0202ea550b2190951250703210354281c4800c2c0d0142c09140340b807040c00c98a504412000b030760000d081616083d9160354030340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 663512958 1250 663511708 663511729
    0x1a0d0507090f060806040822060504120609140c01030f0e03030606130905040305090a08010507080f070e0a1e121a0712050f0f07030e07152313050a03050606 69
    0x50b1030588503000010750040034850350303004a0250005943d42c000440454084150002d110b1000c00a80501002140d40c010156804d86103588082e2442c00c070a070401c900586821080908003040d041e0600c8001000090302c0ca000391303800e0728144055180712580c2811500c3d2881414600c3e00f04000040b004e2920100074503080010030650b0400300d84039100701088800072901200425000507150341c161074102d01807401404500001e000d14031745103800030003220015003015030b011007030340126222a0291790b0790542014003404640007a550303100c0e0820441c1d80c1ea00301480054010001054106900341031110040d0444503c0d0680600c1e41150b00703000a005020208200b0003403100014610719001e240d00a1604035140c10040c02d20104054800304013800c00b200741032030720358402020b070804145001200c2c0c030102048100000c1d00825644042e40450700414009130101180040c50354102801c480480c0d45002012562150103000035031056000151041d40954006000d5181c078030303c1c21 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 663514208 1250 663512958 663512981
    0x111070e1816050a0918060e010f020f07020405160804030c11040c020a02090a021611030304210b090d050f0a2c131808160b04061a0d050709 62
    0x24100180304560a03030820300c11900503040c03180702c0101080140350410784c0001a18440d81c0400211005216440800901180007000e658580482c58071002003940060303410700f0740100070f40d40c03900c599040e40150703804910704910451516001c185683c4407452401220740050f2184200c0f500c594405440c480c14200b000c45422250888000384e90700e650040014100c2c1d50b030010030005a1030310403c640d070000140569409441402065803d464003608451410380080310305500351021000f10b406c500c200d070082d034017100ea070042d5180440d50107940c0d041c1050003190b814149841d5000c1541d1211910900c0e10001041804003205140043c0000c011005603400c01c3c0d10b05040d105c2443c3e165000c0c4400c1c0500c502001c644941d07450502c3c40501daa542800e0004111212580d041100c591400c1e4001074084400810128080d4528205415160350040860f41d0103240611b08000640321803c0c504516200e000c144110904260180c91815540080908a80e50030b2860746001000321a420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 663515458 1250 663514208 663514231
    0xc040e0c070f0312150f061d0603061302121005030708010605060a080601020f061f1e17120d050103030f0305040b0a11070c0f0503011b0512190e06150111070e 70
    0x35820945e01c900d03040b40041080040360b5600d1454890040d01e90f03003070013054180341c10068003500c0a9589107402c0b05c1c0d0000c811140c454032040b5800b100c2d8001e019400f2404000303100c81e070901c070b0000c0d0308507250800c480040b411203070f003591100c03012400e0b02c1451040641110050045550090241d80314592081040c41201c0d00b882031684038910303081080d114804a1200034010604030060080c0e0000034090b070810010f104090f1502d000c0e00342c4580d100b4441240d13018a40c20b9006e100074012403c40c00031180036a5251610200b2500003041c0a1000320046400085190b0041d4040e00a581c403641d00302d800f45000d907580e18100400b924400c1c4038401950010480303040014940615127000d05941181007001c075041c40d00342f40c2183c4420759041c01d002c19588d074100c1d03940c2e401021603040c20302454409030145c6909055817405502d640c0740100c55411b111010105010003d0500e10412000c0a1421030800e032500556440a07030407050901600024420b01000f0001954107030005645400d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 663516708 1250 663515458 663515471
    0xc2b11070e06130911190602030f0703030212010329060607020f030705030307060e190b01090b150a030b040b0613060311250b0a1a0d0201020f060c040e0c070f0312 72
    0x1554800c84000030303000c8601c207021900c2107115040c40c14550180501b5488030b018010700b040c10181da0307406034034915502d000300061000c003018429010703114024000c060019003540c60707103402e00140300030542c110410110135260102c10043c0b80101d42c000c080c0a44101c1c40c120342c94003800441411200250340500c00c2d5030000030380b41c074200300500c2c0d000d00502e400a0000d40b9800c0359401d00754404d0005060014607402000842c1c604189241100d0300c14000050313003c160030201e0800040310040c4c0710618004540446900d8140d0000340d4552021907003000140461400c102d0035000300c0880c1003c0d0303da0500280900c5000b90b2100d10042200c1801e5800c010302580080980d0425a810341d140e014085a1038003001801007605070000c944241c03d100002e1180f40307030211200035024443c803035214130b0428425079009011000d07840000b00300b942c1e520310704400070219540c0188074070030005004c00002500040e055003640d100b1580705280000e040150703101244e804040300012160aa940c4d84c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 663517958 1250 663516708 663516739
    0xb1f0e060a030e0106052b03170106030e0c041104060e0411040f0812070515060607050601060801050f0103110403061e0606020a03030507020f0607140c2b11070e06 72
    0x780041d111640c1e03000c6040b0440120b1a821345255074400b5000d00c0c131146880c01089860403524102e009600e408401c51140d0742011102003c00c0c003843c41e4110b05c1a4004120a91315800c0140f055050008940c0300002c14010301045610f550b861a5400d0418031085c4113841c811111820b00302d400420100d01625065040c01140e4016030207a0a0032915200410840b5420301010340341125000100d41802e01d01c0c1c484540352000c0040c0d2100901c00381c000a80741c0d588070815580e50613040703c200c810079a11000e010305900d10070f000c2c09115010400d4168910761207402064840001c2c0400c2030b051510350781d034001c05000841d045c248100c0c07002800c03400e800b0061003540014002c40d8010114050709007406821250003400c10303402c6400c2455201c20205d00011802c0c0c000e01e051030210350b5080390100138042c90080c2c83c503400160188105031402c0b1102c000d0395011106280e12044d04541d107290084d1103c1d0f5150021415a070003195041050344008221140d0004001d01814210224035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 663519208 1250 663517958 663517969
    0x1501081005040e010c081b041206020c1e0f0313030b1315061409060612060312070323040602070905060118030f0c0b09060f0d1401120b09010b1f0e 65
    0x6000c1a84d82d900c0381c0040307905901c10500c0340c00c00442aa1807041c4c00303000b9821952841180542030300545010218020802268121004034101000303403104081018a480038040c030081d84aa00d610484600d202c2c000d1021040b512040046040b40b40042e04e15070380c45440c01e100821150340318561444e07400206001c0600c0000002c000980014003a00f400c00c0d005c00e2041c0604900c0c002d00000081203000c0c0c6403d0111002d498060048550658803500001d18114204600070299640850720608054000380205000650004118070814180203001000c0c0502e03c41e100059004010421020440d070380816044070040c5040e0900d043e001e100703900ba9880c144d104445904000c4540c6091040300900c81002d041d443d0780c850303d0140a1000102d01c1c0c0582d190003012480e0016002c454114586d20141c071800c0340089403169581e69951941c06002c1c0420103403206404e000000c1c0d0485010722030f800020b07000810800712145524007a00c2c4030a0103000840501550384070010513590794 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 663520458 1250 663519208 663519221
    0x1520190b070816050909060f060f0c070e060d0b090c0d03050421080316091205030309060c04030308132f010207090207080a140d050408070201030e06150108100504 72
    0x84500040d582081c1030001c0c00560001d0460348490500707211080180d9002048815001d0115400c0c00b01d619000f0014292040b1890322130744c458400034810350032404c104040c00a40d610801030351180c641d0b0391400c14281c2e4040b0b48440d840700c0c2c41415100058070703040d00a5007048080e4100c640d000031140c00f040001101701825401304101150030000301c1c080c424041544400b814101d0501c0300e072540c83c481c450101409a05c84605401420001d1902c5008a8801040300c0c1c01c00103580596800c01b0b64590b40141c03180c6d072940c06088000360580191000321000c07203905a440d07a460f40c0ea9000ca54220305d070740050072120b200140a42505600000d42c4040c1100000c29800b01d1400c64100064603151240c1c2c00780007068014085140842e026100391005842c8600f0112904a41c2041100007441440b4001c1046464202800b040c40800c10103030840c14801e81f0200f2011041a0020750750341c80450354088202c282a05142c1d141d44907080c102c0d00004c030b505086450503100c1c00042c056408 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 663521708 1250 663520458 663520463
    0x120f0b130b100f060f0c03080c1e0d0c0518010e011707030e0f0706080a05040201031d060406200307030c09090903050306240d1a06030a05060a152019 66
    0x1102d0406100c1c01000b01c5118009004030b04005840308050302000d084075031111409030501c40713010f00082203803a04a0468110b0301801c9819074007149203c5054480c0d400050041550500d07280e04104080d01500c2202c2c85010340d0b55500c0c032104004001110140038410b00241005620f4940325026025003460900451441e100070500e0354001c051f0500e02540b03103440d0307041940b0840c02000810381021650b5040000b01501195a68480c001079018105058103203c001d412103007807901c03030304021880500030351148505004040c15200c01e411449a00c5010710101c51041020408c41402507000c00740e40041d60401515541c2d031036500300d045495140e0180d0100c2c10000803c090b0b440c020b40e10501c0352059115600703c0c0c01c02c00d900c0702140d026030b50481c51003075647c946c040004940b9040980c50a440100400d50700e14103100014040c06081e0b45c4203000f00360b21400440c148405200011a0041769591507a50f03803560b0019050800354108080e40038040d02d560b04424182c1103004030401170 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 663522958 1250 663521708 663521731
    0x70e1005120d0311162003030c0313080706210908031e090115180207080307051b010902060f07060207050601080a031d030307080a0527010306120f0b130b 68
    0x101c0b0702e030000d02600d060080d6400205410000e0f00107410948512000c85900158000400f07108980000c0080003100c00003a4144400714079540c00c900004001c09031401010160307001c4a03911050aa41c2e01554041e1401240380781c110b0f140c0e000303201941200c2a40d0640c80c00b0801d01460b071201103c0b6030090b900c0c0b180d0064507540c083c0c0000481c7d5038458200254100801000703009101403c01240540903040498070b9400504050380031a805882e14243c0041200350780741812413001c0c009900051407010141e002203100482c923503040c8540d40703078190060311140c50000500d8500c111640142000c54000e5400d2101001144081041d64064100c0000500c800c002c0307414040d0050418941c800c5c02d42d03400c0707003070340e0300301d032008420741d10a01d6101400d1074843e14007200540e5030707001e400c202101c2600d40456174020050300aa4100709500203890030000341d9283c1d6401781c0301103000c2d2006001c0d04001c401400020302030800712684151180394034507140c2d243d0798604907802e42c00e88845007000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 663524208 1250 663522958 663522973
    0x52116140705010507020904120c08030a05010f09141518091b10020706050a030b09090d0801060215040f110d03050c060f0105031c18091a03010b0102070e100512 71
    0x10390100200c60180c90700342042401d1401c1c6a00203075038441c00410040c8403503215031100d950940146e10310581d42c2d074000c403025100c3c40d000085800800091003030a00f60550030000050703006003482014410f4001d40032003011561010b051a94001a03030810b650000e041d848030408160180768014012a00880500b41014502d042c00c0320348210401e1007841401400b07401043c1c01d800280b048215030841c14002c0d10b84207142c1d02500103008101e2210b0700042c660b02000b0344000e000c180c0505008807526031075060798990100300ea607040801140d8003000f005c0000300c1c01103003103007070300f00203080c0b01e840c070114400044030110300e00c06850042140482d402192200e11034209000352980042091035079000d13589004006a0b554030001030811428031102e40c00c690b0f06d4411070409400524818000a040355140c20002c000c00d90f21022201c002e0b08040070050920703041c01029410b100507402403184504021084a13180300107061102401307142d0f05c002a03540c46028001c0301e001c010030041c0402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 663525458 1250 663524208 663524243
    0x81527090d12050a0b040c111005090a02010c170a0801080f03030601080406020309010e03030c0d0b10170a0615050a030c0315090e07030609141504052116 68
    0x51280151280405412100501600e9503022140544000d030101002c10151940981d04d0020848400c9075a0854140b50b5034a6109401c0481000100300300d01c1250030602c02c08489070111442515480420317007003104900c001d0344c0315420460009006003211030b41482d08144160869008000810208000d000108250314040c00310b46900c80390080070b18a107140103000244201402000105540d60101c04a0240c007800d60080c070000070f0580c108d0742d89080c000c50b29a038540003410100d6009040c00013440181c10007007081000700101e91501c8007407010440d400c050454005200780c0405596810000e0700c40c2e0049590444002581c4070555209400720004069174000450142818242681545100c107a114030340e045580c0e0131400940c0c40040400b01d410411903a201500407810a000301060295003684c4d01d03000c413030035000c4a0302035042401d2621054001c41c0e000d00180c0140400310b0100e49034203030328090742206020706481c015803400c8210020000000c203076110b02c1c07003515182c031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 663526708 1250 663525458 663525529
    0xa0507020f0604030e060d02090907020304050a0911071124310b0a02120d0e07060801080604030e0a15180f03050309041a0913020112020307050a0815 66
    0x94000030701002e48000d1800351400b40800701c02e4104203014010008400e8031040c6650f068480702d0310010a4036441d4100307124000c3d503c8e000760084030f20840003004001a60070942c820000d42080410b5182d0402c049910b40200c40b0290703003001c0d50002d280d011200700403191b25046c100f0030141c0c1d00d0710075228441d407100414003082840c0700c4800d03409000c458022002c09502000d040328900001281d60305013100d422401c011120340019014400440c41d0102c510040e0031905c0340c0700d80380c012540020b507942803c5401041c203104191560304a40041408640700e02690095200c020788041c8100d03035903080083c0340040300e18691000800001c2d00c080e69100b004180d07001006081c0d40d03500000d0641d16111303101d1194402c0740f031007199164565980e8110440104000780c100500c10301051030310640711250000440001ca0001740550754015a60a992003641d0240c800d0b90b0b00d0320b05003000c054099941e11b01c040c010b228580d6081c11011465510b161242da000b850a02100e1858210a03a0031107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 663527958 1250 663526708 663526723
    0x92a0f030818060301031a0c0d1404050c1c1b0e0106020f0607020105061302031b0f0d1506140a0e12030417070b0a1d04090f021305010e0604020d0f050a050702 70
    0x740f1802c02000100003181c00c00e0001c05403554804c10045079929050090b00e01481401804095282452082d244401d20b203010548510b0050003034503503001000341080030460030041c42031009041000f13210041031480d1040d41d0820f01a440c01100c4684600d02482c070400242d0002c0016405041c400100c02006d02406401400c0c0d0300091006040401c00240c81c2c4550a0384180134640c0800064400e2048100e0300c89003110018110341d4421400f01310b090180d0001003600d01d40c9040c40b002010202c04605214103c403130a40d6400d281c02040801040300b90703ca2091702d810040000590344284d41c0e0000500f1300c0200a900450340c2e1480c006d0b2004540441100d01615a00038420803ca01c165420403110116084c0c60418003031004044401c84608510503650303001851310741c80500304080c001442107100d008644807100082c2c480c4035001a65000d0040e04e0262150300c012500c18101a006807c071095249004600b100d80c1c500f419045032400c86d00503000d00c1d194020b00424640600008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 663529208 1250 663527958 663528007
    0xa091809110906010801060e03010b0a0609030b072307020103020c0d0305090c0114090607050f0303040803100506090f040b060f0f0304141501211a0604050703092a0f0308 75
    0x1103160b02c3c1010000e402d400c01441424240201014171034110783d000c3d40002d40020004000c4014141c441200416111150104881a038409004a100103026802c1c0c140da8040140141c0344045444884200341d8010140490505801b4040e04094143c00d1107034400848640d070340000c0c00c2c9048101c0c585400202454541805020071440400511a40488030046420740d000d540d074100c9840c2c050301e000d03080380c90070040c0c5c00003101b80000c00148000440c01601c0b00940600c800b51180200851131185800065020f0941a1800c1741414941c20100ea0103100900090608011040100d090340c050b0160f00e8255100008000402c0f281130b80c0c020703424421a0044c0595180001114030f906c406000e40d02400180710380228180301c06010014a040d4041031401810f1507c0341da2900154081e01c0c49072107103040c9000140064840e209081d10f00342c00008910100e980c003032460680941400c8040c910b003604c01008580020f60203038481c0207511070031b2034903030b955241080c0354084072111104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 663530458 1250 663529208 663529219
    0x9010e1009020108150d0b01090b180105030d030e030408070f030510060515030a1e02190e031f09020a06020f0601060512420f0301020c120a09180911 66
    0x1c1d4000d030f42e2020001c0d0303000e112014510285075840e0005000350192840040803c0903000005c6003014442d00302e0085c60000f0366078050307038a80700304684613441002d0040f582c0550003202d131102d040780302c1e030400340314400008103aa1515448501c03040c184403064100740d510340a4000c081040000400c00c62500c02e40c601e41c00c00400c0c1c180300000e02440c5901420084621011011a00300305d92136000258004090400040039505107030300304080e4000c6640401da200c40070500700704881c080c0900203081d0308000e0180c80950a0462081c40c8203451504811702c0581d580b41140050b02c41030019030207006547c00070002156421041450040140c101c981042400d00111503800c45014000750010301035041081c04000700c000c80f610100803c000c070300f012140d00c171041780800070641d603081c07184106071001d9000846420600d070a0740316560899a260b03008070041c00d01c0760300130b2001c1d08001c07240c1d10700010016034500c00c8802c948804503941e040c00e0350315605041005408400103403405002e544 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 663531708 1250 663530458 663530471
    0x314030f070201201b040507030506030c0105220609031511300c0423131503060c0e0a05011b0303050612031321170d0f020309010e10 59
    0xd08040e80101e001c0241409420b00c8160710002e0900360f001007420624045500780803900400984000807410000e00071071420012030084ca200b030203180d218000140040131180040300c011a4103902101080c04800d09074021480780405400d00c00000700280e5440602040c00c500340450942d00109440901928040340d064090080c602940c1c51040044406003c0f0810031020142c10140b4172204c010440c1c4140400218000b80400b074820303580c1c1c243c400101a5544900202501c1480220542c082a03540c0000300c1c0c9075040d040b01558101080c40400341d6a03481e62031405880325001150301180240d907203c070090420030b405a0050009103080130804d801840c0605080a899402404064459000030920780300c40302550210b02c261421281d84084000c001000c48600d4001c1802d210782000b141e15202c0c408400c0c00000c1a00306680b4019504880000040c03503022031004c4c2d00690311020100b00142040c0f0294ac03241214900105041240c07003011424902c060804119031444c2c0301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 663532958 1250 663531708 663531727
    0xf07032a030c14030706150b1c0e07050603070201050105010201051302180702120a090504050703023a09030e0a0b031509130501020406050d050105060a2a1407031403 73
    0x14500e00c4864042c10059040302440c100801107041d8030b5a10100c6200016483c000c000341540300040001032500d051800a40f1400c0080c0c441c400d5803004000140849030500391001d0540c041d402111780c3c6011a00201e80c4c800c04545c4c550002c442c1c0b0005070759104010417543d41c0a0040315401145103104076003011907980020140840494003044298615000035001030003080108072580d031003002151224480070005140010038000c00b4000d5007802c5c08201c6090090007030b11003c0c6121094084009000c0721600007441054440b8100c0c11811000030ba10340c401c03441940c007418020740c0c65120341100d440c00e201210072036902101c1220350820800000400315100060031750021503200240761203036029040c130b6141140024005510010b40003400ea900b04000307212450400d90140943e84e43c95081144ca07004294100e00410b007503001150b030702e80c00001403c400b500e401c1c41b9400742c00c0703443d00c45c00061450044042596030044070240244010800d921090000d514000d500e4a0442c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 663534208 1250 663532958 663533027
    0x5070302090f0f0310142a0318120c0d120b0a030b130c0b0421080d1808030106050307120e03030601050d0905161a041212020a081603030e030313030e0f04020f0703 72
    0x1c021120a520381d08604075509c1c010300a040b0884030390047c450700c40050b03005090300c89030400d07a2400410f03d4500106c03030798440c6015180906c40c0c01041141b49030302d11b480340140381400410701c0c1c2201041d081010009610401420041c284011920341c85a0400d82c194804c002d10b1f5507001d20054101000034006100c20040b107112960b64800850045215080700501c603044c500010311900001c400480c406500001641c461030310340d640d641d44400061440f004071a40420103e910340c00c2000090129400345c001029101004040060610f0701601c80b2418000f80700e80818401c52469000c1001ca8001c002c030800380c1c1c03013032040c00b880d091525149031408019400000d0079030300780c0d2068050303240c000d203e0500c3c12504000080e07070311000317071a40700c21110341b152040340468a01551100c0c0c1c00b0000081c1c9114182440c1ba4180030390301514207481e4044104180350b03006101294101454849001400443ca01c0c80300141d150304141c500500310b40402c4807943d1001c03442c511403540101c0310 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 663535458 1250 663534208 663534211
    0x141c1209170a031d010b030d08010e01090b0a050d060903021204050f0d060b1c02010233060a120b0f0a05060d0305030405010b0405040302030d05070302090f0f0310142a03 75
    0x10521050b500c1c40c0591040d400380118109502900a1840b5004a4554117400120070040e0840507911402103210041c1d4140d0000e00440000c071455100510501100fa0700c800c03184030000b0840500c0790b954170001104803200403422506a0384031007008027055010001100e6001001081ca420b180c20040440d0301001c076200d440d4420680e0314180c0007404150b9005c05a0307818080e010804154401e0003080306001208030032070051103011411114003140451080352038204035030960380070320540c03105e23440281c016007a40c0d849148c4030702c00191038048190300e1200901c41e42000c0840e00e00105841071301c8800902c4141d00b02d00b00001c0000c240e03208030302404000e40c10b040a030740301d41b9282031003401001032600250f003052505042c0414150000050500d50302c0420051045c1e59507003c044090340101407026402103400c0440181525004109810b45180a0201c1d440c202c00c03907a0010980b8030408241545000c600244540d000c4040783c8050003a005001e0000741402c241070b203500d030340320 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 663536708 1250 663535458 663535493
    0x130303060f05010e010c112707050708070321020c070608060f06071524080615011b15060b190915050c1903050c0c12060c07141c1209 59
    0x110b1440000c1000c407140a40301c07c40081e10342010303180c3d206005100c9980c007500081d41c0f1072083c000a002c05102e6001c403031340c0541c884141420316100b95170a40d400c2240c1c20301036880f8410342d4901c80008074644003600482418200514005240030f50280612001800d0075001d625620308030701c00303a01d642c0102c85089a00500306d00107120a000468018403e562291914400b10300090a501110a141e03c09445000090340c410352600c43d22000e4a07450b81d0b6145010030780c500c84031a44011240d4911900a008a004c042e4458803024564200c0c0c00300d40111450f41004038454110300c58101c070391000d05a03a03041c90303900ca60410b12103a0b041582025110100100010703041132030142880412075207906522840010a602d19000d85140c00107000c455641c403440c0709442d030758544001040c040c4101c0d20080c0600303032070b282024042540a000152841a40761003003410420040080d64201d505499828021840390107000702260f80c00c08107060000c0c200b201c0c4901285014a0201d110030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 663537958 1250 663536708 663536717
    0x200f0a0b0a0e060408030a0302030f0a05150603060409060207050a110114041a040302040903080105040b0a0f05150c060907030219080d180824070206010608190b09130303060f05010e01 81
    0xc070181c0001c03e24452a00311140c0d500001c00d081e01d003c0c0e019000f950040b8000c105000c1c2c146d58454840044960490702000109000c045000481c1040c000640e00700b2005400030400594589960050b80c0c4007035800c59403a031058410b5001d1003031010b015400c3c2482441c100c09505080e100072038650041c0d000f282c0340011248041a11210054126002903038098810700400c1c40030b09001c1c191a800f44911406982007070000ca0b00380ca4804070036400d880b0f0404c0c6c032441c06402c110610030043d40000f00010004410030403003600500c2040070512039004c210080c1415802c520600520303e0100d40410500c002c40c15050094200115825925510910b090016603d81810411746040c0d26485605540191749250f9000485004100980d00d91002d20744856100c802c01241d03134000910458000500345004103692018030449074990545201011a800d4007400000c0c0c0c020304159070141c0d040c0e00e0038000c4410150180507880040100180302850541781c040042c080c146014201c0c3d0402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 663539208 1250 663537958 663537977
    0xb340303111204060506030f0d050d0908041a211e060310060b0a1403040305040b030408070210030b0108071106010501120e0105040f0c0e100302040207050a200f0a0b0a 74
    0x400300c01c103440503221030046900150606080c035000418041d00c1a80c024003420f00015a04180041c0912415200e5601d00c0c1c42c280b4007540d010020519250100e500040400c00012443c8031008048024006040d41e25519440c1103000079408503100f0b44003a48918100030400b05041052055000c0104bd00540c41e081c0d4400c8002820070301d09801800b00285440e0000c01d80c00c5a1902038181d280c2c00b03485203a40d03080a203003003003102d0000300d6000f0001182084140001c0301e04030041c54100d4400e5803640e060001c25030000e1600c108402c9000700003503031103850203045d45c1d0040441d0341200d190300740140032041c5d00c1031950711114140501ca06204100e00d0b904184941d03039200c400401c501d0802003109041c18034001c054665030300402e07211100000d0000c103004840540c5c00e80161110103004141700e140d035082c40042c2d04002c00a403494020151100701103840c0e0701250110031686090826980c0600e001c004a554040b9042801101c1d44441030000240c00d104688841560381451080d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 663540458 1250 663539208 663539231
    0x40c060507031701080d0f020109230a081903060509090a030302091801150201110a020d030b0609030303190f020903060a0e12070b040c05040c0f23040b340303 70
    0x84585001c1e01c0e00c0b003006441d000061580011070140810034490747e84000100c01030408030701340e031750340368014000050300880c3e1001108112226a0403016200a81c0d440d440780c0d8884d0358003030b04041c8940c206030844250a2030b089602d8031448000d440203c0e81034242e402e040c0c180b150380e208032107801414558002000403d0fa91000c40d40c204426400158070115030b1184007600d07000301104036290142d030030200c4c603251200f0a0303803d0b580c0e090216030040c80306207080c1c0000c0340500080f000d5281c1120702000f403284191000d2004500c42e89050014a901c100500f1150049503000307108449414414450b01c0340310359000c00c02e20f4000441c81c81c082000c0356100388007030415910301010781d100440002c1500070414130b100520722980c001d0a40180a655070004d100a84850311200c0700020f4079040d10f000b1050085c3c1c4208581c003c1c10303003401d020003886103000755184c1c0f1980242c0ba50f520041100002c0c94840c0390343d0040e006411940c3d88010a0000304a40c4240c00004004c0c10305880b400304020307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 663541708 1250 663540458 663540467
    0xf0c040b0d0f1121040213020f091f05070201081e07020a0b0a0903050904021b060901020c160e0f07020a0b070504030201030e0c31090503090108010608040c06050703 73
    0x203841025151079407038030403241c000002d01d1001c2803080e440d814401c881031006041d4054640c001c210030004071076980d41102d55114100018030807a8400050403548014580910180100611802d451036584044004103e1504005500702401c82c3d4101c91045a031903001c030030740c0d6140fa42030905501a4450182c0002604200f2420708090f062402c01c0040342d5a000804140349401103580d00001d8030b13207204a9083e250115005000b1420400440f2203504090b03000317243c402001b0402000c0000c40340d61180c1041802e4514541a03034000c40c0000c00724600b800003103102c5140b8000030600c00e182800c0c42c15404002000305204001d92000210b019000380128203c00d03501c900038448906d407a03038000c3c01c1c50f00240420b13030020745080040700480c0000102078400d84001400700400720440b20580007c5240c080c3d010007a16256242002d6610f0780b8003c8001c807520610107103071680c03101c80c001400140140c2c0700108000302e4106010200c0c400302801010f4510740c0c44c1181e0b850386581415107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 663542958 1250 663541708 663541717
    0x30406030b03011e0506120c0a050f0105090d03020601080f01061401180909061a030f0a1415010306230709180207200f060705060a05061503090718060602060f0c 71
    0x44c0205080e82941a000903907016030320504003243c11081205802e0090f660b641c21000d00c1a8004500340f500740424502113144c03c1d140c00052404510349985600414000c00224a04a01581c40b0310018401c0c02c4050000700c0795001ea440003003203030901e00400740822000c40c0c0e40440c1440209007210410421290316080541600e031000e2000038001d151120040882800002c2000701583c002040c1d0701e008a800d00603100c04134000c28051400d503e840c1c62130310f044000c440032031007034400c0c0329140680300d64102d00035800341500241c2011140151100d82d00c040011001d60f242c5070702000902e64010740d5100a8602c2081144142c0400e508820300030b10904402a12510150b8810140807841c41150340c407a540a850703009594030000b041c011a03000c2d880c0000d00c00d401050000f000800c899104540c0464010040069403804904000305036106898181c65a00025030600800319840340001c1044420300d0304101c55490b2060003500c840c0301509140300c4250ba070340800c000c407103004140d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 663544208 1250 663542958 663542981
    0x6091b0d060222090f09110111101404050d030c0c0f0305090d050a0c05031204140f100203040801050f0f0a150305031912090209010e041a1e130302030406030b0301 72
    0x303404034200182c107800f9440b1348103491a00d8141803244c1c0156445000f02150310350700c17a03c82510036100300d00546100b191068200da8a100e050000c1075202d01e98000c000060074800c8a500490400781030070790501607034490400501d41400c4c6ca90207110360100080302d841c0e41000b00c42c000481d0500e4122410311800c0352082d032107404c0880c0d001c1030180104880d10f0750361051801c0c1100554a200b070544850400720b10303140002c0140320410400c1440000d05d070035440014100d00d098001800040c600c68000d19100b00142d00c0400c0a000c100c40c2441910303004810031a58a48a1401c541042412031000b080e6568440d1110a100f10790a5a505a10050740e80082600c1e11000c3d1004274088520044100c140000c448500c081c400001c0c40c414007040076009044562240c0c01c1031002911402c01420842c1d42c95800e078400008940c15800c000e0295290340300c403c001002420002c1500800900303003800100c800b045800000350004201c408032200703820081805c0c104000028010240540c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 663545458 1250 663544208 663544237
    0xa0c02090703060f0b04051305010b0a030e0106150306080d0306050603060126010b0d14011406030402030718150506090109030b070e030a05011b0f020309061608070c030506091b0d0602 81
    0x10643d1814500070307001f0b56500761011881c1c0d5006240b408240d4500384a00b01c01c1759401c00c00705205078400d800011204a2120010401542c2c0301d1180703039019010301d0140c001079030b02c0303500740301d20003040c008514500301c6850107000c11810030002410610024040741e05011854050310b40101000985800c082240c603860032296954507550700c91907002d0306010300c41c0c5251030480745001520859460596024440440400411a00b800134540c000f800076a4144100030703000900040032203051120110650010405503100114401b0109031038101521030318040c800442c0750f0368010122000c407904000f94600d2a1503601055541400c040181d40d01801124944801d0100540204402d50244110384c840009600307001c640b0003400171341c100c0047e081000f0042103494610042d040c00d402545802c01402c25696591080d580a000103c488103844030003001800028001240d1180b0031001030520100c4040c09120740800720000540b05010420308a404e001180c2c3c180e98040b0300d12b445 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 663546708 1250 663545458 663545489
    0x7030504030f0c0519050705090411040b0f0d12030f02070614090703021f02010b0d032102031506031306050f0906070c03080c0903210403020909030a0c0209070306 72
    0x1009840119025408a0100d5039400101440341100b0107882d90494058900740e4400c8880c80340222200314240c071184100c01c4007207015030301d0701c1129000303920814401c640e4503c180288016202e803541c90512502e504101001a52030b8290403240f426881008c5000644400c40305030000c000300303440c403c40d03e44080b450300d00308413890307001000d110481e00e5038820b140e541001c82c5581ba80140030003500250504001c0c3d2a110944091418051460002040b1407100d4000320b130340000030328416000280b07114403180c0e0000e0a10302c8448d038000c9004080d45585000b0700020381044d1440c850f40e0240030008001035080d41d0b01c0c15070f42c02d0340c0d601c411b05211500300b078a101c100d05403081d40d0151480c080c01d000305803103030702501360f956040e0ba140d11465a03a940e21a80048990020f198040d0140111060680171002403000d0007400e29042030b09039203e5040d40140076000000800348180740d4003c0009001d940d8005451443c3c80394101c0d2240130030b90301c200c022009011590b00c8500860b082a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 663547958 1250 663546708 663546721
    0x121e090f09180c1e080309010c080703170c030a1407051c021b0105040b0906060d020f010c022e0207050604030813080a21170c0a020f071806080d050301090203100302040203 76
    0x7480c01036500c130801c001e0180c843c0c44000341600d030321034503a120380440c22009610000802d03620180c42c40e03600030f05180000300c03c02039909e440014112202c1048100020401001c11034500c0741665040024103074180390320308050050a40d214092070000420044543e0303182280071a0112020b00c040c4a000181601c40c40c0440ba002c2d00d82a01c0480718428221700081610f1000102c440c4503890040440045100c07075002d0040103c548a012410072280d5502c89001d61680903906000c01c20203a044141a03411001c040d4882c00b41c00901c034211740000038108816940d078020b4500356030b00701800b01e64406c0341018299500c00d42c0d6021506a00514400100b402003081000c000b5030906c2c826010b142207110401c4840304a04441c041d80c3e190498081a5000203080183c540000c2c140111031620400702c0c4078900e080c0700d580c043c40d500360050003100c07000303c00f0b40203444c02061440010401c41d025400050128001400740b0300c0c0c041d602000250250704041d441c00300035500600215541e05000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 663549208 1250 663547958 663547979
    0x1a18101e05031903050301090213031b141005120907080f0a02130b18040201021014060a0603020712080403140301080604030806030706021009020607121e090f09180c 73
    0x1032160a02c80e00030340100350742c06040402010411985942c2c0c00d0b03c1c40c4c0c00d01c6110780c000d400c2400311003050910000007000007001d40c030a912011000c50f03c1c0080d00313858130314003100717400804004034003a40510f4100030455400c00141c0f4903070039510b00d10950a41e107000b132907490708100e540030441d54812500600404500407130f40c611072030300a850f141340092a02400714284c961900c1a96000b0320f4190312004c40c00e800403030180d0014414415241004000b00c03400b015504040040b40e5103061138800e2020b44e140c0700381c02400400301400d007503040007565260f4968200100c42800140201c2030b001604040c421980494072101c445a45900c958403481140c2d034620301141d08401180100300415106d10b000100d0008690040e40140800301944034080e024041420049030420800d003d040005841500360000c07604181d51003501b5802c42115148044400110003400d00480c00004e2145005c117007070701019549603074000300d03422000241c501d40c028600800038000004080d004120014007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 663550458 1250 663549208 663549269
    0xb04061b0f0905010e010e0111150a060e090d090509070212030a0506030d020c0306060d020117010603020a081e070f1806091805010e010302220c020604061a1810 71
    0x1039030380d10540d60f2640c0064a00d4006001703100d0220b11150b011044540c4620303c0404641d4000094075041c7d01041401c82d0507010540b000f0b000e8544401c0b082c0305440a0300303c1140d1240544000380300600030114094440b1600740901d0f8080c200c2d420000d40070600801c100c440c1c0c03c020f84500b070394919041101500501e4181c8060303110340143d5004009181c40050307001741e6818001c0150031580c45001c10003d500740400400c905110729500700c0c1444051200305075000f170902c3d450160f0745c1c1481ca82c000700440401040451345c640d404400c00002884007030b0b55948140789040142c51140d0031141622200707440e4a00350500d10040801007003a6a0103a080c9003220350004140b00c00e01c040d9020042600e13001d0040c1d1105144d510300400261800b56901030343c1056080e00c0c0500c029070071452400361108400c881e00540e000c0402d02013049100e1080348062040d40140da2082c1c4041c3c5e0000707001e0b069858140c02e4003c500d80c08101141c41d4100428002c100ba4141103802c00103c070310395001e090300c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 663551708 1250 663550458 663550487
    0x170c0303090a0c0e06011e030605060f030103020405130803060d0f0f23150a020d020708041d01090c021b0621042d03050d09020d032111070b04061b 65
    0x280c04400241022401c028600517401615100c0300c0c3c4e41303041d22184148607101181800c244c0c43c2c0714001502d4036407800420101109820b03940c0c0e29811401840103550300030301013569981812240c0408100881c00390307038102408035a0740041a41604240800341c0200601604008801204004002450000301070050003a03448416240351400c600d9150140803400314000c881d0080058090180d5078000c0c10111703030094005040c0030040d1104801c1d6040350300288000f207400000c0e000d1418101400c640108038549050010780c58980d002501c0392004a640032141024002e2030700c03107170740e41015a00003c1b0700c0006084d0402c420b401c5c070b182254040d9001d0703a5103503010002c450010040148260054005403d00c1980c210a03681120603911246c5000c0d00a80c0e03c1d0030b81c1d07005903500e03040b200e6041d002c0d544150020b042c21980c043c81d4601c3d8800c50960328600009060358444040a071003003c0d4000368461a2a5503c0c00c0c440f010341151001840320ba2881002400101c2c2c111030320349224030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 663552958 1250 663551708 663551723
    0x90c0305060102120909090703080c0d1e12050a14071713030e21030a05041d070e060702060702060c0f0d2a03030e100c020c0108040b04170c0303090a 66
    0x807698001a03844a0080402c084080405c100740505418900e5103240c10140316001c03551001d50702d8403510170300d8202110028007a040203051322a0300c1c0d032081c04581038019501e020a81d0101b0100301074130701c1c500491075418082e142c1000a44108903039000140e140c07603114407018140b030700700002000c2402d40d038030b0518000d01001c04116007844218003407401a5041d228510100c1c107000400c405484110001c200b80d03184d4100c03403c56541e0509c003929031913210b6203a054985040c03005016200701c41061038012942c0c04c80400254582c0908404580e803000c1d039001d5034901050000c22428820000003030341002001518504030310740052074400800307844c03040c0e61400b80203010440e1103e000042d0742c041c800c0342c2e994800c601e5250a802c03406044c420704001420b0420380a1090403e1408501d003a44c03103540b0071070140869010300c14180122403d00e451075040c5095926081410006000500003500303045080030b40c1c54823401141d07600c68842c41201d4803481c180030856924100c0f14421240359 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 663554208 1250 663552958 663552961
    0x102070f260c030d090f051009020a08010203100504020f21043806061902070e07090e01170f030f04031b230a0b0406081608070c110a030c090c0305 65
    0x101e4041e40c0da180441006145000703003031005180902841c5200740c41d0a01c80b80c07504400a4010000c81442024080c0c0c04142602240100b080d00c2031940c0c40455540d004100700041d514025061005440b412140182c982d004204218507502450f4103031078181000311403102c0704800072a0014803680c8610540c0c07014503403511b1640010403110540300d291442600c007210301b0300c0b070411550390700c143c0c06021241424001c0120700f480702c03200720090001d80c02000c0b05114501c0c20b06d101d41d601c10b500d41001102280b41c90148038140700148a111741c0c2c04042c43c0da5003140403060004502c0e002c41c0c48200c035100e40148078184820303800751000319040c0680469400007421540301c1c0c18210b9101030307440c0c0100b94414080184064414920952080c140400410010402030240002d04000c2e981c003040c0d0300d860024000e00003815401e0f03005000da203108009120381d10512115605a101d16032207a0f101c1c9400124144540c1d070303000240590706020303000c66108080e9204030464585503400344400e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 663555458 1250 663554208 663554273
    0x180b0301090c0e04060b090a05061509030c060d091b180c0512040c0807081b030a0209191b111006030c09110f030403030204030507350102070f 63
    0x201e64880380e0041840c0c0c00c4102c20824035202030342c010341c403d00404012421104e900000780721a10200d9080c40c005075288240012800c0600e2060310070031003110b1841c0382080c4030001a941e480c5c0605420b00c98800002d007550041c2d441d4000003189039020b455040006200a28440c49103143e009500fc007404240e0000c03e40941c0d80640108500261265442c0a2451a001e2030240e4014011b03a400e9100c02d40005075000d0400000004000103405011280c60400c20307004040d82c8480110300ca5804000c2e5180541d0b18105000e401c40414612152500d002058000c0500002030104410851081c42d030b00019070400c07040200301100300c040e1403200040c100d0480c1110a20b002c041d00d01c01c050300082c840f42000b0380c004001d06c1d0000e40c2c0700e410140030101d00840c1354000c9504a000a070041020001c00c103007040780b08050140100c48111624840a02200e041101000c10481035a5030341d100d40e8000b0290304071004541c000c44200300140013070078500e11004216200b41c04204c10042c2c3d4428 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 663556708 1250 663555458 663555461
    0x708061f0b03070f0c050d2313120218011e06030c0c02040b01020a060f140f014e050d050a120902180f190e0307240204180b0301 57
    0x151054407030300d581181c5941c07104650750143d41005406112200c420140440d03000c02100e400c0b4071071a9201d02102c0e1948a088084a800b40c8400080b04810f1000c844100f01028020007078030301e8080d9030090f00c040750002a00080c1004c05850f03e14400000110b0345191102034411607454074604540c007195204402c42c2141c60303282c204000941200000030051509411080e028401481190300c203140f01d8980c00100e900082c1c1001c03031039030340d900880010b40c8821941580701d0841074884c851507140180182c69002481e090803690300d076588242500c04107c001680c1c40a2409151542442c036142844d000c98090f0042903d40d4401c0a00680842e0b01c14001c441e6000001d030b445c07110034800d0002c0a0003420900102305c7c0d100114078450000c030030800004a11410110001e20464201401502400303c40340003540c012604041500040060005c21520000e5001c0c1820b041c68017110440a030640c0005840c90100b400010001b40824141a943c011101801d20401610605404250 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 663557958 1250 663556708 663556771
    0x170705010905010c0e1819021c0606140307030e03040e07020a03110d020a03080a0f02070c140a1208211501110f0d0f140f030a0b0f0f040b030a0203070806 68
    0x10360100d80d01000282d2142150f421a0300891f15020b04400c01001c04040800e907000000082d411086051030503910404502850300106110308020b42c050a440d0300500d080e1000030203034002d0603101c1d10143d198100400071280200191400d1041030b003410383c0001d450301c484c100186c0c0011104003c81820410219091081c41465002490441281d680c04d452005004208440c411358420116001d81c0c0c0781d000500722684a0381807240c00340e0800e000c00c100f0100300d41c1200c0c000c0758641c0044c000d100c1343c055804286c607041b000498036607000d0354000c02201c55003568461482e42442c144541400403101c41c0324408000d07254000100a0445c0c09561541100c0d60b4084540c8084045203003117005610f00311240b0301c02d03d0100c46244413100300403143da00c460301003000e040c8008100424141c1b1449400311025046424044d1105007400207048200d030203078580d00c0b0360381c0d460303c20620390350402161151541c003600b9610003a50741c1506607140c01046400088800191f401d412808220340b5420 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 663559208 1250 663557958 663557987
    0x30504051801050f460b0a02070506070618060e0712120c051212010315050405120d48020a0303180203030325050405030c0904170705010905010c 64
    0x4110403c6800800c40d0580c25400668018940c0010b4040003640309064104c103994115003030801007039454400045085c85520011030180c040c08503104050340490b00c80c04580c0205c03112900c0d0391030703820040c0085c1a00305400e58202e011603c88402c00c44160840744814002e0010b071142d0b1651240c09805000c8520b80081c90144503c8014040714000c0c00d000c48400d0040003100c8440614924415881d84498200516041d40c100100200000103200c0d04955154507030500c09810960baa055076005400d12140c98140d0100e20003941d89515030225180c44040e10b00c0c200c98a000b0b2610000383d01c10f19074006a494126403194a581c041c2c44d8108504a020368000e0104220548045004183e02d036000850314128040100142e035041000e18010aa25410040181c481030100c010b900380300c0400c40103101c42403008201d036941c0850140e00c00042a40d40c030007141d50b02d242510900c4000c0f1485940c4c04404103022061040550105e000c2c0e41c03141c0002c1040d1000c0800548406101c4101c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 663560458 1250 663559208 663559219
    0x304170313030e06120f1b0418051006080f071b0c14090708012306030c03060102070501020d170c0c0a0803010602100515100e03010e0a1110021c0903020303030403050405180105 78
    0x6c10300d2036a54500c083da00501d102da402552008184580f1051390142d444078807039160400007124006010302c01e42c1c0e00040300100074883c003454040e0140c600c0400515144000900c0c8000601c911b01489402c144442ca515803074440c81444e1030f04420b034550f14040c40b61401c0b8240401801420000b10355030056201d615060400c0e840e03e031000d01d401c0c0c90502440c54000b03851003411220384030000a1405003043c030b2115600c0b480d11400092625032142d106604547c0121407440600b9003000c5104480c171403004020780c0e503540c0da654800c078038071a400c0002d21600c143c03000e50007480f00c0c0c3d0000d5816503151354290340c101c8203144807540541b0303800e5a841c0e1144140c800031001030729001025800401300c60034407001400c0c4001c0024212014147c540740240c1247c4072640400039040021000950200c85400b040c001c035002c02541d854480c00810317a20021403400e2800d0900800203900150303070041c21aa503d06d003900e802032850b0000d00c03c0a00807d01380e41041042046004428180c1d8805000f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 663561708 1250 663560458 663560461
    0x10e0a020d0c030206070602070501050603210901030608070801060f06080709230d200418140336011d0f19030c0302030f030c120304170313030e0612 66
    0x70000d0089901404840342025100c1c00030050321381d00041c0c0481400343c00010303206c01807401d005003034481c0144028429000703240c20200840c910a82c1c04950303070300410f40d81e88611240c00140e00511143e0041540c0b0b1152520000300d05205400500c10b403440211b001d0b002680d00d110681e0112011340d05640810f94500701440401e0910080031941c901640e101c1403055070300400319015400e5154107440301080d1604401f1480c40313401038001c580c074003580c0821441c4c05000308031120411410f00101040c002680701c000f000c400f0400c0d0703459000385045140f040b84000b045020300d28146d00d5070b200407400382850003900b58020b24500c0500301d00007a24501d51080b40702042100c035103810704240c1c85407a620349041e52000000341000079600c1031146458541c1507004040ca48810704c481c030300c8168010406804070342408202d070307000481814000e07500c0e0707112850400004144a0b950808000c40442080002c100444984d00401c0c001c1d00ea002444080000380030b014454240da07a1802c40c1c480c2c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 663562958 1250 663561708 663561713
    0xc050606062503170c181002120d0b0901050a0509190e0d0518120712050129011e20010e06010f030b0603010b090a09020301061a040303020708010e0a 66
    0x6004014010302c40c8200c40050b001041942c1c80801c240d03005800082d0307007401c1c10382c413444c901c1c000d0741c0c00c00f58050304141071800b40e40126000314008045c3c0340c001c90740c002048003207500801c9400d000001c0f000b0000d8483c209203203100700519400c034400384226040c000000e030a0410000d40c0301501e40260080f10744c2e980340703103402000c40604580007507195641d50240c04036a1041c4a40300d07140baa00d80c0e44607621840c40541c0d000750500321410920940c440d0740109280307500002e15038125000c0b002c155070060f00c40e040c11342c01003495803010450120f04ac2c0e011032031840c045001101c552426281c00d0040b40841840300390700d26092980402059800e03c400c1200b241d02c400042c52030300c0481c00401c451040200c82800d00000b80d00a1041450b03181c02801003000c03a440e01c541c045010f034001c21803200704070700180781940058806451607681b00c44600a42d00d083d00040007900000c00d040ca5511a00700e91034035540d020340f0040e40180109000030440e0501030140c508440c80110003880210540e8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 663564208 1250 663562958 663562969
    0xb0a0507020a0219090e0303131515031401140702030a14190e030f01020a0509012607080105013b130e030306010f0806090f0a020903010603050105060307060c050606 73
    0xe0110420752040724102401a0798280c4e141400302c0401c000300d41c0c020f2400c0300220585401d82a4515160024400c0000c403900c0392061a4106410420068108078500b407010004c0000300800e6050362900e181c04000c2c0b00400101e40b0000f16000c00070411034821191b419051501a00c2c0540140c100b00400c1003440c4c86590701409046d0402e44091a0110301c045c0507220f01c4c44d040000c008510f08072042071840c0741c01e206040c030039550000203518191803040b0081180c4030b0030344524180b190720003100d8850042c040303032910b4601440d6550200e5040c49400a06442424403500d400034580c080300424401c3c2c140315101d00c030007246210200712848100264034042015200e42e4016529100e45c04000069010700980110200c003d1942c80c10f1110005000140e2504900180520300c4180881e50321032100003a03012100741e084a00503221844440702901c65211071b6503240d820003901005014040d8041c1d4020342c011001c83d400d50f0f64640c42603801c40c00071000035046800603400202c0e01c0c00c3c132 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 663565458 1250 663564208 663564211
    0x916051207050402160c080a030c0314160308060418080301090f0209090406090302061008060f040c0f0303031505100507120207090507110610050d020103020903031e0d060e040b0a05 80
    0x2031050391030064848010804a030020000d4100c181d00702d00081041c01070100001000e0305805d0042e225102d02c0c0d89028003c61041c060040c20000020007a50800c07002000703440848a4000f0351a001d940e1a04005000038010b5810a1041d032600c0c0c0040808495a4109030400da88080302d1401c5a2174500300500070140c011012481d59002c1252800d56038541410903c164428600000c100c2c0190138000e10b03282e0004d0502c0000c2c00188024040c0040008400d54002c160101d62182036440e440c0a1500c0081d643c46160b055208050109c101501034004460f02e43c41c0d40b040740c034201c1e504c100b00003191074142c071204042241002004046448110707410002c0000e0f00440710555958400e0710100e0304101e41c01400504000c1c88c840340140140101034001080250708120f050800d0001199002a40130080c14150300040400c2e1036141030003610202c1d01c1c229942c02e0481e104d600211704a0340807441405219141c500081403000240d4449030045400030345124081d40c0b41313820303c0000c00c170 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 663566708 1250 663565458 663565489
    0x80712080c01090b091c050307080112150c020c120c09130618300e0630010302010f170604050901020d050106020f01060503073602070501090b091605 66
    0x1207031035440f0b010500b0aa5898082e8500d80000d107031401d80d42c8058050207410303035808801c0000400c103001d002030340f00814a0544088120200c20100145455040100454050314416080104030030b4196002f241003d02c8500c103880e014881e1141d00112030300c5040700756a0a078000402000300e0100182030308031040317180c440c480006a021400305400300d50811508111072880d2090142c1c824120a04028000310f076448600c101c500102c1c40700508035250450f42c1900501000c9401003818047c080001004646501c11890a0240c0d100c0444500400d0006034041303080c2544569056100c2c400140880000e418940c142e80c0711071082002800d005008201a903409100d55060080c0301c0c82001d000b40500c0d0028690f50400c10001803d40c1c10650120344a03400400003007004034a050046d1049540030131042c040f00c00c25000308044000104c0c46004442d1020031120108001544102003550080b0031088466942c0c81c070556561910441e0010000060002003169051540300100041d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 663567958 1250 663566708 663566711
    0x3080a02210403060605191406070b090a0b100b030703090201050c1c080105060a0206040204180f1113061203030f06051c0c0504090314030a09140f07080712080c01 72
    0x903001c09040800e4004020000c082600140400410803c1c0c490354004140c2984d040003500310341c08100c62403405a200340328044c41d2039185411140c1c0e030942219505644000081541e040c00951030341c0d11000701030200c1340040c1042c0800c07002c2c01101c003410202e4030700b0704e5000d15541d06e4100c210094071094404905000c1c0611002070039400c10b002c42c081d14000301d1102c0340c0740700341c2490081c52031a06a120394002c0104001500d601c941c0800d0040c1e1094040d2004524204075001071003200649130009004403821000d08820000c91070410440d410044071070312503021228070f101044503224819000917400911290740068000e80000442c0074130f241c400503249a03100702003407990242240d100042981c03040120100114034044402504058404008010740e65401800d40c200000650440c10030200001d10545a0750b0044028107501210101c401d0900c00c0c01c2e9a03945e44151988080750080d1703900801c028030001120030445502d210300301c03a1003109881d111139540c40031100ba0482d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 663569208 1250 663567958 663567973
    0xb030c0406030b06090c040503071406040819030e09070c0b04030207030b070201023415060315020d050a140a020d0608030a170a05040c0302041a03120c0f031303080a02 74
    0x2036a5521401008501a40c1e98010a1030804108540c1000080c0700d08585041407005221a4400040a0082d43c1c105440c5c00000075003000090f4460156500400e0240b044c0100c0e100c0c107090068004890b02c1c40b82d200d201080c00b400c8208801c0c10000c44019000681100b41e807001301d503c842d07001303805c44c2c00307801a140d040307440740c407210140c5008a40c03410150b90009581d0010b07840e03440655032265200960742491103542002e001c003016000002808802e0108540b03010305060b039100000642d03020422044e4461612440d00281d006210921011803130200003411444550060b02ca500b00d40d403085408036070f038800d03160340250051407110b44525602c07000030880460800061201c5880b50311464401c009841080420700780040040c4049810002030000061122080a050b40e41c100c5004c6150201150052092002860001d6051051900c1002010004070007458010303105800d841c10307030000c01c8856941c0e1013840742c2814281050141080401d6409000e0040088184141c2c0e185 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 663570458 1250 663569208 663569233
    0x5031f1d0715080c09040b01051b070e06062b02070c0f0503060c040b0a0f0e10030906050105010c02130b0a030c030615060825030605040e03130b0f0d0b03 68
    0x10051000e428900c0ca901890041c4018084104111685555881c1885861408504104850258003e07182c000d0b6103031200194181c0c000c20170307206481c20800a4441940c090070300c45982d05841e2048008003d50200441c20500307090080310306100100c441c0c60720040c812960030380c1c12340c175981c40d0a003407a50901c80000003610300380c101001010b00d0780200340c940d4200f800701402c12034040d0114908000400040024050140581c3e4040b00130381440c010100550000741c1d043c0d08004d0700c2035031090001d4249800c240d01a400b840c011801003000308216030700d40e001590103ca07040c60180d8000e113040c000403100c4095030040181848043c165489496032a0303a0510311044d50b41040741c60544a072040b05d00e10160002000041c04c007460714015a041c00307440f0628001800d000400c60340309001114a045009420a00040c44050000c01c191200c034181d2984070f802c0310300301030591007001400180d03640b80003050702d410b140c100b0f9101d4a862800020b51005040c1c4020031a054042e143d41c4490 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 663571708 1250 663570458 663570491
    0x1320d060e0c25020a1214100603120c020301061a130e07020a110411030f191815060519030302010e01020a051630030b10140c01060306020f19050405031f 68
    0x603144280d0303c0c903000c0f694a0000b44d0408001051184235a0318240301000800c05880e00004456081c0c00c01d00c4540388030b8001310303014021a4004c3c4034a001c05403080c2d500844a44001c04080071014000c80d081c9440f603418100c0000709590140040c0d02020704a03000c1610360132011900800184001380c10406044991203031f400c00c9680388502a040750402440d4640301035480303002c0c03460b540308114030075481d00381413050722001e500079006001040b107440790500160700010151030018031254545001641081c6a0b41590008500550074405522180e10050094031060800758442c0c9003043d00c210240c0d50b200f403080030280c070800070749040c00c3c0780300000310b6400808108415070314400e946402006015104c543d06071500076843c0b8905400e81e641c3c80503107900595145510180d84503803400c0502d01401d01b580018160b47c0c0f00040d8800713050010170040102c039900c43c4c4101d402500c004005d079400d008034400c054154000c100040305a020b40d001500c000349042c0b00000d03414002c00305828 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 663572958 1250 663571708 663571739
    0x2070905091e06130602030c07020904080306010f0302040803030703020c0a0b0703020d05060f01020c0907141309060b2104150f06051e01320d060e0c25020a 69
    0x700d00b81c00c9980b80440180450a04030300d41040c0b980140b1907801c20251000007070301030541c0030304a19400b0002c56161071102d4212500160002c11402450030203081c9422a9030054400c50f020815441c00300000714045e000307950894100801860450740e0325070b8150080c1d4451082032105020b200d04080005024941d018000e401541d40142c84000d140d10030011030340b0291400c3d1068001c1505002c45a90000342d800111406a84141d9203440d14203040c0c8680f04100303001021590081103030040d50031031040d58011101c3c811024015a03585034042e90461046454404000ca00440b150440740c4880c59400e4000c4d10900b1008800005410341c0400c40310820340100740b0b181c40f00c0041103e864034543d543c0041d6142c80000c0245100c080010b0800c0580c101a40700e118003651341c10944e04024540e001d090b00012110039601c19000c018a0700130503c80c014000303180784100110b54617840042c1955101b01d03490050f900400c060101100c0d00981c07043c8120f070300c54400500425034580a0000300b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 663574208 1250 663572958 663572971
    0x9140102071707020d2a0306050405070e010e010b07080417010e060a060513090602090918070608160810170109050c091003200402131410140a02070905 67
    0x40e00c584441c82c1010502c2c406030020700210000f8052000560b60b10f070102039159512801046450994111040d03480d440c007810500003070303881c00c400420710842d1b8120b148207520450a0b12040d980740e6101c0008a48203005a0861f9040340300140304d40010a802010750030701a03d205820281c1c0c8604401c1008911003001038540d44440640f5802c3e2001c1000642107080c0380810f00481c0e060802103542203410307503a000041500c40c0003800920a05904540000001030451411850300c4025018002c058900040c031305d214a1100107035203485928144d010304445100b183c01000321a8040b2009080035000c01d02010305400c0025078996084e1540005902e040c00100701180700b81482030500c00b00d106418002e0006404002141c000c04900c0c1090ba903000004040441c040d16041c0c001640c41246150481c3c40001c41b00c0c40e6020b01449102241c2d2031490644207600c5038428820a2180780d15050301190050000175100b190620241030552821f2044810f6036aa41041609484054549 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 663575458 1250 663574208 663574211
    0x1603050c0c4b060703091a12090c010c03110f07030605010801060b041401030c180803070b13030e0f1201060905060a050a03030509091e070f020c0117060d0501091401 73
    0x600b50b282102554a0700501030202e1282c5040e00494012800401a01c1ca41c841c0000203010b0080600440c0142c0c050200c04045246d6038291441191007070b8041140e009007404220002004490300286040304004180d41d40250b84645070744c25036038040c080440303030180e00901e1b8240b24502d01c100601c1d001035008000c007007425450104081d0848403070703420140340ea0900704014821003101841070004401b00b8078000408030504081104c0e0802c980c840c40c0410800f604e0001480301d000005048402e0042e01803002c1a160608150069603400700010081800e0100c6200e00e0314109100700c203e6a8040c001901d004c004e0080c050031a0461380101460a5a440c10300c01e160900c210490040c100c02c1d50781120450864502038654012801121320aa00440010b003c10304d10415060f806205e41040802c541040f510140000c032440d03214000611501a070130501d50310412200000c041107100c140829200c80c0e00784907a002c002030040d5401d648614003180010b0002903801d0128001400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 663576708 1250 663575458 663575509
    0x405041805010504200a0f2c0705090a06051c0504060e0a0f0c0b070507090b0a05270c042702091f11010207231e011409031603050c0c 59
    0x14010142d842517190140100e00f8160240b00d90000e020406042c2d40310342d0050720416001210b180f00241444103034200744081002070094154200c40582000c050454520501036190003084426024005148400c00200000307007424041907408943c0107400303900041100b181c2d440c002032414240007411201d011142041c0d40900c00759a40601c00741c02e0101c40d035494400940c0310f0642d500c0f0540580b1118955407040164280c6e1844800c400400c80070f808500c0c00b00d043c50b014400e021824140d00e8500145c4400107040d13480e9001150181d42c651991808a1100c012010742d1142c4034074441c2c0c00d007640c200b20b6400690389031103000140c00540700320304d03580c11000000101640d00d0281c00c4411a80140240030002c0c26801c9695181d0700c0200481d900a507690503000d26155407002d8501c00c0803e01c1070103030850517041d0481358030400e01440524150b110a000301343d680c41403080d2409603021054501c00043e12034030003060807411b80811168400d03840070000ea02c6d0b00d50b0b02da107032022014400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 663577958 1250 663576708 663576743
    0x1003020d031e110f070e0402060c0715080a0506420403060204030312050c0a080606131e0b07050c060f040801020a0f08180d050a02150108010525050405041805010504 73
    0x102c00701c04c4014540c05003e1041c03400d20a040c5031400544028840d04c0b010943d0001c03180208128001816500313006c00c40011180300c05448400c3c2600c5000180d410240061420f05000c0d0181075a510000c140c1c10b15400c0016440d4003200e41c0f80c84001003802a00e000601580410002d000a10b018100051356545149030241c403e00a82203141c040905010400540d41d02c06001c0d581c500c0e40c1400c7c480e4440d59880b000428911900342c0303106045200c8000400c40001c0c0035400028519500b4040c404031362036581000b4107014007078000300f0355481921b0082c043c4c1001c2010301001c00c40c0c032840c03500300340e103038102c039426038000580d1000041c05030000c6e014081c3d404407025070000c0c0900720510740c20048a0701187c450b18214111800c1c000d00090703643e00c15208020686143e00784502a10082d40c40c1c9030000d003e0403003650048507000700d20154130110403854002e4020a2420b407141e07031030b00780b50405100c00b6080980080c524101600c01d42c0010076420300445200701d100304d00850310948400d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 663579208 1250 663577958 663577963
    0x20a051303150c090b071502040b03130210020328020304030c0e071211160206190e0906120d110a061a090903090109050103110c01090c0603050705031003020d031e11 73
    0x1441801c120131034a0400010512808541c03c540c1c1040da420050811121514043d105a41c001891843e0000810885000705c0c1814658603200301c2c1c0c0e00b0104007010800702e0380d0b4000e01040d800c0c1441c0752440d80f0a43c207028068859038804500640c2d0a1981d281c861048040282d404010340c41426800c10100b2907014984c40c00d1600e00b040d04020b00044000000b5081c09044c02c4014174841c0302c0c0d000c8040d59200805e41d021a043d40c0c02d03484c01d95003104d000038081e00c40c681225006c0c0900c207000c100c1c40e140480c0210317440f40199004050300d1480d59030896004403481d548040c0c0b4098940c2d81004150380740162030702821001047c05c1002070010a00007803000080c60462550010302c8100070a0380d01910f110221002442c3c041810840c0c0128595913101c2c00b5000d455540c42c0100401c2080551b003540c02c100d46994808122590b2190001e5450340710407600003000b020210002c0c030040c50502c204051b160b01a2801075003010916151440003140000110302160007501940c8800004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 663580458 1250 663579208 663579221
    0x9040f121106160516150e0a0309050904030e100c21020d020f120a350a14040f080d1508010e010603021e03030d05040f11010314010603020a05130315 66
    0x140343d4404000f90022500811501a20807145062210110020709000700c254941d0102c1101000c104410143c01800c9503036182d00380c5085010030300e5008001040e00e48401d50070b00c285c0c0c2503115074555850000401554100011510703061104911044010403910482840c00800301394401103401c520510180c60302c1100608041103501c05d503401d00d42c41a010402c0c14140141004042d200e018602c000d844004408120703901040e120040c1c802c0049079161048818038001c0041000c0fa1034885280c4103407100300e10b0205030034202501040c0010680780c80007035000d01406959040601c200582d1003525060070015084414108033071000010a00c24602c4400c40d40d002003019034555804241d01c12403960554603003180b030302041000e9403400d008840c02c104021a081016151529241a0a04810805807400c6280704070150b0954041c4c4940c400b2001d80d1079084403160f207410b4046000c0c3d40501c00c81020414203101a0000140c6841640003451003807071311029040030010800c044401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 663581708 1250 663580458 663580471
    0xa030c1e0c06021606090b0403031103150d1703070206100504060602070510090b12010e0a0605010203071b0807030c0320060a0309020109031a16081509040f121106 72
    0x904411124400d410441c0752518035885080961543c806160140c14040300500103800c4508000382d070070400c0444004c40b4421032190f20b040041c00240343d0740003180e01088a6500000350030f404081c004d4a8800c8100603d80c1c415250325100070803002c800110703504242c40d00320140e1f001c90700b8080400600860040030b408190380801500340381203c000d60b204510321074540228281a42054100d00c0b50002c8805009070a0b4026598001408004680c41003407140e0300c4e05402000119801201e980680d204a0300c0c168011410644141c1790310842d400c10385030550100111070400202944248007000c01580a1803590341440c0c03450903c2c3c0d00b0040002210180008003600a20f540c0d0740d0031095903510b580c986000900003aa0b0710060f81c050005d50005044440030b40e04131000f90b40401006841050782003200810b45098074405e03a5003020a4511a01c0000c50510404880c00c20710301156016010364091265802180c841543c034040d85042030303001500719044031a00d50004c00581d1381004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 663582958 1250 663581708 663581747
    0x50d0501090512360909030a0e01020c0d080307091e060813050a0f0c081219090b27090f07080915040303090303021902010b040f02030f2701020a030c 66
    0x284100011000c1d580c0c4442221030508050a00c08200c0c4103030300014a036020345245c10600300000341c80d589030019080300d00002d02542081c4019403010400000081001d4517101e8042015540d04960785c10060040080007800f15001036204c2d80d40b28001c041000d224030b420040360802600401d8081e0082c002e000c003100c20b442480000714005480b02031590884a88603441c100c900d0030245014055100d140c451240f5081000b540c8000c0000b032107080c189500034010b2115411058401641503c210806a0000d001c04a41c004044042c5240d510036580769454519000e40007488104069829945414007803040246168011150540200402c0010001303080c840c550030381c0301e02e0002c0000b000c00d070700c52005004042c002e1701501c01a01c00503c0441c00e415010300003c0c0200109140144581c0c280710300c0010041c80380c401c490081410500510250340e50403004400507030b000000c0d5810102c200e400c211500020301c003401401e00d05540216507806d000c1001012607041200090640 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 663584208 1250 663582958 663582967
    0xc12130b040807030209040212030403051c030c170a02040302060d0c110303040c060f090302120a06290f18040b0609060603070219021f09150e010219020a050d0501090512 75
    0x50300010844104c036070480d4101c001d0342c1d9070320200b022a0020312000643d4440420040108100890780148564555607030f042c01d610300d03241c1101a60840d144407030106800810b540034500001721031030b61000c4552405481c01d50340341e01061032a406550300503055030b40d0300403501c00c19501100c90320007040410015425401d06450701102e000e164414032041c40b400e840c000c1140ca0242e03198500641d0010404402c519040522035103074140c20500f110a646440403401000d840d081d180d0800d00d42d4203001d00010138010041c000101826041035a019980c28800c41d05408140f03040d512803481111800b800e810304006101008070050a041d200310000d10800811a90002e01c41c450018981080c07030a800050000c51103903000300c00309261085089041010407600013542c80211442070300b101a07030f914024030466020314010140e40c01a00500080780c00c64032003469980201d80000c000150260b43c4800040b002c400f00b0108485594442c07001c502440000c0c042003c1c00100c03544960f282 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 663585458 1250 663584208 663584219
    0x3070510140306040f020412020306090f15060a211a0c0d2003130b090a0320030f07030c02120c090105121c020a050607090b0f0f0c12130b04 62
    0x440d14280752208007080440040c0c615a40c9410800c040704072882c00710350b9151902d52118000d440c1c41d0f020f0b8028412803010134460400000e1302d002d0140114043c110400741c0c3c200303c081552029005035800280207801081203a2006229100304034081c201400c9020140340000f481d00e00c0903a40051a1581c104100001172841704651981201b10800200d50043e0880f96420503804030302507012800c0882086542c02d80d0084028503140601c000ca1a103903145210241d682c49100350040004844003003108144c444803908440c0301500c03000707813810401d0038004000207800000082d0b00145100012000354200310440030000152100904903444803072001c50384640040c41307001d02030090307001c414010355401d108031074070481511500c80700140c15490003543c40c505a201034031103015030408184014050030401044680c2d8050396410f00d40301d00f03420318283d002040c003d43c0b40c2008003c1ca014504051007058004248858003a4882c02d28450f80201311440d604001c103034850810007840b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 663586708 1250 663585458 663585467
    0x1050106080114030f011a12010203040503040e061f21020313290103060501030605070503040b0f071b121b0f060b180f0105010e010c0209040201030c02190c0503070510 74
    0x10350f420861809120103c0001083c42c249060a020456502e80414401c00e0070001d12441c5403006c0458140d100b00e540d8118080c02c03071000f13450042280e40100400c0141d09068400b20380d00000040c0782c0c1d80d00c403c264000641040c044079103640045d491400740d283e55010030415605481d8070b45000c60440c0b0746009070075605801c002015040c1d4580d000e40403503a9000a0002160035946031203680715580d01d18000c0050002800103c401703500308400180300900c220140c92046400041f410b06030b443e000d901c05550540a001941040300429460500c001441444004140302d156034140d61082004000c201c0d518068034840c078030324100580030101e440000028071864200c2000942c0c0300e55640001c0f294403c40d603580c0300228500e810449800440120107040b5623003030708d07804210140da01c011284040704010080d80849080003040c05944a0350041c0e01c50b001c80c0c0120356084500c4d203d42556500548400c0f648510744071001c0c03107503080900803400242810b6a418016901c0c4d0381c130140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 663587958 1250 663586708 663586711
    0x5031b03150603010608100b281205070b04150206011406040b2d04150203250303111605011404121b02060409090308070c0203060a1a0a0e090f0105010608 68
    0x20740880c0d009001c140c46a900303501080060a00078211208014240c0701c0030007604185000c0c52040e6200700c402c3c0d00300e40c0540840140c802040c2c45603d111404c00b1100c0300c4220311240155841d2082c1d10780402c0fa886400000c0000e0300b0661a006405050f01800915194050700a900184000c0c04256119103510050314282d40070b0200b00b507100d4030b0b03440d00350381ca805802c0502c0b008000d810b811180c036441c10b100100f0070395104240b8090381030a44001030744d0724460442c41038082047e0013038405030114410141d042e058440d103008901a1501d0171414529000030150b0b03080c04144a40d60070401009102e1550f540c02d091490100c2031900d91511f82e01a000749500c1c2c0f0500850910820350108589640d8400070b500400943d20b540d254503075240144003500c0d046011802000101d40c0c024000c080c10038085074002e008000075610900200060203014a0035030000c5101040300181d50345820b80d8002401c99101e541c011440c06a441510b401c00d00b01405000d64500001440025800828a03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 663589208 1250 663587958 663587983
    0xa020d05180a093c0e0f0109030804050609010b09060409050a0c1e12051902010c1a010914090d03020904090f050a120c0803010504150902070b010608071110050a060308040b0405031b03 81
    0x2001405c0e1011581000e21008905c5199440c1810040426402c014180c3c003a500460868802d0f50700c1c08074550807640152140c40d840b03140f02e00011840c1c035050704103c000301c0c071840a554080f031550392007910030f0085400184e800310201540c90040203044035240000e00c085540c405040b8003e448244d203c000f88003040c020414469182401c1d079000f0082e0002c00d5074004000c030140c41804089007070041c000e000d030b4441c0da400c2c01603640c43c5094551030302d805000b0f03e0029000c50190360320150002e40c070405c28070350010b44585420002c504007480a42860b8000c901922722200c0c20715220301c0c50f184811840b000c0c400d0940134440401c145100f500d0554000365000104100f001581082c4446a030b4081400c0a000051010400801d030002c02e04844444d01c900c02e1035126400c1c00e031800003005c50040e0390356100030b00125030310510350000e40d0805031100c400a01681c50340c07168a003950040e04241000c40700050108003c0c1000c0003c05003a000200440c80390012600010b03880b0075003140320 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 663590458 1250 663589208 663589211
    0x200a12021305090106030c0306060c05060f0711030d02040e0105010311030c0304030201060b0f1911150c040f0e01080c091512121603090b0a020d05180a093c 69
    0x82001c0282551010003400c4014001069903940c1d200c000d01900c0c40b590307483d002070305201d40000c400f80540c0c00d8200b8194004007401d81a982c200d4a961003da0007480c880810540350404805603005000400611b05019800359855040205541e06044c0603403005041528000700c24000c5248401500e030042c0003204681e079a130300c40381407c80c05040d480d000305404278400641212051802d200070142c0621701d054540c2c842030202c2040d5070303508141034031081d07907045040001e005e02e054011090388041e031144068141030b102d580d0000c0b0f001083c0c00486024100c0c20043c8685602081198210329045402007400d20b440c1141d42d507500d03105090680200104c003010380101c01d09010061900307102c04e00c11515401c580c154044a124120019404602008004152880307070703908440e00c0164a80040c9003c02c00c6a20859071540000c484420902c3c940707010b0044c3d9502c2d01000f000a08200e2404181451000d142000c080721041250341d400900c89007298401100020800d079141080f4030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 663591708 1250 663590458 663590467
    0x203040b0717160218093705280c120213090b19020903060f0c13032001050c0607030218030a051005070903030804120309050f01200a1202 61
    0xc088540c0819400d0084450324041210a10399060500c0c40d42128002c690170076810503c4011000301040c113413496070880c0c200700b081005000c0401c94800b501d094245102c06450881c4a940300102000c05048503039402c541458a072260a500004c0c1440c244003104e9942040320b995242c00c41e808034800c144a40300481d15040c2550354455401c0c4046081c00800c0c07241010742e00c4c04658140701201e046940d04016076204181030014420703a4550040500101900c1d103800306100c10401c8003c090481e001401c1011416018001d02800c000794481d080c101c40750740e844041d082d806917002e41102d04200c01070180c0c84540c1e000007440d94020140d828010b85d6520003c10b64442590b18442d19600352103001804020003100041c65444841241d004001079107640c5001c5503507840c9844047c00003104203001c04c0100302c0940c8507040e0072000b4100042c0701c003000d035960340c02c21140c00c0c81d0702801c1c1d6403040c8a052080218400d031042000007581e20303103010108400a8010074040704008026940401c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 663592958 1250 663591708 663591713
    0x80907060f05040503010e0709050903070c0311040207080a020102070606050f01080414100c0c050d1707081f080615030f1b1302070507090609060510080a090b07090806160203040b07 80
    0x201100c0113090040c000b0311025400e094651703940c9200d81308003c141440c0c41e00080d0902404019140d507aa40304080018071403031030315130482003088040c40c594869401c00c000d0000498441c000c1810440031340002d83c072801203060400840340c00341d101d640100302032038008410380ea20010455019501405506c1f9030039600e44da00346441c4a0716908180c6a140c4542c2140054203d11220001031042c030444810314207075401281c0407603206800314010403410b404600c515000d61080b43d0300800c107084499282c0401d4003c003820914035480307640113402c6402440050b4420131400880400154024200e4992041c41c803681d5001c42984240d5000750103190582568404504102c8000b0f09082507454040c18106240c680201e44103042c0b1003032601100180340a65400f0340411117000905907080d0b480303100720582c0c40000091480b00d103a030b82c8009190000e80c1d2901800d004131200d07550031101c10705045055141c000090203440d2001004090303041c40681c004111801d0701d000b60380c06502c2d0003062 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 663594208 1250 663592958 663592967
    0x40f0221070b0d05010b0a0504051201021c02250b0105040905030c010222080a020f0402091c14151b0a2105040c0506090307030204182f01080907060f 66
    0x30404040140206540080c04405401c00381c1142101103c0401c4030f43d0f0f0300c0550760060701c5102c0300d1502081e070601042100c1d25042c00f0f030690303107811580094070b4000c1e14980e1342902071459207500b40d1180c0c0440c0744002d0030031000d00300c040045000070030b0a010310300c0c0d215801d103000148903041c0f00e5515508442c003000404e205035005201c2000c000c3d5100d0300c0040b14000003c10b9060300035100004800001204070700014020394558002c3c286c0c60ba910040c00a100180d4030528099412591503140440400040c03c101d40c40036005554038600500c03000f01041c2815038003000406602d10b0b01007449454802d4034800c181c0686091162951540144030030744004d40403e12456440540c140107049a20040e040544502d00c0342c1c5080541940381d0b410070815004092100350140e01c140000d000508103580721145031040b104108850300d030582c1d140b0000c0c515481d0385403104100404246c481c1400c241400d02e0720242400d00902510b00106819503c4100e031141c2010401062031002d006c5008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 663595458 1250 663594208 663594259
    0xb2a1c3c0f060509070f121802060a08010515070503181c0c060210090308070f02010b030d051c05040f061104031703041b0b0a030e1903110d08040f02 66
    0x3100280700c00c1001011a00040649201d994003036540040050708a0b0b01c10440f543d918003064840450407110f0048040003400380030032a02010700310b072009102680d1110013901d03490000380c1e0342403229810801403114110240f030720f9003c00201408040300085020043d41c004c0111034a072020543d210000140001d581e40b401405290410701c2e9581c28050685407410a881180e000c641c402440000d208040796180d02014000039182c0005c00c2c0101d2040c0604a10001a1310011842c188020006400d000440e02e0030804900c0001d007041d00001130042200303c40100708001c00c0310345060b0701d8030755418145401c0140250350f41d800b5008641108001c0e01c01a540000182000d02d07240c0c100c9041640c410390301031b20751540401002c9013201c114059001901d80100b900f41c10310700050001d0f0080c1004540d14082402100850080c0000c404240b440d030900940e1454003a81d09089124102002c80440301d040040c0301d0104000f05403010582e002c944e40c1a0707084180c008288010350801c041c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 663596708 1250 663595458 663595571
    0x2040b06040308040303030605090606090f0a0801290a06140a030e01050c1c050121020105041a1b010c090308030c0d09060c030b0d0506040b2a1c 64
    0x38041004414000c0f144080d00541c1d00ca6102000107030b440300c0c10085100b0701264555440f074402c01041800b8100201c1d00722256002421a142c5161520345036800e5a030b1064040441c01c075074460509440342c4510f000c1103c68019074103503002d18101340d4000d002d11107040d01c1400080300018844203103486907000c0404c0c40b550000130042c0d820441e1402c52581c0c010701070001c501c00220301030000089648201d5040711061101c0d0b01e5a41c1c0905c541e9800c0c080c0007081039040c048144000903c050040c40d6244c048907110420b50f0783d03911003441e07560081c920000b42e42d038942c0c94443d0f030801c8603030003500200541e0740000d851a100d640324a04201130b44078581c50000300c54100040181000400d822101040303280e602d00380b10801c54503051003081101602d01601a900203000b190104110303048568000d0708206003241002c00001a0f40c241c81d003402150f00ca2814001502e1009107810f6903081d0041d08031443c00d00035205d0286031051182e401760980f021841110040c4156210700c0c1c0c008086102 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 663597958 1250 663596708 663596719
    0xb0306030643030b040209030c0f010c020301021909060906080a020706061508010e180303010e130f05030408160b070311030910120b04060b0304080a0201060506030103050d0f020f0307020d02040b 86
    0x2a000722045071541842c0080a021a0924000091601c2d050094501400340a4010701d0354032070000400c0f4550203158151810720086408000140c4c800b800100980c4100d0b024592102c8802e80000744082d2040d44804d080240500d001d100303241d84040043d810142402e4096110403060500100031f10f416070081404000302d8038288641604482c049040350440300e240c600c16a50000180580c0e810421400c040760002c0006116589411501d01d400c4405114001c0310904a640c400ca01c04200319400d555550020a0400c82020300b041444a0f0a61010038440f0403440d10034403043c03d00580000409000c107401e92080c0b11a800c106903100074400802c103a42d0890704a0018180c0301239010660b400c5414051182d5050400b8041d52045808100c1010328580e101e445541c155000808940119501e4020005240d41c80030040c501841c091b10151502c1c421450b0040c2a000200d00071500359084511100034190003c01600d5100e5010b0f510b076540a02207200240081c030a07104c1c51680403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 663599208 1250 663597958 663598051
    0x30203030a0b0a090c0809010608070501090504110f0310080f0d0e010f180605131203080420060f0910030e03031801151403120f040302132003060a0b03060306 70
    0x217560004002c5e00840c1000000c110407078aa24000c0d454048601400340400d810900400a50a06038052090010340307060b05800c0000e101c002403c01e5000382c9580c3d03990314140701d00784440103040c410742c41106942401041118500e41c03010f400201c0051020b07040c4858803210144c0d243c05050050300c1c840c809003081c01565110700000c1d1094101c07400301b640c120400c0c4400b04039485040010008180c241c0c54404c1e4960762580c54415514203044100b100a9045482c1d0000d03494160150480b8031520b403043c0c2e1101780035400d12040c080260741388003c042c1403101f00407081401200301d9810926800c05200e521040c040d90a000d00a5007010209040c40c4880c0054034403600080224401030441c217556115109441c014018003443c402503169010030803041006243c040d00284460f0b540c0301c80825900c40c110048550550300d106034040e40b140000801c40e0034909511030780003400c00010740504604004020a40d10035004014103854090f40d0703000e40c0440300000004032060901d0b00d220404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 663600458 1250 663599208 663599231
    0xa2409052b1a100e0415020f0408060c03011703070222060f030b09060c040e06100c060f0b0a15140306010216030602070b0109110901180512010b100507030203030a0b0a09 75
    0x100b240449402c0b00400001d0004904002c000c86090b00503a082a05000180136504c3c500000f94001214103404942c20000062541414004e06219500311010781e9200d40c50030100341d0340d0802440009416400400045c00144d0303c102000c03103188403030510705e01102403d0300c0e904020b0a15802400750006500000000c0058500c840c41c4a09500805d03110503850320411015240980c0c0154002101c0d003100040031400c1c022004c006410542c5803035411080a0f44881085840c0c030f6141e143c0e0a900d85201003140c0c00c209842030010304504503900f00e0400c11003070082c00300d4488400381e01c540710000081402c0c0d070b10030056001c10181c0d040018801985d286000002940442403c840990030480001143d45440c031808411110840d520761910080400444046514000180501d40e4000d00410291185041034005000710b0380001107112202007084152407243e4119010020200700c3c62001941c04000d0341d40121a0890115071107200c04c000170500c0721650002c88036645080715000c0ea = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 663601708 1250 663600458 663600503
    0x7030e0f0a021309051207051614010f05040b091207270c020606010507030f090810090b060306040c050d060207020904150513020a0614090a2409052b 66
    0x5454821603c1c2d81050a04010744015142c00d81c4018101d6002400942c004207501001001428424415580002c00d050740d0403e1300390150b000f201c502d500104001825581251441e00311600606069060500d010401112403040c3d0261601079100440340300c98400c000c010000240a29014044151901041510880b00018421010700e0b06251000f50390b9400801c03814026601a52140c1c80c04903903450555505148075480010000154000601c2072000d0000b0002c1d0b5a1440000c039aa440341d0500700205000134040510903004035081c00006410200742c0003c441054507103212090075070401c00028081c007840070b9000342002080200b008400069261854001ea0f010000c541b02c603030050380c82a4610b03000030b4001c41e0202050007000c0c011080f16403240c0095031010300e04030702d00011a1034080168021404007040c40e40d001010520b0340007505035141140b5000c051180b60100080c0d03d4800d03803d030710480209420003201c0e0210f140366042c1d100c1c0e0300503041503d00c2071420492074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 663602958 1250 663601708 663601723
    0x20607050613150903050409020304080904110a0315050a1e030804060306030b01171e3421020f060d090b190207030215130b040803191107060507030e0f 67
    0x325001c11644500c510f0102c54880c01040b19055550241000c0c1001880e034001e510107001a02c80f04001c1c0f00079a616030b5a40180b08003218420401c0e034681c42168405400d0b82d0308299001c107540c08207071050105840345480d1004a038200311855540c0b00319440c06a2034200b441d04090055080006d01003046038054005034100e80c410180c10b0482d030703610380381c0442d0b8010200e401c0380d103230b00300840c02a100b01520180c020060030b170030300780e80c00d50611341205d1490824407201c11101e2142081c1003a5244000b00300d5200605080c000f840d4844246071034104010303584030700248511011001d5041548810b02914004e0720104800c00c0100c4c5142059150b4a06c211034403500340225100701c0c0c044542900a035003070f645c2e140c0c005064031146240018528600100300002c1050b204400701f0111301035844040c0140d020703680c81c69032801c05900182e0601172106101141500340764606107440020380490340125042100000c9070f4551860442c042c0c040e408008540d0b101c4ca62415030030503008075a01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 663604208 1250 663602958 663602963
    0x30a12050432180a09170c010506030d020f1009151805010606091d04080c0607180e1b0c121305130b0f0d0f050102040f051801030b13020607050613 65
    0x1000040c2c0c0c24003040390304041802c50405070040b903c04150720320019044140028482c4000c0a01480c143d403c0300c02d141c110303030444d0171285e44a0050020701d0506011500b4003c10600c003030306045802110740c41c0d451040c41c03040f941c1c0341d030360301401c40501982681c0c4e00e84400c1200c005100c4025144052140e031890604189e490754641440040c65902071004602102c0300d8228440032a0140701d00103c0b0140010019140484100604404da10303081c02510701c65400d9032a1a40d00402421011a10180b81e400c41802c0b00c0c00c1e04140b01403403a10400f500070404841c001c0b1565a0b52191a007414110ba4541d8458010004100c4601050210701d81c50203590042d13500c0c103010154552440161140e43d80f0740303038004d035404a2103902c03030400400164070b030760240380c000f451030300682d448608aa000b039124100c0c03123408110610140c40d20f490b101102481041030f61a46504584404201c80400751002c85145119200082151580c00a4408090b08541030725604c0c50140c01000544a462004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 663605458 1250 663604208 663604289
    0x122a020c15030f090d08060f010e0603070305011706011a0309011b020615030105010b0906070f080d020d06080c1e031219140a0e040902040e0105070f0e01030209030a120504 76
    0x72904d1000046454107020b0a9644c90101d49440061240b600341030060181013000c115000c3c0629201d4100440c002c0d98240d0300000c1e55031401c05200310240d130012151609030081d03001084030161240e100d2601040f0204034982c0d07a1114000d16006154400c008030138411900c01c0500940d40200340075100d0054284e4121160021000f05422180e0074040e46103015818004040c483c24400007402c2030611568414a0300316054940d090b0640044207041340070350b0006880c026000c0340780942d034010500b003401010f586420704000345605403900610010b40c80c0c0c503210204103507070810641c261860005d102039a50000c40600c0c14a0744800c0355101c021500408080c445440b880c0100d448031140740d41c401c20b20b030558004000140103410400e0342e110751101100440c83c1d00c01e12505000c0c401ca0b1311288290b2070038810291510302407020382414944140b09002c4152401b180b040881a8000112201900b01020a40b00c82c00750740c11681a1404283c5410740d014140b072003100d81200703118231 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 663606708 1250 663605458 663605461
    0x11419020d1119060e0712060c0e15120411041a03010e030c0307030e190801020909060a120f0f0b011205071a0a0e0f030d0f122a020c15030f 62
    0x40240e68103100196025985003c801c404007203030040d40300d41050440d480c2070741c45050b0303030b240d10761440c8008100940e4031954921040d40c00d179810010607881503005803032401d85d044544031400c003640154022440e0401c0c1d4000041e041150042d03103014014401003040109142000c80c60400204150710726000390300c1c0ca1612403940000105668038004c03680001d501e00002c0782d030116a010000f03580c10350000280d1400c0710101c401104084080c003810400140c480500f04100321100305c01800c21400341c00c0c124070600c00440d4242c94080c1c1aa0021018220031084d40fa1038807031881100340203040a500c913400031954030740000315001c0300b5000351300311076200c1e0700c030500c0c40e40c01418000100c500a01c00c000003c4c01c00e018588102580e24010080d80380c0484440100303041c0309103e4604000030b454100070b40005072304080a03e6070403080403010400851a1400640c04020f44448040000c0010040c40040307071080001070300350760002c0c0283c5960348200c41c1180e11504282c0d45c00c01d018440c00b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 663607958 1250 663606708 663606737
    0xf03030d1d1c0c050a02090c270303250b0108010c090e0702060a0b030f06040606060f02010b0a06030b120106030807121b120c06051305070f0f05011419020d 69
    0x11040c50700b500a60baa100d12803103070301c810b44a00c1c00c0d88204540324003a034000c10000d40d0b20380021a202303103142405683d8500c60b40b100c1541b020350058196074400443d500441c8140c81c00000d86002200c2824a0b1a10b00c400341d40000700c8014410000f03144802010002c140e10606404c44c18034220192122091f81e0745481d1a162021402c4401d2001030f0b00c0400000d04010064010740740210700981a104201c0d81203550b50300f003007070844003529216140d00e000c010740c07a0f1100c07030700c1c911684501c001c0001e0244100013078a220083c0c801c400400d80c580e40700b00180d5540150110381852450000c1040554a14062001c1d0f0005c00e8140e44094907001580481e90141840b2450550180115107040c029503592965080c030f0415907c0410800300b105070002466031080c2c0303006026174804420400d80780e00d092484c002c495004040340300c0703602c802080f001800e00804000d0725800d0034000a0074140141c060010300400781c40d01c000c1501c01641481d038540108030440c0006566070f902500c0ca03400c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 663609208 1250 663607958 663607963
    0x911040905090303040f110a09090b04030806010c0203071404110408010903090e0108060a0507020c3001020a0210051b0d09020a0b16060f090b07200601050d060b0f03030d1d 76
    0x80701c0146c5103d81c01654480012200000700050749401051940c61984404214088481d0940110b0750f02c07005500340828903800406091303000c542440c09000c00c9200d5400310b031f00d5600601c5000f0496804a01e40d09169407650850300d80385503c00b55460702c6541e80e8500d02e010b00f11260080e008074803801408604410260582410b9400c2d490041c55a0345510a0020050400420510460050404201c80e070f40d205001030328401d0615009008160814545121144580ca0103210580c810010340c09107035000720b240110710703d1044002440d640d81c070f800030401e140f8001601c85a0100050040511800e42e8000c080d024000c0d60200009502d034003d030600c034421200319030380950350310024030b000500c0c0c1c0d0841000324058440110700d250043d6510210310380107a0362000403801401040c0320b50a1404290450003400000030001549032201050121203160405080207848a103a0b20168803191900d4000440280c2181c6da07a2140b051500d005003450458003002e9144206294070a2000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 663610458 1250 663609208 663609211
    0x100e0f100c1a0c040b16060e01060603140f1303020c0a09060e0601090b0f2a1e0102070b0103020105030a0e0f0105070207050f09060108100b1206040b0d0c030201050d060911040905090303 82
    0xd0300c0b1644d01d41420035a03c0620340d004048040c03410000303940b2040020b0300b02c1c02016481c201407000070400038107200000e01905c0c00d0441c219010449082007001b03500f00310807a07d8110b812180c82c585c1039802410200d00b06810100625004080c00c040001c64191a80c440d00c21105038406005454564900440e0b09203c1d41c825a4480c0400b4000d01240740d0803100240344182c5080311030240d0552740345a250f003c0c034100d9200241c0e0f404c103944000c0066291030100340310113183e0008610741241c0340c0c3c07007000318103040c00040c0c104071000c000649843c050703510807605200302c1011036000d542040a282c0c007808048401340018050200700066508100c0641c01c00c3e860028042051550b40341c0044074403103001800310400c0c0c940008001001034000000f000a44a40d100e48182c92074408140419180e000c0410b9009004c240700c0c07a00801c0e21004c5207000d882d82440c2950b610388452900001600503604050300c01480e019500200300c000f18014000c5904040b03080c400f0b030303459000f01500c0703010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 663611708 1250 663610458 663610471
    0x402010804060c110a06022a0616030b03060a1505190b09010314071815020a020103052a0301090510051012140c070c050906100e0f100c1a 61
    0x4a40303021400040c81904250003a104030b24201c0c14a41c0080180b82c036200801c0400c1c0c49850740000e80da0030140450300202e06003a500c24034030544481c070262540e0740b008020481d1070141080c2000d09001480f03904800e111020090441c0e60908007103407a44003c110a002408005050090018181c01c000307039a2522544103021206d0350a00c5c00c14424060783c402080c1d2410143d94408401080704c01c481c4c0e0300d00a04140d07860440982e0031903074042240000d038120b18154403400711141082540060444c001e542d0a1074089455100c042c01e0b0300c41d000c4003c4442c1039800089070b42c5010891060003443c1218200d2005201e183c0718181034504103001da004241c2c024203000380c2c0e803422a0282000c480305854100e0006112000e0107020a03603040151641e881010707001814030140104003040c000030b4a0100c80040081c20071030001403651031001d941d4800d021514003900ea165490038000303028244003030080c08541d00c54003401801c00107031600840d08c0190b051801c2410a0200c00380c18400c14 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 663612958 1250 663611708 663611717
    0x2090a140f010806011d06130834050f0d0510020c100e120a090801020316120501050303030118020717090117010b16050f120901110a110d1a0708100509040201 70
    0x141007004600e86c1400c14503411400070082181c0c0c40604040d00402802c013600980811001120442545c000c020321500943c0c005da4a08089184003e9407207080391000c4504405c0c2070341e00c1e008034654090358031000c0c00c14040c41018407404c00c0e06030002c02c0c1148200d0191031001c00e0103902c807011900364207059145079111085050040000300c1c011300a40355142000e6016640d61501c50f07099a00440d07200c0481c00003a008144519001039600c51500c0146009118642c1442d004c65904d0205104001140340c09113031a2840005d158100e4241d19042881194140c081c139119801c65408504031078002000c03502031680c0211b841307114a040c0c820f1134803010b1401d40b6903203004807203c01c2801c00381ea05c1c6c080c4030414a0310110421041c13459089000d00680c884490710300140008207284d1842e41c0903001070900c0800204c0000b10120448400c071490301c0c540031a03042c25206250102d201b104483ea0030018045e010350008a903a10a12240507503800c45511074045c4000418150303002400324 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 663614208 1250 663612958 663612977
    0x1050415080403020f1006030312090b0619030c08060601080c03010f032004390e1e0919060501050a0518031c090e010501020708070608090102090a140f01080601 71
    0x601c2501d603103400c01c0c040d2044440031000d031040350303040c202090400041c84e0303940c980800825800003203a620206044c502001441e5664580c0850000000d106034820070300f21140029480c4544a00c41c065a00602d0a481c001d844009040e990101501c003107003c2043c103800a0007020104003140e0507100060a4100d9145c5150745001400c07420103501c203140e48207035041c00613940b03c5200d050842100c405005021200a0686c4d2203041c23200400da14160340707042e00c14503009801c004d1031200100141d4040090740017005030803a0100304030101545c80300c0840140160401001c111510800c8070310f90405c015540c0f8030064409204401c44440414400d0006898560f42031845c10107085c006410b4336101c0b1a40c2500306840c0c0320301c14165020600d4480c0a1103080c0e044c01c040c42c09800700b80000d000c0c09092942007551665541b0a01c800c20131058009502a4402e40580e0807440307000d40001c5803184c444008800600318003141502404468004110b19072113407069600405041e156101c21 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 663615458 1250 663614208 663614249
    0x5060f040b1c030509060c06070807050c151008060906160507020f0913170d060519170c0d06090b060103150504020a020111070605010302031b01140306121218010504 73
    0x1000c80c4083e0306001c0e09000320109074032070301c00400802c0007120141900d4541444003404c1203c0107014281040400e2200048148000407000f12085218081802c00c1d501d400e4011130f645200d030440d4429008801c18004c000000240d0503020b400c042c0071460707080c114400221141d01400d54040e500c68119226260b940c1881d4003060703004088044441c00311241c03601d81491030881c844a400c0c07489000a0171104c40070481c46800040c00c41190350245080e42c249821030342101c64010f0340b44000700c00140d070410a0007000400c0310480e0103031000c4c05103005410214014a056502a40c1c003a0b58100000e40c01d604c01d1003070034110310448940c05032280c282030512000b50003020f44401550345c0d5115440c4c001064130081c00b42248210303004900ea605520526040000c5d18910741d078484094440064203a0300b15a46c942d0246d003107240c040d2660388110001d4071442d09000d100f07100b8020003881030444140d80d401040b15400b0101451003103400d0741d0044940780704d207100c3c1481440c0c036a581c0700700d0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 663616708 1250 663615458 663615499
    0x3041503020d05010602071e12030509010912030f1e091514040b090301060e15100306120c140a0f09150b030f01050301050a1103070e012105060f040b 66
    0x48412585001810055588001d000719602a081007001d6400a00d0420075841c11040300740116600b003000002c143e1505c40042c0180c2c019020090074403c02003106c8a01da440340041d18001d01d00340e007400e400301c41c0c14140600072019540080300000c0c1900290807004048285540280b5082d55843e03583e00c0c9405140601081010281802c00240b480f10094020320040a4005450f402c1040d540c0d070b0703a0b83e82c1003508680f030715440050307007041020802044042c44084442690001c2d540914080d0b11000c0850080c881600203602c0c81022050903010300000e40d80c0901901c4000104041300c001800c10020010642d128a141000d40c9800610000d00a030b003100c0f20410804070003482031500c0e042c035500541c10840c2c001c82c030004100b00400c4249801d0140c10340000e00b90b6020454110ba2410f0340249120007000070007407104941a84031107912900c8010b1211a050b101c0c6800c4680d00d48010007c0e2a065440500c80c422028440c0060324151240b243c4140000703156807009514182500c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 663617958 1250 663616708 663616739
    0x50c0c0a14120a0806041404020904031b061a0f030c1c1506061e0f1409180c09030f1903230a030b13090503030c0f07061b080115020304 60
    0x12810700803010b400a10200540150400003866200c0c8100c0d480c4c0300d07041c0021a8400d00e412003c1919501c280f102507207401c4030b41070b081609458007140b02d0040d003408121315907414400400651402c0c80c07500e01a13000c1006805030074400c48110402ca680d12041650b44c1c6082d0707214607409480e140e044c04880c00c01c03602c0d40103018407400d103410070a5007101d040b02c1156003d40c01078003c100e81c5092501c1120000d00007041134100c2d800c04401095000a0003024200001104000c0341e10004200d0782580c3d0716120528203500d05d0107484c205190000ca4080c0a40102003400d0291242d680b120007900300c08200f4003020300056200c242c1820050724200d41c410040090215108084082042488807100c0100050520764801040d80006401400a500400c100714030005140c40028000207070040211780d00401c1e0001110b890310214450481a4030882c000144460310304401e04c000d2031501c13009090840f4058840510582c3c0e141e01c035071440900300000c1d03070040e0002c0106003d141000030004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 663619208 1250 663617958 663617993
    0x20103060302090103210f02071502160902040f060c2a0815040c0b07200102100501080a05060115121122150c030503190207050303040c0504050c0c0a 66
    0x10500c01e649401041e0300850030382040d00c203082402c0101b003200c14400301070801c1d2511460220078031f02005000039114141405554010032a034592019554800c1018170700303008960090a02c030b1551041d00c035000358014410108000b170303028000940103028242020100781c02281c5910b0002000842e400405140d060482070501b0404010441c190300b0418102403421703940a0080381d00f45828541d6840885030f00940e91540c0820500c400034103421414042220800e114645108010300180e06160340394582000e40c6140034000070701c2d07000000d01e0035603090042c000d4890b141d80707950320104207101510411022aa500e020b5000b41e00c4243e004d507043e08002405541800c0f2000850150320340b580d44001c140f80d030590802e1102418004c0504c491940034107094071559190761300540b00e800000c10102c001d4201480941c4d015646030102d980c5141e001c0143c0f40d0340c3c6058a00082d0174012801990f002d6441c00740014003054407407088901e0f040401c001822100c01594400140100310b407c40f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 663620458 1250 663619208 663619211
    0x3020f0a03080304050309090f090c10020f030a0c02041512080c01091505061005030105100806030109050102160b060405010509160c05100c1b0b06061b060c0d180b070309020103 78
    0x20120b02c80381c000d0340c003451003240991f58610b403402c10040c0d054000b070074540e100e0f44203009000f600300e000101d0364402501528498146d0a80d50030a908001e5440c001c6459800001200800c1e1540211641c20180c8201c404020800110303010380d8603400d00340200f01903030100b0442540440c03241c10203008800321860011400b031074941d8171350040e01c03a0303c0e103414039198980c420302140380780c0940382c030240c0c039568540241598904000103012800e142d07da0414400c1c0000480d0b8291401c7d00011455030b0000c0080d9540d040c0103c2014041441c103005450f400c4d03c05002c15180d28141c041c09040b101c009002050a8480d05620080c00c0c40120850052101504680d00000c03800e03c210301d803060a0640000300d6080c1d448016000c426850700c07441407090346203101c0c40000c0803000015049141910910f403a032040700710160340e88800c01148550383c4a00400c001c04102ca00d03008102d802c00600341031141d080303003101d40e1a000007403040040401c00283c00180340907210b0303840010400d005240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 663621708 1250 663620458 663620479
    0xa052d01113a06050301050f091f0605060703170702030c0c060a030f09110a0b0f040317070602180f041802040b0d0f06021809090a081303060f0603110609010903020f 73
    0x954142c00d0b1201e03501c01c0802d80301c200030800c40c40c0030f03c10300d94441500c4a183d980c6141440101c0d440d070103003400452803c00040c503003041d00c2401d0f0b84024041c0001812260380c0c1c8600d401d000d0010800a06a43300940c15040010700c40ea00c0401a500b0712941d1800401c442600b100402c000c68000c0707c900e408042e40c2d120b0040f43d400d91030050350441c90140130b5654a070103117601404100321464124600c040d5041141d0005d551081040f90202e80d000304500310181c4400310140014420000064043d50001c0341031003540140c0c0c50035280c0d100d41181c0890501c80413400b07100a40c0c0c450b10030310440d15aa040d283d40981002d40000310480001031100341c1d9034000355500124401c1d40d41081e240030354007103501800464003049080568400301e8005e074140c42e220302c0455a03003500d0030000740b01c000c001c90180510744d450908032010f9544400c0038400400c0441e9000020082c0384002c3d074891804000ca0749050030880216081010182e45504036142103800f03001152a1010f1a1b030380002d10800c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 663622958 1250 663621708 663621787
    0x3050c010911010807141605030c0a0b150a03081c020c0f030414040510030f150903170703060b091e0d03050d0f05060d030309050a052d0111 62
    0x2061403a040e02c9201c64081510070140010031a0f20002e0051003404040014442c1803004442902c02d08491115052052106854940e081d4050320009080790312600c541c5000300044001440c1c42200d0a1501e0401d050481e0108086448144030140211a0400c102c10702d180613210105501d0b030703604002601c0c1c0440c0350022071600c0003007442c151840d08041020300c0034446400d410a4070240032101484141410500710540c2403140c40020030641e1603048a070100084030b41111002204018104030301881420042c0c00303404001c8901d004022100005044c450007403003040c1c02c0d2042d48001034102101c21061043c410410b121a911302001140138411990301d01172607000d00c500c25a11181c5880d034032440030b01960580c1840545540c10601084034545902c81228182c2d601842e0204110360f503420103d0034a845604003800300c0c010400e00b104804400101c001000c2c0b42411f030045400c0c201c0482c2407c803480801c21003000b003002c1040b589102d05410300c00d0300399005242c1340000d01e000003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 663624208 1250 663622958 663622961
    0x706090b010b120c09210115030c0513090b061011030f0c120c060c070213090305030108150108060c070c08101a1008061903020a0e100f06020c040903050c01 69
    0x240c2c41510b800400040020394002e2074007840360010100014541024080d000007a004030541020800c046006000161042425003003010010145030604e20b2164913800c0c0f03100c2d002d013103014032802601a00703c00140c2e03044030300c1400d01c03443d000025240c5c140c48a50801170311041824901040007015146810031090610040c44140314542032503982c1c0c403010915604160600280d00040d4109000e00d003c0c0440206001f64001c1281e20320b0b580e150b940d480050000921a00b413503003114038150900d010141c001c0010f50607075411030101c0e01c9110f1346100030b442505090268041981160011515901050001d0651648500300c00c40c841511550050b1404082040e600c8040381c85072a0b52420045412417201c0300740095406110700082445c2c05080d050018140301e014010018000208001040d15030000e158024210001c0d2580c2c4d034408030403031106076288808045c4841c8000303030783c000f242060002c44500c1d4014010080100003000000d109800040d014004204024854448203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 663625458 1250 663624208 663624211
    0x3040e090609060c07030206041104020c151f03020d0204020903031209070321020c0906040e0a033c03020f09120f010c02060106091205190305120c160303020706090b 73
    0x22100400030340c507011040c54940580500f130115582000c1142c0804254040340895109030801c04c4003842c06040d4010500134418410208030a0040e903400030401c049600300b56004030700300104021517200500c5560000400340c44002d40c0000b081500304010704140e005031900b190000d040e070303050a81f6144035010282088982d1046500454800d000700010404000c4945030000341c0920341001c00301e0065a40c603078075007244d889501d5070000070b0810f80c3e46420040610080c1c40a80c2d4800c0400d00d00a400301000c000c07100740d141c400b4420000c0c545e19810412840b1500481c40120607080075070141c0080d4851480707580b0485082202d00c0c4c042e00c0301c012074049500714000400b00060b44803242421180310054080c00c541200c2c004019881d4004850300075072700c082d18a584d00d5107040c60107078688582c43e509050200d010300340d05014917402001400a0780c0c801c000c4200c0c80d9072204031203411032050098a4000086080040d40440d00c2503002d891807901c21303003001607034a465403140c1080ca1070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 663626708 1250 663625458 663625471
    0xf09051e09061801110d1503020619021b0f010813020901182406120e070902070309080c0102030406120b12060a0606092904210209010806072003040e 66
    0x41c109106103c0f510650505048108100802c0240403004018007584078000d024500c4135203640c1c03641c081390040d448070303c0190343c02081e190303a980421007a070003140e01c101c031418090b014035102050a07020881d0140d40c5c0d484028405c001140e00200191107602018140c03000e2180000e80040050303c60b00c1d00d69018041140c01d8240304031803c00c4c92401d403030f619140030300c5c055107001002405205c0c0d050a2400e445441c01c28040f5441c8240200000300030804062541d4030480400144000050b4001c00c000c902a684540703650742c880089075a140c0c400380b0342c640164400c1004100c1c03c0d01c1004601c004c940440e4010429035001c1b8009210504060104141500043e090102424461080c5001401c00d4100741c2170f510b2514802c0c10300103411203800e0402048443d0361181d6144200c040b50040c040300d0001c0c0c213404442c0390040200c000e6200c0100c1c0544246000032620140025030613110316041e58590000d000ca0588403980014100c2d02c00501b8031086c000420120201550306d4071071003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 663627958 1250 663626708 663626713
    0x907080d0815120606010e0303130f05010801050a0b04060f050d0212220312020901030b03120c010f0b09060d0804081f0f05070c08030915040609030305010f0f09051e09 74
    0x1015904902c240d0b400b4000903101e245144100c120442c00411805d52000c402d0034019007010055010a04500c900823001c19443d8038080301007140d02e889002142690401c8c0c1e2000d40b241e8a0704e06100075a03030180600055002e0500c400c003c6103105007610540407005282c02030502d0201e0440c46d09980103c020003100ca0300031030800868107a07050140d840101b903802150070350100b58078060000840f6581500003141c000845201a90294009080960015046031592059020891080d030001c2003d4041075080401755903103500a1300909951380801000c3c200301e503c41c2000c200c0510980c1008407000c820038440000c2206050050a40b0394a001c44070382d4840c69489102011945502e040039903551424085c00600b41e44503041d41a120390000140742d0720348840c1080ba10f403280b081c2c1400c51259460003040104855500845412407003514103001d2640c0b1400401400e41c441d01a0807242c840650f0100140d1015822554020040040424880c500041044130b0b0a004548100711903 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 663629208 1250 663627958 663627961
    0xc06030a0b0f011809020d090f03020715030b0108010e060a030b070507030e0307060207061416081b0d0f0507060b0409051614090a0c051b06010f120503030a050907080d08 75
    0x241806600084090030904e40808400000d01104000c0c1800d8002c411100f58046045174104800e0781c04850041d40000701441e1600381454001d59518203030103400d12050466080c1070004c0c0c0280100f611146058440c560035a00705031007030345203c50003460280d001c0c0007404004042040510114003420301070356655907880c09814080d00040302da001c050b001e0343c8096410014240d0214101c800c3d14068908481003144841080c1c4042c040d540581c00288208011001000b62000003041b400d010a42e00c0782001050840c001d480701c1c3c45852200c0404d144000d1245800d01c04c10003001017521034100042d013102907038081811614960011a4141d010403041c25070124070165400c01403c80544032461181d0402c007055005102900204045403154041c0d0390140c001c0c01903424191440140c0303580c1c00b0b01d0403000d82d0388800a104000c41000c041902068040182d6861100260442c000390301d5070325000d030400300030400140036819902440d2400f05146101303108540f0101459070b1a4000d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 663630458 1250 663629208 663629231
    0x40219081605030303010f14060706050a02370819051608010f06020a0201030213120b040606140306040f03020138010e0f011101022a060105030105090304170c06030a 73
    0x300c1c06500401d203e0f6200b480100400b820045000c41234980b60445001400036800c0402d60502480d50010006410601048040180303039001e8082da402c0c0900c01150004251200d1004030070346502c443d02d15604649a951076401040542c0d040001c0c00000e85610414000c82000c8400903160300c2c0d030000711101c00b241c03655404a05580034006880f2078510311445c0200c069906e40e503515009050580200e00b54450080e0313400c00c2001090b2410080c405040309103083c0da80d80c0c40c104c0c1c0c11240c40346081d0f0041480c0f580c1c19000303041d80310064014141c607121500c5100207030b003064000b201190f4840c000703404060302010708005000850a06945900401307142c41b072a2111a2441c02e0400100c58640c28040d03480480d0a070600900303007803403204140074194003800f910030046070050b00445031141e2142c41c00354082c013100c1003840c0400d54016980b561b04140c240e4005464080450348184000d02800aa041d0f0015950100c401140c240310307030307840100300c0540040311030a10540d5100741d0304c002e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 663631708 1250 663630458 663630493
    0x110903030f04080f0102131e090608061816030609080d0e100f2318030a02070305160b12090a05060f0a151a0a09030f0b07180b04060804021908 63
    0x135600003035080030281c0d0401e5a00702118450280d11407100110a00e8040521203c10080c14018409000050b00c440340c0c187d0380c1c581501d0548065240c8103844820300c2c004140310500384a0116106000c43c0345486110281580900c2035a240e1802c000052106855200d01e000d9041884013511855000d614960308449211b50100c200c6400e0414440c10541c01170001200300c103100304881c146071500c1c0c940e10740c080b00410b2010698800060b08141c180c0d00010000d04580c800c0045805412615050071810049480307148490740042c45803010360381425032001e500c2134202017101c03003101c0300f51500b902d0800140e80c0704040e02c03d49020312995440c1030040c84901e501c850b0004418a103008485545801c0c0f0300707040a050039020406030003162062000c000110307082070103046d550750b00e400d140c1d00000f819180f500200b04030401c0e0b0781c51100303103100010440e0003940c51981824904001540c81020003001240d0018034400390a000c101160503c00c05010035400504240281110064 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 663632958 1250 663631708 663631723
    0x60e010f110a2402071110120903050d1104080604080f191d030c101b1506082e271a010b120406320907120b0a110903030f0408 56
    0x52a00422101c404500316540f62103803000c2c187d6035955070003084a000c41d43c004090401c00555400c0100103801e250b4400043c01781c01e42c40090421180c1d0701c1600d04880c2c1c2c480c0f031048280a0b00100700141c0410414001313840c92083c007440c9503141294a00342c031444c0c0d503040c0c02d411000c140300c0091060004404011102480310a0340102051120503000030341c03410690300d87d40b04214000520a002e07014000d003400d203036540143c0e0b4403003a01d031440d0b01030042c01440c010b0050502c0b408480803200450302410100140880a040c114403841c208014090f0000035804205102d0200c05081407412603410080c829020720340c01e903194080380e001c200140070182c0c42642c40200602c2002c01c000e107409a17141d00680d20110000300c81e4141d80d21419036210384071021152071000d4411480031040201424440d085800c00d0b1007515850707113001206003207041c1c005000f4050b2200050024a42c0743c0c050800045010111410070741da28001902d56800f60740703244040000458100541642000f021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 663634208 1250 663632958 663633023
    0x307090617040308040b1909050a021230160303020a0306090204052d040e031201060c030c1407050a0909020108130f080f070503030f041209060e010f110a 68
    0x201d0181c1000d89000341403410261010340203151013000305444194800c2c0041407112485010700480340c5034100140c07241d00b035a0007030f4000c03885043d43c041c0080b0041680c02100b080c0981032141c40032401c002125154004002c01d00d110fa04005a4511207500744510303070401c0c03080c0d40241c4d0b14001008000d0036070b410360b40490101030052209015540c1d03601654007822040c184144801d0710403858006004c81803031106900146819000080312070040001c0408803c44603013542c103640e070b4110455080ea01100080c0001e1100000d501c00142003003034110f12030403104100d55025480b400007131200c00540c0d010510095403111101c0855801c181c000707510000c440224803240956807034401c001c42c03a034a03005048030303800110b82d4001c5c9501420b40d080c55412404032901e9103890114141c19841c151000d036285a01340704100c0071140b00d02032150503100f1558031110f100b103204005403402d060000c030341001c2c0064241d240b50045010040b403412107004068810f4106a404d89818031600c90b034021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 663635458 1250 663634208 663634247
    0x4060e0706050a0c260301050909030703050304020d02010c0c080304090c0507050a0f1b03051609092a091109120a030801031203060506070624031707051203070906 72
    0x810075180c1150a83e0060485410721a8030500c46151002140c003000c501840b04600c01060b040e148078000d80030350b05031081039500030300c0b5444440c1c5540d82e034080c1010042c0003030344c108006801401e110245824144c81810000c8041f129a61440c0f4000360b203800050045e400404c04000c903100c18002c41702280c206003000d500e01201d581782e0030b803070b0240010054509101e5031409000c02050380203c3d100c410480384d40d948100e032a45042d503243c4030a40c030781c1000d840703104c0000b0401141d244120b4042550000d1100c008101c0034080608440e0040848080c03205075072000507041440e030041d0303002403004410703617a52404168200840321400d80e8440131142c0c86514800002500040e280d0b040d03903000400311f200aa40c8130000c0300030304a9904000d411810100300c420400c030071600a070f40051a5a15501140704020800c144100c0c054800030b070621030380c000d504808010000041c40c000c3c0c000c200303803a41203922b0321341280954420385840c40080c81501040254590000d5100594a9111003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 663636708 1250 663635458 663635473
    0xf07021c0207091112090a03090605030112020d0203010b041a03150105060a050903191209290304060902030102041707080109030e0103020307030f2301050306071403090a0506040b04060e 82
    0x80250755000d83d00940ca8002d07621510000741d20922000d0740c040c1080744a080301316150404811340c9443c4c6040044000c03440c2c8410100e0000c1c010b01c06d4a06860383c40c03034900c0d03c215842d000c00181000344001603825560b1101d4000703e40e01d69000d400d1500741642404004d4034000380034103180c810104c1d00c0940d02c03160107006001d036654001c01c640b42058107151541d140e0b41070381e00090804042c490048540481d284900d0b00708a680304006000340c1030b035160305c0b40c025595800c00071681d4811208844030300382d00c990701040d01491406550460b02604002941d54090360200c2e00f2640290011510242d9618000c0d002820070072004010b000c1c0032009102088076a60090303c02c0140000c9a414550040000340d0124860b40c01014104e203407010500116402d0151512441c0031168800c40160402c0e001080b136040002c3c5480c0034050580e9501401000e011400c030b807a800c043c1138689503004090900f400315204100460095003e401d0f101d10a09091605c0c0088444e1000e0542d0b03241c00005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 663637958 1250 663636708 663636763
    0x213140c071403040e331207030206030c090a090e0a062f04050102011d0706050703050706050124030506030c010f02010f020d09020411071203090c05090f0702 70
    0x128503800221220409840c0c80c07040ca03040706100c0c0203106003060740c0301c04034000994020881d0000d005825111071107000c0c6a0248a8401107201c2c200714001c1011400d15001039401d1840c1100140b0141800381c2d003105071658001080e55109032503d103604080455444d032949401440b60001300300c4801d0810600b04403240281c0c951840101c003412282e9500e050b04003949d822440f10307031003075840c4408041081012001a150303810900401d40158070300a80ca00240f034401c10700754000541b090003080c41c02c0c68420121030692145074110f04002080c08480700061085c00b4140c081c00c0702c240f01c050142e80d42005141802d201003540001c15040100307004454801064014500700c007803a001410368500340301a401b510000c01e0f40f03030a15200144040080110341d20140355180708980601c801c08540c560390406001c2d40c90054683d210b254601e081c25402584005580c5100b80000b0542e544c0d280e001a6a5640884c0c1021626801e18104540741c1d50501c0b400c0801c00c0c8041e500000d018001c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 663639208 1250 663637958 663637991
    0x612040b04140610030b09070506030c0d09150204030b0c0f0316020f1504020f06030132060f0a0924050f0c0d02070617010e040f2105070213 62
    0x14002810321566000441c06015020082071080d06101d0100d0302941000c40b0241c0d1140118403040d11010504004210349100110781401102d900804190440e12600c42103141b940c0b1403885290351640d90035540d00094800c1204145d2400c88103c0140c8a52840c100001003100c02000d618210b40b0404c02081c00d10881c00c140ea0f00b00f11060301101c50782d20905e20507031520003240302c54841446848c0700321a8440320030380c00a114901c04d56030b4210351180c0e0030500c41d81c2d010078000d810940054801401c54440120b111a03000c084501c9484003140802000c20071540c00307841200300c818000644000e0103604614010010074080c0c0d00e01641d008805440f007584110500b80d48104540025001450b01c1e40d50155500401c00c101030303540311041880080c0d40c80b003142c401e088c04204010a20060000d4804400f4102c600d040030344c0035980e03100c0e5285420b400000300c0c101c0302d154140032a040706e27140304440300320304032601d48601d65200d03000d00410808840d2510380c03040c00da041c560850b8521003003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 663640458 1250 663639208 663639211
    0xb09010b040332030c011109010e090702100515040c0212090f0a03020604260304080a031b051c02010e16060813120c02040f0b0a0b0a0e060d06030b060612 68
    0x1064065216041d1a401400c0b030b61280d840b103028800361040c82580142004c00200101c04000f002008103030003500d45482107014502c03409010034100c1c000c0da685410f00c0708100d540328600b44140d90f5000c04049082089036404d84400c04040e880303004811023030070705210b0040d001c40b0328001000c2c001d440410700d000d00d204189081c3e00a00b080d9400903819110025800059603000300095140c54860102c0c1100811403800d130b8801840701c0c42041c200c1100881210140c541010140500b1955030310140c9443c00041a2071350012100b0030414046801409290b0310502300c001c481c083c002d1500002400e485c0005056900354115442480000134040c501400b1501d00b82454102d0f41d940840540d20720b841c818000d44039a0080700700d022120380c40210000002e100b141c0070002407940c6105030048804024005400c1076080f001440482c078100c024000c040c3d02d80c680280350202c45008034000390060010250403e456000620802c10b1011005134803001c00d640590501c0c5601c0c1c48404800d90 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 663641708 1250 663640458 663640463
    0x50a081603060f0e010221011217070213050907081c1e03090b01060e04050a020306060730020616140f0706091a100f06050d022a030d0b09010b0403 65
    0x3c2e103109552034902c00790030048420384144021034a50314034285120300003000b052950501c989440c00403540c895040181080180c000c0f1560031b100451405030025035001110580c0e00c1019158100c544800038000c16200f06042000783c5415486d081c2c40318900540c00f00300e542e044050015207100d8a078806402e05105004c40d600e54440940e8050690062811140241c00d100d4110300104155030042c1d406007107180140e40400483d070380c1103070b0041280810b0390800c2e485a0100708003400308400c1e100701c90010a01442f41000c01c81e8160035450074103a50360821000d038100d8010001c000e840e111038013020078024182501082d03407004c0d14080f1481445019800b41401044100c04d00c404c5900410900f9402060200c081d040c140c0c903a03074038150032903245501007a4000301040e803507540c14002d4201ca1b8151540b904041c00c41003540040d40042409010300c88405400d030030316003a0441c460035241c003a00d010b10398440c0f21540c050151040b280f20140152001001080340c810b04c48210b908494 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 663642958 1250 663641708 663641711
    0xa0905090a030c140f03041a091f030b03071202032b1b15020415020a080307030e03090a060309050609010c08010302010809160b040f06030b060706020a170f01050a08160306 76
    0x700d8503000e107014104144d8075105119040b034108000c0d200000401c143c0c0c0341c0c032500208126080c4400c020501c10020320300d0b0410307540d49050412412040361510341d48024140440c48442c00340119281500c0c5600041c0120300260216055080910444074440110342001400b40030503040b00c0700c032102c0c441e5001c00708031141d511241080c2d5115850040994008400c061300c070800602500a0f4109000d12004214000d95415100f0300020b501408290f1044403613043d59184001500200000d0700f5881550000704003c24013a991810040054a91600c0000d8203040f54100b552404000502c4042c9030f13854003108000e0540c016509a046030340c2403814181c00d0340c40da0501c6080c003050842c100b19042104070041001e8101d0400381083e110b8a41c02219403568560040f800d8484600105410140800c4900085456a00207100001c4141051800413420304000507121900700e4a00b40c40d0300c0d0110040c8035914080030114001c28800c402440c505144841034000036031140320007011345 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 663644208 1250 663642958 663642977
    0x5030a0201052a0a03110d0909020f0405060c0106060e030613021009051008040219240e06161106030105030613170a02010e01141603110f04140a0905090a03 69
    0x1000740c1c143c00140450860358290060303030070184499543e061408100d0200391304c40e5841400700e05c001020303074040007a50f4030f9800e16071614004c00000d41c000080400214420000450141c0390b5400401268901030000540546001c17401050b0400341041070303210390401c0041c46481c504015851404079011252070700130100c445000d48000086070b11568001c045083c0d1071810b69007241c41e0503c04c500903901c00030050400444810781400c9402180d4400b810480b64492801000010700c0404075181131082540c1044400502d0035044040b01c4000f049100e02c5036000c2160844c4080c4281905a41d00c9086505203c0000d07210800141040c007007607510410305040c8042c0e44045051304030050207a990701c008408001780681442c118083c103a600341b8400f5103181032100f05081c1329081545a410b400300341c00400310b000c3c04803a01c07020f14002003030000d8030300841607400a000030858002e25804600c000000d1180c420403c0c1d01100005107001e040007408900401c010900e1a0b042c901034050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 663645458 1250 663644208 663644227
    0xa1d0619050d110402130b03060f01020d02280501050f0a0b04050705090609040f0f0e1513080a03140711010c09050109090b0d080c07061d06190e0d030e0f060405030a020105 76
    0x74010906e42c003002c0701c607039180003503005040402140114004d60301c0440d04a851001640d59440ea607040b540107a218450010001c2d20010007500d81e150900702a506021440e1111825500300340c5005840305030b10014000c0011080c4a6140010300c01e0750213001c1031400d8130014016000e001a958060000010080d03011340d1340c0d40c0241c0c02c01c0724524003003007410f100c564a40c0040c130540b01203282a101c2d1241d03c10807140404c503110710940784103110078207042d926a928156600b08a451205160f1592000050540303030010a030b11807107250382c40000e012801c003102400d44820202102c240303c0301c003500340701d680da01001502c00d856801d41c000c1056419800801c2c00107101003000b60240c10080380384e006008001c600700040302c0082d0350751a840404c1c00031511030260141c1361a03070f004404202000c503003120480100d1403200e040c00c20001814039100802d00c0c0d0004680105c0004041294800140c42c020315130114074030702556541c0c02c0074240b40c0805e50320b022044000c0d05201002ca008401d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 663646708 1250 663645458 663645461
    0x12080f030426090a0902070c0b07031713020a0e06011d030a0605040c1e0b0901120b0d0b040c0603090c3005100b010c0f0308060a1d0619050d1104 64
    0x2d210b0101680e400c40b85000000200ca0303000f0034a264890103644100190070310042c0203449803140c2100f6a150f40500e829516170017a481030100720148887c5025150080c04980b41030b510074100c0701d031032074000000c034410025580c3e0140c00c0000b580016006002072079903c0911040790344580104401e444002500280c5407a0015100418450424042204008241441104480c40c1c900001507000140da0b008140d40140d0184103031402003400119241e62144c002c41d2440f0080741000540c0032000e4001c030307410101c0443d0907514540c2c0700d81400f0411420340100d030003e20051500b00001d8405645a4a50340d41034030a003a034685490403c10440782083c03401041c0228140307811110700455203850740d1070394a203a100c400b00d00d01c2c05880c04150350096140307131443c982c06550101c0b908900e40e400d8401d08001741100b42c03c1078003d1400b00b00a0703441c0000805041448013410340d41d107041070401540d541220040d05a801ca1000f04028980303807034a600f808903a004200c80c00b032181d403202150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 663647958 1250 663646708 663646733
    0x203070e090712150f060c0201121e020409050f090d02031e0c0607090e06180412030b1c0c05030a021f0507050d112407030f090804081612080f0304 65
    0x21456450041000200003030b00c0c0303160040368400031700b020a13180d0b42c0c2020b46030400c081a010780401d641214001c100300c0d640e4400c924062a482c60a0513400f64098143d0032030300315030040d0f40f8103580e40c414001210800b0030b03c5580115410010091140794640081d00c0f4040c1c03000c2401c15909034126002009204402d40f51280c02c41c20894581d864880c40041c80801b0034800d07000c030820080b0204203c0c1c109066801c0e10b0f100011684401512507568958409104041850405d40d43d04401a900c1d41d4071207811903080e14403181d00b81d10b041a0305145401291a82c03003103101c1e500030112000140c4820f0400307140081c104000140b50480c01509aa09224500b002015400740b0040d61010b11782103020064820284405c0340d100700c844026040c10700c44812045442440c2c5240050b000701e00c641c00042034490300f65004544411590388802c1280c100380c0013203140e0740102e20740101c11900c0c03040641c024620300700f850143c0e0019483d80400340c031071301076003201000f000800102840428030001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 663649208 1250 663647958 663647987
    0xf090301140405160609150e01171005030d1706041805060c181e060904020706060b09032a0135090106170304090504061b050702130203070e0907 64
    0x44124542407500e2601ca80300d5030301081d140c00c4c2940e00494000e100742101d6040e9107802c0300044400800c06025204160b101c400c2a041000103400c5101d540304001400780aa2a030001d0039080340d080008045c10120900710000070018968011100c01c00a0080d10341c002909a80024148400242c011410035680101030070610071074040c401511000c000400c1e18488617103051404181c1d020800440310000c103c0d00f0030909046280c1aa18079040c40282a4184002d2005143c151243d668009407400c5074803031545200042601c00351401d05000c64002c441c401004601c00c0107400090010034002c0c198507504000401c4007140c20040703180c5044014132500103034000305402c10051407c010104445c0390038554205140014201010000b5000982818018604060070804010300400c0010320075650641c8810018012145040000c0c217024880d030b0350980c0d10000c900610080500c0013419a07116441001000701041d4044c0c1217440d070140489900b4400d440e00c070000c40b8001c100c1c8045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 663650458 1250 663649208 663649241
    0x10306050a1506020d08010909020d150b1903050d08010f090c1209060f0b01051c02161421070b0705090f063903310e0a0f0509030f090301 61
    0x100303d8a800150300490145982e54142030b41c0e8071961102d09441001d2002508030313a0200c005400100c48807080401c07038034041400562140001c0c001440d0750840055143e0400c0d010000b402803000034407105210800d9030905052070351411000d0303913002500d84a408001940c40400508083c86420b46502070160001c0c2440fa06206041030401002407014058450780781009040030340d40070380262842d10200c4c045001c0d402c49640d607580b01070340c490030f130010703a101042c3da100000494540b000d05100080d50003c207405200741c640000c030a058440419128041400032100103501d4420840e0300031101d00c1d0040e1601c1d805008101500800c01c18260700440100340d038820b41d2050700724170020341030b4280c104441038189581d8000707501d82d21880d80c8183c0c0040002c0860200903280801000b01000364003c1e41201850b085aa8503415800c2800e1005044050149900d0940150031011080345010000c0781800c442103079907807042c220b03090012030010862214540d420344c818100f01800144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 663651708 1250 663650458 663650501
    0x1101270c09060e0612010e1e0a12080103031206050d030c1a1f060302090904020d15140a1a030a020907120f06060f1d010e0409060c0f0e1503010306050a 67
    0x2000d4007140c030111135850240000e1159503c15600c1400740c4034000450ba07000d4508401011180c3ca03034204601412405845001c1c0b02d100081c401c41060700310030f4881d40d10108154150700d001454440b1403101649864180030007070029035a1000a04106e071751509120034950a685804407003095080b101810359143c003010452808010488201c0010b40d0500c10360010341c403040241c3c12805000825504011500d0002e001400c0450003501401c0c090040c00100f5045450400d054403d801650f020401c410428400780d20001d0061800c0003030b00c024600c0d10507a004010a0703882041c0040a0701c104208000320700d000d801150100c800054509092242180821818025101d01d00c124800511803c0d50146028810641140040803401c121030f000040d91004440d41c485004159078020358a09903040001d40603c503108003042551940c0300200c0b40e403a4003610501e9001e043c0f5015004281d005400344c000e04040b40d0549502102c000784035110485078900401540f0300039078840b142c890 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 663652958 1250 663651708 663651719
    0x50708062a0f31080f01090f1103070512030c01050c04080d0f0908030703050301050a090501050307060f1e020123011a0f04090c170c040311060705012a1101270c0906 73
    0x1058082a1201340c1c00b01da02c0303110580811030881c1d014141c0980000c00421540c2e0000f10a00c000e1900141c0080855a819403210001501c83e0000c06003040d8540c03002032100042c04080c00354a52100c01040d4250034076181270036140d101c21000b03400e09d04106450303d031400414000c00c0702e54054800d980c226134540340c85140160880e8400e0041c10310038442c4c4030780000c00700e8007805554140d48018010b00380300c81c503040094510030406103281c02408040100c40100e002c3c0941124402000da5001052488209003100e1000c070001403100ca11411410060221009a0066501c1080401400340c4e88d8840c00d82c8031b601078001c0da04014072480c109910b0b64540c6910610b540034002c005d407151907c940320201d41c20158491b51000410415501d20400868a000360142076640c0c0250000b02e4803200d0001d060745c4ae80e442c40b4a181e40d11400c4400d0000b0342c2d0784007691a00083c80f1070020480c5d0b0900407a402c4036440f0100041c55900b01541280c1e0811500005030310041920890a020054850 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 663654208 1250 663652958 663653047
    0x20d0312060b1b070911040e090114100918020303091c0507090b0901060507050705090c0c0106061d0901034101021b061003080d09050708062a0f 64
    0x54452403e5119100010452a80621030342c140826140d1440f840d00f40392015100d4281e4000700211815503907100108000721030441d0081c07184400d001210001400c2c000748204546151992030903da08010102e401a140002140e14054007200c00b91818411002c1440e03c1c905000c8008219008810001920600d84c1e0000051000b04850295541c0e8071118201c1c2c5074016041c01529980c440f20080090382044c0141c240c01c031040941591810035904c40203802d41d004c682c81080003c008042043c0c00d015511070b900d064680c2201c24903c45d5140d500d45484d0050001081c0c02a0811500306016602d00030601103130ba440441040c2a8081403110716a000350400705007007400d0400047e2240c110400402d495100d0f0580058480c8201c0c216110b05200f600f20b070400c82c03006a520300203e0302150b010044d040040480300c0090000d80741c6a044030740301620a108802d00703d20700e1210818140419030580340d03202c21307407500183c0310b0014010048450400f103400248102c03080f04c01c44090b0702923 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 663655458 1250 663654208 663654247
    0x718060804020109260a060f1d2a030a0f0507050d02031c0c0b070c0b0106050705030a0e04020f3402060a030b04060e090a050607080601050418140f150102030403020d0312060b 77
    0x1204401c11803000600409542102c200000c0c5030243c002d01c1c4442b1200030f034031003800c0c00300d1412080e205a40712800e011a141400311001601c0c440785041c2c614041000401003c0003030441910101c5288200790b0120750703602d1007080140824142000c0f41d418051041e24400b00c03c0d0b420107644071107810480005048845802001c0c0c600700840d00012481e94045d004568201d03074403000075880c0501034a0121440c004c50b401da035503c103400b04100000c80c0c1341e10025080001e07549098031503420102211460402c54010002c601c4002106108003503034400c020348580310b6030b034100031640020b660005002042d8903042000b0a200307100c14460700d100c00003000c01d4581d01c80c004540c460384941409682000c42112003500142007000140500205940d1050000003015004908400240341c1d02640d11400c0303c0b4403c40b01d8424040001d2400142c6540d540460b00303002441c6482e0858002c580c1e0541030002c0a018040418900745045c00154860070092982c000855120f003005c07400020740060 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 663656708 1250 663655458 663655481
    0x5060403380f010501080403050d0b19081f0b060a18030f0b04060b0d0c0b0a12020406050304050d0c0807061e090501020c0106050906030604140f060718060804020109260a06 76
    0x40420000c03404c0d50264102078081c64144c5c40302400e0280e000c0d104006400c0c2105880d4002800d00201400d204001c42c910002e080030001418440d0404400200c81c00300254043d90045d08000102c50551038174812115030020614101042c2500c2148801207201151303c02080c4040c1e40c0054400e104582c0c7c1c1103801203116550610900301050100007600c8100304010b416040d050300c080003640c21000051070308020900348402600f503d40808022038000354072120100d4000801c020802c0400c2c410311042a00034102065580360680f00e606240c021500c006110b641e50b90044189210300307023005805410029001d20500c01c461509070702035004400031640940c01c1034400f250900e40940c001e44140c0018005014030740c3d07a5150b8000c0c4d08028484000c6600400c4da1740100b402d02880840e1240700e15444414080d0012200900c050007585d00200c00c0140c00303820300c40181c0e80008070108441071008090110002165100803150451480d8415803103542c400008000c020b4101a41c0c084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 663657958 1250 663656708 663656731
    0x3e0a140c0d08040b0a0b1020031908061813030903150906061d060423040804050117071b020406090c030b0f01050306010c060c0e0d1505060a0506040338 67
    0x1c444898000c103a5020044450f0f00c1055111800c85061246000d80d4840398604c000340c488155048c4030b07504550080915140e5600d00c243c002100700c3e0000252604100d0030b42e840c4c10710310b034086042c0219500c041e1811401d904680170740c800341031160314010091078200317030726000110445402d00c004004100c400c4131309500b0f0510002d040744509441c0c10340000c44804404040e078403901000010034031a100000500c03000504000390034004520184114070a0905954032802c002c009096140c10106c0c421801c54800200f10701c130341d8030207026180b011080070001415106440024050007490700440419840c082c607191000381c0c075411100040c01f00740c0f0300785c440585040c01110144400c890050100f0068442a00000c029a0016160014902e0100e0500c03126030005640c0118000d001c1d202c2e101d4104c3c0c0343c40a95030520410350000c2c400c40340034050300d02e403501041107801a44009001d48490040c041040303078590b02004c142400c00d0805080e01c1094044464120f00300303541030414074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 663659208 1250 663657958 663657961
    0x720070521071703090d1406010e09060a060f0e0414032209060b1c02040801110d0b0a0e1b0405040e07170a0209040809030a063e0a140c0d08040b 64
    0x142d0010b50900544000b5102551170444d034041404075000909104845080120340b01006541c0305012440c068904281000a5810179003001440c0c281c0c0501a801200c1c5400c41c104008035200b55002d08079055021280d2741d950b80c2d410804251004190580024040020f1242d000161450880c1c0011403000e2071300e4480e61075180c114216002030040540d9810300b0031450100002c10001202d41130003000f000351600352900c00050030b42c2c80030141401511400308400d088080c0c031b805000d280400584055031054509a05251070850151a1415020b00d010480e100c0e00e240e6001c54000d481c0c0170b40203001c640d18400c08541d80708114850a021010f5140000040341d00210f54040100c1c0c0080024041c0c1d11652aa11807030780c8038044495051040f4210314001403068091600c983c0b80501301c00c6000f4040415088541d80c0103402801d02e4450049001170481000e03042d501c290326103151801c491184100c41e00254030880d160700a4600c201034a01d0403003a44030040900c1280b0800b10038215 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 663660458 1250 663659208 663659219
    0xd0e0105100807180207050a060e010b0108220308101e060f080c030a020904021c1406061e0a170a06060215130b061c0503040504050609072007052107 66
    0x142c941d6800313140307040d050071803251001a2154001e095900e0141090358240f0b00700340e58000c11070364841664000c2da51071b08841d214a6810a000c3c1d0345c01003003207001942440e860f40c45a501503001080003428040d480000c2031285085403400c902820b0750111201c441d0106402c429160b0009118070800a111a0442c42c41e65114a407814050810000100e08648651002d900a508008203080d00303e98240284041e044044466140c5001a50000a240305c4000e8406010b014020001c80c040c84040002030540012200300110383c452081a0944402c40c050007121220000010114440070000034410003143c0d5a201c001226070340d07000c482c600aa41358445480c507004a51030032150300c40360380700c001245164402300e61010004005258600c69003404140100001906403807503480401c05122a00703091044a4216104032041000b902e8801002409020910401849040715800140036424200001d1000c2d01e001004210241003015000c0c46030108444900c4051240c103000194 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 663661708 1250 663660458 663660463
    0x910050304060b0a081906020f030a0203040c210305090a050603090f061e071d0a0f03020406080a082d030703050402030d09030819020c180103030206010f050906150d0e01051008 78
    0x100e520010140c0388400e00051280c006c52150001615100d0b000c1042d600d000c840e4000071441900c40d0b410058a038109410000301c0e050854110117040408049441151088203012094555040c94407540d98200400441c3c082e210650041e03030000303000700500410041c04100460224941000c03038220307684540003040c0180e021403403004102ea400700401c7d40d2511507440840c20a078081200d40c03551410a002c2044100d03190b008a542201d8520140114078260040c0002410410020180c1e1404d0382c030360004600c500d5183d104c0301c41000c0c0440201c0c1130820034141983c0120381000c2d86926012101030040e19040f5402c0384203004210200c03070701901a401c0b81003038a0300891810f084c00030500076003100d48010058070043d40300c0c1c00004000c17603079009445d054141c42c001e011a61545075185c040d1826804cc1c11800311541d02c4007080c0182d48130f40d0041940320008603a5400c00d61002a1210005c0c440c00400041d13050030001000c1e0b525205401250180d0400d81c0103a143c19546e014254 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 663662958 1250 663661708 663661729
    0x501030803011d0c0d0c020c15090103060f080d0c050f07060c0b060102010203240a08060a0204140a0312080a11130f08010c0c020f0121061401030b030606150910050304060b 76
    0x40c0e442505201e1a21403141729440000707030b0f0060f0f0040320b40703144424000450303409810608038108500082c403402c055900d401540300900c2c56072094184503041c0294961502c140e008804100f054480003881031140c01c108855010030240d0586050071345550b4000c2503281542002e07107151002001250155105108482c490405515034210389818401c44010040411280a07403000342c0780d1001c06c12400501801d800380075000c0c4c0041c0d80da03280240e54400b1003c2480005d06c40c0c00031580170000300780c00c008003c07107012a43c942202940e6403004120010302e550710502125076400714459000d485d14041c43d80c1645c042e003110200740d0341c2d50344e103643c2a29441410400082e1404070410010700703100e44000e0201405040c012031010b840300312648080003120003000c80903140d2804100000c150111002c01410a02e018803140c1d02e020007080d81e03100041d00e020700031001141000703003081101c01500d4942d0030080404080034030864000704683c000751020754010f440c040c2e181c80c0328076140c100788 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 663664208 1250 663662958 663662971
    0x301060e070c1122091b0803070623010b0c01110403030e040609020423060c1203041209050a060e030c0a090605040f06030203060c0a030f020a0801170607080c090a090501030803011d 80
    0x64000316459808101616100808a4000041030b50311b11380240c001c0740503009862500d004607160030807414aa400d484d03041001701c107540e44403862215110604035866040d148144031853717585040702c1d4441d0050100c000401d030440c0c0c000c280030080550011070b84140c8c6404072801e0000b40d41b20f00e0703528102d10039849641c9441c0d40c0e00d940f141c4c5803090859052000d440003400c1d10b0501480c1e0501c6800e00785000c500c070713054101c00404c200800400c110340140c815000e01c0c100d410319003446c020591a1540e4013172075090107070908840e4809c0c0d030100011800420051714000417940e5800b00400503204a01075a0710840c02c103c6181e52185661180600701c9800900400300d5880f80da400760b03540d81c00360405004050711060390b01d41c1480180002d041060090762000b500d0361502800c6019205400803800c2d054001e0030a02840a5102c06104d0b080400c203441300f0f80c0c0d2400c000024000c03049950007030091504000000041c011144084c4d070413035944001c80035080c0e140443c030342901501110130 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 663665458 1250 663664208 663664249
    0x10271806050306070e0f041d0f01090b130204200c0c0f13050c0d1b0809060f18032107020c010507050604060f0b04050f090c060406021b0301060e070c11 67
    0x2d0201031113005e22650074000908500311a5540b580031609886850312440c8010807009882400600b00b002810400d401e079038020002c2041594a00500c003101070880034240d400c2171025015035556a2003040a140c0300c003d0b030501c010591280524940140600f0401da0042d02216030306414003c100303541605008000719480f4041c0300da20310080070054024611801d06008181b420140d034410784412106a2201e00d46800081a0090103607000500c1c015031904506c05011010508140242d048070b202201d10040130600082d007407541c0183d513030f0031f191800300c507400169000668696038000d51442d420303940b40c0d103810001501c4601c5826070080c50f03a400301f000140403900507480012070720417440001c141400583c001806031542510344c0c4100d044d088043c080740900401000000d20350589101e03082c10b181420103901c0b29003c03240c40344c5111030447c00e10740d50f54003948030740041d0840d45070031900c6003082c83c0002c1410700c03820700c111100755a2035412001841e14081c0c2e0f0203e814803191 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 663666708 1250 663665458 663665461
    0xb07080a0b0109090c092c0604060608130203030d0c170106081e1b04080102090a06080108031206060c030a020a0c0902070b0106050711060f12060406030503030610271806050306 78
    0x107668001d01c0c17680c210100700b00d546100802c0c202100301c56800801c0340c80401051410752889103d100f1400548102e00c01d0345010020041030750400d0345664052500007003281c140700607001082c11403040361a2a00d01c14035102e10040240c1d00046407a401c07212110b042c0205a8982c182a900c9803c29552001812030840b4500c0c200404079900a6101e40b0301c1034070a001c010340119000712070b0003580145003030365001b00e078800c441d081001c420001460580340404c1c00354903081420303032640710b9442c6180240c29108001000b075190350044a030084a58800c8a585568910b402911281118800c40c0c52900214002815580500030f9500352a00219007050503407904200340c1d01d035803182c03000320f514540342040c07864260340c0c24014200072080791444580d5a040003803001c00b0710000500d0b461042c8d150440500c0420000401d50703a0160003034640080d12514824199922601100340c0c50701d036040e4110102070098801d200008452100c02e020311080d490064032004d4031b18601941d03425500010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 663667958 1250 663666708 663666719
    0x150c0c011503170a09270c0c111311030c12010b1315020a120203040501020c180a111c0f0e030a0804110d080f070c29091c0b07080a0b0109 61
    0x100102404c0341c07141080141d0036078810b01c1080103101d08042e41300001c0d030a0001e88040d003d034041c244200fa80f41c540113610344800c1e66004417500248580b14004c50384081d26540b98041503000c043e14241304101e094980c5023101c10400c0b00e131722541c40c100025010320700014003010101c042e50001a00c4910031140325080102c401400040654000708601c1503003d144003040101c0516a41e0301c0d405c2e4013540d9501c2c00c16001921703003444c200f105400f03030b02002c88202411041c25596a0464074544011408001c0381c03411404a018080c1820034100044130210314804055000280840c1594406d0202803001103101c0e440340644a105400705505200150020300903122140042da00109101c0010880b07881c5c051103a0001002000c11600001e00340041c418220b11445c0104114400450f40c03d8501690245000b80b10350054046a00451449a03564466000d2100140c0c4030340210b1042c810741c00c05d01c60065081c5c4005011802c0280840c0c20922a030081d081c1d8001c040c0c5896800c3c80c90003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 663669064 1106 663667958 663668003
    0x9040b06041d0703061d10060e060d0803070c0204020c0a0606030c0b03041707050a06020d1e0c0912062309010c0f0e040e150c0c011503 60
    0x11400080703010000f0000192907020401088001403e00d61750b400001103442c400940c01843d000c8088118aa40508100e1760300c614842d5042d158481030040002000300050050001040081c51650040385982171151000c0e00052030185541c0c1103a09205000b2002c60344161210020011321920021100140284c1c01500d031450509035078502c00c00d10311035003c0c400f022004c1003c030113201c0184200c4024640103103096503038805006011000300340e02c1a5848130070321107044050460040c0d100300d14002000d5101e0b21856402c01080d68080310b0702c1d420840342117444009070504060702640940d02c03100c1c40303c0825010b06100c01640d09440881c48510100002884031403107440c0e121590040c2c091040e50005144086210140e0504c080f035007031b00340b01903002414000403a094900403c000900b40c0001c00c40d02a060300301c4503003043c80d440050403200000c0c44010044026 = true := by decide +kernel

theorem cover : BRFrame.Cov 663489208 663669064 := by
  have h0 := BRFrame.cov_init 663489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 663489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 663489208 ≤ n) (h2 : n < 663669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
