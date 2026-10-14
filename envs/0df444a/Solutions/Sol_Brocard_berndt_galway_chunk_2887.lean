-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2887
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:02:03.014835+00:00
-- url     : https://prove2.me/submissions/9f171e57-60b7-4c59-a62d-0a5ea9410103

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 519064748 ≤ n < 519244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 519065998 1250 519064748 519064769
    0x61416021204140121050a06080a020306010302120c0a0315200a0f050c030a09030203060a11220509180c0d02060a03321e1003030f0e0406080303070801 67
    0x10100002400d00943c400c0c400f07810040010b824840c0d006556405803c0200e40030f10440e8050003107030f1001800151920781d522807a1102c00b1420950000e11604d0702c60300103004025981c0b96508100e03440c030386004109442e0040c020400340a8031081518000341d403142901c5400070458180240880e41441c0d403090382d004400d403a00d240545840300300d50050500c2d107048032454a11900c180c489214907051541244030018006126503488200b800549101f1019910a0780300c1003469020350700d00d101c10401c0a0010000d0b008400c00c0e20014035141003403520003200096039000011465038080f241c3e80d10880f5410369442500009010540030102c080b615054040b0003074000c1483e40c000c0d0507001041c1940c5404104070034a0340b8018005030203803040380d05603850702c00c2e50303080007050151960303040d19510403a030721341989011020f5413117040003806409805146850442d000c1841051180c240400c0384100140c5c0c1d203c600610000d070100c0f0006513640d060200d001009280140d0280b02244c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 519067248 1250 519065998 519066013
    0x3070305011a0402270105120702010507030c02070518040c030602120a0b01030c0923030609070f12030509090c0706180201020c090403020303180705040204080d140403020307170a06141602 83
    0x17402c0b01c0c24030800c00f2511400c0540050003e40140d4881c0f045448034a03084011004010185a0540003584281010350f4240031000f40040142e83e0703102507015056104511129010a0b009009040d640c00b82c055101141c2d072381d5803038862504036440f401c14035240002072000c0024400c0350340144500c1c1c42081c6020404544040c10080403000c190262506030090800e042c18215000003003407440c0003004054074200e0900300c2c180c0b079481040b84649071074507134100c0b4002022007240140c207507540c0d0503894244c54a00240100821061b00402c41040f22030148450310100d0210f01c9442c0c0300b0b005031901c05c10070094600019240007041c0d100c940c8503000100070403000075400700903640c100c0340c03c00000c0c0851800314440c600740441e540002c4c2c1c00510200d0005204c10b07000848540f181482c2e11507080c2429502c001001512440c040a501580300e54000c0285903040417420a080150000361041d00105545440596400c05500c0404100304030a1101a17500c080616450351414002016030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 519068498 1250 519067248 519067267
    0x1906140a020a2406080d1205060604052b1a0a0203090a02010305060a211a070c150603080304050703060b010302070c05240703020f07090902180c0903070305011a0402 73
    0x4510300b48000030401e8600c2e045140c2d0400c040340c0700c24004104180240b140c180c4038141309a807009661441d00019150f0082002522814440d15010300c4000d4606840c3c0303820a01030141d214503141c0031080800c000c1040f00c8001200d01c0c1d1300c4005503c1034080302410001c41d0038111a44c480600740800c080d01c1042806034071040051080c4c0c09070f5080c03c3c04030b2250b0726038000174000c0840e0340c464007400c107854845c4101c1c0c540d001c5061060511405985100f4440c03080028004081151940040b030760b5043e860340418502d030000f401d181c00c128004988203803070b9650f0f09203640042e641240c0943c0040b0040c410010349004280c210a42841c0031400c00102da103c1d18a2a00c0382c1c82958065034402d00e40144d01040f4a04103080041d90264050b6107010a00d4002e5a03a008010800e03c1401030b0000401c0b02501070003a100c1c4260010f0101840b407508450450011101501400949108014a0425032400e103c40c100840c0510000035881101d0908030f0031018403c1007841c407a61040021a10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 519069748 1250 519068498 519068503
    0x60a050a0f06051309020604150206040507120c03030c151a10031e09080d050c12010f0501050f1315030b0f1507080304060e0109061a0405010b0a050f091906140a02 72
    0x4018413619000714010103940041082c92107150411000a03c4601000c1d00e03094002400e540a00d00c5041141d2501da0346940ca101c00c08443c0f68009e00b0071210050803c0440d01c1403038031450081c02a001c60b1600c880c5805900112074032989501031041c0c00b00d165a03650714001540500102103801d05001d00820b0059907960581c1e401c40e00c801c4513540742850400e002000c0e0945014007e012010840c1d800c005c41c1444007604008181e000320280316001261444181c40010121032060311668202912041802d145400010400700d20290300c100000d9452070340c0b100184540c0441e28002484410321091004039a1203201480c041c2d114401000d0892400c0e508a0324904d410080312030310382d12245005006804085a140502c0d828602c010061069079846014000314103408100352425040030701c820703128240309144040c5001e005601c0468090802004e02021a081462416240d0400900321204183e107103440c0e141c148505200c40303a00600703840300305c1071002c0e2410304003859010700a5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 519070998 1250 519069748 519069769
    0xf0907060507050c09011202150c06040b18101506050f090609010c0609050c0a060e1305070507060906020904060f03171b010203070807030b04020a0206180f060a050a0f0605 76
    0x104000c000a4042c00303015090107200102c0d81e009004070507650703403a8501518641104420b0344103031180c107941d40c0044119411a5480388054015200d583d40329240c0c2e0702d010b100102840304000b03c0a4203540f08000c18803142901d29409500010b442c00910010041d00045411900c2400001c10a000c402440d440650b090358100700c3d007603503907072850300b0040b54051038181780144002d00303111148040110108203c01c880f01c040c0d4000c001690341d110216121024007003a1904090401c406601c1101c054004551050081c1420f0346802155510502110310030102034a03031503808140b035166441c3c03034016040100245400144418216202c52b8507003181c298074880d1020001481416003a96204c218080e10301c894021034507840c107000003038410001100da07900028a03101440c4100d02d803e10a0303a81090041e0b0040c20342c1d80e03c44c200c085074410040d030020400c2c4a04c1c4240d004501c410032203240314510308040400d030343c01d0010680c402e4030040380c8002100c4d802d0020034840d51300c50b4200d00f03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 519072248 1250 519070998 519071009
    0xa080f01120f170c030409020702011b0218040201030b12030706060e07140c0718021207090f0b0f0903010603212115030c0f03030e0a050303070201050f190c05060f0907 74
    0x2240141c040c01c91500241301d85107a1516600000c07400080b903a4941d40989401c40c000c0e01e9162100e1725554407e65901c060181c0251310035035801341d410602110003480c1d40d00c5441814001000c801c0b5900148007000104524200c5074400110304040044900655000304101c5403403140504007a08060110700c540e95207104400c1c1c0115481411503400c01a1400030440428a2006014900e403c18080d43c014601c45444826900c04180c401c0d22885002c0b04495a40000c0c4241d14104000084c29230b100c06c0041103803501c20301807092036039001c2c8603001c0110b1003030903000b14112021820800c040d0440e05070b03906202c10186001d03144080e214880c541b0124024001803004080050011401041d4102a26450b078880020505c982c035450400242ca000703446015030401400104039005203030f802440d401d50030a1000b10010350069000e0118002500c118504110050642201a415005890300040c402400340414080c05005c8142c01103001440c3c902280b402101d05a0786050030b02c04c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 519073498 1250 519072248 519072263
    0x909070903080d02030f07020a0c14010509090a0504050609030a09050d021314060f041b0302090105120a0606140306091b1b070303110f100504170a080f01120f 70
    0x412591241100001859010755001d840e0100b84282c40001d405c203c8035956680440d80100e04140e00004000400b16842800b82040c80c0c14620800410702904520505101c000e020707008099540f071665512801c10b09200203001e16050070014640318001d0400000ba0300200b0000030010742c0605541c041d900d09a401c1d00742c8080510107c3c0083e500361411201c828581968004404c000c0480a03006800450b600148140310350100000c8608004203120308204002c151041e40340241c014284c0c2e0201410f08070300340303404090780400302041114103c0c80195560700911441d90800c540840c20b0419820341030961601394040f81c400702010303003500054003000412000488594003100d40d0f1b402d00320b1000746030503120300c4825600c035010301088000c00c00c081040f100710a0002005002e1440520003482c0e60360440074510003c0501074801d4810384020102890036103a004001c10100005079540c02d5540386c40c0388890710341803068000380d03807201c2280307481c0c40400c0dd00305070512455003281d41e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 519074748 1250 519073498 519073501
    0x4142b090b121f030501050f0105011d060706051b04030b04020907030203090c040506040e01020c1e030c190201030902040c17100821070c080321100b1815090301200909 74
    0x3030824849445a01c010170540c244400c101101d0301008170300341228400e807540c401882607440c26003404004001c00b560408070a01508000c00c0640d00701c203030413908068000c03048104440000d15954030903081610300042271b0061004504103070f0700c0c03154001900c1c50b0450843c146480d401e0b45a05444c1c41d281d01c1b850300c5002203244c0b41d88640c403484c655032144008554884040b40c031030780ca40c207400d031448030349098401400c2088040032013114201107010010300718400ea000c00400c030900640f4030a90415a5802c1e03108010307110f0748181c18000125440e80b818161451001d003991010050101c0c60900c003100e01003250f00c0001454010024201d51080c0140544a24040300b90298040141c00c5070850900002c003060080020600b07210302060b4a4001c12202200065640096402075800507500c0c0080000c00112005000807a40f44c040c0c028042c90a01d0000300c02c0c1c0e20107030441ca64a2000180804a490700b481001500809101c04002c6242c0c0054035078114003070f03040301a000d03210400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 519075998 1250 519074748 519074791
    0x150f090b070c051909020310090b040b031e030d0504030305010e09070806070c2409022d01140705070905010617041a0c0408060a0c1d030604142b090b12 67
    0x9130002810080c0c030b08544030301d0700010181c6221514461020040d00c0c2040d5200c880c103240c05070000300403001d0000c01d0090032142100ca0340340c0001360020131500043c4942c2d040e802440c003446000c2c0b40217540c0891a54100002d02100060140055100703510400c4100a500e0f0080740041d402200c5092580c04d00d000d5080550f1101c0080d141c0d40041d041c02c1c091810182980e9001c04034203402590040c02d464640000000d481100720464143c8401d0441110fa0a600c503040003050030428640a90034024a559144d02e00702164000052141c0c4800040c401d07035a2050f40c6010116904003110020b08003600c981e040111012900044090a540003401c014602001c5600a0202204441007494101109c00091420002e0791000403080010040f005030071410691180d000140680300f44d4440da41d48001c000b941100d9a44a40210842000808030303441c402c4034404c1c00302d6500c13110070003840b1005101448a802c0511803240502c0251526044100000d901141c00e140008003c0709c0780 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 519077248 1250 519075998 519076039
    0x1a04292d071d120303040b010b0421020f040e01051f0e060f0607080307020a110901030b0a0504110d030e0a1a0712051314040509061e10150f090b070c05 67
    0x10b0b0314150060082503286200310400801140705501030200110140d0301c0d030b00314110f94410340c40340142030202c00c2100c012000300001c0d104502031004201c10b0b0150b0b00c030b80115060341c1001e012111076940d40c00c10004e0b0401030810065100018882240c2810b0a090f00900c0503078000e40000d0080da191480241c00d070321220100d4000300d4204494544a141101e4003e60f100000501240c41300d66203003070440316007003031404181660b92100e01c9100c15a00e408409000741700041c8103031003d140c44901004e8940790042c43d034220754001c3d0307102c0b41c0100140d0107010b6030b5001039001b1940303544480303c156141c48000065440150780400d0b80c00c0714101e0b10f441200c6601896210381980580c0203400100070380f071140344c200071070b00644d01484580d840003001c94913658200d4030120300300c83d040c1941c48141128806c0941c0103c0e043d0074003460b25200d004c107005d03011100c1c40700c1020504000c0c07a901e040c1c0c0c1007034904008220715540c103450180715a5900210491500c1118040c2911505034141e05110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 519078498 1250 519077248 519077297
    0x305040203030f04030803071d01080114040f0c050408150103020a0b0706140a0209031b210f070602010b01080a0501060f1d030d020c0109060201091a04292d07 70
    0x410f80c5690f01d913030300c90030940340301e0b4003c3d0307035007008990840c503900042d030545c50009114000507180c01e142d581c0b80c0000824800d15101c10743d03030700960740c038592035042c82c0920442300e15207802d07911b050321181030803512072400011041e00c540c04402c50004000596031805100c0640c0c843d8841d1b1500e0384000d18002000d080d141b007a050303a007007101c0100f064029450340035080341c103403c804032489850010030401d00340300d4042c103058100401080c06403c801d40401402c024021007412650201c82044440782000346941240c40180d4544495843d950b0740200b4041d0826802c42080105503d440c8018042100303102c00c00c0300b801420300511700c0003001074441c80d030340700000780554131540c0c020380b00203445a11851005020441030800420000d20500c1400b40f0254800078060503001d103580e10b05221000103200b00c89145007041c5240b000c0a0000d82c807080c038206000c400d2403d0070f001c0aa020401e100c810040107070f207002009100d0094600f000c00707070040e842d0308009103d079a1a8452000700403c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 519079748 1250 519078498 519078517
    0x60e1203042006070b0c09030f0709020405041d0706030b060405040905060601030e0f0a02120a1b08070e040305160512120907151d030a06110a030b01030b10030504020303 75
    0x801200704400c0c481c1d0b40e54890914144052240c403020100720400446002d8164050074a904840000d10b00c034160200a1013241001011a40d20905000403203140000a07004411655004502000ba80c1854000e40c000034941c0d800311414480b40c082d0550b0b9404551007000c00300744d107e0080c201c81751a220100c80107440054000d1140c111726007441c239603c0c00162002400203291600c0c4207071821380810544401040c010140581b015181c08104100140c01451401c1e400381000580c0010000c41c501032084d07004d0300c0900b0616280011850801e1056800241180b4004c4200300001303500804a94072054015030f88200e03079a00d41007003403030b00766030154501e1843d00014a0600c440d102480d042d01c1196440c08a98025032158150030091a44120348400f10300d041c105c10403e4214804103a400c00c202900300e94451000d92070744000e484910380600807002000403c04203142e454040d0750323343c00003801c050220f88240b602098208111298001c10540d84002040455905004449030440d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 519080998 1250 519079748 519079783
    0x11a03070621020d1121070f050f130f030c050603010302060327100906062310030f050c040306051311040e01181a07020703022407151a1c060e 63
    0x88611003d0100759100781c1d2200a80810b603030207210b600f4400c6d0b0019202c3c00311a50341c403001420300310040e1090b402964081018040034040c08141c2c2503418804402802060000c000c1d442c51410701d0614038045030400c5008100400050015840300e5007100d400078018490081207040c0d28500c0076102c101c081001c8160300035040d01d034079400c0054110300d8080340540c00c02c221840e661582c3e082c030a0340601c0d4406050144883c44150352070558891125885241404104450b21000c0e482c1140ca045548840d4401701140510070301c101440740e030381e0100d096403c440f82e0381c000303840d07500c04c944c01d02c0c1d2110f00c40d58486030790340c44802d029000b500e80034000035076040502c0038030300d0004546545030030661013401b2080000b0302400c0c8001a40c03000c072600a0072031403501c591205030044810982c0401030740040200a80400100e048200c050405034601c00094411086800d81c92802d01d05004a44600a400880040c1c0044500041d00080e4002d0000954501c0380d8006418420803400d4100504c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 519082248 1250 519080998 519081011
    0x1314010c020d0e030a05060406091e260c070b090303070c0906031e1101050d0b060a0206040c1202132309010b01021e030a1d0a08011a03070621020d 65
    0x680000302c96100501d1611482c03580e005000606607100c0c15042e0180c10fa50000340440c0100712954005040c0500512803224032280c081c641100f644010342040301d88110018a0823810313440e481e030500401e200c60082d145009080501c00340e0301d10860003078042403140068048295035040003100d00299020103c0b0702040d507910007102c018901440103584c11544401c540130010440d49840b0b110f554400000c0c500d1590319001111160041e01120802a59502003408140e450001914105129500500c00ba282c1171906240c151001c0d0f01114010040b0540c2a00690b1100444a420fa8a4032400105008503080801101c0f40385002800994501c0c1d083c440c442c507064115690250003a0222400101034182c40b6414203419124103100b40c205000c800880c5100e401d807441d402c1c4042d10115800d03035040c2c0000e1380c03011341540002c0740c50395580d01d5002100903002245403491012805021030320714054010300030307d429250301c0322000780600c49031782050129810b640720080d142d401003081d07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 519083498 1250 519082248 519082271
    0x12160603020c2506032c0f0f120d09060b041e240312141911030c0a140a12211a01050a0c06090302071707030506131401 53
    0xe50015a484015010302030344201400000418000c5480d5500e80e8a1850f40c50000118003c10594005d98103696101042840d82e00c0c010390301030001d80d920740244c406940801c480da441c001070203070400801d070000d03540791f159440001c041e01c03040710b42508089a11062403800314001c2c5441011194024541088139989480c02e4400c41d000404d0b03007034104001c0d8a0b01030003444428003204c40700c010740c628020034000030b414510412000c058a007048541c0843c00341100603682c00a40d07188800c00e64000380401c05951052004203151501005940f80030050b1900c3c42d150390f56010f01030030703555510b4200b8142c000100705a8007802e41003c40701c03950b07a1088500a0051001d0380710702c1c240f00240c0d14158405070f29481120b6401600f2010003100c4070800c401900d00f074101114010912240841140205440c2d00a81075060312903400307000140d01708401c505107074101c0c104001c0507a01021081c4002800000c0340b50704140d036648105050300041c1740404a451a04680003800c1d401d0010083c0b2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 519084748 1250 519083498 519083501
    0x2d0e1215041211030306060d020c071403150411010c0f0b250503072c22050708130609111210050105032802010903080f0a0212070f0212160603 63
    0x2452040304000302c4201000c07000c542c0c9805031085900e0350f41040011819501c0c100c0014814403410300005030911082c44d140d2400c00c1c4035170b8800d003614665221f21801c82e103007e02246a40781c40c2c4052208060606840d46402050f5800341241403200042e548428021089010040254000c500b08028602460102c3c01c1d051010000180940d95007180122607001d0029248228a541d480d0034103500404800500d0345558581d465034034489881024442c1c0754030140841e944280c8100102487c1c0c0300c001c240071500c00901c04010406054244100c90b44a621581c00d52508003001141042140c10704c502d504046025640d4805d4040000911200000c030311102c207130f40c40031030401051380d2305c4e401c1c15107802c3d44c0040200d40a08058021011000c003501e080310060062401e40c1c5600d40341d80da02220350780241410101c20741d0100307400a2080e410411500300a1440003e1b90401d03001c3c1d40c904210405800c4024401c0c04040b1072402c81c1582044055080c20040040c1401d9a644500240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 519085998 1250 519084748 519084751
    0xb03090a0503040b19090e1315060605120a140c34020f010e060f0d15060203070c060e130e01150f0807050d030503011701020c0601030605072d0e1215 66
    0x1e40380c174200035440001d070700405848048500442c210801a038450300c10403001000355100b110050b000b1004200810140d1199801803c0c540c1c076400c0d0b03500204500e100c48a4402002000c0e418180b100c3c03da800341440d41c0550b0071041070200f16894124000459000898a41d01660340d138244114401e102001022140102c0e40291841c000e140007800044583c1e110002d942034110008201d40080420000b000340360702c0320600000104c41465080f01c5464440a41c000401070f84040b80d01130501040c0c003003800c01000241000d100d0101101c02041e0983c0124200b002400c4da91441641c80141c290802c0d0000c0c08256112651907441700616021224140580200751003162000301c1e45040c0a0004504103405d03494140c2103a29150880780480e02545031220695000d00031400c0c84130080205038042e40c4182004141032034140002800022243c81c40c0a02d40314041403480383c100310200c0e00070001124502402c5e40980c10000c0341d8202c00c4440e07109241e2095460b46002090f07003412a9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 519087248 1250 519085998 519086017
    0x403060903171b03060f0a0e01080f120301080a030311090d060507030627150b07120f211d24060108100509070c05010212180114010b03090a0503040b 66
    0x1080c1940310081001a07800054020f6104140100301190007850901c0188140000041079490343e1511400a488041400c1e40300003403a52040e41d90011900301800700304c62042c89103004900b9580752031090703503417124150005010b165490140c41c981c0c030046400c503440f4100c0600601d0b83c040b4585480b000401007140c454000130300c0c2c484042009140c101c1c01d52004560418800c80f184100e90b0700f4801440d0541c1c15880c000380c0740400107850b4140c03001604169009004110350031008c2c0380040c0c502400090044104401d10125038035014000d1020b2030301001d40e00d40001c2d55684440030355a000200c11107419184568801c5011508002d503808502e0085103030078480b00e40b40c1c04011b440c1d070581911003c1415007a1030062105003000800c45e64020782c94034080d110700900e500d441e400c90348458945a0b0701c85c80c540070840900c002c10490b1481d005110000c0194245c0303514402082e420601800324036440c000041820b51000700242c007035207508001582c3e520b0380c2c0da400324141d990000550 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 519088498 1250 519087248 519087287
    0xb03010c02070602100c051b0a051b0415030327081005010801060f0305060c03040302010b04061e05031c080411090f0708100e160c0c06020a05100507020706140403060903 75
    0x1070a0030f40203401501544a00b94907080e04104020301c544540d58a107003001c0b03850b1709c6032880d010040790701040381060708400c9020f6034802070308810600c0141d821000b801d040e01012050200002136000c107088100b40403e036503000f02403040800701045560b00d644400628800c00070040c5242e05254000b40c1205c0750072000f00030a994030500c00721151080e100281ca00e4120301c00041507030700c40070021039020b446880001440030450b00040c040301d91070b4002400080c148502d00070150842e041d6400904403c600510601715440600d51194000750200380c00c00c0740c110042410840c4001d005405800020701001043c500002040c504080072034000c000901003078046000107281c0f8a211099400c912a440100c0d6602e4a1030800c1d50b96101803901003140748101ca070007080f0302583c0303180601502e6010340318520160030081d14002c60f510803040e0305403401051100c1280c001904d001200c00904046a840c1c0d0381944042003805564001b41c01c0600f030825050405500680d280072240901c0e01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 519089748 1250 519088498 519088513
    0x813050c03031c27020d030201060504020403081209060906130f060f0b210601050f18010e0106020f01020405030c1c0b010b0a1b03080402210109110f090c0904050a0b03010c02070602 80
    0x10241080c1d07010304c2c2000c030182009490840035081031130480c01e00f54000d000108025540c0d80100d81240d00030350050b0743d8044041090841f0540d524030b25a002400360703000301a03e090182c1040e07180c02001e400c031080448440303225000c208807611045070b4940c00c00400c1003003840c8144134401801c50003406500c41d606003940804080140056000c5225a42d001410030380e08010a11915501c44001554800508190000c043d050340407041e000c2d095415440034103502d80800a40340c00c4084d209117a450f4010712090116480015112012420032034001c13491501c00b5210103040e0401030400b5158498007030011828070300e1100145040300403a074952000d080600d42174a6180c1c56002c0090010b0b80d41000700700540340007400d000450614140448000480001590850724640750480c2e00c041400c43c12246c41c40d281048a19120059600d40340c1ea10b81000e044605210b844000f40c82140c4e500046400f81c0020707032021a0108010300200407144c0a4000a9900c1c40188a40c000600c698131 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 519090998 1250 519089748 519089771
    0xf01090902210c040b070b07031b020c150f07060c0e0607030e01020c0a1d0402010203360906010504120326090105010b1614150f040c14010813050c03031c 68
    0x1411541150303085c403003260610091b59034a180010b0090118400c03d51a5107031070f1010b0003800200340c9650401d4000b00007100800f4148044885440ca04c41c54042060100d18440c0c0002002c0f6801c0c141e12210018220200440690300039070303030700d44060b00a0000316811003055000520036500d1003098089a2a2010030000c108140c41c25016910007455486000700c0307002c0c1001800b58100d0b00c14015641048d1420f0300030100300701042200c10b0045146546c00c5c1106400c403d50031600d0700251000100c80c0381510028043d40308600ca6121460001d69010060501c20310119514901e50521041c6091040c620302007988030649414074103510300000050501d0000d81103501044099042040140882d01e56401462000c488045940070f10400714a105000303800c214800c25181d03140c14030030305041c14207000b5002c0f50342020400c8004080d0340c9030281c0c0c0240e0f00e035a10401114202c1d10780c94407450214104045800c0180d0544802300d151000e05440140542c030195410b03104020703102e02c51 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 519092248 1250 519090998 519091021
    0x1c09020109030605070905060c2104050a030312060e0c18040b0906060706060312112103010b1c1109120a11040e070b040f181a0f0109090221 62
    0x100000340030444100c1c08000149642d001240c2c015124109010101c1da0f410208000d540540305640a1381c10010b10302c6001c801181d00100a941c440e5816401c0c43d00700004201144550b00024007400244207030302103000040c0c1c0200002e0507111400d51610304201341d600010380c02140a0200e1040e001c604212030381814032482403020307801003180f4541d03102c0c8000c2c824641e01c40c01096880755101c84004c40403c120380c0100c4020f007119a01d40b00c40051100d201d03402c0403451100011200101c012803140440305e013058a041d6400403090a0b5100c6110080c3d00c0031740b10380b9055110190505103070340d90905402c8090a14900d05407610221031030000e0b00b880d103500324114014010f400104600f1200d040035401203a8031030582045038180c2c3e41f50080c00c01c1c903411a5004940300c8554a409000e43c001803041c100c06c4005580e0244080c05030000310310101b01d040c1d12243e0084000340b00511890b0701c201030010003010440b000f1592090b02d901c11754010208510292800382e00f450200d81d840039034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 519093498 1250 519092248 519092261
    0xa050c0304020312030a09060e0c0306010f0b180f0301090501061a04081009052b031104060c022b030905030601080d0c1103120c0102120901060b090f0315010b1c 71
    0x1c01a0200c3d80f89101e2000054001034024440d40ba5101c1c01d1a00082261140031514649c3c2d40040c94032440020800d46043c0307050300001c18803801d02d64200070500c0341009a500c42520040d00210702d0303040002090a07000410000c690644c2405518014040103501c0002a2190f40c09803010450b417168010145100d988105c04107035200e40514562062a54402c3c1035642c82017042e03a0f880002510070043c1c911582d107072103041000711a4444800da806100307004000012614450500740f030711101070b02e04064048040e00070001c24200300d030749104a503aa0f490003924803002122824140c20024003049050180a02070b102d1600081003081c400030354001c20500a07602d00401146950b29441b5400030310800e40d800d07202e00040c1e00030301012a0301070107041c5001800141c5442014003240541c03140034000c007207035925014050021005a1084840d02041590b400c14114098408640f800e18110042c180c4296080c0001c0f4a410030b501c01841b548140080b1701c00d80c003844003410400c03560f1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 519094748 1250 519093498 519093503
    0x50f100f060905130603060c0206070206060f0916020708030f130b0c06010519091d2515050c030a03090512031e070507060c0906020708070b0a210c03050a050c0304 72
    0x200c00c0104a245003070190404400134160f004100d20340e0302d50b00da00944228910b80c0015070002d00803c02d170030394100941a882038040751f80044840c6400d0100b001ca44001e45071647d1034440c402c0d001009402084000d0080c001001101d03075605c1a6540620a40c000000c4c2c603440708801e030740000c1c51215080640700e8106180c00a00b0803a480e100c10410400c110415544100d801d001d000502ca081c02c2c4150b03545034001280c40040d0b00311041e6481d0800803031103210040030391005906902d001c001c10000d8141d5640c0c00030f80c15017030810407054640f0b0240218072a41072100150b00c4808540c590030841c0c60600c00d00464180706106c40c404c3d8040c2c08122008044031038092200101000c0c00e000003500141d4030b061007031a24083e91196402e8a003200044808104c6d1201c04004103941048010002d080c80005840d000d8244108551644a030007406810400b00140b140480c0c103016249001180d8031400400c01c1c40754818010700641011500e40c0d064500e4200010315903100360b002c6a1044d607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 519095998 1250 519094748 519094757
    0x30905030d090b16240204050a0e04050a0204020306030705090c0a141207050d0603050a0f0c050103060b0f0d0e031303053304031404030f0501200a0c15050f100f06 72
    0x260303207650704410007807000301554941700500210659459184c02c07242d21030702c241d4025a46508110a00124400550040c560b08801700100008580007081c040c40056045402503a651500f02c002032a1445941050390700035241c03024050103202d010000c1920400c180c03039064035190b81560050242c024603014445900200000820b40362040d4020089688182da0010f4103a8a035202c00e0b1030158454000c0343d6100d80f03001c50310309000e40c103122000180703401d181c284042424102907200303501907890f118500e12070100300794800c0c0066400242003100140d007103940f41c101052022201003401d01c070588203801400c7c0c240c40e14400841c003c000442c0c2c000b8118141003c810501420400001d0040d000c000c480814001da00d0003a0000740000c5000720003405248403241412400c54101c0700b03e020461522612202c02c0034000d8040d03520032106820195024003482c01c00e0401c20580262901c8880e15000420039000081c903600c80c000c80e2060344281507d034840d00c010442c0c400702c0c090913002c04d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 519097248 1250 519095998 519096007
    0x15093204021c022403090124060806030102210711010501030803160e0613031109072003120703021b06072a0f050304031b0b0d02030a1503030905030d090b 68
    0x780d2422102926101800c414410b42d060044c1246403c2c0940d18400b00c07003000020301540240900622030b0701c00c19134a110400c2d502d1703036100c00f805410358816071302840b0759200020b840c0da8080d03054a1003400c48280000d071800302c0c50041c20700710030106c80c3c0c10089040041184041c00f070504c5243d05803903101040a1450b03ea401400c042030003100d00444c200511102400419281c46015016000f0707059400d400031811480c1206440c0ca80b109254000e030321032010040e01541c45050b0b07410f1040b40c5845118101c48403d0403d0852003042902c406254600052003100c9a0650040540300d4880584440f100c4102d0f054a84601c1c0c203403810070000b21030301e01d500b010340000c0c2081d41c410840d400d4a400e4140d01c43d91403100c10790020400b628281c01c08502001482680c1e00440681190110401e06c01390509040811a00070240101203484d40400002c0107094554400907200d80a40c210040003581e81c9801002450b00d80a46030103070003401c800703a141c2030144900000b6111801030072800d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 519098498 1250 519097248 519097279
    0x18120b061c05100b0d050703050706030e0609060402120a050706090e012c1008101508030403052a0d05011e022a0313030312110a0c061509320402 64
    0x540359284c84c0745e07440040c0c022400b000880030015400150722840150a0302882c100000d011102c0c3e022120103503403c203104101c48400003260250f405541190f07013003049420707070800524044010000034114480c956010a509800c420340c01c0441d441e0040007505603803030350000d041d078501500403440d8507508031454208080442e0980c55024540e40c038924a46030350342c0d03805403902200000b02448250f91307400e101e950300155031505000d8540140114541840d568400360760311011074004005000441d01c0c025200c140410340750b1950f40c01030205d05054511f040c401d008040c43c00c40055802c001c00040c02c18003001e8000c1e903200100c2e045c00d02d02d0142a06040d810400c000907100c00b41c1c0e00003004000c80410032000014080c6020b5a11080c40910090b007a03030483d40041d901a08286050210f000096448040e0318403a80e40028081401560300301c88444802e8650802d08201e42040d030401100807514440c201c00700303443d1184002c0d8045d505030100009409075000f9401000141c29942d9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 519099748 1250 519098498 519098501
    0x50f03030a12021e030412080f0408030403090b1c0b010e01050d02210403080f0c12180c0a0909110a080303062205162c0118120b061c0510 61
    0xbaa00352030301d016203007004010b00c00e418031456004803803401e01d0110a0109102c01036401c2d603044191401c240100b03082c80f05541c83c001000510007071203440004001400c043c422606a07000344481c41140b0785450600081030307100c2c0004082c0071516031428400381080d600c1015880000501030316103d2130303e8505038040000c2c0d0b0169181d00d00ea418040c03007074450300c0c14403450030b4481c2d80a50b80d000203500b0980f410510701c48002d00300a01404003844140d280b440941412a0802e2103548420f031032401812001e400c02c15502c060035444141c008000600030041c3d0485040c05200b008040d600700413943c10001c0c0d601c2a4003420b14264000d02c00030341a8100058030750100c44c910541d00703000503410071031141903070710469030300f5646850ba45012107050f40200400c6280c401c01d01211010365020b0719814400d507480d0390b90a04000c1c0d662046030040580110b403901410324a11021180c40d094140a208018180c51050066880154254503040d0100a0310341d80c1c0d910a015040c10309400d89141d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 519100998 1250 519099748 519099767
    0x1f0b070309180b0a08010c1704140d0f0215090a03052115040506040c0e0f1309080a091719080c0a05070806060409020d020d050a0b0f060406050f03030a 67
    0x241400100381001c600c840e50395900c1e20540020b100081040403181c030070f00119030126480104a82c7c1800e20f0140a0780c0c100808010b0044400e003142d0f82d80e1b481b4104410302c00b41442d80c40d1894010701007032940c56030f403244003551540190303002c8941f45a40c48040c0001d0b48412502c159050304842198000240f0800062035110070079001800d500507840c82c04050058203481601341070442e01c0c10240709003854000c056210804403810460080c0c00e10000e0031a0355000d4080d072040c500200111816500d1004d2000306c6000400d04111055262420f030025600c886602c402040040e140003c02c00c0740441c0300e158044641016010882511040c10000c911540044404c1142440b45141d4480100710b0300d070b4800e0165000340881850140820708080d030180100c1d0040f41040c0f260710141c1c0319030203a60159941610b00325201e4038182032072400d2505070380380140040300390020b008103103001001c003a0090504580800c20b069641e000c0280c008404060720350503400c18401104c4003405004400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 519102248 1250 519100998 519101003
    0x1b160602060a150f150228020d0507080a150510030507030305090f060d05041a060a050f0f0303341106090d06050903130f0602151e04110301051f0b07 66
    0x43d808a4603022040d80c07a8140b03812046120350001504114203504204030b10904071f48508420a06000d80000708401800c9100070f07000c1e00c12543c420040080811000d0000c0c8010420780d6443e08051600061600304034841c0c0a071603080801041d10b14185202d4101201d5011005200345840c41c0c1e8180c94541154103929440708500e080140b0f26101c00008092403d2400000641c5140c1484c00b000c00880c0c1404001c5580c0c0120100200382d20751540403c2070381d00071218a02000c0003407001660000502e507215401d8000443d045051491182d03e2251360300392941d0280c0342800641e424100e000d0198405480c0000c1020080384504001c80180200d0304060403402030030307103207440c2c413029a0410b49040040c4e5000040c00b0701074481c0d1030358010244c4241e980211505180040007580ca070600009080110403890200f070fa141b1740368034080c0b070940c1a0000381100f0720305400d0405031509071210107030080d401c00e00010b8035040e1404040020b004440b0b0344007900c90418654520304d40000808 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 519103498 1250 519102248 519102281
    0x90f0b13060b10080f0912040e0f10081b0a0306060e0708090606010c0b1905010b0310050a08030f0a0908150a0c0f0c110a18020a020705091009021309021b160602060a 73
    0x502405c00d07c1540104060951901a00e04030f0500020075903d2400061101c001c0c00d0103060140b288044c08102d040a80d80c194010300d47c04000c52000880903500c682c0010700082c50081c00140ca0a01010864840d110589400341940d03949450340e61150400c07100e0031b000403148650301000a078014a46900400000000d44461003010007072012900c3c280c1101d006102d0110800c801240d07124000405084291840c84109242a1489a40c3d00a810002007880c0001c540c02524501c00c3c0005002084580100e41c596222a003490300028010f940b0b602d0018100035020482c1c902032030009090a500d0354131401c0745d48507901c4010410f41d0500401c2e51000741e080d0000754000540207400c88004083c4801a0f0b1403800110182ca8400390b940010700412030013040140c1d2400680c0d82a08032a09180d0150303540c035034464601d0300100c81c0c2e001507004c00e01c04501d02888500d442c2c410803c194100044810403885030b42d11030059040c0e8862a4016840031000641040950b005036500c0614030b0341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 519104748 1250 519103498 519103513
    0x3060106080c180d0b010503060705130308090f0d0c03260d0914030c070f08160902071e080a03110405151605120a081b0d090f0b13060b10080f09 64
    0x1c0034013903d044169100f442d524018003861605008103a00030f14a414002d2410603640c1001d5101c070058172014010300b20118520520713840310401905408001001d10450717050902d0075400401880c0815070341c2c0c0086200900460340204292400103040c110344e0340c20480c2480c0c0a80183c110030a0850303041d82da4521001c0c40c290100044c1030010411340c007421020303040c001c0110108010b03034041005507014004c0107800780f140d0300424040e14680f200141c0d5829490038039504040f07002c2800540c40c015a00c01e44140060000500701076807080e40c00344080744881044009500450103544c0d40046848210607032004480c00038034420444540d03818102040d80c441c1414042610711200b10024002140121150300c0400594086484490514524086200c10040d4003501e85224881030380c1e90546130601400242c1c410641c1c2d4442403c03a8145886c12900c50000d2242500b12046403c0c541050418607241d410070401310401c0d0b0724031034075035241c400181e4414005013051465000d040b2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 519105998 1250 519104748 519104797
    0x9011202031003021314070c03090302090403270b030a0c090b1602090c18060f1308030a030e0102040506091c15051006031a13060e011d0603060106080c 67
    0x41d501c1607000000b034907200d52850040c000040040051845032515004000d803a0712150003210380c01c10007520300360011020b11710301690000019003010b94412890f800304020554005144102c0384419a00061381c103c458403201040d403098098407690503400e2000440b80480390b4400302d018420b40c0307810100a82e4444450b0300d950300c621010500c51100c038031540c00b582002800c1507004030142075074038a04050540103906030a1410011445658001006d250703002620301505d00c1d02000e4912440341c0c0e070356001c4903640c035400454010301080c20402102405d510601c240c1d000c540c4090704003440e000101c0d080040329140301600807640e9100840b00800f107000c0d01c60406075255201400a500c2c10b00345c0c1e400800b038a15510540400d420540e80c00c4201540f141c3c0c68000050550307104031184507160b11030b0040d00030703904003484554902d000018440000d03501015030304200c1c900d40c122512081c0078162104e400740125008160040040385c40c89030408014044010743c0b0b0b080001c00785811 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 519107248 1250 519105998 519106001
    0x6190c0516151107050601030330060f060c0302100203070309170306011d01050703030b01091a030f071e051c020a05030a0609050603150a15081f050615090112 70
    0x41c016601d40c0d14001000c0711031215842100c5801d40400c940f43c0c00c102039503603415a1224140402030420049544582c5800c800703e14405003041201c4070a0400e4000c01e80c0e03500148050310880081000f1041d00241160050070b41500c080d4141d4040c010515400c01500040c2d40046e0030041059510204c810201d20469011400020309072041c0d603030b07414601d00041988100315000800700031510540c5d98107a80141c11078100590500b0301082c600110b50058460700000d0b8001962041c000b40c0e1424002e402030015849414014020201a04d82240488464030079801c1e1100c40603901c07000e4104a40220090040003c1410354980d5080072031b0101c10513600280009404204048180714a0645500604d0090245084100003501c1c1404c00256070700d100740101c1c0c028a038018007190654545401ca681c076003100c10315002403540e440d0032641d1b60f9021402102418008101002d00d03010382c0b401003074019140140a04020811071101c3c40d20356000c04001818080303071200c00104000103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 519108498 1250 519107248 519107287
    0x120102030108030408010c09060c03030b011709070306050f1012081903050103351e030702030306031606020d0503070201020919051c081803030c0f011d06190c05 71
    0x1c81003e07507102c500e03100d4902c0c02e4600f00c0c6061021b104c2d0040040c42403d070301c0724028190640514010950603256070060391581580300d4070300324a1080700d0030841d00070400280d01040700d1045078200035590f00c10480c0d03003851405881c3d030f840100040781c04000031140410f21803120fa001e40380e4649001c05d815010344e4a6080d288540e000700e9210390040082c40b117044801c030324601e0442c04181c28a400d02c081c6480c0140c481d022018036807004621045101c80e41a01c408126840400a9a582c241642e01079941d4000310380c854400c1c412541201110040300c51103104072881d540042a880c61318400548203a000140a0011903509002035140303982c0f58451400701d8050220250800c0d81840300340441e0741c901c55003800443c900b232110341c000520f0981c01c40e01c000d080d84030518040148800040d056114449130448940719560000d0310b104019440a04040c0a1100c000c501d04060350100341c0380c800c04c46900300041c5c4940103014400c3c1c1c141d0000c4140c40c5051500520384000d00490074206003d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 519109748 1250 519108498 519108509
    0xd0503060619030e0714090103080913020307180504330f0f21050c150d090c0f1520010e0a0819030c020619060f090207050c0604030210140d05040b040201020c010521061201020301 79
    0x4510280c2c078102c0c01c00b81000f002815042da800e2142c00418444407403040442d14400307050400540c5110003203071142c039400000c1c2c1099890780034110b548442c42200c03031645e4028414100b88401c0c00c0d04205070407003c0b5b6200c942c0d2040181280c41800710801012900f1602904140c150411905840c41c4481c4600741100344143c011040940c100759100c083c4110a400540c0d60485404214100c60b401100500c10702c1520700d1a0b40381070804c1400ca42c050401203d0b42c03810362040d200640c0c02c001c03d00002d002c1200c2c1020703000d00d03c43c801d90340c00c0301920804140c15015802ca500420018200010710300c107544218180444c007a640d91000084c41010341d408a90f4030780d400708a04003005030a00400017055022140241040d0454000411020701c01d03544905000c1c5441000344130f412100280c49c00f60000c500300300424030700b42c2050f0f51000d20451b400ca00500500c41602042d60081e0f041c0e4501d0740300c04142c40d124a05900390b0f04400b01000e0100c90b400755045c660440b201c1400d00046010f00f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 519110998 1250 519109748 519109757
    0xd060603030c031814060702030a0c0e160216031b03080a030b1e030706050a2c010e0405070503060609041121010605030105030d0503060619030e0714090103080913020307 75
    0x52507030030010700110344d00e02c84c40d81d4541e40c4402042840c441103640050700c0c0f001c0b40c0039546c45105100280c5081803056000f044880150400100d60148907081d81c401d40ea401030440030510740d200c00326291480c190368514842c41990f07081c4046030390f0544180b10114042d40301c0070301a440351540c3c0ca65030020007070540002c1d1142c00f800c806003005058203442184210307801d14205010000641c41d94014018801044404201d41440c2d52088658044504801c60040c112802503c0041c0542d41c41c15201808900c03c0051400300d41014811584550041d40d140380c00d6840b88420000c15a0010041942c041c0d11000c1c14070400c0b5009001780300d010750351039296000303440813100d1411981c0141d0004003804002d100400640e00c004c12012059001031400326507944e1030350002140c2e4046e45000001804440403910015a0194003010b596600715040f1a01190b403040e06034110b10307040750b140d0740012803040100300084014001d042462001060005104842c88200040342c004655500014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 519112248 1250 519110998 519111017
    0xd05150f030601050f0603090a0c03030f080711121809011d2a0a0c08030a1a030115030f02031f060302090606030403022d0a1104050a06050d110d06060303 68
    0xd180c41403411140306810340c0039000307940c942400210216594141c45006080000c0012031010003800789443c00d5078040c9040325019140e00b80105412048881c080126010700082511503005030100ea00410301c8400420903000d52003030a060a8120313040c031000d4501e0340c1c204140c0c00d540d040d2200e8086c003503042100508080a0b00019a280700c05840d10741440805d410848a00d103803008140d0901c1080c00c1d0180d510001440d01301c0f0b2185c603894001c2c145600c040207019880c900e9411166140c000007020400d407a84040425089580381d14041140d481d5031b01e400c000060001c82c0c0001c1e450300081c150343d15052a80300300701011021250218000351b5030b032418021883c01c0400d81e900840140e82550441c0f415580195071807200b000f0180c039040104800c03041d10701c1d181d0f0302d8003405046841903c944500070f1074850b4109403c5449644114140700004400e48102d101d44811644000d15039201c0d8000ca898103425844442403050704941e40d0a00d24001c1005401284002c51080c0e0340c4031450b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 519113498 1250 519112248 519112291
    0x110a030213090509120315040c0f081506070609060f0501080d02160f0504051302030f0d090b0703140313021f0f090311040b0d02030d0c140703080307030903050d05 72
    0x2045007604102c911030b1402c4240103814500080082403001c10030041581c82d2940d008560b4494040040e082d402400c000341141c00ba98488400b2414030a81e40f94600c00382c8804840c0342c14034000070600d80c0c1220303007480844046a0b032504881c2e05280501c00000d010b00904c180181650002d800c0308115601c2644107140443c1e0403c51450480f0200001c002c01900704401303124060b0a0344a05071040c0d031110049581010184680200241d000307084807824800e200d207168480d0303010881440480c1550100148803490700089540381d940c141c3e54026900c11541101b81c00f900013a028503074048000015000686890182e180d84101480700c8003080c2c030809400404015a00c0610030070094009001c03c00502c070314401042d21742c030845010514807801c001003204a41c0c084000b945c5440346694108c880e0380c01803884500c0740d000f0b01140103d221040051942e52601e40f0000f8445102000022000c87c4203900c00401c1c3c88c42880e03c80e1400c200000000242c40b03080e0f901102e0f807001c0c80c3c0c1a800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 519114748 1250 519113498 519113527
    0x5060f092403060702070512010605010e01050a11100e100513031107171b04020c0a08221701110c070302040b0a0e070f0914090f04080f070f020301112803110a0302 72
    0x21001d52188c0280101c80c02d04000034140b0300020390840c1440004145c07258142e025003031f040c142a9040c8112461507000349250307401740054464400e2940250310b209800c98019007d0341d40b107140e051424181c544a2641e0459809419298114250065840100381600c2540c0d00000c2031000000902903241c0120050515002c4111528411072040180e03040b1b10070081115000306030810a1309031a05c42008000380e51141d4050010340c102000880491120075a54009801001d40002044039106000341d00f8918400c000d00080c0700c0d40b00030420001458260001d032041c40018000c4c580c4650b984040841805d010f9800d43e000c41c0c107502c80100000d0b4420740400017010b00c0303400c00300841f001c4400314189000150600c0d08252131803002070709200c0c540003101e40042903000e0442e40c0c1c100c0c90a0018600c200800220702ca5402c12600e0070b0b11a1401095520361030b007034440031030503503d8074219404118440c06480c0605803101160610b1034017440242401900c261805031303580c900001d5615 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 519115998 1250 519114748 519114769
    0xd0f030b09040212100f060816030f060b040b0d080a031b0c11040207020607030819110f0901020a080412031407120804030e03010213060305060f0924030607020705 72
    0x81528021040d012a5504111150000d4060b228401c4c0240000c068906180c1c0c0c6018045119003081241020b8003040d82c0800100c5845606585004600502d101810300d21480007400d903070031100f03040000c20303015400f80c2c00c03140b002400011032039101000308029200146060300c420b500814442005601401480031410300318007100321440301070002420130007182c0f401070840d200410040016884949c129200603400a0403103403a800340b8500100304440813070b1140d4121505403814800401c80d4024201034050340d10060342420780d020700c19a1550810541c01c0e04600c05c3c81240000301c0d502030300801c00b624001070b401960b65010b0601a20b070480d04400c071400760004012041c0400c01020706000010000c0c6801580c1e521b83c1e0030201d403001c400648165041d480060b86181049455858000b12507403610700340600d41e1580100025021407a00706900903107154005050000780d0f101101c1d003005104005003208902c100420b183c020100c8925015038810381e4107000501d0f00d0080031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 519117248 1250 519115998 519116027
    0xb0906210d09030b0a09021c0204090c15141e0306010201180b0a0c2a030c06060603020310170601052710170d020d14120f04060b030d090b070809060c0d 67
    0x141b011a159502046801c0114a925242d8160304100c410031992142c0180450f15040282e4ac85000d45510549004e10300004a0401060b0f0300d40c010900984254103030f80c2000b400d0101101c11502181c0149a1503000916403130441d540c0385480540d0f41200458050801e004000d059064500302085004880f01c22520a0034031801d04003c0c910040c8600301454000741c1c48445401c0c1060a207001d0b5240741121400825107030400744041042680355000e54440c8a82c203d44003209681d426440810402c004014281a001480140311a0a02c003c5000d502c01403444810700480b0b0f80301401c41040c000380c030501860380302c00c0c4d1308101062005010450074580e83c4050710142c0a1500c01940c0e0700b0811800d801400701e01d010400201d400c2e081681c41e20a4520103c2006182000c00c031442d06408903422580c492034501c139440366090002c1c141c48049039035112041818180021079101ea002140d086a841d0410000401251110030140500a40440040403a4210510080c00024040340ca5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 519118498 1250 519117248 519117251
    0x120109061512110111030a0206100506030103081905091305060a0b1903091e0303091a07020d030905030f04030318090c0f11100617060a0b0906210d09030b0a 69
    0xa00030741c0800390030a802d880c2d022000303210031444000140d0344c00c103076071840c0381c6113002c081482220705801107860f44c8280c18002c1d603000800d40390010402580070030701001d40b040c1000d0050f942c41000c81c80381d884020300541055410140c2650014070500707921810840c003d070b11913050001c2070810318001c0f0050000d04c0d44403400e120300910000c03040c0c600c120091017010b40301e08150080c041c010020740400c00c654241c01084c1842401c01034090801c0785c03000c54080d0910080d910403001c481601e18000d001940c040d016a10908500302d010340002602a0780b50f0004105001c070b442c444d84001c1c0b00552081d1030f90100d180d50b9031500308942501d43c0c001107000d803c001300988120380c410100c1c1c24164071410488084d01d0036410403072034000340001c001003052404c0004070300e52404281052042808600b281ca040c1d80c0d0020404c190b89415007056041100740c00072850a2a2008060225141146030514040ca4150080d49440494880a4003040c40d81906005004450070482ea02c080003910 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 519119748 1250 519118498 519118541
    0x60509010501080a021018090501060807030c02071202010e03060411030d090b0418150602100e01021e0702150a08010311060c071e05040609051608130f030e12010906 73
    0x2a815203413200400300905c102070a200c8245540d0141c02c5220002c01e40743c8485004a0300e440d2504000d05003070052002196405000070a810b2080c001c0000d0044076501a084552400107007002000000608a040c0980c59542d00b20644081062502c6117000710203024a42010005040c2490429421a410440108070500004005408941c02ca0b030200741c0403480541040905c0c070041134450111148903d2000b40000e5040d80042d0ac10002250281c040100c046282c000314201c4c4189060011902d41030b100403c04020040c0143c04042d0020303000c8003146980f580d602480394051014038021613103c100500a1142800c4c090040394000c2c2e842a1501c844403000c0c1d580c0300814800c510301d52900520700030f114040002c100c2d00401c0301420601c201e50b02c4106007000707810202c44e100300402040f0101c100301c51149a00901031810300501c07190b130490940701c01050090341d14040d03050003140c0c5a481520b80350622110811502d000c000502c00c0c100d46420000d955403e4000c1d03200405000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 519120998 1250 519119748 519119759
    0x909060c0e012c0409050f0a020316141002030f030405060f07090605160606090608150a09031707050712081602010c022503050304031514040b0708040218090307060509010501 77
    0x2180d0004611841240b0307110700c00d90b5000100175004481c4000c0040c02030700701c040c5015500240f60010603200300c041d00c10000f8480003d090140305445508141503402c10665501c4c1002d41100941403100d1064034904051070690205940c0160f1f8116031a0f8440010844911011003046400c142c407441d041282c00d00d4100000c081d4000e0142c0025000600740b00c0c507041101d1944004000c100c07004040c00710b40e1350f81e83c190b44c4810320485440c400a00080008004e0030540c17141082d031651603141d081c101c001c40083d01070b14000081400c000d000342084944080b4909800903208010280e80781070484c84e01d00009a8208801418001568141600d1a20164000c5000302c01031a00030f14070411450001159a1311100e1030f0320141407400b00085c00300c144a40c455041d08400d02000d8140a0216110107081d4010301c129006461161608042042d46120b14103140e0054001002c82840c004401461003520b8400d4a0002860f403001650700d0401056010300b642c40760480c0c0080004d5807401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 519122248 1250 519120998 519121037
    0xb041505040b091b0f10021608010606140901092102040f020d0b030a0b070c02030703080c0304210308040201050c0f1507020d1103030c1c0e0304050103050c090f1203040909060c0e01 80
    0xc508141b10751110220042054420058000303583c0c0d50506c02d903622030369104040e00034410f0f402100002610441c400785464041d01c00c0300c130700030010307554025260301d001030086585080c0c0614541d6142002c82074000750350317240600c80040d84803d0005031744d030b40d802034100c04403415000018041d4201290442c085000680c0d0075600204034100302c442d0103490701c002801c003200740c0c10050084002085006d020703440040900103441500030f40b4007170244c000f180c192001d03081103801400151060000750055201e14003070a107120460b01121a612580c0c15500e081004100030001421410010440010b07810040038600501074100f00c0c403030740c00c44032071140c0381e1000401c82010380400041a01a145031024892403c026040301000f9a2075411103203610303640f2078803403030380000e0600d00820071030024a012100420030040500c072200406005001c0740755013802c0130000600090100050000f05809150b0181e03102e000c002404003800f4a02078101103902035068104034503101c036652141c508 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 519123498 1250 519122248 519122269
    0x30c0f0703050a0306061b230610051002060c0d0b011e2c0609040b1212070308071b1502090316090c02010501120b06030703020d1a010618030b041505040b091b 70
    0x4420708110b1104140c0501c1c423000c001c51400c80900c2200100503c800c142107200c02920000c591282c000c22070780c00e049036500c009440e0312103200d1082207035904005a5920820744e651040c1041000287c08413003012204850b10800030100e113407000101c01c100d5814900100c2442c1d4940418150304900c0d01040340750041112850246a680c1c0425585580d07002024503440041e0040b41d02c280c0790f1034444480340e04a12011004141840c000c600c009000c0c1141600d00300200d00150f40400c043c3d20381c2c0002030b0303440005040b666401c00003c1c0464070103101c0640890302b01c0095000c018a450b2a640495140d07102507021640b4000052110406040400b20b10030b402180820040c0c40314000030341440314a500c001c2d0f22041e100c3e90760040207100001803011802824036241c00f60790341c8005032490300000d500c083c0350b10300c0380ca410300001d0100b091154026000740b0401c80c005244030b1001048840c02d641c113507071900d4100d0401c400e0040410014035180d100c1e400d104c10041c0c0903008107812509 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 519124748 1250 519123498 519123503
    0xe18160911040915060e04180206030a060f12110a050109050d060b0603040b060108070905090105010c050f0d0512310f0203010507110c0321030c0f0703050a0306061b 73
    0x444800d0640c290300300d8030542c1c018252002041103a800365840a6071580003501c10100400c4141c040d040c1d032031816118070b2a07102c00d150003520301424640e0030445142c1c4020585114650340780f0000c1001c00d016960b032000380100384542d140340c0440e802c2150003081400c030380c0391240700407010902059a0051042044a0064900780b20007003642c42c00c20090b0240a62041c0c2000300481000140001c81110318054542038803070f00f50a44503040110307804c2e6814015681c21580c0000100700f154865a483c492547c0075100baa024000c02c3c90010f82071a42c610041d20011344041580c1100c41800842c3d00c2e081400c421003002500c241d91148101024007003024501900f908528509205181c2c8071800450340c0100200b0092814090184c41a1031000312903c01380702d4081246035a00300000c0401e0140f0510000440700c0c0c1071160301c2d264541c0001d114844404d01031005070321400b5804090500c00c0c0c865150303940c8495800e0b600904540c4190300210401c22400c0c10340e4000d203070601703481e0170198 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 519125998 1250 519124748 519124751
    0x12030b030c061e091c080304020406050d05070303080606120c0307110f100b0411030703061802120604051003020a03031211070f03141309090b0901090302060711070f0e181609 77
    0x4004c4000958041c118074051200907405400c8035040040150046105a200319020407041c1d40751030900000a610b01d0006245a011907000d1011034060034242d0b622442c000d1020f40f90a0b5001180010150b0903150985034800100c2800f5804e41c001a0300d400360141980103103602d16083d040207551701c450b62000040e865442042c0d40c02900c1d00d802041c094011894010340e00d0500b10700081c0140060310603c41349070340550189880464900842c2d944c00301410358203519450320000c000050001814482504c50345501c00001a00c5840d106401140651141c031220b856803940a820344480500c0703034403c0f070300800c8044000780140480201c625018035240b10340403003041c0841c00500c200083d85440c4070200307600140c004407070382014989900c035068000d0306480701050381d402d031182900001c01507000340d4001908584070300c84e20b40c4185030a40490b0351541ea01c2c001400310444642180d1101041c2c5e03030421089226030112003000d0400c000081c140b43c507201020b01c6010070540682c00009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 519127248 1250 519125998 519126007
    0x1503161b06020a0e01030b1002030703030e0102070b0c0a09080c1507060b030f030717040621060b0a0503061816230414150408030d09050a12030b030c061e 68
    0xe1096120325510140e00600456481403032501c00307011003581141103030000f4281a00304005040c0084508009500c07900214200001658160080d2500c0301d0000340c03d650a0019101180c401c052003802440d242c0445607a40300c0304640100b500259070051622907202ca0011310301a103071440d81c0c024070409082d8240d214250340c03a02c800070300752041103c3d0703251107401c8688c11059000710003802414810728440c075a1143c2c40b00300510b40d01480c1b103840082a92a181c002008041c6102000c1c1c1c1c000c0060f000034410b40b90654544140c014001c12400244040100005400d199810000e52200d03486104542c0c6008001035024040001c8ac600c01c10078815038003403442e804214507841d045ca060180c203446584030505030b0220906032120030702c581140880340411100350004c6500b0740d440d07032021f9460301d1f1800c10890050712640b00c08a42d039102c0d000303900d0040351020030340f070030840000d6a0100390f181c5220704240c9000c1d102440c2c0ba00c545e01c1000b500141e40700d5843d500180010351300700d8a469 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 519128498 1250 519127248 519127277
    0x803060402190509040f290105070b070c0b0901200c010b09190b010516030518040e10061d060906031203011d132402040f03030201050402150316 64
    0x41c0c050390348079000d8003600b40e041039100c680000c05481013000c2554204144840f030b10701c64040d90f500c0c6012090300030550910340755282e248036911030b906c038041c14210300d000b0003503943d0f0b00c072581c0403210034002560245031141006112144a50042007203002400b229055600420030300c6070650398070f0140c0000090707107604e0391804e41101c0b81710381000b13008110310700c0c181181150707400440c2a41562203192242e45405580603005450b8802401c042541c07488450317540590b115441804081040d450b111407001c51036031103004101440c1e40d008007901641d501e000a080940d070140c0c00c02c0042c10840d20050510114085550f036010740110b030400069294040820308007404048296491600040085002d08980341e0031811708540801c0c1d28465235030364010f62030b102d0000000820b4403100892404040c0040e401c8804000d64007100141342c00e50356502128003204652003280941d440d10100829441c02103d58002d14a01000c11451460003045020482c12003036402d80902c26110601c461 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 519129748 1250 519128498 519128501
    0x106230a051614030403030806030c0405041e11060f0913051b0306040f0e21030709030803090c031c1d06040b0304081920150c0a05190306031a0c0708030604 69
    0x103075003c4415a5522526400c00034007030601103c0350b600910031001c4880c0b03903060603c90140700e940c008902d105001b12900d8070140580c92094255101c55102c081115550340c2c0c000200070102030594003d070703070303031404810300200c03000d000d0b40c6110a502c0c01040102820074041c0d0b40c0007c90301131030325580c0ca941d4080010000c00b8141c0e24448494a040c6001410300c400280c0ca203038510300da920003d0322040c21110142584021a0034a000503c0d0300004c1002441d400080c503004010001624410b03420040441d1030000c19a8400c0403c9102c00d2000c801140c02103551244162690b042d240544902c0e40421507610944c400c10403910740c008005010b0190360410b542240d051880c1c00d00b072100040c040102110f441c0c05030010041904050f20881c6c0000180c1c110b8003c058001a03401c654078907403881a644c1100c10003030309004040040c84440030b840406468410013546000603180d0841c105213090598850501d418020b0100610442503410340c26203180540c000019030b036959403600481d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 519130998 1250 519129748 519129773
    0xf03041208040e0408031e070e010c03030b0d080301060908010b18101805060906040b09070e03070306060b04080c01110312041e0c15020a110f04140106230a0516 71
    0x110f50751075409110402543c0e0008500510007401c81c01c9a540c60203480c8403120506403a588049028a0360100b0130354054509003141602074140000c40c24100c0340481e20b107004400080358400d00000062010030b030030005c00809030080e8402008160031401c04258503440b4402a00a00c0d056200019500f08280c00e4030b00151550403415024080805955800781034181d403828030031b034200d500040a9080910a040c60890000c1400ca0503449058040d1900030301614641e425010b0754234040007007101030040d88000e1030302e03c1c059079070745103040b0201d410303d0400030000381000070541001c01d08240000c1034550b45100303044050b110351035a250040c40c3c41341d06008814040c5aa103100c0040c0b281e2240c480b070455000c0943c1048400d00144200d032241c0e000ca00040808080c0c0300904000d04080449000344a4040c0c400514862a107894010320383c8240d000f030000030310705026130078054001c0c030306021440310003000507085c03407400d280150036406a4140108108003002c840b03000e11000c0300c0e0b1075 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 519132248 1250 519130998 519131009
    0x1c03080103230d1e0512060d0804120b040c050102070b0d0b040603120201090c0603050c0a0c0f021c110613050603040302010b09010b090405160c02011214010e180f0304120804 77
    0x21840d1000b01403019050000381100e0545141071110881c540e03034041e400b100c1c403812200d0b0301091b2507501c100410400c081000c0c400d98040f41c061201242c90080e42003a049036501034024840d480c40c107450059214400da402240c11504114410881c045070b580548100101000700407405c020034101150044c0b441e84d0004d8012280c21401c0d414031a010351002101030b01441c200841c980c1c40303490540503a682520441c040c210200817840403544a140c00803a02031107540032429036903030754000401c810400005003c0c40e501e050340800c02c00642c007194818140c0295003450500080300701603111000e60b4441e2030302507840040002c0801d40b00b90710200b501900184041000d58440c02c0d6003a141c0c004038250760103207240c50042082441c46040e034a26605241e950406c0c01000c690045806c4011100c440c2c1e0003a4488031030a0740e04880300720150103080380c0d0307100190380d141082c600c42c0d0598020620100903040341e0350f0b1f40c0413800080111016100b9803502d44001c1601e85c50074002c07130b2085500a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 519133498 1250 519132248 519132253
    0xf010f031523030c061606090206180307080a05030703031d1204080d09050604090b0a0e010806041a0402100e03030d02040902071403030118050a18060b1c0308010323 73
    0x2003010500c1204504545810002c560460099001815070b0b80781d07a40d50780c075030050b001d1100c20000b80e0346109040181740b24140204400e0002d60114a403600712605064074600000718500150500300b00d88001400880010308021030f03251504d0b40c992040d224007908040e100e000e401c078550001400b452034a2144003c517042c0c7c0c88554501c0306140c100d8002c04c803080c0207409040c100c032840342c0c6c280e2066801c001c0c1803070701d418130b0b0100c80d800501c01c550b000c541110700030600181c0284040303c0305000f4003250f400381502d072505207050f01e0103410300c5884400c1503e84c0018400981c54018486610a5407424840d210000d8000002c0c59030050350b00000f1f045000040204aa031280e40103004064803071310300c4400d151814640c40f03803070340801d0162280138059000c0304200342150381c0106410080d100c1c4002100d04a07141071820700440034005940030381c3c503280e294250381416a4101c081444004100c11070075003130f55006004e00010322015042000c40320400e010740c2d000421a43c14010034404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 519134748 1250 519133498 519133541
    0x15140904030c1e021e03060135060109060b04030b1306020c0f1608031213170708030f060303041815090501060809160e01030f0c08120c060108010603020f010f03 71
    0x80d0030451907003d0481c012000f10a0400340c01c00001c007110317442d500040180207181e09080e61503850044020410180001020391200001c0248220305407000c0c18a016254541c180b0362018207460041d404400e10001c200820400719481e50b00b1a03402184c05903080341c1d644241c0c01e05038080d000d120b941451500580740300020b0304400040c0c01c0c4a40403c007425499076507440c103041e030f103d000e6002440c15582060300080d5041d94001a00039009104414410600302900480750b004e8120301c1007203506520000c2445402091524043c1d4007030343c100c005610300346c140003418910700408551aa9880d8542c00c0004510741140c0911003e0415a44100220340e980d2600030038020b003e540c50711a5010b0f21102c01c4010307100d414410185ca500425207801c0f82d03c0c6954103103061500c0903090362820703c6524042403002c800d01c941c001c41e03840000c2d0641c503104c0d4101810304000c03040c0c4c01504180e01d42081000140c413400c003240d4255409080c524101040349900b68043c1101400d59001d0803120300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 519135998 1250 519134748 519134783
    0x20c1203070606170319050c0607050a02010e0106060e011d0d060516020a11091801060e090705030c031002030912120f070f021e011113060315140904030c 68
    0x3001d40840307406031209216159642001500c0d40d01010b4100100f0b4104100e0004130450030074042d070a0031400e00d0722074a004080e4034507505141c000d840b40070000f18000b440e20030440c2c0c2402507000c18007880d002040bd00b4a40030300a0302c1c1d009051000c50610030084d9441c2c1010b402030000f4103c500d8050203014024100b40751140090004862101164007950a0000c0c1c031071000440440309540503000c12100b071210700c10000b400350300410400030190a404111050882809880010005209414400c1c2442011281840082e8000d80d0007075105891802d17140e50009003800c035140302c2400040c4e803902c172111090b040c1a10301c40c0d004444000040c100e140d0055880e0300da0301c50000e121311402c2c140c031038902c1111048400a10240140c0c0300f212402030352040c1940185072001030302c00020300303130480e07000d210200d403c8a091050b201000003000c00c01c290700740c09050010122820030041103810314009019002180d00c00500030021100003c04140c050441032070500d401604410914007041e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 519137248 1250 519135998 519136003
    0x1005012112030617031e0f070b060d052a03010e120306060702030a26070b071202040504060e0105090f01150c060204180b0a170a26030408071a0105010e040507020c12 73
    0x701401b0101580c0b4401c3d003400e0501106945107180c40c07828440c40d0290070b4a882d2406840078000c1d5500c82c04440c821000600104a07500000810396503041224200e194444460f00d61501004c1c020790514400740415140402e03503025102418000e0b94407910b5580100b400c5004800780290144540c0c13052806116600d50401c0ca0400c500516040351030b446d5003403501342e004043d001020010b0300340109102034010030b0191113038080d2210043c20196520001016595503a01101061140c80018859420b1100046030b1186e01031a42d202154944180e20346402100c80341c0303100f0817100c1c11080080110540455004002c940003240360200c0c0360700c0c500d008100d0044018440c0d00c0480001a42c6065403036016000000040039104080244e111848065223041c3c00c0e021000540c826038200101f110060740c0158080d800064a602d1145809801600b1503c560191400790200421881c1e034011580402d0381c500391008180c648030760740d050749052079403103034a94001024004840e800400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 519138498 1250 519137248 519137257
    0x302031501090f06030b0106050a110304141207080c090a1e0501090b040507080a020705010608030f09090703110d022b0c030b041503060923100501211203061703 71
    0x10b510100710403070305010b41108865980c4401400001c00c0e400401c40382d80200081e09110689082120b01c410105101e1030960f441600070400c2e00740c08021a15007420030859a5880d10300e0f100042081c5420001d4080d82c0d00c510030040b0b88940540c20024401000581048442e1018032555908450340100c0b1000508003d0285d07440c21842c1c00c00b080c19628003030003603e0062005480b28540d5469100182c0065440780400361520342d2a203e00040b020400c00040400d0100a0a240d0700c5808650030000e1540c80a4103440800d8200344203c64000300200071125807a05001d001a0ba4985924820020203000344003401c5046958a021484582c15000000b036128030740d400304800c0d0041401c03c0125850341c034074038000c0004400240002401e55111001c03a41c00749801c800e880251054688400e0a400b41d40c020f01c2d00007c1c0c0810701400c2c0c5020300d40c050b00d075240d0b40150f2002d1092000c20340700392542001d045c590244078000349150195115001400301c6001600300f9010003400d4654a611 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 519139748 1250 519138498 519138509
    0x30108011d1b01050d020403080f1201080a08030c090a090c020c0306070f09091104150306081204180b040e030403081201061803060b03010633050a0504031b0302031501 74
    0x211000d00c0c050a02041524211102e108001d0341c03201150011140da4008406100704c5d69801c01020001c40c0002d005021186100e4603040d41d2940d0002000c1207149043c0c1c07215409a02420071000011004815643d0107042c05070a0b5843d40400340001e802d80d1429031044418074030304426554442d0303000c5280f000c02034094003120113544401c00d084030b1444138150940c0c00903202a506125039000c0b034102c000e21964442c15181000d403210112440c0644110b12900466503c083c00c01690708140043d628509401d15140d081c20300c1d04650044221510980030005940c6501410b0340307a413142e03c41c0713550028000c1100d45958492501e0b00650b44400490b10f85c41c000440001807482c07140f080c800c691041d40044503165481e43c1d540c03801403c0c0181020350325540f6440049900d940380500c2c070308241000c6242d04412a20800c40042d1801524000e00810808204a04a042c0c11200b160b003129844448051600d40103c000a20b144580e0402503050180c2e10040c0301e241c03401d401c101c1c144d59 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 519140998 1250 519139748 519139781
    0x70f240509280f050609162408040c09060b1308070f1719120e01080f01120611030a02040f0b0403030c200a0b0d060b120a02030402011403010801 64
    0x101c581c003030560788160403103503941c1c02101400606285941c001000745043d10800c2c00c24040c000995070141012401c4405030801e51002805074482680b1055000040c851081601c544810031a0541001440000b808017800500303004601007000c095010001040c45e01d004022aa40718010f100b025440440140c00c010103400700428442004a03070030003203444225401103883d1030f01910000c80c4044240f0b00e4903d005c1c0242c800d255400300c884c5422001c3c400e800d069900b12840300081d20090a482440d41003010074400c22a0080100d884981942c0018122101c0703000c281c68403001400e441030b0852090880801441102d02094004e08203031003080281d16000390f103400c001c0200c1e008903c00900000d00d110341000202e52006080b400450a080b45541400da54101050764950140c2c0078601b91000010b007002c42c50501e101d440044e204c0c01070344034070301816040600d14044014240d440c03042c1d40000800c0031680a010102000304000080070703229a564001c4e5402400404009103246 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 519142248 1250 519140998 519141001
    0x1b0f07090b090c04030b0423030901120c0e1c0501020412021819050612030316030b03010209010905040f1d030703030b040506030a03080601090b04090605100e0312070f2405 76
    0x519050280b584260820035540b4142403031a182c1c00100c001c06001501d221400303011030031654a2006030008500460402165500c19a60004013421203940c0400306841c07515210300040d951200400ca072a1908031a9070620209160a0400301043c1640043c1190310000d00090b6081001104281c150b008907044c0e0701000030b90001d400020400c071502001c004080807415542105030b8040c940041c03020f0100741000340f140c10a540303154402c1c0c0d442d800310120001203408159043c081d401150f6001ea0007513040544510002c0c08444542c09001d1145c5d0b02c8400700e0740000d03450781c00b02c1031083e5107042400c124002461429240e501c00c0b80c0075400682804200005400d0500525000d001c002d40103002c00307040398071304595258024020904008007a231001880950850180c030140c264000d00085251500d01005003101601444009000301e288080d100c0e0394021a0000450700f01400d107590311501880c0000309000c4016000b4a860360000c822207141000e88003182815028102c10041d9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 519143498 1250 519142248 519142271
    0xf0b090405070e040f0807060e071e0306050a0b0604180b01020706090302090907031b0602011505010c080c1f0f0c0914121f0b090f040c0b1b0f0709 65
    0x46110846000d003080d0300c0aa4200281d411408a260340f1900501180c1c0c140c0f0300d01d41d50710509a100f42c8094800b030380c44400ca00700d8400b003800640010318219139660402d07801c03d04008400c1d4050711010780401d0765240040c0f04485260459849650020035082c1e40e180c0750102c0551f80043c0c0301d48400303010701e13042e000d11255000240002c180c45c83c2e900d60201d0b031032543e030801c40c0304c00008010007958000c4175000400074403003c400340106604841d81c400a40e0404100a00710703400b1200701c03900c02404042c100020f0340c1050481403880d4200c41803a9903441000d01300c914110190a0900c03204000340c089078203520302c680c02010300301655101404003c51440d4211a5280c0c6800ba24107022a00300420425160600d02441c2075103c030400d641050075411090245142c008000c090042e03206d464500141c40c01800190b401404d0034030340d0080d0301300390701c2c0ca01e800050742c02045504000018a146941610b054013402c0e4003590b412948049000d408060302d07140341c0d1164030215405c2c1448100c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 519144748 1250 519143498 519143509
    0x10801060e0a0c0302072f0904021003090507030503030403050d0501120210121103091606020f100c0507051605041109090408160b01090c0210180b280f0b 68
    0x72200300241202094a444042c04001e1126031920001c0c1982042064001a541f00d000b004100c00524406403039005a26034007010f0a4070861070f8030661a810400006a44041e40f0040c0780c0403038500007400650ba86805031070001150809041c80c80084200030070140d00000900e0720f040c61714030512259076501540c141d0304454400c000d40c00510b15100d441641d200d05078074800e100781c01f032000c101e180a050883d4925801a42c03502a41c0c0c0040f840d104500040c900d8200080040e8401050203202c0401b03180d4841610400d007400280d110f0b8030b486401c9210b50140c1d601a6001804ea03801c04c000c0c080d1a0403015218815140214203021500360b0b80e20071081036400c4100d014040c01c3c0140d86550304c0000d56803021002001880500b002c0d2004190080111400391944e00400175600c203170408082d1a1007501001c1c004111300f00082c02c81300170000303082080326551020446400d0307100c407980140002004603445043c0d2006c480c40741e100c1502600036080f402c409a40400208074408180030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 519145998 1250 519144748 519144761
    0x228050a0b15180a15051504091503020915060915090910082e0e0a0501051b040302041d0d030c1202031e090304030c0f0e090d0e0d0201030605030114040b010801 71
    0x90680c10310001503904c3d00c00d170095900c2c0310b02e01c00c0b0346403202d0300e4400140400440321a802505e502c00708007444410250300c228044503442d04500c810003443d550004107544d60041c5030800c1d407001d0360051109511041c00b03a464101c40100011a1400502c4902d1216044a800140f05180300c401092082c803180c4415010b48030300901030310101d031403a00c1d130200a12401368443c202221151400c82c4240407407003104d4800d0403c101034a102501420607509460000c2d102140c80d039061100c80800a0103170040f10f045030741c142d4010400040e043d03002840f4a4101c0701e91540c502421180084859041c1d0151807c0f0075075403514441c1d04452180740e8101c0c0030490348a0070000c401c601c4403410415655500754405400c000712440e05442c0d9941303401215081e070211800d040381244c2800f800700c034401d4003984194490020541c14008039002000707101d80c001b515000e85807200074601564425006880505800b800074010b802201900c151940002c4400740d8942e00404004540a0018015203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 519147248 1250 519145998 519146029
    0x2100c030e040e070806090a0302060f1905091912031103060f191509090e010c090b090a03170a020606060c061f0e1302030f07060228050a0b15 63
    0x1815070100d01c909000040ca403400880919200f090780c00507100b60204a12841681c0d03a002810410071185400303403034020050281101462080200040002100c40c015040c028000c00460662a05d6200300c0c00c007044914028091919a0392500c1807000d03010380039032002c920f907404200c0d48104628081c03445c04140c0b0b1544e480070300c0d02d60064040c50b0500107211141c9815140b885419540c220500b80034030810410b5020801403030041000b1107552182c8590409a41c0c000c0c0a100d011800043c1020840c1c029020b01a40200d5015401d48071040340350091580040c3c944418182d02404107001e800c6404000018400c032000905682009001c2e40d5003160074600411850b10380c05101d040600280240a82c00d0b100130a0000319030a07824001801030b20928504000e1608a00605045c070480d17290342c070f1180e80618000c100d81ca034009880d1034140858140341c80007000c1c000000c1c800030b1003090042c0141c4142a00142030088028185004090b1700d0004911a0000428010701d0303003448518 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 519148498 1250 519147248 519147257
    0x250b090109081b0102090904051605010f050a1d060f1801260702010b130b030c040e0c0108060f101d040c1209020409140c040608010e060118021204080702100c03 71
    0x400c2c3c00c046815080082c8540e99000250500c01e04c1c10200381d10110468041d1055400701070030b2801255180b8400707001e44005c1c82c1ca280f40086c0c00e64040c0544c485e01c02a08100f0102d444203221811000c503074016110f40041034266035011000045040340c20642c0a800d17801c47c010701c5030b04e20398003030700c1300c031881c64881d06509042030f22114402e01032400090541c3d05554a0b0580540c481e51549410071031203c0c001d030000352040002080c10b10344160007104901542c80c0807503a80b80542c00050a0a9104c424030305118569a0900454810703429450313416001b0712510014821150031003141c40118444185600c51050300000300000d41e2000703410032002c03540049800020b10242e400c03035650180043c00114401d6403683d80c84002c1400d8003502030a6402141d0034080626190280380c00600742040240100c0e0800e0751020344504041c81411500c02203003047d0030340c006150301915100c0526200004081c40c0078207003542158001c0d00204d1141d110384d078202124600550201c900c45405594 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 519149748 1250 519148498 519148507
    0x302030a030503090a2319050c040c0908060702060105090a0219030203071701030b16020604050607180e0a2012190902211504080a050f250b09010908 66
    0x70107507420361000d8000758050250601040116500c49400340c0ba100001e444a549403900094640c10044040003c2d00e0481103c030f000701c0450070015441c9480c04044a0000c2d0f40180e050003640d8a80460b8084a524080d0404001d070f50b40e0040303001d90403a4070130f5039890320561740d003020601203114034840900311a950012448041d8800c0c0d01441e0b22407054103000c0381c142e01200350071000c110264803ca6019074071500b0003000c110000011105c0b4095030004202c00d0500d0f40d100e5072a40b8008080408028010380081540030304a00c042004001741050b58203070b0b041c005111800752940d598800031516402104040e400d0100c81100d1405007031000c05001750720b911304d400352081c11060190640310384502000016070703990b10071108a0039101d500c8900700c5070b02d00415801d25400203c08050f825075a8201f00c0410810340844d8070002451802584e940704032030711180b0302d003d5204909a9000113001e0002030ac884d50081d180038500982d0f91081995940108600740d440c131701401411500f0522 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 519150998 1250 519149748 519149753
    0x21c0504030b1803070c08011a030a02060c03130801060521061302031c030b04050c090d1202010f0c08091002040b1b210d0c050711010c210f0908070302030a 69
    0x544240e080100e100105603e100a500c1c0149544c104400540350f003018601c1c1003120302024413038080b080610002c100800e18241000980b50000071902a008000010701c07840002030900451302d80030074a81d80c00300c07090b0b11400e18500804241c0980c0380210542e2141422840c0300c44200b0411880c400c005003807139a00c90100b0311039038101c101d04a8140c4500704507195420000e411980c0441c02596001800411020801094078005084101c04840030848120251500600d000d15035810080400c008542da000490041915010400110b40f070081041c43c078992109805000d48805000c84403400d140c02c02d20001ca02c00c5100e031080c4c1003010007040355110150210004601d400304250344501c544008102064010303221a04154500001c071001c01080c103200e180035000c020f140c01401c2400c195503d0211010999120f814001c00514450030444101300041841c6d140140918006400000140070300301c140c00c140c00171900010010452000000d81c502c101c0750024001c242407520342c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 519152248 1250 519150998 519151013
    0x2190210110f060108031c0204030807170708070804061205090718020c010204080307050708060c030615212208071403040f06090f06020c010903120e0d050a03021c050403 75
    0x140d500d044a02500807844040b90042c001d081c001c0411401540d55a030f41c908140401080400304001245d2040c08144042400c0703006a46885512840d902c44050070354081c460640241c0c035000f803c0c1c03840020308070100480700340907000710b8002d0b844845100050003078900a81c1c6048490041e10b0303000c210100b140c0d00c1d403500210390644404400529000b140000c0c9400d99200340c0080302982d1002036410204101006014003c1240c6405440b690400580d40002840090081c500c2501d091009055031981e42d4100d400d41c0f44410412030300b6103800f00c171200c00d200d8101c1701042907480504d19040d59079901240c8880d104c0d807041081d4603040d5144d54041088013114007050307143c40b003400081003460794100204050155900c03290300c801d01d01103101c924800035402480854110000034540c990700403c2c4502039a91000010310000e221100440c0c3d50004900c10035440364141d83c0100501101140703020106010b5402d5421301454007900c01c072107010400d280000640100320400201e6100d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 519153498 1250 519152248 519152267
    0x904050a050f061e0616120c03050a0509041407020c190e0c0d0e1207060615080601031e090b0a0c0203030402150705120a0305090705040b0a030204090204060e0c070302190210 77
    0x11102d800344580c0400001c1021a00085512185546441a035070180004287c40c105a41d00760b19021384010000d0340c00078818051044440148100425034180d01c1d5034a030030141d00c04400c19503240c8030b898070090095444215500c0103018440c1c01412000a850719030494060360b141107006413103500e0722240c00c9026400b1034004141c0a660f04583d031125907041c0b010f114034000180764182c0320b0f2414200782d0100c800e2544215010f284a00d005800340d40c2005106a10101c00d00b800102480640002003c130f0b00080c2081182c2e0749400000000c11081d884410300030f58441300e04000c549102c0c40280d81e00c0c07000381d030b010703600c8040b01c00940020090000241a003522032802d95442c07050140071740c4043d800005440c008641c0f41d0381000b0a082c42000490020712040300e00b0b11896180a000c100a0002d40c0400390080b52211032860564850f5003208004002c481c6c500724451401c008072024641090700d0880042c02a141c05030982c2e580c050358500b480703030020202c0b00300e10b10f21750b004d8944051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 519154748 1250 519153498 519153529
    0x90f051c1704081c0315120501060b03070f02150105010e12010f18120c030905061e0c0d02060903133303050108070e0f04061e0606050904050a050f06 66
    0x1581100e000101d070710701c00500010315401e001011860400030015598000380340c1c0e0f600400d80303040c0405600b0044101200700711001010644603005403400d100e405000140c0003000384075000000c0c0400c19602102c00c07680d050b040d03400d80c1c0d140d0548416115881c40e0a10809000454040d001c20036440c0843c401080e41c5a20b900010b44100320110140c16038255180400d0a690480110b07024418600d5405041c1ca00340e291119080000d0358024150003000d001b014000d09004c01c042c1c0e20007000d901610500404400303d1a140d800007421a9540d903520184180140100c6020802c4c0c004000150380c1d1600340310100c8070b041c078101038a00b0107040d05141042030141004541740c20180c403d040e02d00320b00d01c0580c0c0c003042960620030f0003490b240e065444074074607010010402810303001034007080390003a61088010651610703d072070505403088416061604a0700c3d0410000b180341e08003004113804d000a03907051185a81d0000602c04030750040340d604507070615201c0003035958070742103c0c2c1c011000c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 519155998 1250 519154748 519154763
    0x2100f0e0a032117040c05150903060c0309030d1a030106080d0f12060b1309200313020109030510020d0506010302090d02010806130f0902041404050a060902010207091b090f051c 78
    0x40d030000c1d002150013401d45003600e01c40e040d000f0601c07441c249508515034400d035040c0072601e882c4420021954400d00180914030f03048010000c9085800c05208948100c8041401071007585885283c800d502e69040f0502d078420343c60010001460700d40454030500f8503000303807a02c1c091901090300c2512801e081c4460403400c80c1d81ca08001c00d0040301c10700a084050703214a05615001d0600c0c111034101e40762039070004102102c210400000e2042c40d0b080325841003090b01100a510850700c011b03107030790100c2d82000300382d4003420000d8203400c0440c0d0301401e0034940062050080b5111900103400b284106041a600701484480b240050b50003440382c40d4000c8800381c0a0660840170320140301c11601001d00d018002600d03000f8040a616090180c0038030180c106440701b900342450b036210b0383d0790301c11107800504807a10b9404400a40e03000b0302c49940103020340d203810b10140203543c114210214804034124042951020085071049038050f40c00c0964030090501031100c07444051051a2143d066030485071030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 519157248 1250 519155998 519156017
    0x318060708280e0d030f020309030409020f040e010308070b010f180c09180b0f030c06090d0303060305010504080702030615030318030a080406051903090f020904050a02100f0e0a0321 80
    0x50491291020740d820010240c504c1e058903140003820b440100a0480b5034900510a110703200034007008903411940c510b5401030b59000380d40001071030783c06243e014042803003e0b60000418001207100502805108504031070070f60b03072984034076118001903010b08840300b0305100507145020502d90060a400400b0304050140690b00e0310502c400381c05100719040c940303441d844040c5403030070b15055441000c08114098601d0720b501e800810068010203080c0c1c0d2181e40040480d45c14140a40c1c0500043d68004009014500e024100800264480003049000341b01d01d100217107040018038035111503804c1c02009545001c02603d40c15202c0310107035002c9a4107005510340100040d891100400c0100f0a640303c15442e061603040150340d1103d05000001810b0910704558001140042c4070f041040d4100c2da0003145448500300245030000304800290403840d481200003140f80c101000d07103201a03d036500c42d0381c4000b100d424030a00419030b20008009207503041300301062441040104141044520345007406 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 519158498 1250 519157248 519157321
    0x90203010507020d0f0801080a030311251718040c0e27060901031101050310051e040605060903100b120d12050c0906070611041206020318060708 64
    0xc450064071014050303808007184c64040c1e50485c1c49041145c0351800c0c800c050350301d08807816444900000c0001c040560302c41c04040441144000d03915004a090415804090342e1002c154000d02a08005d0f02c5a440800c0310005000100c02100d20382003a094200c0d0600f45040140f0001c2d14903505254144950500b0038034054442c0c07600001184900c401c15041540382c02406030105002a24040c000c5220b203005001041900e40c0c0f0000d41002807030610359075628042c40160b001c105400040d80440211004420401e40e44d0b124900400e0444081064031355410412a046c0b0503101c41c1501900425044501c00701d503640000504803001e400105840c42200c0c20f81c2c2400c148454090215002c10100c198244940c4034003a4824014503015142921502c0041c81c41d01400c40028641c540302c03100a030b02005980c0985006001801401c0c04035440740c50b02c0030103504112440492000f903d403600404107800141c8500031005910799481c2d90b1240c03e410070500b501b10440a95041140c65401c80307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 519159748 1250 519158498 519158501
    0x90f030f1009020a080d0203070b07030605040207050c040e0607170405152d01180222080a060b040513081e031003050c100807030905010b0301050405030a120e0304140409020301 78
    0x2003456005900084141092042103100703504c68010446942c803200c40c002c2c40c0c03070b0000202e90441da0410401d410f1607035030060403401b03020f260f041941c000d400030920a0403c200040d0003201c00c4e804a17401d01c9482310300703450983ea5120840381000000c040030102001c0d1000d40002d503400c00e028100f40c42e9041b05410491031051025114001c44a220100c1442c51520006000c50403241c2c110104055514150f045c07580d07003100a1410f040c0030b0303000660001e66091800520300c0010380021100d0581d0303503806125241d0858800a50701e660034411140b40c5490517101c0c0c0d920480d01071150b1103180f0015200d0040c2e030f411400c40f544805404000c1100007101c100c001e1880381c03c00100720628039040d03103021810100c502c12203078040e0500c1507a0b5400150030001c0254402d14070301c4d00091648041c200a8050590100060740552800c0c00303100034400b0100041582c0385060710340d081070854a0f4610b60440301c0e0046045c0954205110500140d0380686900100c018018008078280505070006070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 519160998 1250 519159748 519159763
    0x8190f060f181b080702190528020a03060522060615050a020604171204110102071e05090402040e0102210a0213030b0c04030503121b04050303090f030f 67
    0x490805946004000241071815411400070b040c500610009690510041c2641d03c14000300003440012400202d10300d200300b0140036008803440c00445010340038100680c58070079402840842c1e560740c0040f001c11021400c1e25030645030b400341c4107041552541d21048000d14000d0f01107800c0e24020522070380d40391801c03040c0d18030043c0a16800116a40340c15031003400c64210200340c6003801b00601441506c9600851402da0064111954141c18414900d42c850030703214420f641013190003a5410301052094208401407500001e8080301c081c0c507110700006003103021401480032103039600041807045041c000b10058010744060004030b080403034080043c0c00e91304207442c2581c03200d8803002c22248190490040b0750f082203200004524004201c40901d54408203400041c00105040b40400d8003018484201c4000b1504042640d0f00c4041051100103450f82c00e907210f05d100740c03007810030489288201048808503180280114580303809017040c00407255090500551500640c0240e202030319041c031106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 519162248 1250 519160998 519161009
    0xb0c12160201060f030f140f010e0c03060105030601150e040204030f0b1b160303110d05040c03050c030607211d03040609080a05150c09030a0305210708190f06 70
    0x1411414600402403c64400c0c0c1d100b20010b0f00c0441003000482e66002d59107008a4019500102c020a40f4913110301c1e00c1e600d40001001c541c64070803260a011004144d00c04070000403001c2e40c40a907600c20401d5969042802181d00d0204841503624500e40100d0203c1c4041c3d40142015061568070340320a51401040da0f0183c84907e040e90030410b2002c09050b84600070f000d074501d0b080c0ac2c0660094140ba4071844040010b05065503501581000d40200c0705980c415a21540e00384050319081c60305200e17000e41c40c402201d0910130170784150305034900400c4c4284115001d58a018885200e03050700d001903000305c148052956520b650381c035081406140c15410700c0c241c10313000b150303102e207040b0008114410a9001c1c1c240360304655000e00c0007801c0450f8402400481d038042a026448003005018144190085554540f080304140401c1640100180c500320035441e0006520310b10140d01035116a10407516800010151400280688100c105046148440580000340002041e011300700f207603541c0d04103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 519163498 1250 519162248 519162271
    0x50d0606181a2701120b01060c05100b131b020c06071a04080c1c080705071101081b03010b0415090609060e12010c170709080303040b0c12 61
    0x280726007812101c44030480d0118090421003004000200c208124851641d14031600c0000b030000203034400402d0b41c038030031001002d91a0031075a43c2d903003410310324559140480380740c0b02201c00000c5950058a10240450300900503040a040102c10400200701c8105401d50000d40205101801c2b0070724890070b21034424100301c5050711030300044040c2ca0100580d090f81d00c2200c3c20040300000400c01c4003200b03041e002816603a5150b031102d24003410075024410b809210352107189010310310304285d4503048048149036114081716807a030120407a406c4c0710707011000c1e0006080e0348004103554862840c05510112000103038580c4541008a0310103644280d01c05440001c0100301400b401c07a444c00140da500c07000b400c204401e68508080580402011300c11300092100918403c9a9901c07141550540030044a00800c0044400a8040c2650600f441a00d040c3c0c200b030000604030034058000b0381c0070f456408000310b00310761b20f40e42d0f1046201070040190b0b28440e410700c592112191007031021802918503d01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 519164748 1250 519163498 519163511
    0x60504060e030901140c010608371121010c0c02151c090609060e030a12021602120712120f1b030c030903151a090c12040309050d06 58
    0x20428156030041c00d040080790010003010025a07000001044102050400b06442d94503c81c81c0300d006110035400080d050096001d0008170121001c0d1700800070a0120140c0b042c3d01b044640c2055000301060010403001182e5504070785031511041d03100b14108a85003480305010107240d003a0a491704d0b81c683d1400b1401c0c9802440c11403401071300021142000d80c05282c100740030440045005085404601d54255a403901241881040d0300310720411508500c0500400301c00740e0280341d40341d0250103d0400a0280c072a4801241c001d4001c44105424811003900c03070101c16000c104d07140e1400b5660300ca0380e1007075080015122540c0041c50321214040c10b244290300e101e503507019103220345840a000400402c420115000a0154400010705030580f4125410801d6440c0640c0c0700591600b01810014150104030601c002540201c0d0b890500b0602c42505e5590903414444942c00a0b00c40c0c03400103100b801800209203100b10129406402071402441284d50b6002140e07032011645029a001a110700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 519165998 1250 519164748 519164753
    0x609090b151902060604090b010522020a05040611010608071a0d0e032701020703030f051227011107060506190e0a05090a02030c01050c030f0409060503070f030b012c04060504 77
    0x810917610620584050141c03004650300c0c0f80041ca814010284200100d910700d00351051081c004641e040c2030781404540d16000d400010f030242d0001e05c102c1c80016222040080d510034180140012500000020100035050400140e0121002083c08040c03450500010038013200700e02800b000c0e8000d08001d550307110042c00f1200c01d0345d05059090400b0740751843d01c1c80c4660340e000a84200300c0360503140c00d0000d84101081180ca40c0701b40080090f45003000d00038801c4000841010360707114011a00260b40904030840792600b601c0c800750701406801002d00070785000c100150450307980b140c4000e12f020850364094a04c460a400c080e00a450091040e00130000040715134030030280c01007035100051a2561190b40060381c0c80c0c9256218504204011030f84801910080041c2c4050803c1600e4594071036854440030320003003641c1d0aca03003482889010800602904078503019010359400c035055038540c1c1e080081225501c810b81a1a1882915090040d085440c29034070f09401548680000b04142c10300c0e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 519167248 1250 519165998 519166003
    0x90803040c0b03040c0e06040e0105100519030c1401140a030c0806090606030604110405041103100f0e0c0c0c10050c010b010f0507030e04060e011d010b03010609090b151902 76
    0x5400480749854100280404110f90005e51001c40b03c50350380c0300a040d524213000c9030181c1002c42d903441d80c035820b210a1020054842d40030b001940c005480001d040d068400115882d1700151102514184004509000c440751b0124203040e90501070400401c0a04150151030203079001e0604000080c1d5541481d10106602404041d048001100c2909540c20008001800c600c0042d1649108540c0c9480c64101c0c42000000d540080030020410003030100710744201c600c164000c99100c4084402c180002c503030450149059403c0e070f44120b4045906685801e04846140c1c0a03001c5900a4440d0940b12a480c0e80c4440c00840410000d03540d5603190f00074034240390700b9914800d4840741401404281c180e4103d90103025545103d80606e49001090300d01d0010a001f4003a84e04251500ca04007400440c05070030321481c446e00d80d41c81488045403680e13142502d5000340028012040050455a005c01071031900380c0040081401c0140b240c0c14190b52118410000d40c070410142e25644205000842c83d035405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 519168498 1250 519167248 519167273
    0x13080609070f0605090f060309010902030c0a06080609280603120f1b21020102070218010b070609060f060801150503010b0d0605070203160305091f021b04020d09080304 74
    0x84030040081d18200b0140044008241c010074003005004122400c0e19070b00d0400b0180020409040d4695a0030b003580010b001e01002d04050b40284114032030940c49080c60480384e01200d807650749010581e2030b104200b020900003d000711201c04515259081a044403040d0820080d071001d0b0001915441d52078000080940c00f0360420500c4110142c1c0c4007040e8001507003004040d54401404400005460030b030b00398003148000d00d0742c175500903041451102d03015070052400c8c1c1c1c021100c0540469019a101c103000742d003401400c6140005101c07410000d141e1b0b4000540e0a0b105403c0400d00c00084000c480441d03080c1d610204980e07444101c01418418240d00720300107410140c000f4091603e800000c66127980301c11100421095a640c0000e042c0d51082c015a1503103902c00c011408045443d040c0205650041031404d8410115400c0c0000c0b200c7c03400c00e00d041800816000b41012640c010340c00300004896400d15600320750208000b4140640314400c00f0015413107171002070303101c1c280350600905e602d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 519169748 1250 519168498 519168511
    0x7080d0c090b0c060106032301091a0910120606170a0b09010e0a0809010e031209090711100902030c0d0f12020c011403040c09060b0901030b060a0f03050603030f130806 74
    0x1c040003043c40c0007401050032070540344117080100724441884035803c45800001d04481e070035032060307001186200c4150043c07000011000d0084400019000c10840754101c2500d500710321400d51101000040c103090400140540200b100191203a40c8101017002c03c542d0144060503908407440d1441001004004507400141c0d220082181007481110305d5921854800301500300744001c10901803a84c8180b4040c0031880c005420798040c20040c0c00c1d064101e4003c11a10340c843ca1041000031075840c440e81c2c40c1c2d0b545001003001414540c4004210500602c50360030243d801d409111031b403000d40d4486101c580c0f81c0611680a5014050044c02c0c44c04511508801c1e1108540080800301c4490380d0222000c0c00700031924070042e81da0784492034007401040b42540001403a6007001c0c00007424080325406020140d6080c2c9081c09104a510104151031050030501d4011030712403040a04010b210754841039100401070100c0303142c0580d40841d9190b81d040030301d00c4800c44881d07410a0106040071300040b0380107070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 519170998 1250 519169748 519169769
    0x1406070c03050c10030501141201020d02040f09180c17011d0c01021c08041506120819030b0a0902071e08031006180b0d02130b0309011a030a1707080d0c09 68
    0x50400b45006030031074088008c14801ca032500105680680c00b941140c41692a0075821175503150b0716075000d22500881c0c0f141c00071180c0342c0241c11030700e85c01300821000c07403e5209242c49402424050b2a07c100d03d0014001c403c90b41d61600c08000791002040340c240ca103660840204104012480020710305a00801041c44895010369081c41c0ea9410042071600143c0c420080c08002d00780e045010018841544070440c0e15180b060b444c400d0080210046c400c090004941c0d814107101c0d40c00540030f0340d052080094101d40b81d41420464504260f02804c42180300d5a9101b40404c00d0303007444503060414000a84905c07400000344010064072821060040400f4245170380101d0303006050341c06811042c4075840516100140b080e50301103940e81110348a840c540c041c001010b0b223a1070380d050250011101c0c4003030b0f9071074100c2000401001c122542e500c200024014800342e0410f940b42020414181c0d80f00c107981c0400d010403c0060049005030003484010b000c00601d08200420040210070b03d584550b8820 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 519172248 1250 519170998 519171001
    0x204091802030715050d0908030402270604110f03040c0e0f0c070b072106030b06221a0909030307030f0903172505041701020f041406070c03050c100305 67
    0x107031030104440041300d0b00b0070000000c5410301361094859109403a05089180c0c5084119020000d918003e103004500a46011040c400d103d08103012201508191441c40c0155400240b01c03890300d0b801030451480506101070a00440d01010603003034009803400c46451805070303024400013075804121035200c0300c00b80395114542000348001601d88582c4901405211528000030b5081303020f02034403011342510328140e4240584444001c00104200e00040710017201500200d1174a00c0d2904280302030619018840ea103624490030443e000740780e01c040303800c0010340308190501e40b59680075210784221100005940d44c3d1820318001070840711a490004102032802440c4008a40e0019148429442c80c80d90301030380f40c6031a4603803c110111204629440400030303104410283c2d11801500480e9003802d90303c1c03e0703001e411000d00d09078080c5003080c045096003844208104400c9000c045c3c040d0002804035850f11003180c0f0713112600d8881d5001903500b94002c02e050591800c3c8681046114406c52901f04280d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 519173498 1250 519172248 519172253
    0x70b0c060a1b08150604121104060e09030d090c081e060a23060a0b0d0b030115051005030a0207120c0201080604060b160201030e0d02150c0a0e060c0109050a030302040918 75
    0x50700c0601100c0210380c1c4c02e02130169036116101214041c104102080340604510b14240c000d0300c448541c154052400d0000018041102a140c103016280904c040d40c149407103030325250700074051150142c03214008180c1c0080c03600c605000030407824200c2800340b10b400072200c00c500d140c418080d24420b011490f04c020007040070080030424006943c10102c000c90b0340c0794800010388410740b5030065a4040ea00240c42c044c21a140e52000e070a44030260024801c8070701628002103010f08512445070408164400781e1821440b401c010340d8000301c0c400e001400c4c40390350340701c184101d6010361030140401c850701d500c00c00350340e00309512542c0b00c1d00440d41445000d08004100450303000301304c07009480b102181c5d410400c6a00a0304400d1285030403a0407101107420280b4000e668490039202c0c1d40c1000080710118032120883c2080b6090050749494001c001d612482c14130003107034405a82082c055580c0c41c402c1d00012403d006011407103002c0c0d074015848a0601030144111802140b02802003980585d1b140300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 519174748 1250 519173498 519173507
    0x10804060209010c05060c031501020106080307020603100b1303210f03182a080d091509050d0501050702071202030a15090c06080114040506031e070b0c060a1b 70
    0x148154055005a100c6003800300680c0d4890b403440c03004055020700300c100522486140d000d10b20500d9800d02c0d046402d45007a0040e4229001d500419801d504204241c17005401d2070030007160800404201a02c2095451021a07401c0d00174481c0e4948205590200f0814002c08580518000506a044e51050458880041c00f80403104000e40103243d180d1560689140007040f41510850b0801000f00e41c600311012000101460000480b1040c1a110404500e0703090000d40c5d00440700340b903180d900070340b82011211684d405140e40060b007040031300c41010030035450b01e09412806a200380c0010586040240010382419019002100301510304060300d00980e6001400f0140d494201c4079500111055255802c09807000d014090f05c0402c584c4000661594801111812140e00020381d51080e0b9440007000242d440c02e50312560b155003c0700139405986d03c03c90b1016089000d84080b2960141c1e988403001168225074240704181c1c11840400100f10254001c40503c04c6a0340d106002140b4500005030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 519175998 1250 519174748 519174751
    0x71205061003090602040f120605071404171f02031e2413230f01030b04020108182d0706021c050405030714010315030804140301200c1b0108 62
    0x904241d25060100d044c04030650480b005007011544070343c103030760b1640900f1442038406001241c3d49843c1000082501c1d200b2488200c620182107056807030945042c8042050020300403007009980030704800744000c01c0d91981980c540a013907001c090703240c0c5083d03001180c1d0a00078088a607210760f941e50070001c1c10700008043e0202d5003d201070b80320701d500d00d41001c0741c030321860703203006070031a504e40104d911081c0001660008081c4048101c1c111030745d0b40c031032200302c2c48a080c4001000107000c3c901140040d8042d4005541c40f01e08180710702c00100406000a00d0080100300000c051902e04a80610030520110504801100c0c60f004043c0180ba00c24000d5070703100001d10b8680c403602c0701182365824500c82c170b00700d6000f044001c0441d43e0040e20f40301000e9801c520110000d020030300c1c1c01c440340b40030803010040354100c03a08000c2c41130a10345880c0302c003050380d8940c480d00c2d9410755075090a200d000c0d0548015420118400e2441600c40d1072800c0c41d1483c0000d180c0c40304142540d05468cc9030f0b940e0b4410100c0f07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 519177248 1250 519175998 519176029
    0x40f0903120207111203190509130e15100501090812030a150905010801020a09090b0f10200303040308072c06072406210b090c03030703030507120506 66
    0x5960301400d06004d0b1080003440e54240c2d0000080841281d07062000015010380d10307143d00800b021507030b030f02e40aa41902c80c112016400101a104c0120840380c01d501c44d100b4200900140e944201e00c0305910081148100c5445d1039110014005004030f5900601000c06010044001e14202c02e1000c15010980001440050b40303a44903600001000e0031850401c000300188503041c880c5584400805001c0d400050b185030015440940000e221010750003444480e0802400400c100102c2209210340d18801d103c200d0107214175481900e405410010f40204d110303c101d00034685030300302031400424141003c0c0030f103c1081004001d00508420200042c88400c0254042605560401008c661240620b400103406038091200c039030012500c0600d04400c5a444c000d0070041c0760b44401600d804951100d580700c02c6420445440340020310784001690300712070014112800351810600091443e4005501100003a8641d4180b05d40b07103421150840305d2451646050000785408804241d41c0504e00900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 519178498 1250 519177248 519177251
    0x6070206032a0306150403232404050601060305010815071e0206090706080709050103110712050a030e0106210f020306070c0c0f0b0f0a030b09010e0105040f090312 72
    0x8510748140d96481d42100d050854040d03001c51000844040c09034004403036803801030246000c140d201c1c0824a080340c6c10340c0ea04c20720006020400070b820200c12402c440c004011807054580105668a2660444100c0684658007901c0c42c070301841c0c028107066041e80001d0034181402d0042c810071502048098150220344070003042a41c80c01c408a0308074403988154156019643c1d0000010390340813603070900c5041c1000c100c8000039a030b01001c81d441c2c1e4003291040001010048240140d6110ba002250140442d000740303400c0070180c1e00c903480c415040d511050003060000421828194246c0071320401d04842c04002c01200ccd00c7c281c18012000a040a480c7d01044030203640030400c2002c0e202d0300e1005070050704941c064648180060001440c186080e40d400d00c03803541c001020103020601d001500c1000280300e09058095000280540102c2210002d240d21031034031302c829407a010f80311402000d5003043c0c2e5086501d002c0522003110f40613088001e00c5800c0c0703080390000c17940050f86c07445e595500040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 519179748 1250 519178498 519178501
    0x105090d050d1103010f0504050f0c0901030b0f060d27030c08030402120a03020618030403020a0b03070507062f070b04080c0a0f06020a080105010c0f12090e0403120b0102010b0607020603 82
    0xd03102c020548601c140540d22000310000c1b44003110700c50024190307003081e902080b4a4a80401041c40e240382220101c04020b13081207a41c00070352103600041c1d4001000b41c42d01c624141d55800040c0c0d243c011240c0c07852541e40d90040c00716000d130220388400c05803058a0302825420b0300c2e901e0080035005050009407800c84004080b40031901e0b5140d0500e507a5410070180d5080d0340d21403600949403d002c0d9900b0700f1016464030b004100101c00300454089aa00414459003140342c04a1070203030b608000c181d1070034000140441c02c0428081e016021a65003146045015003000740b01c1034040c501c04420580141e0400e0260400040e00784245540080d0406100e1303031981d0322044154582402c4510082911214808040401040b40c001e00038845154941020aa807200011510b90849880107899a5401403180021030304241c8079a80a100c0791a03c901d1040d2200c044052500702079908030001483c00340326682d401c40e24400e02c0300d40030707091009000d00006000003e42d07501071600042d11a0700c0010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 519180998 1250 519179748 519179767
    0x60109051302030114150109210302031908060a062124120c080a03020a080705030d05130b0a02040602031b0a050d080406140105150d0b03120a030b030105090d05 71
    0x1e441001550090007400f80815121240b5040c03201500c0e005c144541c1c242030a0726541c003801c0f4176030546924548010008201c1001120b041c43c1c10081a403e5000410124801e200d4440300c040141003291a290420f0078044144070340c00034190300090802480301c92000c031103081c0e0310f418807a00d44d560a01003911028402001583c11020440e00c060f00425000040c5000c0b02a6550440300e0040d01d01383d092130781d0350010980b02c0c00c40d15001070040c2c210560031070003e07500344040c2c903d10b40640120b03800c040c3c11000e810100c0d1015501d019100441e40c007e030081241d0780400d954000140401581031901e000d0029659002ea003c0c014200c42e804480c030034083c0e4003000407006050301f00d012500f4a0200c42c10180c100d40003518195052414107480c208100110441c2504075030b0042c03c10030700c1c4000c844813582190400c0c030b49000e00c561100000b20181e9004c0200c0351030581c92004003a0307101b08844014040390f050381c01e114000e9062004001d40d248001c10302080540550400310fa5412154 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 519182248 1250 519180998 519181021
    0x11d0f0109152304110f0702061c06062c0f1003020c060a05090f060f0103081b1005060319020a030f08040906060306090e061311010c080c061e070206010905 69
    0xd802800c0124010120000c00302840b1003d00d1000d202654100244c84450120049a124100b20000d80850802c80940107007804002800c0303408610300003c800f00c0c4050003410903502503a01c204001481c181d0b1034004016502d016241100c11408085051035a40011136403c9402c41d56862280480e10781c0030016500903012280c2124240d016100f281c6880c04800004140c2529001e1b4944119400d01d04200f00001d40c490141600007050070b402c1c0c5c6956100d1106034840c0962071044045041d01c907485260400c1565440c4400b440007149034544582450724168860141c080d015042140c90030241e00c2d0801d080003500d81050061030084154188458940301726441810b0399132500d40700040c00703503069000a098030407900083c088401c2d80280f90740c2c1d542c400d0b6034a1229184c040454000101d8100c043d08401c003040c10071881c0040c41c4e07120030046401000405406400900030031681d96880e0302c0c2004e2041d07111031154030608003540029500c0c0414050307011040d5030b0f130021400107141c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 519183498 1250 519182248 519182291
    0x1a0f030c0f0103090f120f050a17040804050d060b122a060909250f0e040e01060f030309030605100612090201020c0a1502210d05130f0506011d0f0109 66
    0x41400b00702c1720f58840c80e1440400410a070003800084070b2140215409110303508944038241e00750b17540400d04004c016000103c41d4058400c580504040000107880d4803000354190b43e0754010340c1d00003210060700c3c041c000c0e0002c00c000700560340d42059258115854545440d90080c0e0741c04032340c0c203000d4298030000c11010b1144030411030f840604c8908122031034242085017407119440d17040960000c0a890b80503a802c0e05540803403004071340c0010301c0070f4050030540d100440060000703001040581d40c80500302d5150170b0f640c000303800182000d0030501c140031640c0681500801c40c900415846441c00d84000d1032038174407580e41c011702511621900d00396842001001c259190040081d0302e00d40c0d4031007020600001040902c0c0141c051300c00302e140240c0c1c0c9a103c1840e42e0210341542840c04503094254001020700814551884d0a410b80000102d10550b40903040345115600816065061242e041c0c00d03a058100000c07088500042040021100328102d141124015100070501281d0001d250225548 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 519184748 1250 519183498 519183503
    0x4050a0e0d2105041202010e030a1d010c0b130c0e010608010e2a0703110c01050d0e010f0204090b0a1a09060d021b1c02030405061213151a0f030c0f010309 68
    0x140404d00080c021a071040890354040b540080141109980720b00b038590241114503004140c3d079030001c440e0008003170400e4440d041c05250494503003c1a07920300c071102d078050307401c2d440b6401004803240c200b1060200b16000351029000d50111581741c0400103041c00014007520820048003400300302566070000452042c0450414070648070070349503540000030740000105a0002c0c00b4004501410180424480c5040206030b66983c03600c0650b51010b40a08058812041290750318036083c43c40100e030f440640040c083c038060206a40720a4400c115050740c042d0842c05003c004046226007a9003c1c60880c2c0181c00103a13402901c40315446504002800360b4418030510b0f204828840103071020100c0c5074008610700031ba00131080e4000e004100d980b40994011550044000c01080d000c8207041038904c0d51012254240c02206d495650b50002c0c10001c041c018402c2640303d15900c03032101e0701c1601c0c061008000340c0d1048906040341002a40c2c81d07034140d503418001c032107524490517141d03c43d8005c42040b41c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 519185998 1250 519184748 519184751
    0x61908030a08060103060510020a111201060308120709060801210b0403030608010e0d05030612190c240c02012a080c01050a090f060c0c2004050a0e0d21 67
    0x100c03030100640702c030000300e8009001a1074500040342c1807609006070b501030300099009041d00c504a0b550103648001c61002298040c40d01961010039a40074001e030009544210403054551004200c0b081c0204030180851081c4003100d003050100503800558641141ca000c0805000c1144211424042c0c07800d100c4081c02e180202c00c01c000a15801d81c021000711071509008000814800880c02c0c0c4030f0759904a40340008508101068140c0780040340c0c00301c20304401044e20b10302510b040d540403056103118411a10310301024002c01001540300324034011110b1050001050a1000e0802400340340c5030312009050002c0381850072964016083c540e04095442485090a032065041c86c070015000080c000e0555820100062044d1680340a520a019441060005c030070f001070380c500c4090411124440100102c0700d2807040840c0745c413041e400d500e500240004001030041000e00c415201c00804690040741020340030f8002e11030000b040c4000102502d48030100880d4208191101008411010f8190303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 519187248 1250 519185998 519186007
    0x804020d080a0201020c070602010e0706211b030506180f040615060903051908070f051218190501121e09110108150306060d0206160506150a0b0306190803 68
    0x11030f015401070141080c01012221490390300c0c5002c03800d851448114440c141c10145081041601402104001d0100c40030358140150307407151500e046800900c60a05000217280e10316812642512956800020954240503171866403000d00b81c50a00c044c1c111031a01342008005002d0000f290312100c0d144c0140202c0c02c1400351380d100001d00b00807850205644500401e110992414040c04a0314516035001c403125050000c075803034440d205800b44100b03036200d0190381c43c0d6910002d8400d00418a411184c012076030180008024004000f1240d0400144003183c00018001c680c3c01c0300580407020068800420703078201d94564410a600b818400ca08440e0400306608200019020588041c41003039031801616540c1402400e42d00f06002c8505405801403004100715040185c0c60039041c0303002400c0c20b440c001c0720410b540c1040c7c0c0c0740c01065a481e0444803d004094003810700c001c1054008640782c000c81400e14080c03019602c0b0291605102e600700d1080c1446015400000b10001d01001c420340707885 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 519188498 1250 519187248 519187267
    0x15141b060421030b090402010e180403050d050109020319230a06060e0901031e030e0d140613020906040e0a02180a1b02060a0b01050f0d0615030504120804020d08 71
    0xd00482d14000042c0c00d45200307255100b0b48280700b8082e011030010000101501c440c0c0040d1045186110242d0308012030f4113201001c0a000314007a0302562103640c607280e440c0e00304540901244e0341070b0800c4903641d00400c00d000c0d0301013118005030140120440001000000700740070390044000e40101402d601c0b0000d0801407018903076131150007280d41d9620b0396a000703a01760040020040e8240001070622810440b20107010300780f031a1071409207100c1d00b8080d00207140d900014040701121305086504107000c030444418400203200f0503401c00030300004510690459030000344900c2d00101018001d0b40d40740c0da40304000d03008001d14a28075030060508604940803c5118010340c0084420030115414404200050758812960404020107540905059210006100040d021110303145042010601a400700141084010241201c03207500005405213000703920b80542c1c0d4450103000034189050b0802000c603d1111030002856560316210106548510001f07890f400c94610181c816200864003005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 519189748 1250 519188498 519188513
    0x60311040302010c0b091612050c100507060e120c0102071a1003081c110a020c0d0b0a200406030e01050a09050c120f030301030f0327051507022815141b0604 69
    0x235144c0c0030703009580d036400c00c071014000d41110340910030000a00400c412400304800b0350040c0054481c0c14240c072828500c1d00c0d08500c040d04640c102c007603d654005201420802407440807000e401c2405902c05081ca408402c01229552070300c000b4010b041d000440340416000200300140b401e00445007007001c5921250144001d4010481c588058441c6075007103401e501d803402e011440164048486034883d507501c01d040d03002d4038070201031000c030b0070202c03100c06d144c03030500d5025001400326a80c00140b04c18400c1c60141c01d494001d403a140500d8501803502e0046100494421030000042d640c0e44609200b07001028070782040031600c10040d0001000100c10030041d81e01b00982140a0354500030710403406010700d0001d5061f200b56200355100c5290070441401c000e4a424810480389014500b03283d115004280100c046400201032552034144070103207140c0351a501e102030001160f005c021941030082c050040c142c0c200000d42408408070301c81c00232020852044440b81c84850a6074560b0506150580 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 519190998 1250 519189748 519189779
    0xe060307170c040b190c0203120c1207050709020903120c070501110303070207060f0207080313050102011b0504090209130212180102090f1203040b040f060311040302010c0b0916 78
    0x410421804011a680a503034400361002c4c0c030741110120b860031107481c00141c0034684030801031046c0b11000f0303000c20150b0f8040c4841080b03090000300d2590340381041c010307030740c100401c104030783c2c00000301480382d0310129000141d8402070fa0088880140d4031b200307182c0042d2070890568a0b4071411800055442c80c0c207080402d400c012118207890b6441c00311600810182c5038002101c1e002c0050303010800c10494984034001d03c610f200d506006560f0015254050242140d0010303038003841302c0c204407004124a5909125641a03111a5100c14440154040c0002c00c3c0b4401d6200d500e0300c040c2c01203032040032035407107289007080344001280c1150345042e040c000504060040750b500c080c88080c120030361a0500c041c0211008124018118000c8821050030485480e804c0d010f003150314071013400040341c0650f40d00300500c041c0016038449100c0754500900202512400414003440c1c0c00184010030060360010b1003d880f181c2d02000400d51030b42c4411500b1310b403d111103456130034890380500001c1d40980c45102d89 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 519192248 1250 519190998 519191027
    0x90a0603090c05010e01210b060d021e090306010e100b0a0305101406070602031305031201181a0409030311040f0e010504020f1c02070c03080301150305060a060f0e060307 75
    0xb50032565494005407003c10900201902044416070014481e640103c446d0042205491000072a4061180445d800303800090a0010a5a00103108481042c1d02040300041c0440302c0701d0a031400c4100400b207500c420061141e038003400d203102c020401950608103610b010f0142020b5541e294144d00b04000d004c0c0406562000801c0c1000c030000c15400c0b443c0e403066180e4079024090502d007044981d00c282c000c1d0701c020304c030800c01000083d00d1000940140010810003c0c00300408119505100c000c02815542c0141551000d10b00207260304800200c0c02c810401500494001a5221b1a400c040e4003500c8910168070221400081c0420040c42c450320440599243c140c40c8000e5031388480034003040344140f991003c00503030184042a01c810703141f20300d5040350b281200007500380203480c1d54045003504c1c0c5030401c0354400c50100050003000410062040c4210f4039240901c05410940c0204900303090300c0c0144401c00440c2c607030030030140303018000c210a0500042e11240e42d0b8580510002c1240b030224410b03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 519193498 1250 519192248 519192263
    0x7020f100515030604030f121107080a12050f0610110a06050a11040f031b080f031206030d090b0f1b010209041b050306010509040e03180306061e090c090a060309 71
    0x1002c2c02c0d400c00055a500c0381d58143c0b10003c0d08615528242c1d20050811b17001d450180d06d400310384400c0038112000e000030600c5800130944070050700c5005440d070488180c0094400749404100410030303a1000c1131f00e8000400b600d003500310201c5001c04541c0c3da201110714103c2441020410410440e990780524496102480d0400549034020700c000b00600c250f218024940308401402d0000c074819024118545c0203511a4402c03540d03031200c1007414030321042c991031915000030801003503d108041420350b00c210110040c0c002c00070003000180030242c103401420000c03080414002078408125048a500142d125400709054204100e6640070750301a84002c2e00803428002a011078010319000c500040708135444482c1117544800044901d82c011450702640b180e15403046000100d020b00040c140d500b840403250301c020002d081403503d4070310046d0170304d030041c900e105c003190341e04031030610030000b9030320840d4030460319100c903080c2c05407a0040c0311714240d2042807407800041c600e805a00c0000c001b44038030340 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 519194748 1250 519193498 519193531
    0x50d1101061e091424150c0a031e0203030a020d02040302120604060b040b03030318010b04090b010f0b1c02130b070807140c0604120503281205070e04020c0115120c0f050d080307020f1005 82
    0x2c0c2b10b0100301e07902b003d48001d0b90090001c10980c03000742d00541038100178510700500f410fa9a40001e1000c80031381c0030b10780058000c1d05c00e102c1444018010703503a50180a4a050012495510101c0d59900c001015070054030250720241c1c0c400e44003900701c4200b00c00b00034802d208412035420f0000c05a6002e00c64003a604c00c000b00002060b107012805e0b02c1144d250180b800e01040e01c0705100300d020350310503254200c40101310034020440031404406000000d0058154540394031640c2b500140b5140517900c0c850081d4003894040d01c47d547c801c000c0b41d0a40340103448025031540c0d280340c140c4c51030050b00d01090558400d0001104164200c0c03040e1a041c0304940d42e074185d02110809030a08680b002d903a4a00011030390040b0300e189080c9500180340e02c441c440c0001074039075001404141142d103107030803d840d403400981108051043c01d00390600070703000401d0500c0c4450704e400700241243c8514100180010f00100001c2c010b01d0003440151060034581080d1605003c002b00e03001c00400301110088849082c5a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 519195998 1250 519194748 519194777
    0x80601200d081303020d0c0f05060a020c210405040b060403120e1905030d0c210819050f06150c06250c050d1101061e091424150c0a03 59
    0x2001030542c4d8254028040358000c41104039400c0c02154400e40708025a40303170540c001801001a00e00c61140703181c0040e00c0d110b40d4100351b070810b0485d18011001c5071011480c070240e4400c1d282120122401220005080f604440105000f4012648041e10449440b08000380203600070003030683c602c1e400c40b4600fa07014070560840019040600400750954041113080590900409018001034000c40d0300c107201751402d00e2010242106002040001021002482051400381100c40390941d00038405200900c2e280c0c0c50740c0070307403900248207900c51040b51305107201f80f0484030f04990001d081c1400b910364514101e042c0e4558202061902410402c05141c6038480512a4066489a0340e12001800322012500c00031070314020b81c83e07001f82c8555652000021809040c15102c2c51008036074401119440c80c0c440f40e1411980750402881100c0b0030b4004101d003e00b07c0803c00e03c0070000301101c0900d000703640c002050042c10444040280c2c901c0007e0003401c00540011610085131080e95100142c17404203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 519197248 1250 519195998 519196021
    0x1406211207110337060b090403090f0f080627240109020f0d0e0c04090323040605030408250b1503030a02190f080f04030c050f01050a080601200d08 65
    0x8401d00c441014840e803070140c2d40350503005004402c40c0900300100786d0312000070010350028000c0da41100414480c8404000b8649070b07440500003003c0051403252071380d03d04207403a52901d000801f440030140d1207100c4060b030b0310301882607401c0c03842403002114005002c4421944981e140302c1d40b50460090211b00001344000c10340201c2d14051403004c02c03d0b0400d030a00301240050080200524094011055860b0716030311075110f101d00950103a038405501000240c00388440210101e05259419410802030080c01c0e00700080700c1e0481c0d0701505290b0ba519480003072015042003c61114000c884204591082c08040100c05009129104613200c00d003284108144e07691103007080c075101582001c4108901303810700e01c80c0300410a000702c06480038031f0310350740d6003842c241d00c0b0080190038813601007014418844400f030034001900c0107031100390b50010400d00180c500c3c020ba000c02c104203d9051300250999100742a031000d6210001c01150320b81140d04001603c0d61500d802080c005500e1400044815844 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 519198498 1250 519197248 519197293
    0x20f0f030a0c0b070917031c020412030c031106070801180501060206150d0204020714070602070807030f05030c010c030204090b01050405130203180d080103020414062112071103 78
    0x9038540c039442000320b544031408003c00420300000c0c4104a0400144031140313030b80445400d1020005980e81c1d10110840c120840c840e0301a642242d88188000c5c00190081c08070f091710759804d0b0400341c0805600e031038120380784034400c0c1420307509004003000c0c400b8880c4c01402e9241030b110300c1b40c0d050018241404210044440901c5040c0c01a846000440c80800d58410540491880600bc002d82c2c0000340e0080360603640026000c403111400c115294000d40020301a55001e40094800b4100961800c41c04d1641e4905034040501180c400e000c0e24400c025080040351949002040203011482810102800a400c035105190203e8240041c0c0d010640c4144101c5007505c8000348291032040c2400081c00082d040102541d0351550f0050316022888020070a224001085070b407556599819407042c001541c00520101202c4000007080c003400742e442980300613411080101c5490540001d1280c1884c2c100d0501100206100026041003801089800c1d0440044150100c62640c008010894001101c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 519199748 1250 519198498 519198517
    0x105032d0115030912180801020f21010602060c0f0712170a0c09030f17130906151d03010b060406080906160203070b040201030f0f02070c1a09091308030106020f0f03 73
    0x10202400b550150290780094141c80808403500d512035107c3d240c085c2242c0c4660403091484101056aa00307480d4541780c0d280681c1c01c0903410a00c29450100081c1d541c9030084d1402126070030101e54801c42d65a101c00b6a034180380c00c02000340c0500d150740d2001c0c2c000e409800c1d04c1585a01620001220340e80d450040b800030110568400004d14516191550300d0b10b0f0b8044225510515a0100e5500d0502103025082010607445400701144c50709a00f50100c0e402680040a88003441c04030203400d94001c0c13509030202d0710800607030084013035100020380100424580c1582c0300001140100380c045c0e0042c0e8040c450700b0f44d0001c40d0141e4a40c0e1a802c20004000c01020005030b2042150300c00241d514034034180c006106040c0410440c0b8015080d109079501c0c001d1010009501103802400d029155511034000c1134560b074402c00c0540e000c2105e06c8c1c20b10410340d060b4002d0042c03101040160458804415007aa0003140e00c644950f140c0304000e40312a540c0d01303100c2c200d10035541018500c00c40030044901182 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 519200998 1250 519199748 519199763
    0x91b0503091209060c06160306090c050d0b0a0f08030c01050112020906010f05090a0b071e02060313050a050d020c030d021606030506030a020a030302071e0f050105032d01150309 78
    0x409480c40b1925580c841c00d10584c002c201800b201c02c4118040010074025464011800d010740480c000050072156aa800344042c170741841200ba126541003011207036944440000461004d1a00e0040741d0a12069805036800b1820700d400000c41c0b00010020341203201100c0003e0019983e101d8852452004504002c0e6026100d400803c00c0c941c000c0c090041e0001d12030500600f070800400001d100d100c4c07a070f400145415400500881040340c0c010003044c454001c1041e401100607140c0204034a800003c1003003000340c2c440740a0209001c010001c0c81c9105501404a030002401202e00075101c03050b0403c024024895900b5881a0034004101000414564210054507d103854821405880c0c05400c2c240c01d0b0061507440e03800340e00c9900c030500156000342c00400c8440e2501c030780c1c000804090782c155030001403034000c01e02046402d0b505420494200340390154803130321500d42152854105100300125000d00401c0ba01030520b440754558101c404120100e000c44840c581c0990981f40d00d034074000c004a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 519202248 1250 519200998 519201013
    0x106091d06010c0f0c14011e1d0f0d061a0a1a0702220507110703052512050604020f0402070b0a0e100218030c0301020a020303012d091b050309 63
    0xa521900000000300e014640000e07903c102c0d40c1710401e0140c031940001c2402c1400081d1803001d035801c000009031160400c0c11901001e014001c004140010120b0f0389605080380c4000c0304181d59840c80c480c01c00d01001070140b0001e0b0210720308800106460100034403940e041c940c184402c1d10300111781b241280c0d404406166000201d03443c0007080d0380030f208126403240c60010b03007072400d041d901420524000d50f1030001031b2301e040c680c4001d0815045003203010352035440080148002100404c418440008003007200c50610003240d0b94004091443c0c008143e1b00d048800581c0501c2000103045001302d009035040c81d142c4005c402440240d01c6007000103440000c00740c001c02c0c4008002c0d80036103860012001036403400543c010b8180242d07800021144240312003252030071441d1a0600442e0b6050004038021450b0102081010752203020510030005c100c1c01034482c03611990070403031030080b4680d10741124a04691700c95080c0801071040f81d075440040300d4000b00555065000c0c00860f0302400c004801130804 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 519203498 1250 519202248 519202261
    0x406140610080a02190c0c080f0a240c05180d020d0809030708100b1504052d0301110d14040503040b1602030601062024070c0b0a02030106091d 63
    0x3100251800080f16805c04c2201e029402403c4500304103986960b49400c03110f09400d020240028030340040f4515003280218a00c2c002d40059005500f580c84600f00503440f442410b00c54078030040b014203494150420485401d001d0340400240150180c0140c0500340e070000400340844000d15820080d0050110000d500101d100c82d80603005c8140000c0071200456103601040d424003a44000380400c454842420105503d0034558a00205203103072081810039140c0b000003100b9040030010703803242400d03008201c800d41c0c0c00889405490303c0060000c0c406407180c295500003541c464100e80c01103504d0f10086540700144c8420481c0229040802541014203003150501190b200d28440c1030240048104d40c030050b01d00707101d668003c001b81c0d12910a9840c08644081403024480c210040b141c001c4910610000451581d5a20b44214041540e07202d0351907010a4490490011000d0300c4604c40d90200458848681c0085069a0150303440b038000b03035900c40c1d40c0a80d0302422440d0a00404584d40010310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 519204748 1250 519203498 519203507
    0x1090c0815060c0d1e021c0c03090806010605040e06040b0a0905060a091a01020c030a03090603050c0c0a06200a090504021615020306030d05071e05030408150406140610 74
    0x3a000401810949425a50843d00d4500700c4144d244101007418402202403030442012080c414081070f0010b00708002e0561303443c100000c4c40c8041a0180204502d461003030510414109010305004421500256141d00000c0d0031038001e40302c0c021803200c21500040f59401c01b03014a160203400544007030707240c1e0b051040e0300009d802d005040c1600100030003000a030101882c003400c01034a5170360010312882002c0600080c1880c0398102864083da100a480c00300180e4000310103002c03031f0920301e0005400d4680c000c0d0101144541591000381d071040f070603600c05210315a8800055400d0031a01818050309042e290b01c0c075070040d00e003841d012500880040000307040640040c080405c000c410700c240068282e03148642d11404a0383c40b50b1059010003080102d0a08100c000b050a14500b040340c14407400e9500c448208408044101030944542c0c91503041040030800d49015005803400d0307880f00f034110342501c21440c10071142030b5000b508141311802c1c40c2800b204140d01995014100540380191410140c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 519205998 1250 519204748 519204781
    0x503040215090d060209100c02150a030b1509090127020c03130e010e0c07020d0f050111160b06060304030219081207171b032d01120b01090c08 63
    0x6011041c1000b100b00242c0c0c80e180c5806810344034410060710740c0891800c1c0300c0d4416858040000b440382900c03104025035100902180c1d41c1c2e0941c58500e0346c0302a0000110094841e2030442a0407074039200c0c140c1694840c1c000640135502060318000d04981e43d41d01c00c81c000d00040120b4103020399040000f040c1261441e0028400d00d00104102d91800d600d038820078600740419800400c11281c020014010240410380154000d070208401c83d0610b000c7c1c0d00021264800000002c003070304001c2700e0703810802400b90030111075010303443d904c06e889403120b4a042032103024454048030b0ba0048400021101e00d4000c1c1a81d00441e01b6500400084c00d00740b070b81e080b50042044c07007034680b00300034441c441010490b181c209c2d00c11421a500c038000c0541d04042103003455009013600802da4440010414094400e00c2540da10084001c115070040d040c0c09581d018243c10f044090310318201c07650012802403005003803500240d02c6461380c4c00c456aa610b070304100700d401c0402540c0000b100c100120780b8400c080414030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 519207248 1250 519205998 519206029
    0xf150806091b060702030a020306100e070c030e0405060d02090f010510141207090b0a180501230901090e0c031f080a0f0c180501150302040b12090114010b190306030305030402 77
    0x3a5070311f403480d400091808808035209003540c2d100c03020911040c103170f0f0110346800c00e80c681018500c91034256006010b40e82d400041c6030082c0e40d190005540c550f00d22070510312543c0c01601c0300300c10b03040a020403510011b003401003500903c0740e02c0100301c40a21456204009408000354182809010010000c60160141c5010300b00043e1880204141c80b42c400100b4182d0030317907250080c5401d281ca0034203100442907070280f41800071030544140e104405460704220806c0100850780c4e69030b159001a02c13a1344168001c0e98440849004210a40302c41c80d0003140510302840c010746d41c488600b47e40e250220894043c0c46d040390007403000d080004081d522000340c094828031000e03c10b6030321080ba1072080072000001d50b1007961210010130114162201c81c5a54603160325040d45014200f609030303061449200040121121024001120f2410a50007000320202e800e0b100c010341c0d603403100d850070103400c50551603400410103650240c0d0f1600a100c1d003000c80c2d6058842ca030840d0b95540130408082d0850000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 519208498 1250 519207248 519207253
    0x2606090714120a0b09010608060609060303030f2206092003070909060902040f150927050708060103030c0308010e1009020304210203120a0c0816030f150806091b06070203 75
    0x490b000a00d4940313958421800714000040032840c0c50511481d1600180c1540c0c054100076051049644021040b00e500c01e503000184151900c4030740580c0101041206850350381d5100400c0d940c10014103800c5081e6550107061203055403119411120140442c084d80a549544101c84c00c00c2041840e4020480c1a8011074000600a0890b0003003015038110000c04c0c140e030b03543ca204646200d0200e80c100006000c600c5001c0042400e4581d400c801d6540001c81201280c00081c808010007400700700e0076000c3c00c6101d050300c4036542e5902e8090003081301984110045a210400803855007022514035110740e90100c500c0c0c1e0f800d468802d01100035400900300707888812440400c080a90b0b04501d158002c2c40403a40116a48c0b0305011030107400500140450036080d0a048503450307000d1340119104e800c01d000b2400301101659a0605900501e071040c02c0c1a101030620541c0d10721180c42c881c0740422105a40151a116030700e20400c0c42e00e90307060501d003100c03001840b081249241051005045101c2c8007408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 519209748 1250 519208498 519208513
    0xc1338013c020d0c030219020609040f0608071a04051512160f02030915090604080f010507030e01020c06010303050903011d030705011b1b030504260609071412 70
    0x400c0d60000e03009000085070200c20070220415810440882d8040043c981080b13103052958009456000070131013203010502e0864000c0035540d40c901101c1c01068000c00412100081070840b0300a000c06d482240068000c0c42d00015034800031100200c400020212003c0c80c107410b00d020003501100c0c108115481000c02c0c00701502d408201c403503050103414031180002031070909200050190910000000454105101c000310030b40f1902c2d500c85021500341140c0761506080004034420703004561080049118400303003100022010340c081e0b40960003d0360f05029000005050909070701c64405040740301d900c1f032401040400d128101070032000341300600110740d2031004d048010810b002c03c1d00606264000140c1d803c1001400d00c1920303c2004a8425240302000c084c1000e010072241100c402100490034641c3e500300751059003280c002e00620700c000424014419180318031100c4041c011011803090381e0100c3c2040c0b40025245c1c0445131035044d42682484c141d01400321852900640028612031100e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 519210998 1250 519209748 519209807
    0xe0606070819030615080a180807060b0105090a03260301141516050304091a0a0e0717130b0a051017120f1903020306060711030c133801 60
    0x40085d420f024295880382c1c030b14140040c03110111010000d10f4690501007400ca00c00280020068801060f0824400110000c10390010380303180c4034524006a00000ca9270020082150300e4091028070001c04100402000e000100700080388800c0c02a18170310040e28082c038189141c418001a4840980b203c1c8a00b042d000000003115640f900310200d406400202d41404101594483e10340100d80201e0b046c00b0484080000c50340049160042c51b142e040000005459035000d8610307a002c15455040200c05442c0101c42e20074a0340d00c2d81e404031800b0303100b000406c8071000207000d124050904034041030051494807071445d101a6000b43d2200c02d1b0b01440303955400347c1c088074024001999048203030f079584600c0c1407a00022094581034180c1410320510510601b0384400701510101d903400038881d140c128151001910700400d010415a0003010500e54500c0258140c0054a51200c05074101e0302801c4040c500c00c0300e84038800c404094070b10003440c02e25a90740c1308a1041000141c1000070204442091 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 519212248 1250 519210998 519211019
    0xd050414160501021204030f020915060301031a0708010e340e152502030a0c1707080f100c09090e01060609060215061003020c060f010e06060708190306 67
    0x2540e020101100d41c0d01000903503018846000203e03540340680c1c0c5400c1c2907945d0000c84903a901006030213000700f100061201100100c20744c05a600c01405240c40e503950340340c800b100000651102c2d80810740e4401040c0c8807402180b034203050318000103040c0880c0c0c1d588010040b0030340b42d524000300100300783c84915206282d82400c00752002c119641c0c142072004128140601000035540708005d034102045401e0800700903100d105400d800701c0011981e00e6180340002407824080b6100074141088134000000d80c9800404100324450000094a603141d580ea01d440b030712265540446409604507005d183c07000c1d88284e000c22100455400d000b00760903280c2d00644100c4846c003080d030f681a95140e1080c8240c1380c01041000c01010940b00170701d242940314030303400f5414001400c01400380c015004540c2419001c0d4040c1c0b140c20b01007000701c0c3c00c2881d00c400d040300f1045003849044140d454004c0490400d0910404485a264003c0701c020b140c0010104045090100700c40d40100f05507846601141e070b05c030b04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 519213498 1250 519212248 519212263
    0x1511090d0c061b122105090a02010e04151202011e080109110a0e10021213030c050a0b0f0d1518050c1603030b0402040b2d09060d050414 60
    0x100c0c0075490300307414071501030511075072000002c1d44500c56038088000551005040103200015290000c2c6142c2d01041e160b6400880c581070344041030400d82006842c20b4000b80364000c5a000341da5628402034400244811100110714400c4507030307066a0284612008003100030151403062500445012035290301000c080c0c1411005400280e00c0801000a440240101d1303002075256034800f841c080d01004040c01c0034034107c2c034150150001d00040c0c01c0d80340c000c0c03200c025100c203640405903441c00110890444410140000c4696071408080400c0d103090000c100e00175500301c1c0213100c1c68000c6007050001940c000d000c0c424030a41c1c4588144166452201c600c03002415421600b00a041c030308605803080d50310080420150042c2030124602d0451000c0200c0c02054150030005415013565012502038803035904070020b44080025100a4001c200e1200400c4405410301c001511280100714a41c603c076071244558403240078000100300864039408035400900c203400106d00c02e000c2d400614145001c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 519214748 1250 519213498 519213503
    0xc030301060c060b0a060801030b0703060f150311040e041e05010906020d05070309052e02040f0f09090c0b0a050c0a06020910180b03090709020d0603020f0d1511090d 73
    0xe0b10410410070036a4040c118003164115120003060b8200000180030640510001d0005031302c01020511140c0a5800003010b402200c0500c2d02458550009400c070200038106100080c1c80d01c480701c422401508165001d440070b0104114460300c50751100d1010200d440700c1c9100b84100700383c2c0300700014403d120b140c3c1010710454016854034008101c0710b08858004180070f00381170038640d038240054408108906400e00c0c2c0701414640960b888028058403101000d6041c55034400900400e001d806136225408913450601c581007082d449022400c247d8910080080c228444040305000c10390060001c2c01042100740b400d1030404259500407460441005829a0039950002c2c07000040e04114141d502e25607118103100545445403040644004614860055042d801101007400d50340705003c40f070f0042c2083c26095440d05601a100710041c4442d1100f00e205108001400420342020842040180e400044121062a2808141b00940b0154040347c0c171004040101c2320f03a5a4640340c2d000321090 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 519215998 1250 519214748 519214757
    0x1403190e102405030a0b0a0507020106030b09060a201804020f130e060a0e04060e07030807030807030b040e0a12020c060708090301050a020f180604090c030509062203080c0c03030106 80
    0x3000d6042404821040e50440c1d802500070300118004100d5040a2a800c001f065071700061300e98540f0001c0f0f004090903040140708965070414860360207400141d450007054161410400070074030554006944201e800d01468040341442003140700783d2480404080c681e07000e032015141005410b10100240d2202191144401d0b0392030007401451401000650302902c166000d2008500304181081c0c0c2c1000103200910b800d4803505e1051000509100900055a016100980714800b926001d00020b00441d141c00c0064503000340100c1a18250145040d1401c80700f000c0e050307120350743d120400c00c007484100100961003800d114419940b6081e0042c00d0ba13034003544200e0384607010700e8105420340704007901405200c2c4c0144034032140e845051084518440c3c1c14410035014080d904041115800b0b40d9003c5261240342ca890002416010b400a502c11507202041d14581e40d29481070b040c5c141c1800000000c00798002e01003a0000340a41030b0250880c010341950b9040c413a5203101c1c68650381c801d07005800001c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 519217248 1250 519215998 519216041
    0x90102030405010f18020d080d02040b1c0b01080601050307020c0604271a0603131203020702040c08040305034201021002041503020904090507030606061403190e10 72
    0x80c820814003049613803060180560035140043c00c480a100d000e4454003e400c901000c00072034400303e8080c080030590554440d5600d01e00c540050300641e071110404a14140d114241c2e0140d8850882d4001050f140d0903103584607500119100d400040441c000d40c8503607500780c1100d0b510b10010304018000c109254103244100c1c0620015900360183d94696141001c02000018400341002c0b81010410744a01d9180d0761056181c004d644603072180540144d5801c01010903141c0d1540003449454020b44050002610340c0c08204ea28210843e0044e000138002e001040920003102007583c1d0100380028074508403114281008880d1048402400074881901c00410895030103004100160702d03052021414030703183c1264a03030743c80803c4003414109907000815103960f0b41ca0f0750002c9202d980050403645119224a0320600511150091034003041200c10262015901241105d2040d07401040c03e50300c0d100324108200241c10034001c03007855802400d2104050107090300c80c8020541c981204000314 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 519218498 1250 519217248 519217253
    0x1080c0307140a03023102070b01050f0f04051807150207080f03040b030727080c040216140715030213060329011806050306030609070f120215030901020304 69
    0x60548030742c8081d000a01d00e81d440c0700c2c0c554980c10000100d94041d81c1e80001102c10184000e0709103030b5607400c00c0c1404000d41004031b000a556029144280c441e084c107108070798032003040002c540524011294007516100c1c004c0745a00b06a0840340d00144031802504041c0007070598141010080d8000b160588500c41802c4103850303040001c40000c0c80b001c00034211404019110580320311442c02400e0903510000046003007640300c0d400c01c003039504140d5a82c00302d1032030b2a45101e81240b07003441818141d00c2800c0d089245850b2a20031130f080c4a105000b03c4614815644d03a000308103001d005480c1c880d0050840000b6030f00301b64540c2d55118011540e0040e0341d02c070302c40011601c50f4443e41280040510344100c280da61a5075140c0381c40e0750000f07404648c0c1800c61080c0100c0c2c900308281c0c40d2500c0041e4082c0002005600200035500480046040c1e81941c4d0f00e200440c0c0c0d403002e5900c038800b030a40030300d01d0070403424010040c481c103898009040e008144209030841d400580c002e50b11821980c0d030001c2007106 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 519219748 1250 519218498 519218503
    0x50a06090605031009050c0406060512090c13090206040e0f090601080610030b0a06150210060902030603120a14070b0f1b09010e0105040801090602130e04080706020702060c0601080c03 81
    0x1500d40e0100800c052828100420342e508103107004842c00590780c440700c4050000030046009040742c02081800081d49401000340241c11080507014800381c0040842c0a4120110702e802c0000030103042601c0b4002d50000a60103094000700a030303000102003101065012083c40c03203601c151305100300004c560410789016860003a050780550329076000740c0c0034000c511841840c1c4d0303000c60b03401002500c0280c0351286010010b041da58803081f041c00d40740d1044080241c001c1541d0350b030020000000c10000795540394070740c140c0c40101d45069154015044014011400c1c1c4080c0171400928544017580700607690908103141d000d402c054801c03d0403038082128100305001c20703540c400c101c03d40407100c80c881c04614141e50701492104074180007400c610141c0c242d01c0303103003900e004010350b07002400000720703a0070020b0081d44a00713500d1015a0721030b440400e08a41d86032441c2d0240d82d10112062805c1d0031501c0d420000d40020b1000caa101c2010444440c0b0400e08100c02806051904050000c00640408040c0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 519220998 1250 519219748 519219761
    0x603090c060903020f040b01022d0c01030608120a0507141006080c0904030f0c0c0b1206010c031704080919050f0d0b06090702030f0c03031b0301050303031b040807030501050a 77
    0x300300241d0038800d00050311000c140e102c0c4040246ca02103101044030700142e0812414031020403000d528155a04101c00003c0007420966604c901507501840340300c001102601c40900580c2d85580c401c04410441c249031704010305200c8201d185c0b0b54200701990350307460014407a4440c04161036006c800071041c804a544201401410001d0040c1540400b0300049146824004c0011301444035408040c944240501010b5a1059000001a0215464030014419030704400000303004103260318000344ca2035000307500e0180180e4140d1a00c0d2a610001d41898850742c20090089480384c106215040d03603034581c0716401100120201d01110050b007440107100140403c560441e200746c02400801010405101c0b03910f1700030400341c644207079a950390081645184103410070b900003e400061070710058000840034601840c1030124002000014148085050000b070058581c1030f003040021926903480d68039075141898042410606161742e5100b6241460956801a15039075105d8040100c5502c580c49500d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 519222248 1250 519220998 519221009
    0xc080a060c03050a0603110906040e19140d1205070309120206062803140c06070c061223190c0201091a0103050309130212040f02010815060a0f0504030b010603090c 72
    0x10405d0b54030355100d038544980c0c4045400c1c0511001000f05800d6207481e00301c81040d40b0050700320f402c061402c050f044040c0780200000d0358405030700e606098031030034003146080701d09a041e82c40001503408010401d0081401410a0f8145507481c5180d00000384000c03031040300b54401d84c0250a1901e0840c051089801e84c20307501c202e030054042500c0e000c0380141c00c248170075650003080381561403402040d254a0110318404240d40004041807000408c1490381840341501c245903100440060400e480c0419200d6000d100550017035900003107401220582c5c000c550140b042e18062404400c82c00f0040c04480c0c2c0840d2100060351a008071409102001c0000389418001e20300c0b2900644c50340d110b0390f80303900600d4680c0d0301c0349a82c1a00d034070760750b86240c040c2c40502c049a0480c2415042c5444e0044040c50f600c03804901042e180e1000940c06c101c1c1e00c0003c800782102400c0765140c2402c0b03d0007125081106a802e20a0242c140700101c08540300706030740d0b400b034030540c2c800007144200c034209141868081d500c0f4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 519223498 1250 519222248 519222251
    0x11060105031f090f050c0a090e19030c060606080a0c0207121101141615140601180812070515010f03030c06090803040b06040b040b010215040c080a060c03050a 70
    0x40105440c00200300c0b4101ca50b0300086403020315620220005451030001c050038081c2d90480f080140326011601c2200c45a003151583c1020755520310400c2511002c080c85070980d00310f110401040c2608241d15484c01c3e2107850142401c5030f03960341c2c0342c1c02c80f6241d410100000b0100d60400c038007010b00788500c0110f03c0603030000380551442c0134101c0d043c41851030801001030401101c0f5110f03590050310507000005408008a84501c80100502034440d00c10308207680d2078580b0f03680450807801c02e01c00c80c03000017680b4603032030025540e0500545000090028909400c409400009001e2009000300c60124120308043c0b9680c150ba8140b55190030b03101d002d0340a58640e03100041104c00d8911111a0890340c3c14200000b050750a0f080000c014090701e80090040c40c000000c02082115094200b442580100c0703080242c0541e4130b080c881207803003a040381409644111103240842c041d10b964140d1140c89103c00e204180d840f001303000d00700f0303200b400704031540c1d9101c000340e0032440e030540078455000310003210 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 519224748 1250 519223498 519223501
    0x1512090705030d050418020a02010e1c0e09060d02150f0a17060103050f0f131401140115481a070503011206090c0f0f0b04052b05070609061106 63
    0x4885118048800d80e4a10041e1f0000d244442c8500070b4001071500218441511403a07141942001180700340f541c040e0f000100b041c1c0c208101072802d055942d0203804040e0014012020715400c0c0512909800c0c014a0b10308400d0122644171a4214002c0079203400c5640c8018003000c2c101c0040d86c1120b0044c064505060500e0208181d800744008484e500120100d1510059182c0520080304400040d01c090642a000240402c03d40d005401400783d003400e201c0b0240160782c1e502c243d01802c45902040c0303000075440b0f40040302d00c50400d030241c080d261146518114410205013040030030301d11b10001d0040d0320003041d881d03000f4000360003090036641e078000b603148a892800140003805d0388414003030440e18544c1e0401c680f05005540c0d1010042c2c42c8d11001205c14180c6450102041e4a080d1045c800c1c0761851311310100d00401003009460031664080c02e0b80c90a040454000c07024000d042c0c040e01c002ca807202103020b0114070100211401007185d91606ea041b5400c0540c0203001781c0690a04411a520480 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 519225998 1250 519224748 519224759
    0x13030c0f0f0909050a1707080706020301060e0d0213021b06070804050d0203030f01150c15020306030c040204051c0203030c0a03080a180308061e040f0f1404111512090705030d0504 79
    0x4c0c0c0c1429668006c04070780703441e0000d040343c00c01c40c02114000b03090940042240010411680e0085050f2204c80e21042208012101000604001001c000307402080c0c000103110383c0310fa650050b100180041c00094084c6080994903480c00004441c00c3c00000c1014040c041070181c2441124000f0143e07201851840c42c05060300030b4240418820b01070b0340f0741e094513240e4110b4415100d2800150348082091310802038103020030044d4000784c8005119000307181c5903105614061003150f0884a000e090300221001d00700c000c034003182080d18181c4c1c144c0000c002c02103001209001544042d0310917100c0083c00e0410140343c0c0304a603170180d03070108000c400502800100b50400c000c640e0002e012244544003046291070342510b07a0340e54002a410a05050b00702da46405242c006a500500ca0042080588003100100031600c07001e54014142c0c95030450060340d1814084458164008540280d514000b20b0b1810540303a01801c80d030341e080310382140c04244080d150500c081407191100d464050308050a28 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 519227248 1250 519225998 519226003
    0x9050c240f030403030f05090f0c010207081507180306140a020a0e10090f0f0e0f06060a030b15070303020d0e01020c030a03020d2408010f110d0213030c0f0f090905 72
    0x41100d05260100030002034205071003071b00204281c1d80c00180074881800c0c00119651345905001d0440c201c6c2c050132005c2d0450394070000d0070404558650000300654040480100d0031108050b020301c003004007000ca10403009400c60038050045101d003900040349050410748101d13503000070381843c0c005801040f40004050303008620148040c0f003210243c83c45000c0d0307207054400407181ea101441e8101c0c50480040e10150040409049031400352424645640d50024040f00440403991164089000e21080151f10f00c00d41c171290342010050040390f1000b07400d01e56080c1d103402c0201d0460000c2e400040404148015001e44000304150034000c2d820883e608044c60345a00070840d81d4420158041000c80109485030010348480c0c201c3c0750750910302c3c0282c812464009c103030f83c01048000d43c2403884d9103462200381c2c8a04481d44030b0000c11241010751000d91ba4000c2e510084100c181c440303550b6400300108911208840007449901039104015143c9150581c007020f0550103c52603520300240000403e40c007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 519228498 1250 519227248 519227257
    0x10e09280b1306063b0c1c0f1b09080717100606021c1e0807050910050a020d09030f0f3905030a02011403060604050409050c24 56
    0x201c05405210754800d4180022404a080050110790901900007a10000100900e00d50000400703500400a10040d0b0111009100b8594480c20404c03c00041c226010310340280051085c031012510345901f21380e19400507030340e042d0016580565540b405425843c0a0038910420311018104005001c1c0f814020a4941616105440c0408801d0143e4100040c0c10710225150800102080119030b03181c00b002562050380203511040440c4603208824401d00881d080b02403852080c201401c417580c03025044400410160a0109000040c003c140c8a5960300a034085a0003440d920b0039114401100f00926040c801d0031007a0900c0000c0000b4000f00b650070160070340300c41d0424070240b02c00f542441e00f074081803441c05481c0c031004800b10035840e4910703040c5c1500012200c452164000e15840d10101074445c1182c0e10000c0c041074103608e5010040c0401c03005164440710051400b410280e8840100f0266402110b0481d00e0b900410710890640c50682414660010151901c42040d1810811040280f26 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 519229748 1250 519228498 519228503
    0xf0c0918060a0e070e042d080d020702010507051f050c0a090504020702030c0a090501090507110c101e02070806010801020a0c14070518060f100f080606070209010e0928 74
    0x1290b07000c8465160040100300c004182040030341d07415113450306010015a890003000e40031207040012100c02c010090b40c9454007d900140c00c0e920380441c4100a030001e52040c0000ca05018040c860240420010b0241442c11403640c60a40d0740341d05618000300071108010101701c100c040c10b0012034201540820604180c400545005a072824503000282c036021603100b0081d84003603c040003140c40c0045070030550403248104000e01c51900c400d50706a61000750003204c2403456020341042c505a1a00e600d1100d001d84c2c160500407148003061040c0320201d0303128000ba1001d6803002c5810040400700301b00c49030040c04070314004c5090041529000302510b40100024008175118814614601070500251004045c02400044641402501120310540c1241d5803480384440c0300380c202d03690400b10207440c040141c50f6900594060240000c0d694204040e000c80d800840c280640030050300d5170718000f8060305a07013904010341e1402011040c5030141c90340880c90f000c0340c1c0044e80702c4841c803486000d81c001903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 519230998 1250 519229748 519229751
    0xd0e0c01031a0f1f09080c0d020f040519230105090106020c101403040c14030706051606470a0e25050301051809060103020f060c0f0c0918060a 63
    0x1c200004007a9054200c4e0213403143c05010544c040d00f40c011420070119600201601e07110300c0d24004015854544203406500410404d00c058483d2405038489a4081204075a145140f0006c40e00300c02291200740e1411034410710302c0100304058070742c003d00500410046580c0c0d041d96050260003500c41180c100c1a82c003d0001001640230035002e20b94807a8000d0602c0c151a49030320f05814030500c560307203612801c480c4102c03925248a0f01d040101d0041c09072041500c40603d4003a40300c002d9100d98180302e0094a45550b2003c0c4001c030300f9022a446551403038800c103514070441c0000c41201c0d003420f803070040040200d4961154030554035015903000880d204c880d204c0c01d0300da403166100200d6032754680349205004a900d0001d1410358100016506959051350342c000907144110002c9a8a0016220081c1c1e1340e0181c00104012b14140703c1c0c10044d404c001d8000c50074940b500305610714203600c0ea40e07068015000b41c6858002410004205035110302078072204940440e45085541d25103901070600320116 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 519232248 1250 519230998 519231019
    0xf0c0d021807050406030e01020a020c01110a060f0f050112030807052a010c0807110703061a13020301030b0f131b050d030809010606030603080a230d0e0c01031a 71
    0x5603141c1c60108858002000c1144061400e214020302d43d91160103168042132800b0000103420405200380c0340144002d0b002000720b14500d000543e040e0746486210701240c0704d5103010000003401801840d0500d001e1003000314400310301511030780984d4016009090369a10240251012a50083c2400e422031100d00303290f60b41c2c090302030700004445030402c1c4080380d0002c8110244085201540a60714112891382c4004190b214084102d644401581b09084140c0c481d403024400f11b04141e1109070039020711010b40d030444002e500814000c2015a2119248503070100c01081030001e040d040c581c0c401807c0c01182000d2404241030021460000700142c80400030b081401031a0b04111440c4c0302a110080a540e09041140380c000d0448008440e803c005500b00307100004c90a000f4001c080070749a011781843d00b44024a4011110384041017660340000c604506060203031481040204803e5034218008140c4216840549141107411142e0134105894004125001c451201f048440107100300d0700d030300c0007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 519233498 1250 519232248 519232253
    0x7060c1109070e03070f060903031d0d05070602060a1401030b040f05010218030f0c01020a1b09090c05091e0c090301020d0606030c110313050f010531080f0c0d 70
    0x203010580d142550440c1800c0c05000d02d6076000b41c030341d0b2002e9408404440440782c0307030580d80700600c8251040d040030802e0340c5401d00c0020300034030300203004182880f1610710004ca440e00003282c03100d11030402d03603064110b004144165035045c1301035580901c558000f0700c800740003d41c444c000b01e001440003a050000c12004a0108840c40040108154000000359217940d08009142a16865840800d1091091000b0001900c0008c55001c0d600d59058002d4003017800b240d00c541c1c0750004200002c0d4200001800e012440d000d8500c55107151078000c2101e02a0780c0d082c181072100c004c07009003d130400c00740c485003c14001040381d02500c0d4044409031416865000a03008640640201d117814031409040090105810b03038190b100c41000c0a00355200b50081300001740c0c10303450f4402ca01e4407c4104581c3c075014842c50a101818082c2490b040c9801e901d488092040403d14544c1010881284038480354983c0d15400c0c4c03c42c81ca00070f80032140103052280070000b4119500c00c04840068061102d01c034020f0705 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 519234748 1250 519233498 519233513
    0xc030c0204110d060503070b030c030618090304061706101101090b1317030915101e0504060501090f140d0c06030c0201050f0610140c100605120102070507060c 70
    0x24880e40074005000b2601404000a12500b080e401e261007989070601c0016285000280c110466000e50009891a1205011004154802040550040c8030708006040e40d160015801e44500000c002454940d802c02000514000b008507aa40810105005111543d9074004051040140d20300b000c9010306450b42c102405010000d030083c007203420140400031990a0b05c13080d14800c81c4550514000029180c681241d68041910300d080c442e8000e0b92440105644103000d030b600902051010310300e007591000e50f904141088103e001390300604c100c040142e82414000c40c4042d04003404d090015901b000c02d5420b0102c4a403107a00d0f50320105c0300d44451140c448203091710205400c1000d2040458455030058060070a000102d0015841c00e00007917020300704484414010300740101494202d0b10501000c4602910021341c0f160300104c01c001100b20010208045100281d00950220742c1310305c0d0800300660115650b8201d0b80503401040100005072020641d103094904034240502e20492a041086 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 519235998 1250 519234748 519234767
    0x809061314180c191407050106050f0103020403080d1a100f08100821040f08030315150706050a0f0e0d080a0501030305040e09010e03070f1506060e01030c0201020c15340c03 76
    0x5405c070001850024404190070540c2030314010b80d50403903040307001c00c0110224400c4d440054888902800040c1d014405500010503085c40395143c2c8100180400001d041c000c150b44620300801e403036240302c10849401001c04c941c0503e1440703916411034038001c1c101e80c0700c07004444030088014280110000200c41e510a85025021180070b04031100d031212002d44c1d8070752040c2c07580c0d59020302c00c41c800b14051801600c10702c0744205654146080c8580e40e920f00d8094031000c6c202034000d03500d450b805958040e02c2d2003842d00050b10f0300700510000903079102c040c010f0705000d0b01084030f41f41000010700109411a08860450b0070030050f445003a85c1c3c3ea00d2090040494420f0007600b4000000d608043c411015003402119002e0072005181d1410003545400310340c1b0030300c198000718101c64141d1440d503000e50b0051000f155140000740c9400001c4180c107041c0391010031140002003c16050002550024205003101000c0c01d09a40e10b0400f05d140c4c031060508848440801c10030300714110810144a030300c135071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 519237248 1250 519235998 519236027
    0x1e1002010618051803070f0210120e030415020c06070308131a0105040605040902100311070b01170d0504030c0b0f0d0f06031403070c030809061314180c19 68
    0x3280d004a25014080e120944010315184130b0301c030307503102541c80100407200f0300340d80601810003080d040c1d42806400703d036111080e0140316000f903000c2c0e9640c025000d09100200100040c5a5036030400c211040780c407807025103410840d0301c0a00700420f01c0d1030301d03400c40e2000303901401d001032182e0f1a10701c8039010001095000740304183c0c0b503001341500341403065414142c8800b100c2c1840819100c00500044038114000a580038054800454000b4003a902503503c052014201610344081616506144502030f030000344000c241e40e411410703d020901020a800c0f07004c0c90318038030b01480d503141c8814601c01c0340907403540d82400080b407a540150301d20480303407804800c2c0c00c2880102040039a03040280b00602c0b05a80d060010301c07901e4090f020200449151b540e00080c0ea002c02811916044040e411040f01141c0002c0200b02510a11107842d080200a20203038440340031203030000007404008030340e160300107072820303001020b20070024003e50541e9502c14400e881fa1542c4070310100102c1d5140c42540c0391 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 519238498 1250 519237248 519237269
    0x2f01091a0705030f0a0320120601020120090405011706010b0d020d0c0f021203011d15041407030e030910030209010207031704062006070c050304030218151e10020106 73
    0x121143c2c40d50f030344040d010b414a41c6d1000c000c0d00782c0300ea40400355082c040d12440070300b41c02002103500244a0318030198100506200005d944010b0507082240c6441c40c0c046e00703820f0766010039802c03068a05405a9409170181c06059844c0d07444480f403c60307803130006010340483d60340045407000d01800710354156509242070440c1404046e0740b2807000b42051828041d0306006000d554440aa00505a01128101c072030964040320411007180b69240f0300203018081c480030401280c08122030340ea883c000d07101600103011a040c0c0d40c1c101424081d0445112444425480d00f040c42040400c0c1d81e61140d05850003000c0c180541d5500140700100d04001168000400c13014407490000c0038031030305c3d9010300107454498440c00b207540c0e030824001c844070000111040b2103a21500004d48940e10030040c0d281c2084c886e008503400c26480380d00040c15810030b5050510f4000c5540300300050172801d4080c91560400c01e4620007503445491b5039171036400c507040c1441400349070101c0110310341a20035031102000f4101d1528 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 519239748 1250 519238498 519238507
    0x70e090a0203091b0604050d02030708030c0313080d02060402011b0b09030a11070f050d15050a0b130b01020703110a030b010e090c030706392f01091a070503 69
    0x30810000d400039030303086015118108100d0f446404c0116800c0762808000c00d01030420740781808205440790700c101c00306d0305806403550000c0d01d100108003502800354503901564039a01c06001805014080f507100c48020f0b8050401d207840c96401140c9160415020b107010300000c0c0c07030b950860702010610403000700000000b10400c0076008011010702600141239a48200005442c000155148006d0180240004030024100054600b4100c4441101e1255140d030407070114103904a0112503084801c050001c5e00e6400506a5113054166003003081c040520030040d05042600003542c480c0385010040c0750b07180d4007070a00d1040e50341d503056100460f448000300d446907850301810343c09884c003030b540040a0305c142003101030b451801048240540d66195105c00300e410300c0c0d003400c000900e400110803200b0b41010421401200c000c1030f810a166014440a8510400756a414040e00360035403498841100044a01c03030a0ba0b0f40400320204031920f02c03003805194800c201c601d01d8688100040203009220028 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 519240998 1250 519239748 519239761
    0x40b0a03021b0a05060a091109070c0803040609032006070305040615030303150b04060f03050c09360601020703020103020c01020d02130306061223150c13230108070e09 74
    0x50031081d840d100744c081e14480c1d02e0700e4010900703407102400c000b0201c0405c40040c03001410240595903102c0c1d003524001e4004000340e00d4054a0398020740f0706680d07481e101ca01035405d06400014100300f50581c214029200d441ca0500c0d0341c0c6441014204400b0162101d001c1010302c40c098200740200c0c0ca140d014040b03256070f6850040c005050321032807441e00c0c40301321400041e20b1043c5000e030ba003103441c01d4980d0b10005e50b10920840040900601118091800340002c090350740705e5282040d9207107585070785280807075031107054064003000b0899108694010407080042d141d0713010425400301c4c1d9081c01c003d40c4520142c120b1078064040c0f035485110700c034404501c0180041c01c0d1702000040301c1c01102c08000403520343c080b0704136514400d580034100290301d5808042441500d090f00301021000790a54180302d800c0202203c00c1681540c1104503804d020aa5802003d01441c44000400d061441500e46180b440e441140044030030380b00034180202c103400540510f01404002c5d9901d00000c1c4411040e2a00c1c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 519242248 1250 519240998 519241003
    0x1d01230901030204092f09060d0f02010f110307082104170a230910080f040b041b0e15030616030504031e0203070b060f22020f0f070b070f05040b0a03021b 68
    0x814415110362080008250300381840c0002c270000ca50402e00543c0312113031640064624460400c2100d081045000607516074140500c05401076510401245556005100e0118080c44000c04007118160400e4240800101040c544c5824088001600d685981e2100d1042d14107a4004040041ca6080c0c4003070f1460038400340000301024407007100c41042105594008440340c03007048034000004076907403000c01c010440d150400c0f03a00c50701c503008407800b51030410407458109405501c400c1c1d11000c441c3c14401c40c140701c025011082007040e002000c0a107056070904034140045005017091594501c00f040515104490043c060210341d1501850881c21110013592030303025580a503104250303000032034082c1c230344203125007030700ba83c01020300880729407124410403001d925085918142c2c0c0d00b0000c1074040707048040a0030030005146c00190712000c03542025403568100411031810040361504100015800205450903985e6190400762100c01114040d40288140c01f0072581c1e511010828080d0724800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 519243498 1250 519242248 519242333
    0x1050906040209070c0b0f040f0218010321050f031302030a0f0204060e0c09010f020f01060909060e03070b040f0f0f05061005030c0f040e071d0123090103020409 71
    0xb642e803c2ca865540400490700e110311038070300402071520070000c64000c60121040b5508a4090305800d000c1d00d0080d4009030700603c501510301e0110301d03c03400410500851600c000085210468100a459041702c002404c030302c140101611400741c00b20101c1c07000320021007235521107031b4054211040c43d40c0c2403c0000b005103000000302e224605044000c142c41d040310141c54040c0140c0454941400740107001559540e17007544115086100718003a03500e09038004d00078a0003c0c09c0c0304000041004003410168140c42120162a649a01c00c0100310b001425031080198403d40000c00003942c0421380c5084218950914000307070010103d8848441803200114110740541180250320200c4c554402c141340c0c50744c02c41e040a070f5101d9040c106000c0c1e5414640c104e0302490300c551003035030011525000311105000c40e108000500c2a6428010b01068980301005c440b1038910f0555142010000c000141c070003001400000d02481c0c41d494030008100d81600c0c408418410340b43c1d90450740c2244041c200080e070b60f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 519244604 1106 519243498 519243503
    0xf050f030a122606060a08040c0302100327080a03021b01111b0606061606090b190c0c080301150504120f11060c0706030c0509030105090604 62
    0x540003004603445458682c1180520f81d528055003108103201e0b0322900030540c205102681c0c1d945019207081020600e0305c1c11080d80c0b14030b8181995111a4002074103c0003110f050209160150084c0401501d00074402c0c04103081a800e041e6069184a006005400304000030251284030750002c0043d0852090359020f00520040b450f400c4503074080da604403070744000c02c04044004215000121015005000341824280800090020b105403004a00c004000c10a00001c1110b150000c03030701c05800000e060040d107001c00002010601c0c1c540c8450203d85440b0000300b241c2d000d40708000c10150050845800c50303003000d9500d2241d00110041c007040c41000d1100040c034245200c5002e103401d115241c080360701c82c028544880700125040e002441030308144800c04040c00c00040d81e0301101e10358540851660102803094dc0d4904ca401d00300c030340550034003081216104000407210300991 = true := by decide +kernel

theorem cover : BRFrame.Cov 519064748 519244604 := by
  have h0 := BRFrame.cov_init 519064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 519064748 ≤ n) (h2 : n < 519244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
