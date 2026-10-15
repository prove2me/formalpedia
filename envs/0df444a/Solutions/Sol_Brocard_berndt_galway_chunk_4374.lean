-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4374
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:24:51.368216+00:00
-- url     : https://prove2.me/submissions/e33af380-c58c-43b5-b00c-fa4194286085

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 786510791 ≤ n < 786690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 786512041 1250 786510791 786510793
    0x240b030903041a160515070509012a0c0f0e090c0d121716141201030f060e0307030c02030c030a110d0314040b1b03071a062806230318 59
    0x8003c2c00100300b0300c04c0071801c6040c0d4050b0004c0d1564620310702c20452596002200c0d00380282094150b2000800f01c4401440140d80036041c0d0b4030a12442104d0407407246802e40c0418940c400c241c03900d0308840d08024510030f22906200034804070788500d10200d2203031904c0e0380c00348c100c00303111090783c58042d04850080319210900115806030928101500c240620a03190281000f24107045144001e02c00120700010000d000414454600c5c20a880042113045a40208039105604020300f0040d00401c034a41d41d84620f07200024580d02010340001190794600d0089090760a51180362050603100e508041d002031641d807100c181c0b100c5501d8000340580d07005009203405611445012107094031a4000e8110800032200482c2c4404d5001d100c050041d40740041c00c02844c10000555518880d404500190000180e02c85000400c00e8030303440151000d000400709500c0241e80840c1100107145c00741d0041200040741d010540c0345101d001d10001c550f4030301a0200c0c602c1c41d96403100361541c1c3d0082540342442 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 786513291 1250 786512041 786512047
    0x60c070f0b06040f05180d03110a031e05100608090f060c1308070f0906080706020a080f090907121d06241305160e0f04090303020d240b030903041a 65
    0xc4002c0c4150791050828501e4141c3c980001b404841c030341000c410401003014100541d407040603802c0c1c01594006412401d0114078481d051000810030042000c11005a51500d402c0040c480020480081181c0240c0c580496940398040080c0c0c944107821407091761356200b840440e02841e8002c0060134001e050b0500007840c96215519a401c10701c05520062200400407000d10462a0902c00c02008226200007060424903001019480e0a484039001d4120070b40440c4074110806544121480d11500030301c1c0e440c06203013562014105008bc120300c0c074042c900e054811400729424000d03040100d004100105465641c4540e2491005490480c0cc04900c1404c141200d283d20740010510380301d810454081664502464040251032040790214104020080704840d5601c07103180481058000350342c007046248081c2415400b134440c81c5441160245003102d01851200041d900700c0703040203e01d0f0554100c0d40d4074000e00f445404260b800b14116081000308021345c4180b4600c421f1103002041c80e80e42 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 786514541 1250 786513291 786513311
    0xd030c1209080d0305150303070b010e040203100e010c09140604050f040216121205010e060415150512060405151e030313080f12030c090a0306020406050c060c070f0b0604 75
    0x414000c0304a50f14021075220018030568440d110840d210300c600660041d030401201c0d0f11090301000041c4520f1004203040004542551010f01c00300707820301000701003849034059024200d4020458440c0345800245000400724010310940440980040014000c60038141410304024030b074603014108582c003d03402c02495002c045400320580616000e0076590909010001c800360a400c400404d501400345000010700c05001400f502c5c5070000340598000907021a100c50041d03811510390440c60201c420841010701203a0300c00e0080820399640508405540c03100c01c1071000b91031041d07030170642000030f40c0300e00c158a01300780c403994000080d140c0b440c901c1280071202090441c0e11071644845032480010b01841104d00070010280d1001c0d505004040c8043da8509851042c000a403d04000410018031084180c5c0d4102d000000341d6040482107546a40e1840701030095440100010200d00802001070b404404081c1a255810782104007001300c00510ba0750145c000c800145541e030311a568035424a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 786515791 1250 786514541 786514543
    0x306050a030c1706060102030a0f0c140f0f0102131719150515010c1b0f0902040e090727022703060a0207031706060405131a0d030c120908 61
    0x18008502030078000d400e41e420303c1002108480c1c41ca0380d5180320760000c01072001c00d9070700200700e80d00050076241c0710502c00e01c1c640c0f04480310701c60060084c3c0100182405007104107000b01c0c100310040c2800085806c502112000d641c240d008001460325103a03458031080040503001b034660203543c0c150106642402021002c64420542403403410f45200320b059114a07200c814030f104075a040f01080854500c5002c4070f1000a0000c00c014200800d00203002d210800380d1400d0f801e1910151480d0340c8000f4825440d181020001d420602c98141112074000100b000c1d064041840e40039034444500700c003901444400b0400d459011010445001c1c3d600f003061821106400c0510000e600f00004207007900e48001d0304151900c0e0b00900040107a9104100803c006504001c00103100480345070120745541c0c42100040203805598001a0440f540101c042d06041980c0d001400c0c00603034141c1958a0500e00d802c0c011001010352000707000c80c1ca020b12036000b10f400f03005c40084004480c6800051152528211 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 786517041 1250 786515791 786515809
    0xa08090a0f0e04020102160b03040609080408070909060b0a050a0909030e090405030c010c0203030606072603091501140631300b180a0501140105010f02010905070b0901030605 77
    0x800700403800d90b0240300856906225650454504c050000b52640c00c2091002403444068801407405039900004020400312005480003084004241c039210f03a950320f0340c1d81c0505525042180c1e9245030001141c40b0380350050040051701c00213042813242605210700c1c040140780c807030400d405008041500700c26940d56120200c1c4181d12171800742d6240d80200b031032942907807480b1030144103540091080110b541c4825040e105555000600c0c03c50940702c143c440b0030f010300c0d8030000084041c0000100001840001104155801e1703c01e641607081e0303a075905840d040b451001380c856002c4e008100310400c070a0420b8000300f0001c14003200301c0d4a078515550145144075641d0244980920048800e900c6582c01e1134003012180f0301c1800c1741030040c080ea42d1028507000c02888080b03880d0300403042c540e1540d0100600c07103940c0c0d07001d0001c024480d43e00c501c8a5002109106150001e41d0314081458654818010303032403500d502400903c00c19007440003904442d0840c29405041554501d030008180d9200f07049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 786518291 1250 786517041 786517049
    0xd080f0907210203100501141507020a1409070201050403020a20120619060302030a080a02030717030103120f08041106070b0c030a110a0503010b0307030e0a05060f1303020a08090a0f 80
    0xc044503080d02c2d205040c00c00e0b00080d01e131080300d86807400400c02c0c0349400740c006c1c0101108403102d0004002100d030302c0c036207406200d2010703411101c15503022500c0215810205594002100c1d1713103a180d601e2180480c00d990301194000c0058001c0480c290025030707031801e41e264608810440d11414011100403910f1440440e803601c46951108040c4812400396040032007050702c050500707012950850700826900c56a01c038004100c00e03c005200d45070070b4402c1c810764000710342c417110a0610247c40301c0502030300e8001f030106441c81144415600c034068050034818035101c000c0c0c0c64049140d9526210f000041017010405034020000b046220002010340d0701c0c0720721912403614401d84a00744440c81d401119400804003040c95001c108150605400c10240c0e0304641600481a51360750300d100c0704602074680c4150204c00780c45008454003c004c0082102c074031600310642031003000c2d6914201841803036594240503015170041500d0320007148286006001f60500580b102d44040d540f480516080011540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 786519541 1250 786518291 786518339
    0x5060408211c2f03010b0c0c1201020a410c10060f0e04031e02010f1d0c0609150702040b0a15170f070819060801020414030d080f0907 59
    0x80c400b003248a45440c098580407102c20010500b43c0068640314030044c000c45440080214040002000820980d505a00c010782000e07040410003400c14080e4111200c1d800200d0308000c40c048880100c8103084000451004070401c90108184620300000103901c00b50203010010852041140001c00c00355200ca0459003001901c2c91510ac46a483c00b54190800070340c24180005000201c0e620000415800d810b100041880300854042a0300515002e50303800380c82400d01c44002815440340020fa02c8031217603c01603400103510941046500e20445070b0b0303191301c280c00041c0c400703910b91424060301c270f00c03440070b030001400708501070000311000b0f0290312601c0011004901c085489600c5000f54002c4207a00001d0002401e0000c00c000c1442d41c010304202c1000084400502c0c1100ca0144400b54160035820800030540c4400d5598040e6000d406122107220907c0324448a0703041c00500f94440d0041c590b148055500c4201c40705500120180034500d403486080c10201e4600079410740e040307004044403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 786520791 1250 786519541 786519551
    0x30102040b0d3b010603020904060203070e04050106120c1202030901050103021e090601111c1823040b0a1d0f090d0f0e01020708070f030c05060408211c 67
    0xb404041c1e403614040080264078008249004403840e41090a1080b1000c55002040c1041c1039058010701156201039071151550043c4001d0010385c2d4000c50042c0c00c04c0d81c500580c07544480038407042c0ca00a20030b10001444003001818140715903806580e041c40030b4a01070718000e07010b0300d42006980055030b03081c1199540c1c1d4010821407908060241101441840641c5601c00820002e54018401031101e414804d0b9036940502c0040c0c24130480c442d10f5080818055074060b00b01e0010a0b0b582590003d1241d44504100483c00d810a00880888465140d042d05401c010090a11000d45500840560041515040815102400540c0818103a01800c0081142c605131041c490942c0000c1d140c0d8441ea000004102c100700e607c000000c515506901300300040f000e1002c0100d1400210b58420712140c0035000001c2442403560035000c3c2228003481c51240075a071200b042200e81c0c4078034410b41d101540000d4040200003410207400440c584d03030149003810041d50b095155442c040e00d002c1c2d540303c19611 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 786522041 1250 786520791 786520807
    0x3080f0a0b0d0c0e09070f05040f09051504111801140d0512070204050a0501321c021003020f0318010f0e0102130e010605070b06030c0406060206010801051b070807050a02030102040b 80
    0x8400b850b0710802d5a801041c46c14980204110704400d070b0b0060764044c7d6103401e05100154415048451460381c0701d8210b40300800ba01980040c0342c50152800c4850385d5518401d40000d2404d8198200382d149001016040c0f44d1a0003012280c000c0b14296841d003003613010050354007084041c0050079100c050018003c2d6100f40501c10401244c0c0700400e102e084038581001404102040308a01c41e0113801c900d8001242c1404981e0485a5481004004e501941907400301d246200c02d0003a01c01d0883c82543c1071401e52040709415000c0e801203c20310001414140002006420141200180324401c100002103001caa490b01c07206407103202e00c0c9111160b400040302e03807040000400d0a030090100010004140d41018001400da20031900e0240100001202003200e42e5400c0c401034000d00f0f0020001c00000303a03100b0019460720720074802c501265180400080140000030000e141841c0003240891400c9141c0d594103110f900982c005030350754406c10503d1001030300c09100074000b030040e1b00e00041d169551 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 786523291 1250 786522041 786522059
    0x1b060b060f0703110a0305040303030c0903080d060f171507110303010b040501020c03070b0a030207030504150c020102150621030706050f010f0f030c050114250201030608060403080f0a0b0d0c 84
    0x451105501c10341d103d0317800702001c06c0c0d0002c150340940e90305240200d120143c82070122074500c6960405401c45a000801c803180394141e5000c6411210301104c100c00c1e450343ca14400c00344411004205442d90000740360b14009401180c5055400109400c042c5074414901040d6851a00241c0002800d075800080c14445980c041043c458426012030007000070504100c5059006e010368441d86081c5034000c0f415100301401380d01510007500b94201c1c1903480195049000b0240c005411059000d4012000350740c02000513820365a00c1880040c024202125a4008506424507001c15080260100b8000f00001607500d003c1c06004c0c0070480c800c100c0310350600d00d01c402032890560010b0406200074200300b002448500381282100e02c24280040c01c02d2107400002421301c54000f41145da200000300c0500002c81d003a0030a1080c2d0f000307903001c001068035640103540e42e04081c1d030090085400708000030f08904818040c03591000c0b1484020901203409008500401d01248080780d0781d20021100703001c103510f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 786524541 1250 786523291 786523307
    0x4080102180a14011e1412011a031b030a0f0c18061115060402040f062f0606090c04092a0905010c0f0f1a04060e030a1b060b060f0703 59
    0x251090b00c03a951166824000380840c0100002d140050803030500d00d0b1750403805845004007891042944655844a21414600d4520b09001d0b8881105c010b500715200c1d003084c1c406807032083c80d40241e606e01141405c4e840ca1450b40000b8890f0070702c2c58440e021184201d069001d4003c0030301c407549078030501d01030410f181c3c1400b80c8182c010204201a80120001c01c2d80d0000308841502110b4048800381e444401c0418085d1245411903609495103000c00901c49a00c1641e00740080846002204140f00780e141c0040c000788440c0e85092103038462004100c052400c0d4602035000340443d40c869251a554034a510281c0e00c078518076a410795180090940c048164900600c08081b0905d00780904504002c0007800700241403070003034035a901700101501008007a03120030700400d0300022141c01d40c000702c150307080025804840448040c2d00b0042c0c400380c0072500105460362400c05032200780c000c074061003241c040d100031031501703a60b201e40741d02400c12a9101c010051034401c040c0c2e403905649001a013000b403c075035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 786525791 1250 786524541 786524549
    0x703020c06030907090b06120712051303050a0513030c060903110415032a17010e0105070e040b040603020d060b030f0a030e09180f01150e0105130902010504080102180a 74
    0x2481c02c20800c5078040c0003041e10700c250f0741c0d02d06001840b43d01c40c0022031f900f8004ea0ba10030ba4510020014003001d2038000700c0906002c541c0e1141070245079202e001410b2083e080c010014007040342803101d02c00e902c1c05070300070f45100c01220410701c40c00d5070f40e40c454025821040d40404007290b5170400c244248420a029000e0485040d60301b80400341e0300d4060445005030714440034000504030017841500d4254a03c0316281c944c1c0900410240940704c1c00390103520380032a03410b14620b600c2d01c4058881c41c0410700606101c1d09050b100c0e0f040d458140741c02e2001508076203c2c010f0b84a9034a840c040016a02c061980c04001d000f0900014584030b10003c1c0341c03a2410000b0500c1003644035550a00000f6031001e013140c2c0f0410182c1f111165500c070301514081d499005180012240a403c0c1599420081580003a140203c0040a4007a140d40d41980c100000000c1c011113803c0050404144e584401942021080c2c0e031040c9000c9141c603a448038260300f2038011b600c44a000030300b404000c01c0036207400c6c24003074090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 786527041 1250 786525791 786525799
    0x9061e022502010512011d01170d030506010e04090609030e060f0306040b041d150a0b0102030d0b1f030b040f0b030c010f020118060504061d0d052209020703020c 71
    0x115031000e20061440900c00700314540405168070380c03411648210b090304c0c5841641d00d10941d241d6104c0c0110142880e03215900c0503c9050000000352464110600303000c0313039800801815800050840842c06000c0c001c01e071a06029002141c0d21a6454910070480020300a080000e01c1e01c0052400410919840e11240c0c40b0300c00c00d02070102c44000b082c084030b07080001100e000841d20306000100d07001e00209015000d850082500d04000c0c5031001c42c11034402030045800c2800c5654400284045412604409005a0052040701c100d164194040211034800800d00c6408005040308140c407041c22800c0c13107000a8503074141c45007a041501604449000e03d2006101c8500c41d4401329688040550800e030400c1414050003503214000c3d4032031801c0c07614413a9448014a8103050001c054901a2000c0302d90718509012100f19884134054030340840441005030101ca11011001c0740c05800100c0c1c0642c9210040f817030a103001c02d003117140c0d100420941d04050f031600a10700740a420000c07241c00c10340c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 786528291 1250 786527041 786527047
    0x3060f0f010807051c05040506040209160e0d050a050d020f0712031b0f020301111c152705040f0203151012030908150115020d050304030302090d050109061e02 70
    0x16680c1c202400b00d42c850928605aa1a92440001182c03a150251003c844c02451301d8240f105000700428154805c90007610a000c641e00d400000e44090b011001611001554402525010f03240ca80d0000c5442c07801201110040c2d01070f61282e906203d08015032102503030102c5800224200144811001400d102e41c1601a940390b540b00500b803003260f012480c50f20368801154108010410f4481c40c2d1458010b00200060544035541d4803c0364448440c444000c00802080322052809004010400031102c607185076441c81e0102c0c4101504141803254034412042404244140c8507100340b62107503010303200c0200d91540341c1c0103040c240403810b003200d1080201c0740c0400004c20703c02d0351418100c401c441003d440a400c07600f0100c03800001c6400210781c900036405c0c03008010009070412030684445000e4075144100e00d04007aa81c4200d05145100420810310008000c0303030007540505240c08000d0032003011000d1650f1010b0844918040440d00c3e10760f0744e4441801d04a40d402c0180c000e244400d01145 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 786529541 1250 786528291 786528319
    0x3015061e0a17090703050d1101150306150b1801112109090f06150f040803390a030518090907060f02030429041a04080c04111206120a030503060f 64
    0x82c8030140c005111048c81103411002c901d000095005600c280304446000b800280c0301d180400c0503003410040c140020b1a400804121804604c1c1140c0c9480e488801071010080513100564011001140c0800386009120442500e01e00013503a40c4203241801001c5659100300004010004070058020340d5106440b500700210b0351110b1b99405c01030030303800e410b598488a0182241c0002c0c400d5401000c0f5038013022480e0f1035020705c80b26840c40005401c504208690024800640d207000080403411201d80c020742214010030f0081004041010780ea460b004e04c01e0204001040d0007113025107c1c0841d40c0e02c5114204809a8029100f05803180544040c5141900d400c0c42c0110503115204411180c40e50102003c200c04451406c5600034408001c59015a05000001c0c1809411901c01c1000f90302031203030511b103035180c00e1048401107884050000c0c10b025034000b015070610300003805180c01095100e25040901020070040074124480e5a41542d02d10340740c800e104011502261041c015612111950 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 786530791 1250 786529541 786529543
    0x627030307150f060303021506031608030310050117070e030703020909030c1c050913020909070f11030301052b0204020d0603030e0609060f031b3015061e0a1709070305 74
    0x18040056550200241c1c279a00c0029040100c04000c1804100b2014800222400301001440c4a501d400c07103003100782036852005403000074120b02d448080c5060003000030145801012841809140581254079241d1a82d0205032101c00540ba94805a070000c503980015002c10401c030240c085100d0701c00303028a90750300e5000e05079000d1082c995208502840d00200214841e5040d07030300340e42e001445d0144505000c40003030002c80c0303c00b038440700140d0303080c000074100c040c0001101d04031003000d0454910b500c1034000480d4110404514064412070039401a00941e4950019081c0480d00c039000141c65031840c0713070141800f254025980d000320f2042c0010003050b0384450a4507900414903207175030b0f030ba80d0380e000c030042e469013040e607591201d03260102c1c0284100d5045414021250f03903540802122a40c00415129070035001c540440802d0140000c00a550401101425801060402201d071a107828200311596410a109010020300d1140000340000350007d02150000411400f4101c1181152201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 786532041 1250 786530791 786530803
    0x61a041b0e1003090f0b0105031b03070b1803010606050c0705010305040b04060506030a14100e060402030c3f070608040b01050d0c030b07080912090627030307150f06030302 76
    0x115101c1d2850185004420780a03130003401c269644050703c0f42059100d40b50184141c0e80038003442e8080d100e00104c000d200441ca000a00071042e0050060006603d0702007840714642c0280e072a0021424082e0315136819840c24040c0902400c1035459103922040c542e285a841c114495100504040c104414440450095a12207400c00d0f00000080385550f900004207191003023058008000c02c022140d40045480085a02c550101015806020090190000b01c0e41da4078103540180d0b05030400c00d08a00545041418440c1401c4d80f000d0880304200e0400d0209044070900000c00c0740daa03164a01c0012601051003038030090607003400c20702a40d0178641c1311010418170500606005074051003460080c844117001c03150003983c0c031100078070451903d5130004003269400c0d01c41d0b4989100d42c0c45011400140d00781030f00e50202d00078000d00d09142c054004076098481e814540099211807507130380540392b10103000400c2410b008403400e804590140e0480000c903040c2d08803d0030000e15094060002a82c08a00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 786533291 1250 786532041 786532067
    0x9121e03022a070803030414070f0501051912020c070e1e0a0504150f0c0905030705240403020411040305070e10231026100b0d09061a041b 61
    0xd003940140150703d141103400d41000314640720210410041020042c0039844111801c4161035095590b40c2c109844107046d801403601084090220703401c05103580031221201011403030120007a40425904004a80c07005031981d031550450881400420f17100b181c1c5075085110400f0300d0000c15002c0310921b070324540242c000c42d091529640424103010040004500d2804c40600422405a911000340c0c020803600640341c003c0742c2000c40009451070040f42c1c4e50304a8102401280c542d84070030014015280d064410001100700500011016031100d215420410301e84148182e070321400c6090440ca440ca107607100141d50402d0744200603d070160818154103c40d00400e41c00d440c0b501c8280466040400040d11940181e04c05415172416917010010015600e109040510000d0480340101100ca0044544540401149004224030b460000041154036001c410001e060661a914001a15616080b007140404100e9012015146c0f91044001c00e034040134810021411001000d02410801c2003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 786534541 1250 786533291 786533347
    0x2090c2d041203020c09070804121e0302070203120c031e0403150f0b040e060a112508040b1305040f0b090411010507060501080a06151a0d09121e0302 66
    0x30700e030b0415008000d50520001c00601110952a200000800501c81290b0540d00e15070844a030002040c09500c2e260000c00380c0e0840300c404264001e0083c0c000c2d60004408a07014411206c41c520005450f030043c190400d0b001c800745a6590003048000541411921114120381c404c00003000003601d10022112440148100810903000d100503140061440c060407940150411103c40d91110020482501c2113801010400091684000300c110034011000d845c00c031003880c507400d00004400825804c074541d1250742014035140c1c032001404460381151901407984003c41e0700a00c41d9242c24007992521460420003041585288c030006401050042e0026042584814602c9a180d1150b000c544c02d09820103428401541c0d18111665104f003089001d5551603e002041d100042103042d0600485c0e040c0d15844101d0456080c2288080d4419144c815600307940d90843c41c000340451a03c82c03440c1c000d58541400c00424803900d164140f00c0c5499510815104028640202c07654840040300c50b0313a100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 786535791 1250 786534541 786534569
    0x6090a03030f0216030c030207080a03080a0203090f0a0c0e150603151203120907050607050304150c06050f1803040b0a05130815150d1505040c0302090c2d04 69
    0x140c0a82c02841010711031003000072240c0d00a000c1c1500003054000c8280700b5400c90740000d5031840590344070580454010001030346003010409410746500515009611582918484142c00b066245404800f010440b20981070040030040f844903106440c4c2e00040004502481242c502c00043c00c0d40b200510114541c218103046e141c2549861401c040c041c1c041d00b084030340d01c442800c1c440c0070303003441203400d0145d52140c0342000c94107080c840207561007954003000540c2400e0410780003c0ca51060380d540c080170061a4030810b40410114021a40190400300200e5841c2c00d0020320460035028041c02d01d00f041e441000104400741c10300045580c4241d00d441c01ea030310389207102c00c41c02d4190840e81c1716403900e01c11603002071290524401d51a000c0d203075400042480312281c0307003804480e00040c0f2010f040383c0704000100e800100180c101d1588548145240405152642c4c0001c41c24041550007168095001c681643c41c19500710081140c509071100101d040544041d00030618440ca0080e528503038001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 786537041 1250 786535791 786535811
    0x30c1e0309021003140903070201231303122309010c020621100807080606040b0409060c02010608010b1c020609151c0f090f021216030503090f0306090a0303 69
    0x81d03101c6481c940e0300800c440e03e0f40d0021000100a80803202e4031130081c00000002c2450b0b02000000c50321210ba060310780701c01d4804062107440000c5074044070b2a0845604002900030310441503207850140d4411202841d40511111008048040010714816070303503d4a60b810510401c0282512a4100d09191414180e0514404600380e405080607156000809119a0403640e9100481510a242c946082d00c4c21707650300c1904542c0c84065101d0300d2815000040890400c1c00d0541041a500c04041c0022401010360340e1030404440b070660282c00180d40d1103000340b0095a003805007290020089500812030302c0c07000780c1c01810b15000e40b0028490140001e44404136200c01d03000c04242c07100404215200c06800059120720a000300110402901d000c1e003901a6644030311401c078607d9000104c5052800f02136080c000ca0003060b0303071072811607c1501c490052144000445102035032189014581351108074041c0552015104241d41c03003600203000300310841c2c50000b05a40960f40614012480c5425 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 786538291 1250 786537041 786537047
    0x8071718210a05030406030b01020a15470a05030c0d03020a0f1b24031d0118060b0f0306070c0812090f0706030e0a030c05010b03060421030c1e 63
    0x5504081d24034058a42c040040c0f141c0403003e441100e456880500092014800480c2c480d01145401803006002a00c0b12038a400d140c0d11080e1070ba290084654041c803503c101c60302151651030520204044096800002c0900c00d00380700040c041c043c0d5007107404505100002e925032410107c854040c00030b400d1502d05140c402c100c0c8102c084d41100030b1360855030107410903020a244101c0001d5010300c10080000e45030000308403003401c0981e80c1e03c10000000400c00220080c00258507e5141460312621a1140038000e2041303a0102040400c808544c408615107902550100311040c1e209a50702080100c0c282c402240c1d065000c166450252141f03100b03440c2c008101e0144c44040e6800043c140d00b0001228030016194401d40c88100844e01550740da139504405031a440c0c00c10002c1d542006070400002401400e0380b500f6280314100118a8012041c080382c42c003201110192401c10301c0303040000d8410741c0d0303030020500c01045140512928120000c06040b45500c0d42465151461604082c020320b44 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 786539541 1250 786538291 786538339
    0x90308130512070602060c030f0103021905060406090e01080a0f1b090c1715010207410a0902130e06040b040504050f0d030b0d0209070215010308071718 67
    0x1c80205206003820307003400c40b140d40b5180342c0a40c401600c02d040100d00d01c00544030a0b80c1c402c2611900d017941c141e09684c00d11000402d03103550720401d42d0f16040d010816603a072a0241014050b19520007400070b0ac0c02e100701001c9441a03003e000550406446807000c980300848901040d90407034030180f042c40211424000e40e203d242c0c42031241c10f14250034484000e510031f14052103114a0000c05003646c85000c1c101a107444195a4640541d00034441001601240802c0341d070f040c1c1038081c00c0502401901c050a2241d039901e95100203605440317000203901e00e0010040c41c09072170210402c60070b06100001c1101584041d0094180281a2200140d11a03070389400c180f200c0314000c0d00130702040c141454003950f039142002c0d5040050040b807865400355032191044074003100c00281b00903540c8a9030340074032800183c0989050210b000345039001d105485109003242c000d520948409964a0080c24038014120540544105810b800c101800713207424003010b0030320050001c490054001c03c50900f5616004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 786540791 1250 786539541 786539549
    0x606220902040b0a030c1b031407021206010510080705030121080d06030308062b0212070311030d0e130e0309040c08061504050d03030f090f080c01060902030709030813 74
    0x81c0005404584070003000d02400c4984010b032414004400d0381d510176500e41c10040d592141d0112801582c0000c40d1003000083c081030710800c841c9182160b07a4011401584486100707000c2644018010002803c00c042c0b404400146071902c4411070805017401000f03480180720b141030046414018007081140560410502e56015910030b076281c00301c1800c41c014029510080e4007040742c0d1400500c0da801c0c000b260202d0007414004281d501070010824505c1c0c03841c681000e0760411110b020903c0c07503c0c0d0400502028500443c6100131602d02481050314107191502007508011042c18511400d49886a00550840e5180340105184039404138040c91405242c12013544541001e080071030361a08054054011003040e213445500c0750301603000c8121841288102a0031409440c01c040c0420320070750041c05c40940700b00000c194007001d070701c44004e5043d809005840200c000240800055801d2140c50001c0124134000e40c00d5182540021303008066030710002d400d005000610a28150074000714134060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 786542041 1250 786540791 786540809
    0x17010207053c01140a11040905100506040b031801090c060c1407150e03010501050609060705030909161803030503010519090e010204030b010602370b04140c0108060622 74
    0x4440e60400141c0605542d0748105141c4da0380b04003046043c0994000c00f03142c074600b24080307441c0900c0e0240035030007000018440040b03000041ca000c1071555940008000424080f852240c40f41400715080d5000402030046c901c0503858407105900051412040c1130031100c40b0f042c0920311000c20f0a01890083c0900c2340c030003080c010300d10045044c00c04030050303256003403940d0746045103d807000050608840d070070b0140e692b2025090010b00300c549090310040c10002c4c815000c1e2400d01c021540403540b140b0041d15090740d00c00b014008076040c82c1c0d00c260003103055051154202c003128a5030310080d0807840306002d294000c00401c0741170f03982d9a80340100d010040c201854104641498040118003d4125000440b000300804000142c030a10010340720902010004200342c0741040035003410040076001040c9240000002c000c00082a5036018061040c4d02a40c2106100000180d100d4248241a50424140800d180500045855410a494403201000400014100d04203c0080300c0207040d40200c0307031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 786543291 1250 786542041 786542143
    0x4091509060510061103040515210106110303060d0327080303010905100b220e071d04060e040204050a140108210304021815060c01061701020705 64
    0x40148a0780094030403404601c00032440f60f11040c045940302c810f00c0700c603d0960700a000074803080c0f40c81400000c242000011312850403010100d8000e0041024a402460600c244010800c00790400100040204084003542c65403400b02c00041c1c18014200340070b070030403015a11191807100b0144071020380c08400f024146131259a40078007651703030b8030901030141c241d8180008120305d0034660b01010281d904204940d810699144000000444041c5400c10000300c46040014040340ca1000d4074091105a6501045462a01c07511040b40d0030380c007652805140340030410420aa481001182c00c40d0f0f0423940411252180c040003030292889030b400036442e000f40400081e106100207115031805044c140001c41461406000340218001183c020707401c611184001c12101880350305c10ba906c014501c4100d0414012480850b04e290011034407954140c1d92000c09005091440391041034030b819000c001d5117440295624652503491540c100d000b6411180001c5112410f6408412460303181406100341e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 786544541 1250 786543291 786543293
    0x4111210060812130b070c0306020a02100b1002031c14070f020c10120507030f0f06050a08010203252309010e121b030a1202010b1c020f04091509 64
    0xe0a803403062001c0c81c4940c5102081d071003d24020b0742c1e034003141d010b41d00003100d180c164109907a03444200c0861761a00400c10100000b0f4091024203022182136008092816081003004101e412000c00d0764400d04001891480e10b660020417502c9884d4942100b881c111032004128010302003541c054410910b01200300f100da40da100c3c030002c0386030701d03140c5c200c50449030a0300601c900148090205000603048e1a80c016041916412294020391981360000360700c00310f28111012030307006540340020f00740c4400080040d8948515070030060f000f4040210300d142006030704e00c40700e10540086d494092201014030810b1a004200a06581d500415202507c0010340d0016005074000c1c5800f0b07010800c90f040c688582c5c01d02e031190082c590035000046c0381c0d130b0070803a04419070010010260795141c031800b01800001130303550f844260f26404580010985158480410404070103203801c0119410146072100090303552056200c000c810140c2e0005040c00ca142828070501d81c48580e20350310503042442041c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 786545791 1250 786544541 786544573
    0x904030203121005100507032319020f0a060c05040906030606030c092d060503030f28020a1e02040212060909030901050d0c05040317042301020303041112 68
    0x2d44101c02050035540c0d0207100703401d034441c2c0c01140e40041e05400200301e0b95004400610195000c1c0c20003101054400a0361400700e05043c0010310b0710304001c1412031444c0203242039400c042501d40041d00003031802c2c0008942d94481d00c00050401501c60f04c00441c8640100c044038040c1c21251000d00c001922414001c000e0f2400e0b100449424a01e000c002602e10464410f10070515144e2400100110004410100140d600030110030310381c1d80c5000004c0e469a04100800c2d24042451005880d040840100c055400d03001074412050403c1d0a1102605980407d161441644c003682603d0062100a9000c040c0035505400035049440018103012100090340682e1080004640591031903490003d425242c2c00350101d19030100c1c4050041090214154100b1502c140e01413501c1d508050b500c1d1645090005400d64030710a4610006086c01440108025050a606600454940d04500400007542c074407001740b002d00841c5502418501e19039510120381c41c4101c540e8100d0300d03022007441c5d42e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 786547041 1250 786545791 786545797
    0x114040801051b0702060a080907090915061a031f0e13060b1c150f0903050304110109051011010e01020d0c1b080304140a020a09050609070908060109021303020904030203 75
    0x10b10215070703900143c0784042050748101e0310001d50140c10141403440e401c50a8403100006482d03c1194041e40c50b003c100f91b03485104142c0c0076030003400b105584020300b04174002141c410341c210600741041d501207001220708032400c4136001103220040b00841c98000079282c6582e070316508422110242d820501c00705045c905904102e09018000030049008003404000860248091864900e0004480b010208269640a10750703021080408100c5000d0410440c08542414170f0031004a1404024801031090250b89840041c000782440f003802400c0c4000504070500c0c058514040284188140b0380701c0b44203400008041c00904001d5448640600c4005e0140085a45080000b415085080504103e030140c1c20710132a0014005862341c0c480d62145c016880009140f4040c034442d43d071a440058842e610040010b05000d200050346003080410402c800002510200402c2140304003409a1100071400f641110520040160340c0c0302202c04101c0a0840359101079400351101003000280b540100003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 786548291 1250 786547041 786547051
    0x6070501060e07120f0e0601060311190804050f03041a0a1809023103140a1e02010809010b0a06030c0c0501050415060503070b160201090e090c01030c02150f0402011404080105 77
    0x5210170041c000f11581214148442624590700c5040100101c500a600140e40c2c24069642d052500c2c00b80c407800006021003d02c1d401c0000c001c48204401d010b020302510905c003a80740003840c03401e4540052404601c00000c0c40f04503000380012b440001c2030140c544001c1c01d01d002803584800720703501d070080402900103903100010441d0120b4540481031b82c43d41510041000341980582c2181192641d5104503060045d03040b851148440f4003001c6084228142a0011401c8118100310600e10004149200190001c49180e0400824101c02da58031085141660010320300011035201c0c1c55000c9070103d04004024241e5460300041c0070920109105201500c1301c0b1309810300007113941da420f0550741d00e0b19100f007603011350b4140105082c0103080d50904280500502d0408452500c1755003900c40020151406c2c0c0c896803000c00088010350301401000202507107030003d010207001c1c4581c035000c8c44000600d0039405010441c0082c08580c054030581084a030a40070064407a9101d43d6254005c04040d20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 786549541 1250 786548291 786548327
    0x40f0f0b010c03120203041b03050d0212030114090a060504020708030609130c1e03020612150114120a1b0206041a011d04050f0322080102090f06070501060e07 70
    0x20400ca1154051032084036010740c15529400d50b0106841100300a4001030002c50749245001000c850901d1a052908041d40c040d00281000c2c20552070702a15040080d4410306c4881000d000410080080b4448407401c050103a5002d40107545000300d00e030041c8040d402041d8014070200302a0240500d000241d40710321000d80e48040d613500c03400504041002c2c0c4001c01040b020303000d07005004808010314000f480500d40845049655140e6001500b56003003054003580c039800c030318200600c0001300388003030501c40c00c03e00b407224164945502d07070019481414200c40c1c60a01d1a0086002119503038408071b000d00300c948a02c2c00500d05050001e40b140019a01643d004190807101441c0700c0300380c900c95040b15801c0003100400107a513520040c214100078000d0310f0324003c0900401546c0f070280002c1600c000e00344090304050004502c04c3c204050241c114080384d07031060001c01256104d0b0040c484201004442d2140c90340050724144e4090319498000040c15815a024441c0c07803a00318100d9242e9800f046 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 786550791 1250 786549541 786549551
    0x1060909061a100f0e030a03080403170402010518130e160b0a0e0f180406020408160308030402221a040f140c1b12091c080720040f0f 59
    0x198a1501000c034403090b51140c054031030900103a0041d00c901e898440d807401d080301c0081c1705000003030501060040070b0300800c500e901008205580410030320643c85144260410714202038000070070602604010b10310010300d03500c03e0015540c82c0031644001c07600c2948203020b5214a40d03041307502d0341035065031034203000038504011070380c44450310664207800d0381a41c1d00340d1364041020410100031044a00180c1040c14141080c000040b50700c0303c01e1007603000708000360780c80d40f4226a091402080c1c80c1804080d0120b032600744002000e080c2140d400540413141040c842c2203405003c3d5004c030f04403502c0c4410910700520310a030b02c000e4007015030100b00c040b1000c0010230550203004050ba0103121800e418480107200081c0603c1d2030380c024000000a90725410844991014481d01d00003c1c0403040d0b02120010072800220303c0c001680640c0c4400a4030304d00302800722030fa00e00e03800380140c240c010001002034001880c600d00802c240c1450b500010018080132600000d0b40e0000e003940f10139600010700744 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 786552041 1250 786550791 786550811
    0x81605100c030c02061c020a020607020601120302060406111903050912090d12050904020403030e0310021c0f180614060301020a05070201080c1207050301061e05070f140106090906 79
    0x4410118029401d0740302e8a0f868102c903400c1018907404801100407000c000e11700200b04040300c0c4090701050145400800c0a0300f00703888042e160800503444040b051200d405039400081c1d0215030135812a61008000c00c954114591040150040c00f0401107803008a032038008210344d058000b00c0c01800060f0581d40110b41200c0052031134031985004a400004e1008100d0010303904081420020b1640d141050901c1e00140010f410303a03010380d1040d000200590219078451805001d00441e81905550451030229410100140e031401c0c0510b0040d4030390358440d1654802c505070080e030aa41c4181c840d0700110b0800e0714114004103010107010354131160f290000b8005080500c200c031401d1900b600e4aa0422000750f0045403080d5000b00701d003c00500034400b0215148800b080640103840a488064880d0304001008204604504001980728085180300c4103030b640200803070301d02a81040c5403900c0720a0300d0802e15000300362071b00c2000003903107443e20005070400d4a51241e89a94450030084c003c03071200c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 786553291 1250 786552041 786552047
    0x32e03150c0f0c020d02040509071406071109070908060f0708090c06160303090c0e2202010e060304061e060501090f1401081902030708040201090909050c10030608160510 75
    0xc411005004290b52030305550030319014503403003005a0300c0208000031000c0b4a42c08901910b07801e03160304000d5800387c00117208904016000c603410343d002780d501504001e09504c8001d5140201503000380108215008150280d2141d035042016004940031a082410300710000141c0507800c4640000240e15039000c1120b00002281e007858100e401051035081ca0700c40040c5012070059a8800c5090540da40d240f03900003070043c00207200801e428004002c284c5441d0401090f400d15182411445210505019006030380000c2003001c00c01c0261169520303075441c1d2a0660027806811601076100d05c80e00b42500c8400500d80001041e80c000382c3e01e02441c580d82d0945540082c800740500c0c4a82c0d800480e00d4651544580c03402640b080d2408030010f00840d41b001124126401601c40c1030020b0004000c020035075810030038010091404180411540c2e090ba112183c58961106100b446000070040f0301d0103403442600b180014181c50030558210303424986100e0f00b011090b2040354083c821000b0342c40011b81c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 786554541 1250 786553291 786553301
    0x19060608130308070e0409080a0207120c360603111e1513090203070305060619030507020f12040302030105100503030304030509031501060305090616050f032e0315 72
    0x41c00c07652000d4120345035001e461404006204008001081a240080e65114024454803a001d0440c0e80d83d10349284000900b049d8a5410002c984090021808000340544100f08100e54290303c941e80340180300d89c90104240c44044030200031018034400a15400100d6010004403403081075000c841d04018014414800c0701c0300d546030030035541444002d000b030501c000702c1005085466000341c40c14003070756500c0d00000c4250308140606070f070100800c0b0030540c0520078240c1103441201c0e42400c211002d00b010428240e01c90303a4508041c0c40b0004500214000c000020004a007a825113481d940448100303100c0750400d120a038031171b41c280000301e80c2000c100803d038403da0388083c014500e9550346407010f40315917000100c01d03074140c45100311400056840e01001030203040310765000b140c281055030841e0302d8a0030140440b45000c454441c1d0340d500036040f41c01c541c2c0200d84004070645a55417070082c11000c0f031071a0708407075a00c118030032020304560414100c0016288118500d8041c0c10811210070201c0d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 786555791 1250 786554541 786554551
    0xc10110d0c1b02040504140a2402090a061b0507080f010f0b102d030203240a180605061b0607030b01080406092f011d0f0f0d060519060608 61
    0xe0201c000b80260505400c003503070103402192000c0d040100d0110041c64246070540994202e84101c000d001c0c10f100e2140c41405425404030b066040130140307000a510b48542d440b4403000d00c00a507502d40911401e04843c441e1039900300080d505441c1e6608a070a4440d1041e1086a8140d46016083c1507481107a03c1030074501c06000d0005491300b0014401515440c5ca061580c040c983c0c9503174180300c072414880700800341800491f5009612030030814580649503440c503001240302c04400036070100c1d079129056940c4c00c4683c424984400a03d201440c030005102c25080b0310b42050000a030300d030f045440c0480c9902c074280340350b04079202d640c0d9400044007254214800310380083e1a900216000c41c9898003c0c407405801111075215401c442c405000100c00888030700c0208203100031414070550b81000250003841c0309180c125a40010000005401e1454143e005110b03036807200004a00f17407522400500c0541d400780081003103045c01c513003084032903410001c441101c5041040203d00b491207110034038025 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 786557041 1250 786555791 786555827
    0x4060e0d3003020412020919050108011e05091c03020f120f10030b04060209120a2303040501051c091e06051e190e030406091403010608030409020c10110d0c 69
    0x100ba6508002e4030003c00f0b044140241c050710003d408000d5944104ad0007460103e000141e040305095884500540303074404240b00c5031414013009003400c1e0109800585801800203001c860000c4501500280214084c41c05540c20229050410143c1d2601144c0500081c0c800740045660f98190f10060204a010082c08000000c000c42c0000e4403540140c400c041e0002c100d44e8405603c440303400c0c90104083c1e002d40c0e41280c040700c0a80601010004c9080281802014502d01410000080e180d0311481155200941812420188150340d03a4080001c41d944079680810441c01503d0201700440101000e0382c84074603140c042945403507542d44020400740b010402a82c41da0710741d036400e00001c0070708505880890720341e04003d01c110310500c010005000c140e00c41401c42820000c231894130f40b01c036050300341c040c1e0701d8803800307008030764000007620100d4184000c0940e441900645041c102091010b00030b001d079040c035140e038000e5070700880a000140f585140c100520800141d00326940c21900341e0003da1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 786558291 1250 786557041 786557069
    0x1509010c050a21050705090f0405270f030406020303100609060e01030e1e03070302010e0a0b1602120a030209010e030114181c02011407020a0804060e0d30030204 71
    0x1407140290f10360f10405080039031071407200d448944810b0503204212400000078500003485401407502e460580c19441c2d007610100b080d864403000b802007081c0c4207a42e25640f07002200b10300881c00400c100c0b00c040d500c5154103480e140c0c1c0d52220003a40e66001030714140940c001c0c2d4000850b415200341d0315001114001c4d503520201c140b0640056000300100c113220101401384802e00c84201d803051442c03840c040c9000c00150751b10326960900a08660118920403001e400982104020031000741c00c0340d41040741c1c0341c2c400b044400f007020264a0201c00d115500303038807a00070a40346011a010b41c00740054607020b89560f109070400b8407c050072541a940d8840e10b161103000815114101504417030f020041504c00c6903000d1006005000396814501f0701c40700141e44070134008040c86000c0c503825400c65000e00051004082555600026010354040d200400c14003030003051072951001807144406411141c403000040c005901204c544101c051505503980c9004400a03000380b280c402c030b8046070035030014160 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 786559541 1250 786558291 786558307
    0x40510140a020f070c0b0307030b09090d0302090a0e04051f1e02131e080f0624151c0b03070503100e03040e0901020a031b051902031303051509010c05 66
    0x70007900114039680c0c02000900000c0001545c81400f24064105400103545a2400700b00041c19a0b5030560041d0080102000b0301980c0003001070036800c150300034240035031142c0c44400440c1902000e9800b000b2580281c6d810f00c02884408540924a45440c00720f0301c0041e400011038100742c8003d100740b8900da1304424010800c144c074a9002d8008661440c2d40480034540d20080d107000c5d04012810b031414058210010130440c2410818000c81e440282c01030110b03850306821217080300c600007055005d2a61042500340e19540c4d10340301e820426510040c03407600ea80c842105405034a12040c1d000111a1408840ca002c900c0e00003403003c11204020024078001121146d02c002400d1400301c1c5182c03501c0b040c0b01c042200381e901413919108003104d0b000161504000305008040e580345503040e8560b5020803072206030b919405402c4038130300c030540f410580d0b03038030403001e01240380d8400c10114000c2000302002c040b080100114480249408003040c1540d1905c540400314229442903035080040340307081003100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 786560791 1250 786559541 786559561
    0x4030b070c0c172d06010303110a0f060207020f03060c0d0e0708062401030b092a0c030d150609031209080a1101020d0c0b0604021e0a0804051014 64
    0x1080707881005151461503881a12480720301c04449950016013003600000e5140022101140401d48070822400a00c0c440c0e18800c1d40303a94060002408000c50401034030409041041070035001a40303c46100300080700b904100009410020b0200c8c405c5900d02030420300e5213400202030703008034070780d034840352400141c125560020924a01c02440c18060b020001031020000e0241c0742c824a42c0620010901c81030007507000c02c8401c807a00b500e06040c07070b1060040e400c2c2c82d110009a8019403024900c000d020518480034502c411945a000640100051070700f4030030b2001c0701520909881400500c50315003240d01a214546003401540c1c0014a030301c00c200b001c290360b41504071414801e0300301008a1500c179250a03080c12001c10080d40c00128000c6180c04d9540e0400841109030f00a1404013140103a55a03556107025014004900c00ca8011803000c03800c2e44110b07000c4481074180450703581d998021901c06807511008683c161142e000f818400d01c0301c141d40c7c2c018100004d21042958a01c0d0380c0740000c01d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 786562041 1250 786560791 786560807
    0x1206120d120b031504171903020705010e060411042a0f090e0a06032f0915090a060603060803130e0c0c100e0606010c1a0711100606030c0504030b07 65
    0x14804035150004078400340c50034042d01c4d400034640343c0070081d01d28050a0840d050f541d40004820801707810024550f880c1041c1c0d04400c0c03101c000345805a95003c09041440c0509502d850742c03e410b0260000340b00411400c004c5042d094202510207000c5c0024680d46e142c52054a50142c00440210030042c401003489194001c0e00d0720000d040036100540c45154495040c4412540312141d19035522082c400e128200d0f02c2001002c1c1c4020500780d41c2c20400d41031007440080300d05080d00822048011500703515000e40068200000030b4a6424940341c00c6800001034151441141d02080c0b0b4120007080c207180c04400c07501e0300b00c00c142c04100c405140c02c9020150b204000d01c250304140c170078000c120b02e03c1814002c0c0c03000240010004140c0c441032034401403c152018001605001240381008c0024540092100725000c544034000010707503410f8400e1b2041d008080100d50340e4001e022526000b5441c6a0050040d0384060303400300030081c40c0702e4055415225034080a0f00343ea82e05030008030348074428508 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 786563291 1250 786562041 786562067
    0x3020c040612022b030f121e0c0e04020c0a060f05070518030106051c110105040602100b12190b0a15050d02040e030c0a0201020f1203010605031e0c1206120d 69
    0x3041d040340381c0e031000c041d041c00d00c0401c0c00c0b0002801b89001c0310940342c2c000d444c0507507441d40320b008101c624240300303244030f404201d080095210f076160780c004a44680101c51511a010015006554580b0440403054a403402442c0807107000c0e10f41500b80c06464441d206092040d203442d201d6910702400c21315491140c80304105002e900d03640340d92002c116519005104040d0415048580d8190056441c0540300c038401850070604000090101708810742d400502c400b614043c864000034041c1024010420100405030120710501c00d0a800c0c4081140341d2400c3c20905015540c10b091a82f40d60000b0003d4030889000c1302e4070809604010300441c03034940c107840f2005100070030001c0c4918410040c0d60954010520348503150700400d0004c1c0035540c041c030040000c1c0c0c202001800010042c180342c00701c14001809108100207002c00000d0120104285401040b007020111035172510306062441070726403240c906070141a2200e0003240250803e11015827203580d418019000d40084444100c6051074030040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 786564541 1250 786563291 786563329
    0x60f060e0d051603030e130c120b0a0e04050313060c03141c090b07090e040c170a0c03050318011706011d150d0c080f071b0b07030903020c04061202 65
    0x140e400f28203400e528407000110320946030a01003561a00030400c2ca0034022107034034142d42c101559000c1c40e60384294800403900b0418000507002e40340402090407508070340c110241c00c078016400d01c0144080000500b10400c1984050b4410781d851b0b07075041b1845c1071440402000304100c9181076a00416080c00b510620300d0002100072828001c07902581136034500c3c4410f5030984650740a00c16050b80c4080d01c20702400074440f28020034140381d44c0d580621580c07442076180004850348141d1082e141800195840368200d5104400c46489040640d1203900c4505915802c400b40070452982d94060b4100c3c4c4c0050f03060440406d440ea50784001592000208003c000b1041e4100700d44400644c0d030100240703c603200c10b00d481500c0344204040c00b4202c03a5100100390a016030002000b00c04d8220314003c6512400c14507120344811040808210114803080d0000e00a40c0c1440402021944c03650100d8440c1d402582141c5401c41528148821600240030343d180404803a03040c8009820068004c21045203059 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 786565791 1250 786564541 786564553
    0x110601050922140609120301090e0102221d06011706010207050a0f08010f051b0f0f030f060a062618030a0c0317070e1c0204060b0d060f060e0d05 64
    0x3280201000c120000445280f400c401c0c2c0500045000c012403036020020000a04000c5c103030103075030405030105200e06980c5a4072042d0b000e501550a406031412003400003101c1c5035072268131090040c008a1401060b040320300307180c008203080810b240414051748041c1c66103180d41d03a500002c1c0454400060006055104042d000a95900c5410300d01c0c00500151a1204126041c1300500e4251410412100d640b10b04001c00d01c40d80c803400001000380c40c00840440b95a44030480d842d00b41c0d6000710b41ca03c4407011404020000c0003804004d440384290350403510440d6440c0c50b441e0aa4030f40003d031142e00c0c1955407410030b00740048036092815030016000c42d10100490380c00256545142c0c082114980050404400b140416401c424081c040c1240711158816502c0c0c6054010310384005c00e2a028032540c20404140b4031400c1078905040103a40242062000a40310171007850b072644600b1000000720b14003c00050b184014030007441c01d4421950f120020321140304200191140c00c913009461602800c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 786567041 1250 786565791 786565831
    0x5120402060901143606041809020913060b0301091e05030909070e010801060302161709030a0b0105100201090b0423070602100b0d0b0609150d080d05071106010509 72
    0x348050003207510a21400b4421800396081c2e00300e020714001c03400c8008940300c400240a075842c0b0302590142c6008c1c031010b08c074041e00c05034440003038159072101030f400141500c02d128091032402d80420701140958001c2c8002c11001d03080c50308850414001400006a0704448450740c20300042c051940c1e801003007260705001e21040080d910344020b88290010580440c5000401e50300941780900520340345c1402c604152400401c404a103101c45802090f0614030304151184461600550307070310300b0000d411650f541da15460240a01c072420302a4034401c90b21320401c040003520501882d004103078840301182458960341e44034034489851801c2030000003c2c8000e42104048100414801800558010818076171403000760800ca94466410034050544c440f04900070034400f060054000300240c48103aa55914208480c1e54203009514181c1d10a50507642c031028043c2e0702c000340c2401064620100100c0d1180002950b003501c15024550340c03074024100400c900d1a015044651040e0703c80c0310300ca060b503a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 786568291 1250 786567041 786567077
    0x905070201110d020d0617100b01200a03030f11070b0c07080a0315050402120f060303040f0e15040603020a090207020f0d0f060501151209060605030a030801090c05120402060901 78
    0x200b503614000c00c56011905101404250161600402402001d01070b487c96030160345484140018600c1600d40e1100f4075404c2c1c0703900c210b00b03070144c9100322409002c102c0074a040e12a11070385001e2007940000c2c20201c140130203045502c2aa036050004c0c03641940341054642c4c6d00345110310001c2409503000010b000000104400100170f05102c00319550003d00c0900d94081c1208081032500090301807071040c8030340781c4090301d0b40007201e821081c1c0c00761107000d035550900040d03d03610554001e00c01040700e02c1e1380062202103c4114900032101c02c00c00c1c0407410262801c1c4822114507204c040e6010004201c100304251156004044850015000c440d0742d50000011450300c4855840c00c0f0b660f00f003500c030b812041c019248101800740c040900d1000d000240c00c3c0004010580303420b0700d9058503a4452014082000340c2d40018001c1401030180c400b4041a410081e2000009114030402181050700418265200c1c201310b40d5109006403000c0e081d07417140d400313201030754104602c075906001c01c180300d0140c2008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 786569541 1250 786568291 786568297
    0x60303070602030c0304031115150a030c06020106140301020f040618050307030b090f1606111c09051c02010504060c050c0409051b0a050d290405010c170f01090507020111 75
    0x160700107a550b43c0c145403800230000c005c101d5070261341d03800007010000044134110000d17411080c0c01c036180c1800c0b601c81000079549011580300419070022240006052901904540c0880d07030018020002c1d030016030185800d038850003003091124a4100801d20200c0d00801403501c0d24000c20901d21300450300c8002180c40c1030705640080d5000140700d4200032100c00c04200224503004110050140d40741740d1040948501800c5c02400d060003003890039000480001c001120507c02200c1c8a007100e400d5912001d40b40700b020740034440c0120f50400c151100c030503800250000c25a07041c1d42c0c1d10300d410b19001d41100c0710f050f00001101c071030044004800e0541d031039000d00603801e40604040c068061004d80c1d1640808010350314180a040e044c1c0042186079243c40055040d56048004c2252a21100b1790401a002c04c20241d0000c2c4c8403510140000d0040550080440440a44940d0181c1c1c00c1075400740b8807030f9030494159400c0c1210400500401c40650402038004040d8000852030800150001c01d050b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 786570791 1250 786569541 786569551
    0xb0c0a050f07260d0509040e0703061a0306040c090906090803070e0a0807180f09200306010603020405030307060f020c070e0f0a110f21010602060a05060418030806030307060203 78
    0x507202d42d0302403090712400702c20003024070160343c02400100710011525498076180d919210500c0303004195003d0948441e00000c04024030036059a10250701e070303d0400010107100c140e103062621810364520030b034100001d03101c1c0030701c2c3c01c0300305454054503200242029200c8900119040c2d40c450402c000003414030303000756005545948071440008040c80a11800560f640c0c440e0086c1d9108410030000114a412429074803061020049110200a0181009408007980051060480500c4800000a4581e0352804844101c082e03420607640e6840031000d034000e9004042d0300da001080300307800081441d880603407490031103c005410440a07000340e50900089901c02400300300604100505902c50307040c0d01d6800391031464100940b90707807e11040c8803409032401c513a030100c00001d01039442420815400c9190034411588003c503603100c5800940307501c0c06682072441c090810300410a6440d06004841105100000240344041d548d2421202c188000d0425078240c0002c125a03000700e65240000c0d8031407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 786572041 1250 786570791 786570793
    0x30d0501060e030c0402180d0219030308090d2c180a0c031d071a0d09110405160e061b0304120201080a14010e040212100609060614040b0c0a050f 64
    0x401030b0003d050034480321116207071099204110307050012000a142d00d007401c03400c0c0c0c0c00604685403840440c2207003a940ba000d9500301080c020010408d94410300c60361040c44c40f0010382c1c1d808580c900301503820b4041c0c1071607011700d05818001107082400091156050700700c01405c0007140c00c030009454043c880c4c1600c00e15802c1c1e844e85540e4407a2034060244217840c428986441d806c200c0d1910382e4a4076907940740115040d00c8001c00b4209401c1d04039505888030018003175030410066046160811450741104409802542010300103030344440200b110500c000304540750100d070300d01120100030456110707041c103042c1c0650714040c0d26a02042000074001400300341b010110228031500024049100007000005002e0400c448160b18003558006241140d0507500c1502e0700b40c070703140300240c07400a103011a18000e100d203c090301d149402d83e0700300104441000000b00040354071004200c0f003100c0e030101a45020782042008100700c130110303c0140480030f0040c06a411141c0b0343e40c1c50a00300035101102e0001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 786573291 1250 786572041 786572057
    0x1911090a1d070f0e0612011401051302031905070909051302181b16080a0309060c020c0f06030a060803040b040303031b0c03180b0705011406060c100905030d050106 72
    0x445075010700c282591150020aa498a00254007260700740501072101c0c5210a400800c1e03c640340c2d01282c41c258801c1b00003d02c480d5401810710705d69806e0921502d4401d1b5901da6a9215200c11803080380e0280215075007549400090042007006840b001c0e040c41d00b00540c0c0c11000039154520f00c111070158800000d400210341c11401000b0b8286412116486d50101410500c100a01e1105840135001010f42c40582c1341c000c14009504103050140000d0308a5100065521101d54542e0041d80021703c5082c080108014144080f0782d01c80300e02c0c54054010f01142044e0007203240240107503920082500001c00e9260321801202c1c01c6820691100c1c6440c24085020f00401d509401139901d854004a81c07490744140c01d217801400071020350740c0503060005030b5010b00f46015403518680c02400e000e070b641d6aa140014a0000c0c002c01ca0f00800e82402d44801000c01c104d4034042b01110594141c0c04014000c2c038224001c08002440c0c041021181440308005080220045010340b80c001c041640720701c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 786574541 1250 786573291 786573311
    0x5150718060e03061e1306020d0e0c030d020106060905010c05010e01060810050106030908040e0a0e2d030304030509130923150c1e0702031002070201201911090a 71
    0x490000c014200c013031803003400e04600450b106004001c661040e136400c119a006c2145060480007442208001c0e0906802d1200382d030512080080e4000355507205408071b030070948911804900300c8030640980e8000484a45040005601c10307922101c40034016000000c0782c41d1010b0361300742115420ba209084039003040c4549001c1607024810030703005242500701440384090940d10345016100f41d0051030400c01d003010103e890fa01041e0310000e030f1040c00c08121161400e802044001d0b076140c41c2c0381d0041e0383c9071003142055004030200980b0b01465040e201c65083c40700c5c00c030800c8103560181404101d82592481c011021800c034044103044d50524581d0980341b05c01100e02c1c3c908018204a22040c080811801e00022019100072034980b8403c001e4031070841e10103228403501c1da22440e600658144a03e500080c1e0014983e0f00034800701e8800d0301e0b4007040e4102c09240000031650120000c80d1900180800460102180c01d0306201e6440b464084018441007070005070480c500307031110316007595201007001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 786575791 1250 786574541 786574543
    0xa060314010b04030201020604171201030c050a0b04050603010312021002070602030f0a02070b0619120b0a1413030305041e0f0309060c051024031101091205150718060e03 75
    0x240501010742d4041d01c2c043c15900042d5450f003016000800c0c03110540c400b010f9055810090341c18104c1c044981040c1941d40e4102031080144500400b80700340070f1100700044201506086404941300602007030f00f582e10355118a0f83d1001540c04050940c092600c0d44c10200c02a03100412550b445108016240d0601212400c8040001041c00080314410080d0001040005108a03800203048410711050543c44510210745003842e408000740000c05061803041062480d1034611403510071604012502c40300303400c407186407410b40c0e5186400200b1403202c408a482a04166880740c0038040245c1c103e0580100442c460002c41010751b020355040400b10f04240e40000c06078010321842c5009071020001d5252641c0710700341c04403d200010394031074402d41d02900d40c40c0703210b08183c460b02615500555a0a008195021200344039000403a00d00340412406079a04200484640040051207001c2041003080c600f9074000d0000c105200301c90b06403a40c0010580c00c1c85000e803003140e0701c000a0700b1a540c01c0c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 786577041 1250 786575791 786575831
    0x1509110103052a04090c1e020a02091308040e16020c090c0421020301020304050313081f05060102011b091a0f0a120e011b080f04150b0f0a0603 63
    0x2203040600700028050104034004468150014204080181d0071420f00c1d0010203103c1c3d54004040a828003103e81145908411510304407449880036220095503440101c0c1c49542c82c0800a510001c47c4002c60310444030351080b1900700380719000d0540340c03d86a00c52400703490421030341030781d452001da8480061550305000ca100c04100644450320581054100201e05000700d0013030120101c07a441c24a100340c44d013003162000242d000b4008664900349810304032740740da2066024117000e030103900300081d101d240026138032024603000410030442d10358103501c07501800c800340074241190740710400c01c4030254410031242241041038440d04000f83c0b400c05e508001c40d000c8640588110f80500c141103806818200315007445c0c01e1480c0084c83c0e10038003400b8400626108100300100d41c0b80440c0b20003070750301c150130100b000043c3d5115854143d807890359412541c04200c8000740351004410a034011104190010a5031120060241d40550105004104203099952018000a45400f007040a5000d9002380d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 786578291 1250 786577041 786577073
    0x230a0c03111f0f0e1810050a0f03150518060f16050c072108030405010c1416171209101b021c050708071a090f190f1509 53
    0x2c0d0701d4125865410207010002c442030f5100610980c0107540750940d68607940d000d6800542e050f100b0b40b40c140703040c220741c071050940281c0c0e000b21015800422004001141c58003141d030700074031944500b440408294040c15000e0710090b4404200301c0c140c003144c0403d0101c148926803107114213900740b9025001c80304000b80000040b061010402040380711807400f00340760050f0350752802e4100044025402041d101200c0d400040e10301c04012042c0410084190040044124250340b032184900f200c407501c4065200d03c1c07104e29a84070000d505040028414160302e210b5242c04000c1034148800c500d40800d800108540008641c0c2150301401030140062003102449a04199502c00c84405040d01075030318000000108880310040c61104080e038402c10464000f039034002c0e480da44a41180c546144480441c1d1600c0f000000d00b00c0008000200024040b08074801540040440400c0d00d8003440c0302c1c2e909610107842800c940325040c030100b1b0119034042c40f00c0c0d052220000c0c096003607007042044204c0480d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 786579541 1250 786578291 786578329
    0x40501091104030803040809060a1101060e06130c11030a031d030a05220b0a0809280305070f0c03051b04110a030e0703151413230a0c0311 61
    0x22070079560100e20425a0b081c2ca40c0507400c0303030b501c0d00c45040c1407066018140b0400d074483c0c00050b8880318140d0201c031461300300c501440280405900c900d00400e1040d02120040e0f04050b006038808800700d82a000840d2890250404514681c0b004445a055510200d004ca01182e103554048141c11000880c041049050102450034040f6565000301144a8101c4040710392520000b42e0031603510305a100001002601051551070140c0c100290041200b16541d0302c0750f014000e444015883c070100b0078880942c40300003448400364560740686454109a600b87c80780c0c0924184000000c4418a00501450003000284003045d035001440e854003804003081030140e0700f042800343c001ca8000c4151070540810b0308001c1030b5901d8030040355180011503440136081c0d0310008000106c88816a00251240748582d04510301aa10640040c510403841c10005005041070040a0080341c201008213800038001000e80d8100910f5444403051824590000d84403684070701c2d0010207038074000e600d43c070745c8414002c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 786580791 1250 786579541 786579551
    0x9100305060601081e160e0904050d180308030f180f0601060807020c10030c022103040809060705030c030901031a0d08130f080d1115010902090604030602030f040204050109 76
    0x2a80c0c4a0715504040d001c6030620500c1000706004413005000d4030071400c440d6016445610b40080200c1200c1d0302a0b0981c000308444081e00b402c2814094244d510880e0040c0c02000648940403048918980005201d0f015080a07900440021940d0009601a0a10f407450302e8040c02c114032210602203072079511029540c0100c403038001060010030134070704443c4c081c240300c42c01303a4520200307a0400607550089640006d49651010060b5010f44c040032482031694201d4182c0c200d440110483c4483c2c01842d8a500785051000a00044180303008040c001006400d01c0c0c18564266035a52840e04a490000110340000c84c1340141940c1c140304d1031101141000c03021481c0c040030408504c10760351000d009000c00d0380020314540301c40114010035008018803211298078681d00c082c007075181c81e20f0181e8400090340c3d0f81c01e85010042c0c00580c8030810203e80241046a902c0d040400c2c00035409104100c0d000307541404000041180f501c003852240c0101d600b101da59250500c104021640705130413050600c1c1c940303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 786582041 1250 786580791 786580793
    0x7061a030307210c150614010f170702070b0c06090d0314040f052d0d02010504031b051906200412021302090d032d0e19090c0c02091003 60
    0x240e12000e8a2000c0c143c0e81c16940030b00c4401c2110044d0003064003501048149900c00c48601c815030212044401950f0403000b0b903c0904011600d030364034140e29900040c880060380072001041840b943d00144d0500480325001e655445008080d00b040d04216060f40015003080302014050245a86940551a04103d150710810b010048030801a00281881141214003030411130100314450110a54414070900c00c03588420300d40000c44850701100b0308e0b0064101a68030240140106030081e9415210000043d2103c8440b01603541c0f202c6054855101d10761500144214400c0c1800600c0c1c080c540100354401032211403041c250003200c1004075100b04120800079014904a0b4240d1590704a41c0e0f80c8071503500e042014080c0c0500d40c1082c0d0b12088441d0140201070b04101c0720380310140560203401031000c503200140c54400340c8440203004107800c0c44400300c01d854841881d0599000c2582d02d0320245490b450800115940010420007160113003103982e095107020680c00c2d80c013008820511044c0c03415 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 786583291 1250 786582041 786582053
    0xc0314011a01050a0f300b0f0321040b0a0f03150f0b070602090307151b02011d0613090203060102010e061302060327030307081f0b0c100207061a030307 67
    0x1e10503007801080460780e01c17003507040d200300c0b0040134042140c403007003500c0c828100300102c40c0150401e00345082403821114090509105602040369140180903141c510740569030709050345404901506c10100c1003201240c22031001d0083c0200000b1640c6d41c200c40752a80c840a001c85000d10b161403e541c1342c03400104050105000c0c188160b601c043d0006072101140d14002c00680100c26082c0e0b454040c071500401c410901040042584030b09584001c0e4001c144400d80c10340c4402d1180c064006121104200c40002840c150505145005055103282080c075200c0050800801c2c0c00810106400009014040da8240641240504a40050f01990400c01c41c0c0c80c3c3c13510001c4500074081c50f00400042c540c0181c03418039481207424a080d424207d04820049500c0f035008a562801098850005c21268407110084141c41c0a45da01000c0f4103034141003441c00160049282c07044903100f10500007081046600150104611800b408a0f990010103592441000301c0c0020034080c3e0f01c240000e60209403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 786584541 1250 786583291 786583297
    0x3106050106140712030c02030d2406170406180f0507051005040b1602030f0d050307080f040503030a05040221030904060902032202010e04060b07020909060c1b0a0c0314011a0105 78
    0x24130b5040c0054450101042a070840c003480790b5180741035103812a2024017401100c2c102204100c0183d00d800f155480d01e0007500c1110400580c00c401403440c400240005906502168010140703042d5851104a5541d850444004000c1d003103866801000c42003200d03050801075042d0140711400c05500341402e0030720001081c002da02d001e65400d4a0300000400755201072010162040404040c1c400c003c00d419401f4080d90300a880d507a00186101d0700082e5190384120f1030134011580b181c09185541c40e02c032103c4000c3e00001c1c2043c1c5e800408540070090104650020100a10503500559201e00080c81008111111507000c0e0b044035004008104c108541200c42070100c0b80040280c1100c1c01030303400100e40c114842405140c01a1400b100071803500088000f0b0a0b1003407003200c540c0801e56032085034070b88488095510810420042c081a41d00b843d101c0820790480c44050119141c9071706a0701c4440c0d03100201c0d8015541036041c292004098078082c001c545005440c0d03e01031180181203400244648 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 786585791 1250 786584541 786584573
    0xc011106090d1b1a10080712150e01050a1d0c01020d0503070320070203100e0c06090319030809070f0303020d110c1011010c021531060501061407 64
    0x448510700a54071060301c008003016507500201c540c201c05001030181c0f03130004400d940c1c110302c408038020001902c0b24006400c1041c4d07034102c40340e8880074400380e4070002c0350500d103403600603d903440740300c810607404003407282c14440d01c80c480c4042102400e01e202062404441d4030075000681182150070751690300040c55149615031031030060303a02d55403444100c00602402d1a40b24542c4140e81035141420046c60150640c24000c8040c3d40b011001c1081c0c0000b11210900c80b04840d07000050011801c2c60640003605040c40040c041d5920b0943c3c3c07d43e050000e140c10101103010404071402d11038058000c104980180030303203001003210182140c50195440100710310310310802c82c1c1e0056000c014142841a001c059102601e01503510018513400760820140000c8062191320b46000d04160b42e10020b4540f070310000e03c415458154845090b1840c400040c81c0c008601041c40140004442c00994400f0038040c0c0200000030741541032160060504a807c40700d4602d1100c103115960104d019441d00b01114 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 786587041 1250 786585791 786585797
    0x13020d0605181b0c03040608011502060f160e04050f150a030c0902073201150f0302060705010207020604061713082a030408071d0c04030b0402010203070c080c011106090d 75
    0x10704080040c03106813058162080c0540004103000490503042043c00781607c2781603040403c00415103c049a45007821034000141559500205000400d21a448074945c240c41c80c08404403440320022500365041030300c00001100c5900704010280c10300b0f25640e42504002c40d0030150311031658480c0100b0242600540d1104c03580062414200085d46100f030390080d00c80500e2081e00340d88441144d035030410000d0080269402d1503075040c46921910083e105442280020401c01c3c1d083d034090101c00e41210900301d86c2c0e503608025071005692004090f000800513640d9060881c81044880002050040d041c6210402c81104910008074107005580b5403404280c445082a0f40b21840501090704451018100d07000c00900071520343c81c0803e141098030041181a55191000c018109001d80d01710343c0384a0215041c8400d200041d1800222a0401c3c014030460703051842e40d488006880045038801d0603039a11a4410086650f00080d074a20124000e401038207517443e00851945e122034400c0094420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 786588291 1250 786587041 786587071
    0x70e0a0510080624040306051512100b09010807180e01020f0a020115030f0602070c030c08010b1e09130507090510060f0e0a090b130905010204060809030306101d13020d060518 77
    0x1209e09003602c8070860014400301c408148513800a4840b6818030810325040d041c688140745509240c01064106c6030300b1001801120b18110340c100d404041d060094200c19100c0b1480405214240040d21300201403140d401e6440382502c2000c1c0c21a00601198078030040b40300c13020001300c0c2044420710041600b21130056030704d1090745044008941c242e04024a95100c0d1800440c44030415407000541e4442a5198074855680007240c2030392070070411980b07078000d086034006240d800c1c0003808005d5151149049030313811038903440218143c2d030307007141c02018210691800308281030340000302c404480c0b02814404480040303072010807032101c014024411810389445148605031180d82240042e002414010400d000e004d250081c0030394440c0c882c2400249119001c965000d1012080380c1c0290801001c188031804150000d0303a8009592030307000b042c0c2112040703070202900d802850342042c001d945d800503654a08014181c00300d1358a42c000c80d0084c0010030800314107245900100d5003141c095005240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 786589541 1250 786588291 786588301
    0x70824010c050c04050a290d030323010e060103050711060423060c0712090b0d0b010903240f02090d020d08130e0f0c03040209070e0a051008062404030605 68
    0x40f82500d00c0038943c1c0c00500c0d0104201c0340130b00302e911100040071401f049030b80764145240740d0f021071480ca41c2121b501ca500102c0000001c1d000c0c0d03005614031101c44098400c0e850156201d654900f400340d01c00321a40305600100403082da8140f0506511044906024002060201c0c50a0f503c034001000201041401030035107020700b0484031590300140d0300700c0c211012490040010045500060400c40d01c02d0407410003820002d0091001c070b015030f0101d522050622082c603080c2e0000c3c1c0400c41e907183c1031026020022011502e5011940300b42c0800000d480c1c4900450340703148049542d50003800050b82e10520802c1c404e903072280310084140741c0466200c16045000d060448080c41000d03d0664220324284002424130001740265201d00d1004002c4401590743d008020178138802250000e5222a00c036001580d03013405050420600040a800c1c5c1080b06e844c1c0d40403601d000000990070020800020402481349403500814034551096001c00011811058804041e40260300005041c903840d240059 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 786590791 1250 786589541 786589543
    0xe100e0712020f18100302270612090105040c080d0912060b09041b06020a0206070206031005061b0106080307020306180a0501110d050f100501050706180b070824010c05 74
    0x10709510440c01d42d041d9500038213264503807a51221090240101d0050108171610390192003601d58540710009107490040c0041907550040343e002030051b61121051280000c0c021a85402e11f21aa5611000007800d0405090190b248607507540301d503446500c40a005c80c191540100b09004032003140c200c0700b403c4012447d008000c1c110922420790005802e50801c020311480300250040e41650802e02002203403941c1d4100c4c0ca44145030f10281d0410002c000d5080141045001540d02195400c07507035a58585541c00581141d2000c1400049203032070002e03e0040490030301ca540c00415419006500d80a05680071036161000104044141c8200808211407204140441312103580c0c880020000e005401c040020399401011560441c1841d081c001021021141100307030003101e82c81319040c03140b03141c00700441c0c01c1e900441e070854006446011400c24500942034504a0750312440142c8064600f2443c000c1c40c43c94010120b0241c80c040d880c030104143c2002240c06240d40003880c3c50107a258103402d1071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 786592041 1250 786590791 786590797
    0xa0201060e040305090a0803030c0304120c060c120f200304050a0807030f1407021e03120f0417030f030402010c1a100f0b0a080105090601031806060e100e071202 71
    0x1c03550000441c03040104056011000f0001c0c1c01080f101032400c242c560f511180c0c3d9000868407016201030410200e00481c5410002c075112400500d00041c09405958800701a1126910102c001c14240700d00d00415400501409920480a001c10400003100503541402c0c81c840030f205d22a400701c004041401d01074244507900300607422032a982d135100c41a02d0024801074504509000150404003209420040041125413044c8c0092a0001e9400000007041901050481039035040c410000c400303003120f0b4100d0240205141c040005031319507240120207a103007054180c05400320b170020484604441030b1032054039003241d0286000603000c141844c01c200288040b500084d0585a48420416a003c0200c101002e035a60000ca1082082d650100e500d22070003451401c03070103d504e200060055060110585030711100c14035000c04c0000c291504400c181c41501d1094070074940300c18007404613a0484c85116003000c000f45ea4901442e03d05060703256902c0001e415074041151300281c1d644000116015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 786593291 1250 786592041 786592049
    0xf0402031f060203070c061d1509030a030309110a0302060724020c010b040b03030a0c03050c190503041d0f0609130b070e0a0e07080105100201110f0a230f0a020106 72
    0x88a2a03150ba80c003940c0c03a040a42c00b21000b440807500814843c0c800c110b22080c02e4450304e4145441c1401200304803112440b0490704a000005000f040301d69913040040f07280040c0a510002489051400c01000030161040f1032405940c00d0301c42040107803034440c2201c0d40c05800c1600041c1e4401d080700c0c003800003229540c0d0890014004190f009000b80191701c03e802070030b01100c041104240d00b00c24140c42c3c1c05400060740110362244019004039001d6001402c251103c0b9003502c0d4403c0c00300200c00e00c0402000402c5c1c03541c0c2d0011030240107540111501290203045d1510130611450305a0344000d400f500101403a0040a005011030810000340680f03e0384160300150f030390200d142081009000801d9500741c10711568848400041044460b2241b0740a803072982c3c1c5003051381e0300b05002d00140450604c2c20310215942c0d100d41c81190300039500135000003044c4401e100c0e42d0b215100c000611000b1401c4084e03203000006070701c041c480591402190266040385294688550300741c5402e87c0142900c0e80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 786594541 1250 786593291 786593341
    0x180f0c020d110c090c030f100308090d110603160906030605030d0525210c0503070314070f1a0a0b010e010f030e10090506070816050d1112091b0f040203 67
    0x42c080e5810309107001d58440d487c41c40e042001da0740c80a030280c00c03002aa1101404a400812150f1202d00b803100040c44041c5c0291501c403d003800c240082542a40200c0b0510510802c01d02c04100150744110682c0c0248020318042c032045080c000040e407200c1012083c03000380100025402c041071241d40c05038016403c1e11080041104190034503038402c203007014421110311803e200c1081d50f540150034007091240c00000450521348641d07000c7d039040c1c80c900f0202d221303440c0034048040010b102404500c1e4143c800c220320350b43d1103075080c40d0805c1c0301405440c12241500345421442540d902c00c104400c99002481c00b000c0d03507100318070103400800c0c02e50341600c3e8034040c003003984150046079003201380030a01c9242150301e1030350307000c3d001c680c40d403003c0d665030405002d410800d242c041d2181c4060000c900c00704c0d00020306520084281c86140d8415000030180030510401c0184151003031000301c0b11b0800182c4081100440c00d00000d802c0d10509411510559010011170f00d81c0d002203c1055800442403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 786595791 1250 786594541 786594559
    0xb010807090b1b1014070c030e0f010e0d03050a1e02060f06060c0708010213050a212909100e030a05160611072d12020c0307180f0c020d110c 62
    0x3004003000360480ca100004e8072070050000c250094801c550030402941c06603240400380c0680030401040b0700c2c60308ad070346d0b040240010071030a50b42e4510704482070b240c1c443d80354659104203500e03000c2d210722050351044942210034040310030b0030768001c00c0850b0b01045e40721501800c0e5031008001140c500401921100b1703440303800c3c0c02040200341503004082100155100e20045a565000c01c10b0480c3d460044071458201c8494044210400c044007400407441003003448800072501d0058000c43c8019800e4840e140c080c1020f014603210140840340303011000100070b10000100ca9110340d613921901c29200104500020500480e8805e01c0c40b0121883d400740d014016024101c0c00747d8180c1e001054160380c0c038013110507000303103103e41d007915401440303d800c0322400310f1412a01d400200715000e10350b84055025080282506540034401c8a01900c01214681308034078142064500300c03042c3c50407202219107841002480c1036000502c18aaa8010345042c5100030a0791001c281042844648190014000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 786597041 1250 786595791 786595813
    0x1031b05130e040c051c060920040e03032e090516020a020117220309090b0301060e0c1b060c041d0f0f0606040b0403150b010807090b1b 60
    0x3008140600718a0302120040e5101c8804007002c201c2510004c201001207042040f80303003814001026050890101d0001c40441501d80c03100352801d503032045907501a00202620560700380c49100940000556042094482d141881540c030311004e8801940d030146e0200c4450465202c1c91504518800704040b043c242da0344101c13150103400b0581e007441912003078081c0c0104840c03000809000c0c0a40595500b000f40146c1c28203a601490080d00030348040c2c4180001c03040711040c40031b41c09480f0b032003a40c80d00a4546000201c0085078610100c0c940700f6414501c040280e003020300c00454020f81c1201c0101d60300c40340c01c0c05c0880210800e95410301103005840c1040340600c21400030b80111000c00c0100c08030344841504d030036004002203c28001103912030003c031f40304681414100d6801200581490720b8252590803500481e04150320440f0582d0a02408800084990080c003211040070300302020303107007000740f000351840c1558001c580c81e921000c506604403400a40169142d2080c02d002d0f95018410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 786598291 1250 786597041 786597047
    0xf030a150212010b130311060d0e16060507050a020f0117010305010603111219050309060c16050f09041101091a070201110d0e150f040e0f010605040312080601031b 72
    0x1001c00d8050350a01000001020b05400007201e2810090b8500c04001606507aaa010030340c042142c1f0a4204100740701c000c8044480f0b1103000b0a803985070300141085000001564180105500210100300302030041c0d00000e500099120307580c07681140d0340205c1c40d205900403a5117808d80200c982d80900c0d19800003045c0501984402c068a0040d209024420145810710088034040c001d00e0025600014540d070f001b042c03203403180b00c0e22031040c030aa0b840c02e00e0340000180030303802c0416022841d40003050065080c40b0b0650414000303140503540b444941562000041c11800003d002a1041200703a80c030500030380c0709041ca0005841c40c5e40200f044044164140f4032550004442240800d404030018007410800140c0c0240004069031200341c49507010f02030104402411002c5a00d400301448060031140c0c0000c0944054120500c43c5800d514282541c0c400c290410f80c0010103000c4200810f02c046030481890318040401ca0925140d1500c0c0c03040100c00400500c219030190074100b0301102c5031558 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 786599541 1250 786598291 786598297
    0x4021204150c0c0b150a1806061e08070c06060503030a030c020609061005100c050d02010e0d08060901051e030f1c11060703110d06181b0e0f030a1502 66
    0x50820415400c42e940141d52400200002a000c0403090b03000604880b4040034801c85c403000a41070807001c65484a1410404410319000e400458031307a8818001640c0c020900c02903e000e40003048110029860b0240c0301c0310000c0c103250700b00a407010b481820312203182c00c10401000e0150840e40e50f08400c02004004146d29480d281c01405000e0200b4001900011306034050914240c2c3d8804003890b050402c106100051000b1080c821184020408140184a00c3c0d02c4081590008142c8405a141550422134007410071410310003800d050142a440306541203043d124241c503440700040c00c62103425002e03840040c0c0c07141e25101d401020900c154004c82c0404100365140440342080d6002c0c1c1055030314a26100c03001303405503c41d400054035148030303800c0f000110303401002031460050703109440402c1e200c054000d5a0094408600c1124500181c4154100f90040b82d001c41c5c01c18080a000800003000c041c1024494000140d2007000c1d42c5d0180b00d4090590780c032204907038510604811140282d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 786600791 1250 786599541 786599573
    0xf01051b0705060a0209181003031b030801050103090201030f0c090603060b1e090a1509082406040906060b040e04020307080d05121f06111b0d0f0204021204 69
    0x4040d08034426200c100010a480c4180d82c441c0103481c0964480189400a4001c1c0c0405648100200e0001c16105009070403580030711030100048076014103505020b0506114803219104454000c200c4d0404a0f07440041d15064810920300820599900d00040f4041d084c1140007044d80751520f14084102c9420801c07a10413680c454a0912a066603209040d0b402d004000480f01c032403004011401000b08071500038028668003d080304110750b04c51054822030b40c285a80c07440841c040100c00d0040c1c410400654140300c2c007121407a98030340c02424118610780401350060340190740ba540e0500800002d500040e000d0540a007000340c407995103061042125000781c409a00901914a01103a54803010a5813000001d103038841b03d181c404a0415454100e01c018896200c032485070b07041007014160710004100a140550700d144440c2e65504009080000d04100714802c811a94401176640c2c40c0c1250101c0510f81001c0e600c1d015100c1350010078080d1081c82540c060461500f003c000070006000100e80e482 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 786602041 1250 786600791 786600811
    0x20d0f0c0f050405040b040f1401030b09030702010f0809011407020c01030f0603050d1b21080601030608060712410c0f0a0302122a030c0d0b01110f0105 67
    0x10034403400056954032000340c0e401c4005a0300f044213102034141500a62030032140601300094000000a8102c1113444c1d00c00c244c0c40314440b0500400c180107041500b85c0d00242c40d5005035250240540c0043c040002d1601000b081c03158910014503541001c4d0702c28580304001e48103541103460150700c0251100c03640043c40340440e10b4030100f246000d02a00c20f0304141d03a4031500034060007407090806d90b0300c090450f0b0803503101c80a031076405001490780b16250001420b02d05040b02069401000600b1840f0000c1105040619107002000703031250008a09400100c2e0303060800c40c5142c020181c1d4050810b4009440d9014890101c2c0084c05001003412141140c200b52000d0380b1402e4110011a40d190a40345488000310070712001c280b05082d1b80041060000500b4018901401c45008074050182140d80c450072340c4001740680e1420018442401000011041d414690b02c1d151840d40720078040c00c01c030002101c2c1d44500c55119a4050303169904102c48140844001181242d002400b0b804220f03141904 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 786603291 1250 786602041 786602051
    0xc11011b091a090d0203190302060a0617060a020a05070f0b01090501060f02071806120f1412030f1f03080d060504020301050f12101107020307060219061e020d0f 71
    0x10b00c0d10700c0840d8a40d50141100080c9028608020010140e00110701680c1c140620070310f0307040e040f803800308800c0c0d0340d032090300908140d2070010003d0048070f06560080f0348901603140c01440c03489000c55040d5101a00303400060305c80b14a40307800c40c1e0074041c8000081080d14507041981c18400315140c0c280c101d44020303106021580e00d8900071101c4038800c0510201503400a0750a1202d2000d00620082a2240320340000390182d407030240f03600702002840180e0f05504050048014010307841c2100600701e0700c400c0100b400d0a082c3d018600c1c84e10004140060840c0c085e0081038003101c10101d0b410680c001d0445402141da182c1c18003102c2640302c100d589071514900200040c15043c18020360b81216001413002e080800c03840103001d203003030a0040420a0780100680202800300d1031041c1d240448043c0401078482042c0d105151805020703030040b80542d400314595010040001d5a001440f43d0701100200e4907c0d4400c465032054507003150f404021030b0012529030901003056101e801c54240e01802448 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 786604541 1250 786603291 786603299
    0x120c050309060c090a0605090114030109020a0f09060c02040902040b031203090c0406060804060903120c0c060f02160f211d0108060102070b090a1a040602120f0703030c11011b09 78
    0x1034138424002c490350851101e07042040024041e074058100d164041c10002c0d0041d4002c01088100c1c0c0c401d030800403446a0215035010303865880368004244a120f410002d00e080e00340b500107401d551203201c0091103192115014004c40d1640d0700040c00d0444c001e02282e001144a40340c00d80960405c0310014814461088544042c0c90503004481c122501c0751240c500c00d8840c0e40321038001d0810044180c0902403883c18a0840c08802c2c860300284a04a944001e42042685004802d41e07805070407104040380140f0101441c0340303034009402c00c0181d00000303500c040006441c0074692841c81995015a5003844d12100300001e8005408940303210006403001d903000304180065400c20400e840687c0180d02c801d40500a4420040003032980c070340c00401d20305c10325686901d04100040351002d142001500400c04020032901004148140d01194461f00d040520072128001c0c280600400a4101501c8480300820039001e45805100c000d144c0002b480021403640c8140100d0510080020004050000001e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 786605791 1250 786604541 786604561
    0xb0a050705070803040812010803091003050c0301060f02151009050703090b0402010e030a021210060602060112020d1e110f03030a09231207050405060d030c06050403120c05030906 79
    0x910032001600c4003400d240350742d1520000c43e000184100d50f1a8800c02c0700d0702d828481029118000c1c03d00030021980d4013a80c000380b00e402080c2d00c042e00149802c0c04184101270060b002900d040d268a0320f003510045140050491610b002c3c5141d0513808001e260511000c031196035101005e681c2c02030028880d9413290302c4110121814020b001d0012030720b2002090043d07115559130411004000c0031074074080741a40000701c3e014140c5008401980c40072142307074449172050142100814030303800588901d40c500074044910800041c4024852355810700e07030318100300d0200300d04208640000010a940e0255203000c80e003a1483d9a801ea10130b5042e40c698038223610300001101c122104940c0c40c40c620914080b03991628030500c010240b1a1003901c10454880c0e00d6081c1d10500c400451801030110a24000c14002168400352000b4000d030040d0035840003007078000f5019418594485400601503440d424200c0b145140b8020340f1321464107018245050f1079009014601450012090766420f0b240d40e040d803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 786607041 1250 786605791 786605801
    0x60b0d03020d0e150406020f0d0f0f050309070e190b0a140609030106030b0408120c070c181508030a14040311150906031815010f12081b07030b0a 64
    0x5005070702907141002c04074842c44180d010780c0701c0034160000800c0c0500800d81c55803c550418801a8090514014044410403401041c4109402c01299001c00820010041c1d0444505407044c4140000420400c5e9030401ca608000e206603001d000d82070414000062020081c0380049001606015a080c07440c545007280b101200e25100e841c40e00804142c0034071a03103070408030f4031943c1550b030341030300101045100042610070703481242c5040e82c80f0b0028092640840e006030840505103014401640010600300700e480c01d5a500380303a4100e182010469080c0681092405822440041c0d080024041e0001000d041c0c03800d10780d00c0b103041039110090514001d010310701c0050a000682401078000c0e0502c600404d4070041165103640c904080000072a02e181d1094a081c4065010007044800d0341005200f40b00c20742d82c5444030300c40300e540f40803101c0c080d09803d4001d41025007600c1340c502c0c1c01c011008003200c0100030000460064602414001a1070b407500e4401030704e9280c108000188007416a10070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 786608291 1250 786607041 786607043
    0xf0807050405040b040e0613020312160206030a1b0207060f11071512150e06100e120307020a1d09070e0a020f16061a0a0305060105150f0c010603060b0d 67
    0x109810280b07800c0800000c1c200d8401303440d800c41d5036a0384006020740144022031241c8100c6401c200040c1d0140305040c945592007440318800c034402e001075004580b00070741c48145950102c601c2612501c440c100c54006042c103004400016580030401002030340c0204400089901c0c544902103220035000c41501d2805403203d00b285190030020060040500d541d4928001500c2c42c03a148440c1d100c460240c07001c643c04242003400203986c80784100610705090408a81c482c3c801c3c5c1d040361700c10407107884c0070302a8442800000d12404440c08400344124040094446440e0000c01c2e48801541d1141c00c01d041c661195081c0044102000001d203040500003660302c115202403a42c0601583d4129480c0c009400188040d03032200d20401036050703001c1180c0c00580341c43d8018000014802130120784000b01e00480c1c0c00d210300502078680c0030800f260021810b6411544140e5510303001e00d980c1c00024050340308039019110101d8000ca036000310711005501c903109481c03142100f0003000d000c15080103005090008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 786609541 1250 786608291 786608297
    0x20c0f030a0519081b1510032001230301030c170703120c06021219051006030b0607020d050604030f0309120e040b0402160605010b09090103121e09060f0807 69
    0x110f00e000b03001540b81c00d6003030103000307800a80c10110400700c401d032842c44003a42c201e42c80d0322101540c652000440031640d00306103801c140704140c904e10340c0d80e9101d4900781e0b2000616100500e159441d41e90261041150810981014003844140703400391091a800038002907074a100c00b000085400c400068061030803a8201d002000a10b246030344681040e503025401c0070800c0b14044c40200010581d0020300708030188201c11030298600414452031340c2114401c0f80901a0401e0144100601d00a8210066031a04d150200e120101100407030b44911441c140290411041a4004184400440c1182c041d5100f41e40710624200c01c26421001d55030301d50f101030310b00429840119211402448822400c90011f040401d0080482000400300e81101ca0a01240c11690010404201c2030f4410140136210440e481d608206244000c24846901404000c04030000441603032105401451203070346001e0703001c1d030540050030001d02c028007400980c890000440d2140100b0141603006000b420311843c0169 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 786610791 1250 786609541 786609553
    0x1603150509033c0304060c03092001051314130504080a200d0201020919030503120c0c0105010b04051512041e0605010801020a1b0f02041d030a020c0f030a05 69
    0xc819008401d1101180000241c140303c2d1018100c1d4030b10381c0c05100038501840b038a40340c0c40c050400b0070685014a034540c08041c03400c940000002e0320042142c15100d0b0402e042810203449a006031510301c00d00c8070b1201140000c4100148000c444040c0204410041d2601071f0400050f80030001030311070a550007070151009000406500303202c1c4002c28201c03004d030a0b2829509510b041c00034140340044901c4001030350006680c0750103043c4a508824281c42c181090f454092468030307086c0e12070051044415400c15582f0100780403000842c00e46001200c07420003000b281d6960b50b081141c5a216205150003980b106005a0401c40882c00f610a140e454442c0510240d90390340d20306c0c03643d90004030f10004540f422414440402d2852003200c0c06001311000050f65403450351130203410659409900c0001d030841c462000c0000c0e2842214030303591030b81920042030b49080c0369410b61300d03010507181440740c600c4041080d0b00e11f80d50000302103030354920507604040341d610300100385038859440c80405415a40300e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 786612041 1250 786610791 786610807
    0x140a0b0d0507051603020a020a080a15050907050a0b0301060f0309110d06180c0f0b03071d0f1305060109080105070906050903190c030314180402071103160315050903 73
    0xe802182d40464585482e41c6003030b0f5441e51200141500c501c06030010703444004e1810850900402010145c10514000c0007841102d0340c074400c1084042102120341340c0c844000c1041d0038020000040a888014441e101c1c503a2640c40456864109100320720020fa4222716410500340a0302c1906007180e01310a64120050440c000d10851901c2404100c50417560f0b088a50807890408200007850f500c629003419025240800c0c012030303c072250b0400444c01c0070070800d110885070001440c464401203003041c280040040310000d40340001c184403c9400c400003e0750341740d45941583c44640301d01426241c0d10301490710b40038a0f03422030f0030460b0050041105020103001035400b480c040c02c08a40e001b021110580482c010841e60554850411103003c41202818001c264022144007204462604540d081503082801d0840e95000d80c140d02d4042d03640040d008041c81030a0b200c5204a68000c0d045031480441c5a10118003110359110580c0c1005504208121454141c004e850142c168003000318103004007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 786613291 1250 786612041 786612067
    0x606060c11041e0203090304080705030105090d0f050405060403231f0f09050f0a031209030206061201140106050a020f030711093d06020609060c031b03040c140a0b 72
    0x846042e1002000c407002c103d5114801400118898040320300515180d0b480c004440e4030713200701c41e0030a91203a4102002c00050b2000064560b20806c12443d259400000d4140c05650520544c0c008070f401c94030004010040c0301c1102e500305038044607203180044034101c0851040e03c0b04040400b542440102e00080034443d0403940240c01c400035528400115039042d540d82c24070b0051030420540664200a000f0014541c00000c40e175100103511f03900340181902590700a450780001404184034036201925142240002d44c002440f01041210f00041d17540c544a0180840d08501c0b00310005114441e00391b111014080244c5011b0340e03000c250407102d0341d00b1030308100030994001c1000701c420701c4920170802200f420582c6070800342c243e1180d0342c02074101c00312401080f0b003580e000700f015544110107005005200050307096224810080c00da80340d03210403800daa003141c8868400a51442c01005002c14000c50b1035040048801404140308150302100902c22503581034800c0649400007032150304c000e021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 786614541 1250 786613291 786613301
    0x507050f1509161509091404030201270b0a02070b0709170f030d0e01020c03072d0f030c050c0d0302071521090501020f0d0b09100b0a230c06040606060c1104 69
    0xb450400c110b4468950209a04132487c0180440026891343d003031006054080c4601900e0280300d080406261580f220403580c10180b20750001c0900f00030b000042c0240c59950705541c007869000d00110807a041c940e50003412154103000d861110f072000b41604203400c800145e200041281e4501075401e14502c262410300900f05541880e1440d5020003502c2e12100341032004204052040d000f10000c244103400000300301070b03a10b10070a0b8440303e164552020550662109482560500d404062038103d8070741035003481800908a500b1603001c0b54117070704044e0080785810968080c40c4600041710003810741194000b490841402e01c008101d040320055400540042e001c250040d40090302d00585070000d40501e41c801c041401c1c1c1282e8500c00300c41c140c5040c98038540c114083d0060400c1c1c95040c0001d50040c0d02c5010642010f020b40f0301004141c0c0e18044020700c1070040406004c03904e40c611502150b484010072541168118a4008049045406000c451100c80d4118036400082d400352414000204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 786615791 1250 786614541 786614579
    0x10050402130e0d020111090108010e060d0c060f02060f0601090b162f192705010602060f07021603023c042306060702010507050f150916 60
    0xe80301c0c050104542126006090700440e180e4014924243c60707a2000b400c6840c0303140d5030111580c0030058600160303442100203040d03492101c20042d103615140c0c0012000150500f000384a403064060006003d40c100d400c00410368403640036154242e68580c0f10050f405400c582042c00b03e042c445007440301d000044090840c403908000c0c802140025601d84c1402800000d040000b5000e00e42c7c1c1c030308081c90301c1c0c3e41210341c5084142c51030310300960706001802c16156036009001d0b5242001c1c814a424a02c1d4810200e03914402c034004216a50710303510006d46440b002c454811214410300c0c0800d102510002c4c04441c0050a0021030102d2800e503400c01585075a801c2116206055002404a600341585a240884e1480b40c002400b281000700501054844040c8400610680c0f00700c0310821808510b40c03242c0c00070003290710701e0b682e4910303100684050040301c1c0050100d10541c80f808a204500150300a410030318070b1310780700e210341d03136003c0c0281d4078400480140600703444910100302d01a58400c40040c070f6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 786617041 1250 786615791 786615799
    0x9030f020120040311212b140d09381005130207140f0115080307060908040315060504060b03090c0d0309081501031a0601051b071d09010e060910050402 67
    0x6c2250145804074080c0508041e0032031403050321003840394400c0c054035203000c010400c480442c1003809061003040f000780f0714001d400000c50031440f40c0e00c0d5209250050b0f1207500740c020f00000c44000c103003a0405907000c3c0d1480b582d04600360030140c0d203600ca0741d100d100446044094241040d0a0003250b100620302c103014030382c090260400040d00b528907201340312848401041e01c0c0706a03802c1542544c0207614102d4408800c14018428482d0100032141a42d0300801d010401030480d250100542c8640d40c07014002440030340842184036440d0300700f041190000ca40922400340c840401d00c0c0f2070b102c20707180508182c2c04401d582d100c904004072039201c024003a042c120b400550b10040d10381060805e034060700d452400340c00180300704441c5040201004591080c2c001d0180380100029106100b1502244819201110710007803042d000c0051030040c0040107400628501e121172010350006061b1144016542007068441d049030380001c90900c1600043c1c000c2000d000c540f5401402040050416070300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 786618291 1250 786617041 786617059
    0x703020a0c061b0f111531120201050705040909020d02040e01090606090b0d02060c011e0603030e0103110d0b0a1e050306011a0708091309030f020120040311 69
    0x80b500798030803001040c0c049071003819203401c598001091000b11140030000e000042110010b80364000884519400e251240901c0c181c4415a4009a91036010303100c2c41d48000040c119141d101407601c0402c00c1c0e520610b00041010506001a8240c40085a0700341c0001c20500c0700b08074101081e00030b44815070018001c0e01d088000c0c1d80100b01542e003500d1080500760344400d444d900700010303441100010045840100148410000080d403075005140010380305801c0800c2c4a0030000082d4802141000c10041301405580f210080b01c0180151307100942c0481da0008509400e9400b90088101c0c00640e82c810324a40000311300b4071002011030001694000c200c000c2d000c0780c046a00200819101c4140a0804001d45088100f500e0010140c00c8400e035891b03840c1e44005810880e205403411568001c107815241c0480342d0104104d5606440001e00281c28440c0902c14150882804915212544c0c024411504410003091511012401c07440c1803110401003000031901ca107a20720440c2c00c0043c90610 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 786619541 1250 786618291 786618293
    0x1081005130515061806130b0303040e040f060e060f07050a050c03030a1401120b342705010c0b09070b0304060c031b0815130c020f070f030b0703020a0c 67
    0x11030003099400440c00c40f00f103602840302a1a000d603030500381d0900007091660915100010940351034a00ea030583c80c45440350200481ca9a051003a14003400c0008070740300452805003825501a0016001580d11a29049624003590300216041e4852080b4080990340e54031201c40441d4564001138409080040501085c3d900c1442480294010401640c01240108541c100b0045000069011800100d220040d040000d28642020341c1c0c0301c9a08001403881d0440540342036620300048031400d030715a108503a50700c0c02c82d402501095070480350504101e02c0c1e1100000078546100c0034090140452511a1514001034210700740d1940b00b41900c0544901e81d640751100e0556030400e44040b02d02985a102840d64194148222804010500d02040e0a8203d0032400351109e80c02424583d4110004440b20701d0a40380c40c8050505403d015504100026803890029261f04442c40f142c0e030a0300890307000040106554200e4420b40307421059684d526180c0b4503003600250301c044205810301084030b0340c1c0c134 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 786620791 1250 786619541 786619543
    0x30c1101200609011103090a0b28051f0b070f0c0b04030302070614030105090c070c030219050f10021c021212061009081c020a0c1e0905010810051305 66
    0x7600300c1040700020165400e20348101402d4031a010345614103001c040c402c114030030300d0000340030680b02c0e007048503107a413500c820480ca004443c0c0150041540049807102414650007680b02903c144042a031803e404070f4000c02040d422440761152640b414418011003021900980c0b07d1b8600740d115580e2400582d581e4454004180c01c503034130540144c0c01004080105a03000803000c00700b5801d4100b0140b8660400000548464001d401c1d4034080c1c1000c0350017820009840e6082d40a141c000b84940c51713103c5036104400d88514240505402039015510743d0740c2034141182040d00305490b031b401400c1da0f095801e50381e42e0390040b034400010841c410b030f041d00d81006024400500811031060071038134152501d10300780704a503003c3e00110010040f078407204109688001c036080714500c82c90645450f0407261410304900d0a1440c10b0301401c03400307030715400240400d0010701c44400e4146031001012403035611501c28003260024401d00405801c44200400302110f42d601040c0d000064050306441600180c980e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 786622041 1250 786620791 786620837
    0x2250209100e271e100c1b0203031c1b020304081222030606090c0503090a0b0c090a120204050106020a121b1406090f070605090d060612030509040506010c030c1101 72
    0xb180c2240301800c195018108207010441714160f6a0b00280210103003d00d0040480c03c95000c200392100a0002190031543c0078800c4940d90703110002c0300030708072020710603600003070000504e030040c1d00950004600c40e0742d002000b92006c50b4190304c00b60400003030b00394014656912100100030202c9c0d41ca119401d00c00b80440618010314064400090f003981852505822502e0b204817201c103000041c0108030341e600c2c00042100c010360740040760b0000c0e510348141e0070392940242202c45501040c00a80469103149002c110540103008440502880c0da841d9402e07a00d59402e1038020b040d0810001c44641a140aa01c003180103640c0c034503095628140e03a803140f82d06d8100c0030002480e0340e00100140034103030100700301c00140a4010b80241ca0201d01c0d150b409040e03481038203070320345c0110b4042c4006010f00907254800710040ca054180600c14001a14004180d6804608044e10640c80d040100303038254460400004265456107034a80f4680c0d05d0344450003041c4405403007038100003210a600180c2110a001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 786623291 1250 786622041 786622063
    0xd0b01090507031404050a0201110c100c05070b030426040b030a1b0807090e0a020f0c10050a09170328200f0901050d02250209100e27 59
    0x5090400310401004e5566508141c0001182c00c02400040382010414001240d42400d021103d40490b003442810400c492182ea81c0c001009440c9081d555080174010a05c0c0d8418000d0720007094841000803e2400144c1c0c0284c5480283c00c203429100e880152100e0164102e03548540c10541e40380d10040380c2d941b048941440b101d07150200b44400210390480b020003440581045112460005001442e00312184a810011081d400c00314501c41c2d165811100004001100140d0b541f0803a410346035224960141e00044d9413411000840c7e0409512880d0445940b0100044000c003d410114040e0f400141403d000102600c00003000400c000a0f40c107210081804041800c01040ea803444001c1a40004e014075440c0802c043c03c1c89101c10b01c100c1d0a114000d00340981c82d0b1714a0f0703028100070b01540e00c561136000400e11890403402c09840381d580c0802e1080381d1100d805c0d52030f903422042e9a02c0e03500c202c1c000c1d54010390100e50001041d0b0039100d01da080c4a040703086514076824900f03150240c8244 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 786624541 1250 786623291 786623309
    0xb0303070804030b1612230103050607182301031806051504020304080301090504030917060a0608010e060c0f1e03090613030e0f0105040801021201051c0816020d0b01 73
    0x1010000c2200e00890180d1041003178502e805801240c06015044000381090038481641d11001d464110900c508090000708030707020000c800390f84a00d401c0356915000d441e0740000c216110b00030301000004000c80b60039500340d070f2100380d01c0c01540c4030318202013415481c440f07040c182c0302c0d040300301d41016240500c2c400ea03019507004169420710810700c44050407042044c0780514010001c10001c41c400354100da0444140b910006040d598a040132100000700e40c118002007502108bca03c840f100c009213081c060280c410041050b156124066800c9903141c54000100b90030800001e910114807070064100c24900701d40c031b940350409810403031000008881d60350000135800b009000501c902040b4855021100c61044243d0b04199100601b420b46a0300345144205160142400b09920920907100202400d600940d01c400342d40031400d00080d801d0044500610a00740364420011100c0035041d4034503041400a0314090000c403a04000c40b0300780000742d0700314200c900f803200020100d04600d4002c4c54205 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 786625791 1250 786624541 786624547
    0x30d02010f06050303040f170c03060403030b0102011505091503031b15060103051902070201020c0409060c0e37030804030c09150f06080a1506092603071202010b03030708 75
    0x41d61502207a82a41109000740c0c000c3c0070611460704400c3d402019150b4a511120090300c4084419250080340d5503807036054041e02080c04105034140c0c110380e60b02c4409800900100c41e4885840350440801e03c140341e031200341100490b40000e0004a9001d10060240540f460501000c14140d10064107903802e0010780d004244030108406140d1b8202d0f005402485d041c131045c00c110700c2c00c20902da4a040381c0c0780c000754000360740800c580c000c004070688084003900920010301c00f030812800030810045c802001c02c0c41710b400d644d26450032001644004404480c041082c03248035450200e26a1004892000705990040200c04105020040d1000b0b40c8141d07240030324107013880d002009450940540e0071000705d080030704cc4100c8420b0b10811042d14000d02d028903483d03580c96200d00c05000b0f00000341e200d2500742c51001c241c3ea43e004901000f550700004001d980102c1c00c01c46400c50700c10514039204c158002348160400189010a101c2e0091814030010481400300c1002a0031503110b01022240c081c000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 786627041 1250 786625791 786625811
    0xf13060e1608060f0a15090f0e1602010504150b061215010f09050612060103090c1502250b071a0a1b0507050d180f1511070f05090a0b030d0201 63
    0x209802c10790080b01500d20b000601100c00103c0c0204145004020000740c2116103c00114401c0213110010542c812100300001c1e9076a40090a4010035220300301d1819455607080d450600500500340610fa0002c90707030080040c41003001c00209070b6514900c1e030180081226032410341140303c4413409042903804204014020341c0015208184810b51003041c05030100c010040c50381d900702038070f13580d1410002c001d0b0250b41d0700c40101e00804a4100041140c80000f10108070740a800c1e072500d0045102e6000c4840c0881074220710341d004902116140c000301041d01050200e400081e01524000e880f5000c034000380c0040c0106250a8070049644100c4541d44003030000c1110041040b0381d10640c0581440c500d4000c881c4c54168880020072111014401c172a034440140e8103142120a0081201c410701d07180150319003031914618007000781c4220009840300d20103480300c8400f10f1807004440521140c50901d07803402c41403201c8100c00521095959a2301e0070010482c0c0c4007444000a400e04980c0006800c0f000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 786628291 1250 786627041 786627047
    0x24290307140c0304170f06010b09010c05030a030e06011a030114040908071101391b080c090a2307030b040c08070212040b1b0c06072405060f13060e16 66
    0x107140c10550303250780f01b0300c081d0400e004080752950545501c910f10742d51715600940140c0719030300d6008005010b88000156401c038150b0540c0004003080108040d283d00303903038801d8620b0311201006c4055210130006c2004001da0035106409040c030045c042c20203d08418180c55454860304001c10036150103d4051103c5403075a8841e0030f01ca42d03020390a00f01d407852204088044044c3c004c04040002e040301800952041c0300d0500f4601c180038034644080030119460341c1c0090380740d6210750b14807802442c0c05c602180c2114564000d81200c048083c4000403140041423182003400320240a40c4149a550402544207490354001c9100d0100c013611a285142400c1d03000a19010001d4403d03000200705200500c03401d825030040754000b41d0890003043ca83c3e0320100413941414032455501c1c0e400b000024803a42005540e00328200c0e9a00340521101d8071001c80c8081700162242181c8039640900783c1d0b80300000c03030726020700c40c1d43c902c81d0401d47c0020001d450f40300c0d00d00c2c00c00050f1248ca960042800c4224043e44d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 786629541 1250 786628291 786628319
    0x14160c0302360c0702090613020d2a14030408120a022808060d0302070b040618060c03020703061a121c03110703111024290307140c0304 60
    0x2c0c0c294104000f4509800003444078060040001c1c401d00f21607011a071165600d4110040002500d4021952820b0014070345c1c0040c221291000c41111052003920030405140a110748020f01c0e43d181e22001d0f030552205403086034001042190400024401d0031803941c841a00144621038040f00141e64085002240b8400304050013421101562461840100380d440380001d81c00180507682440b101c1240e00d41139042002a0704410520100450001170f07107a0710643c2900c8a100e80e44140c00c1164031420100c0c1d009000c40b20203005a4001002040010b06c25446040964030041c0101b44c0341d50300000090030031008000106450340200350040010003030124a64074034690b801d040080ba860400045854000c440c001b900313008945a40a8170460140302c0940c440c46512401c00000c59420080e24029481c80305292181140140c0800d500c0081c4906030b03901c128013885101100c2c00342503031a91951005243c0020071260184940c0360b10300e014007a182034600304d0301460300c0d2402c212992005034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 786630791 1250 786629541 786629629
    0x908190b0c030402030c100e040e0109030e150a0f0c05010f140606040302091801021e040821160203100218030d081303081b0a08070f14160c0302 64
    0x1000401c1880f00581d40041d102c0d6880d0070596076459a0384a0038800c3e1101080c40304420381281c1020303050400300c8010f41c0f00c071054034465101c020400108805000c0c1021060411400f46801001401c10807400790384006e04402041c980405c3c9100303659651429140010320300d2450649130340200c04035580d40445164401001c1e101d03941018038603000607002040140051502c4d00400002841e048000e40448001007056104402c24407440c1c01080c9940d407042c480c1603900d005a20300d1910740c0b14680607881818040180c8241095060350f42d41460481d4040700303c3e0304d842182020310b001d44040c000f6001b44205202d003994100300e10740615060460020081d07040281038030400104038845120808101d4041c5800f003001c0d42c4203030110b00441a01c1c1e1080d0307120704005c10003a2a4a90101c032240c07041c010344ea00d2a21b81c8001442c1603c4107a2074003214825130b10180708054045003443d10551a281c015810154030640d2900880c40c089072020028000000c5c00d021b0600000d1f680e44000414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 786632041 1250 786630791 786630811
    0x206070801090e120d140c0301180903090e10380702010f05030405030408060c19021516021e0307050f071a1b1606030b120304090c0908190b 62
    0x43d03c0208101625504116580440b1850105203e600c0c030703600d40c0c0700002106d2040b000000320b081c00400255150000d00c07038034680882680e1000301c0d00046004040003198584c85200002c2d062103007125400c0d50003418411030b1440c205001402c0d22400701d0403002440c0c42d01e0502c8000004051050046030086e0541c1c814207820046c2c1401070340c0c40803000081600c5440c00c0c4d030301e0340c0312031400c141140f00303a51290449100300350a000141040d032000300218041489400030111300c0c07241c1a82c58071001880310300107084c2036001441824100010011207602c4d031043c1c61020f1454400c004664041014a2900b5440400c1220030001c0800013909102c24000c0240061454500c0c5410208a0761200358000100801c0b032100101e01140142108280701083c3c07105050381c60061640c02d081403003807100103030400350410440d0800668400d10050314001543c6030a06261000000d445000740312001c0000204000035104800c0c4102100145000580804480642898252800084e00c07411076 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 786633291 1250 786632041 786632051
    0x13060f09092304020102030d0603110901080a0512090a050307080a06050709240509040207060f050c0918040c242c10090911030910020a020304121e03020607080109 72
    0x1051031445502c285076103450740801155a10f00c0100d00354000c0d0040c94040e5414041c001c0208216021071240840d01036803c05980da0740c92402c04da881402c00c0000d8819008007c85001c045c8101000f0141040085d2a01e40100d996002091520406074032008035034110403921030410a15002e00c0b6007020052800141003420528514154030405110444200c444442d11382400e018505492540c0b034010f000b1500e460035410005c015000e40902480b005150030000344050182c50160b03050008082c10700d000c1d18118205407504000080d0040e5040000d04400256003202d54907a0000071140c462500d54085040c04003610842c2c070340020f041e0304091a920780301e01859942d8600c25224040314202a0321034454800d8942070a170743c010906690a0209102c110702e842402940141d4081007200c4000b92442012001c0380100c00444006800801c001c00010240a5008562602886903c06001c030a40360000c600101894101e016070451003c0008140c1c0014203140100911442401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 786634541 1250 786633291 786633311
    0x6030111070302070e040c09060e060f1c0308040501060506041e0911070615081006060221070b0901020c01020304030f080f0405030a1b0f0c0302100302040b0301090203090313060f0909 81
    0x900c4c2e94650007440004000440010700340086860544014181c070442080308a440e40c410f51a10602260082d0050141034480031050078030440320340380c46143c2800d40715a800300303580403100c44101420a4079150340318400840d40740d4500700104001e14a50a6200180c810340c4448410014141e000030340d003904c1c00b02c0c0030816410b00411600600d60005000a50070058840c0d10756403107180d0003e0005101d014045443d030302c0c181c1d200b40c0954507035400320759031000011914101c0180000b840d0281000034864200040d1035006402d811070290400941024080c140c0e035030883c1c008a40640006504092400e515600401119042909a40a01d05514054440640c1da20411181904202c0e40546804400d22840c009560681e8406c4134030b0f035040d90a0602c0351041c807260005034800c0d440c01c008030101c2c90081c821141100c0119403000c0c1107a20700140c47c402900002d042c0340181c0402c0003142c02c0c81003641400000b410a0b03840b900c4242d820700000404048484e004403140a02d0184010307 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 786635791 1250 786634541 786634543
    0x17040506010e04021309240b0a170a06050f1e04030f05090a030215070b0c03010f060c020103230709150c020d1106040303021f0605010509040b060c1506030111070302 73
    0x2905442d03410111001a880d1840401d1421080c84200d806040c9041d250100304603403408075145405030901d103088603905421a5000b192107002070a5481150b502c2c0c2080780c8107002e004480c421001d08140d41c00201d07503880d1041076407011074510003a00c199200300080c14041e0110303801c0c1030f050003806403001d03c0c00740c1d00170b044c00c540322041c0402d0000c08a43c1d0390132a076070880e00d18041c50b0302904040d40039008041ca0390f000e0308401421500443c55400040300092000300b81c030b04881d0900c0300800140d2508405440107030b1090030a9040545800901074010844240a02444c06120000c000d0303240c00c440c014800c00302508400a40c400c41043c801d00071b6449071844c911243c0440d01c00740c0e02c45040ca00245c019140108040c2c101401003400014580c000c1080904c04c20400303090700b26040b032900070500301ca0650241c10b01280042c04407009038102640700d101c0940e0080c10031403600f0501c0c0c02c89480d003c0194101015400340c0780c01c01c95242000c1c0070714482c0f62284031215003002541d65001e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 786637041 1250 786635791 786635803
    0x60207061404120f3e010309080a050f2a0d020316140f0d020a030905060412031b0804142706010c05101404031709030405040209130c0f170405 63
    0x41c0003242c0c4070002e14244010b41c6440b40085c0080750300b081c1c0d10355110f018400130104c50030700388080580d041c0d104401d82d4001d00a44901c5c540c018401407078542074060a03226504441401082e80c00300f4840c000e0042c030150040d0422044100151400c60400c0103428503041580340048210b40050001c20402c1011000325200240c2c0700c80c2c24078420041c1d101080c070340603880503821110b220f000d55102540e40c01040c0c40c490f450007a80c0b9100803507211802d000c0c4501ca144100720880e81a00741107408288100604492508240c0c2800000e640c0e0380c1b5038224940107a00495540e2408041c0354000703107401c00840c601424410b03c204000440340760014200b1900815444c1402030640b40d4400300042404030501550381d03040304000300e0812050b40e040d0103070111400c0b4040303104800308241108405000030b10415440c4025490141844140310103034000c00550354000800c0344000b440c0f48034a010b0000300c2c1d00740d6550420301e400000d400518401100188002c0c0196003414400072039404551 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 786638291 1250 786637041 786637043
    0x32310060b18060d14010314010507140c0a0209040507060306050108041101111005090304051003020304150e0c061c051b04060e060c03030a090209092a01090f06020706140412 77
    0x400d00b01c0030b6450045401c52041124030401a4a80444901045900003445046c0c9003e001210940088507001030b0881d0011386050000c0f440001c0c1c0801311401c0e550003040140301100c29504c40c40420f90100d84541800d44048455400030716090110325418030504006100902c1c015401d8102a01c68001c4c2e9440302040904111481c0d0362016505802c2191403140e54035000c0810803807401091150b10390f0001c1c00307158450b2081500644009104e402602c0c019034022030a869540042d00c0000c00402020b00450554040c1a02004055a034080030b04010010700810300b0b4076070b068800d400708464004040d60b8070341810030800c1402d000d281081c0c0702559002e0070301002148595000641d00d01440050205903c0700100f04190210320790031071140140b090b198030505840741d00c004e0380c0b02d0ba4a81d001440c80ca020b003081c040e51004448400d0300d80c0c0d806041a8188603100d0002046100494202c640564004030040041d182c0c4004116401005981c01d0b500f010b007007800002143c188094 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 786639541 1250 786638291 786638317
    0x70f0b0703020f0601090608190218150d03020303042306070e060d09060902090114180421090e01060804030e3c090c040b0a0f0207032310060b 63
    0x40e09020035000300b12200003100d0103030841d80c80d5a501c0c0c858201030481d0740990ba886008102810038411600300c401185141d0080c040e070660090000c5104c04030340020114800c001a00b03420f200c42e926803001c0303c2241e60095010355030300c0c580f90401d40480304807000c0800001000c44e00d484181c031340214100d500030764a07180a0001c0080d100010302c0781e00400d00c01002552070308445404010b103541c450b00000e80b0996140801d60b81e00c04a24140c203482c800800c2c0c000ca840000b12104902c1e41da00b0b07aa00c10711070f20b00b0320707600c90740d01c07580c150150141107695020400c52142030000b264200007060040c0f45c2840c20078800d16181d40e0040c080c2044540a500500c040d030103504010507072080d491f42005c40a01d03c2540c03200c3d01400561412030700d1048900030780c3d4003008251107050f040c044600355100c801e201880d011074000102c2d41c0e0b0198101c594210302501300c01200041c504030101c44842442e442e81c060020b1000304150401c2103400d10f01110528240d8108510900d40c4191110707515124 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 786640791 1250 786639541 786639547
    0x2210d110c09070906020c0307150f032424020d1d15030105043207110a050a1208040b01030305090d0803090f0124050f040605041d010c02070f0b 64
    0x381146000150408503611900900400510710b80c03042031081107884507800c803400c02040100380750322071a59024909075a1032080550a00500910703060803501e4080c0f40005900c0e0340c000c0304103d114402d488854100384001410401009007904a044040746801c0381c05400c405030801035a5140c3d81303414070042c09400c01822214001072401003224920186c41c0760364482014010307100310303402409694400d601e440c00c0006e07070b5194408803c1c0c42046500070300d94228002c244545c07410710018000e000700024401c0514848074240907000c0e031244160010010040c1c45c1c60540941031114110004010030b034010031011070569810340b41180e401d4200380765603140290114110a134840d0300034082d104000240001090002010408020200300804c9224103401d007484912132200c0c6010001c0c41211018007261400e81000c1118aa000b400002c4203a5078070003090030740b4400c21809084d03101c01d08070805e1002c002c0c00347c080d0388556031025010483c14580c007415010b600703019070b5204540c04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 786642041 1250 786640791 786640817
    0xf0606080109050109061d030d0f0b03120301180504080a0c050c060a0810050a03080f181302030a050f07050d230c0a12050106211407030902210d 64
    0x5610440280c05408000d0002200d10f0426a000c0e01a84504940c01890034420388018040824030038000380c80c0c2005585000840603519015081c3e410344014180c0c0c0e2024508900e036000c0041c0e1001b901c05001d0700c1d4803585410b000025148040801c0d00c12282054100710000e1010720403501d104a8038200b50310040741c1d501700a46842084442c241d0007400002e040852a6001040c40d0322900c04c09140780040783c0c0b11401c1c006201e00501c0700502031401480060101c400d1200a00880400a08075080c076594070310014208014040e490b091485d400020300c0141c21341d6006940c3d1205030201042141e06103803400428074402c0b82c400900762a41c9940c070012903d81105030703014100515440c809507090003240444a640b080c6110404100c04801080c1220001e014950484815480f100c005400451402140b105d114a20640e50355a440c80b204611022500c480d000d1031141d500041c505509105020382001d80220340008001100c07445007409100040341005e182c014507150b214490a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 786643291 1250 786642041 786642053
    0x3010219051c1d19050307171603030e01050a0c120f0204170d260c092106100f0b04140316080a120e0112110405060c03090907020303010e040f 63
    0x1541400c103224146010000b01165001203c403110710201c0603110305000a41d015102c101c1320800c02400d41d0400c2c08641c020034440d085615082100c00311051803d59140d00080c1c4581c9000d00c1180800d55036044070396046e03802d1290383c2d44503403070540404c0f43d89040301018200311a0b031540412016180d0428000c40d51407a010382d4010800e40d219460407103212101c00d911a06e0400360315001035002c40030182c11204019400300f8241c5c42441040e59512031680780500355110030002a04000b030300200440a02d1100c4105c02100c0c0d03500041c2059007006800f22580141d540e01040c0f000304401020b000764058081110129810390300002e070721002e8500400d0070448811321001c00c016081c00700180800011512520b014030a41200000d101000b00944240c011544000d00142d8002d261027041a92035010422414044030441d04060b07503040047d15503404051450429000403580e800c2a0a04449060b08042a030015506540c1015000c208962000300050304849d506000c01051201c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 786644541 1250 786643291 786643327
    0x90f140732040b281809020304080c0a03110d02070b0f070302071212140307021908190513080106180b010e0406060e090105010e030c060c1204030c0e060301021905 72
    0x560105125180c0d000c1184402502030f01d244010b80740000613403419901c0307120b217484d000c100601d020684849170800c0c2401009420080c07049030810010440c00b0324400e030420a5001c1d080c440e07a01d100c0b0054008450b241401c101c9211601507500c02c680500c14541d1074810303a075181103c0d12482c2d40314550780c01c04a141401c80d40c4500c110b000f41c22280c805000d0080080d0300100d085490f1400d10007858640c4c00414071003200d6010041e00000320001c01c9889009a8411035401118042d080004801c0c081da1155101a00400441e600050307035500c2c407020002a00040c0400c00c002c102051400000301d061031620007800410640d80c081117281e982c000e500710707400544064420440c5030b0710342d9030180c0304056002c445407103903403100e00018880d07110b81044141300c81e002d0003a0190105070b40c01d10003903402c544180090b9016088030915415a90406080190b01a96114515a240c803407084400728010705014040e9004116070000c1402c56413400341c120309203143c0300e96581c0503d9942e0503688 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 786645791 1250 786644541 786644549
    0x60f091504060305160f03020a061805130b090f040f15090512030405161511030706090b10061704030c08120c040f051c110109090f14073204 62
    0x285460b0001c400c0c0103000034008680000746200300c43c190384554880d0702c072480b203200c000c0d80070407000c0c000e00c45030384100000200c50140300c03016908103490348005001004404403001089503561766203030b554034001040341d410819034109030032981066100e0107101c00540c103001e0200e86c400d10040c0f4101805038445c002e0142c02105440d1004c44035440045981c4c000d4034180c5a030302c0b6501038007181c0958400c82e40c08035090324040040070f0384207400940300c41d000070b10b49500c0c0e0301080c0542004078649010302d100d1148034a12140300c40c03a003010740d010300302d0481c2c00800070480c030300495040300380d600008960031581604180d8101841441c01201d640310308103800c800000d070403062000303521540014006480104180d4000c15448105214485c0c111040c2828031031141e040100201e00a8104280c20305c8042c50321060207600c403000d410075181e0034000803030742c41d03511100c1440c1c048244d00c4c1d0341d130080c01521b000e2044000803c50340c2603900d00d81121500b254901040e1011030201d03002150028 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 786647041 1250 786645791 786645799
    0xc10060905060a0b04050d060e031306030c080a021201050906040914100e150a3303051b030303131a0117240a0c03061511100e0a0f05010b1201090515060f0915 70
    0x3e2f5844010060103070120a4a03040460101404601c08140c2c1d402510b00450030300044c1e031042c0c1e29102c1000325001c0081e255641055640c1081408104000049102082120010f041641c0340d60340c0d281c03c48120940c01c0754142c01c030140d40b41045003c20f0f021500003483c110003040c55560011810000029129210201c0d04120052508114031180583c1100d000d44142c40d8649103002005068240c0724489aa15400030400500050368103510461007a00031010080211b00d03110301d00d07614020030707041451244e0f482e0803102118602082003043e003841c96030301e4465040c2c1c41c4001da5a0b200d0081d1075582c0050315941810300d05072082d4000d00c0205192882d82d40360b0b041495002e0000400411894828044c2c034952a8072004140599001c440988008114001c041d403134413200b01e198000c040f0b8241d500c6000d031111580d0b4070124805a007a00c1000028450780c14540949001d480240403940785900e9020403100f982c071741031303409407107003090f00c034101c00303036181e0480e801741c05c1c101980d40d640 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 786648291 1250 786647041 786647077
    0x30a1104270c0f0207030308091c0503041106040f0e040204091212051602071e0f03030f1707090b07020301090614010302120a0807080c10060905060a0b04050d060e03 73
    0x41c0490961070101c1c6400c0301c0000c1280084400c0100c501c605600b43c48400359210f5141080024851781981da030154618003582c1d510503541d94a40d0702c65582e5000e00707000610200510091101d009030821030a04101c911707600e00352900c12118510301a50ac9031072081b402c5000003500350344403038102e80c4035141e0111200c00765502140c0301800d0050f003000c001c0001864100001c54209400981c1200c81846030001e200c2146440c1041e05900e243d8003108060100b06a8000351400700382103420080d61203510b03105c0890300d4211000f401d0602986001c00c4d07014407041070001607a0441c0700c2c50255514401465941e118500109014081e0320a004004516110f180040300814401e9241a2442140c0f03400d2240e6401d2455680c80c8045500585a001d0420140c3c0001c0c241100509007207017082c042d0703000390468010190448050317902025201d601c03201000058a0903420800160192112203800d25040c1800b040d0000010400180b00f25a514000460b001d41001501d8081e035418408103c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 786649541 1250 786648291 786648329
    0x130c151e0302130602071a04030f06020c1c02060f0703050f0c0a09030c0b0c01050f0912160827060f1b01110304050a060b010c1220010f0515030a08030a1104 69
    0x141d140c000b48a00b018002c410300b46e47c001d00416108039406c80350403050403006181c031501d07050000c0d4001c0145a0706841081840d4a1405070707042d105006c00c2094000d08040c0c50b0030316000083c0c00d0300501c2041010f00e84001c208104900808068000c01d44462880d110252002c0070b503080240e540001d0300483c0d01041c0010410700140042c440c1132000e0300244025201d12883c0c0d103200e0000c0e1003c5181da0010941c01441382180c1c0301400d8804006528500c21609035200c103140703a405582000c44504185034001720141011010210002c010303500903150800c0400541c002e0b028100e80311034011140340c00c000c07450000750805140040c0b01e00203242d903030506141040e955038110904503012070414605800d29801450f07030508403504110950607a08810b10102c038400d24880e499050010344100c1840b00d2282441207008801c0d09880010b294106144e071009000e811408141c428bd1100c41800c00148003002580d4108200074408a206030b044031081c8494052500810400703e81e400002c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 786650791 1250 786649541 786649543
    0xf02130e01050402031209030d0809010b06030c0306040e0c180907080d0f030506150409020901170a061a030103020a17011107080a1209211403130c151e0302130602 72
    0x6000f40d10031811250404d00c0300c06280101c1c02280201039050300520340ca034030300c3ca003e1710303045030301c04034407000040c0c0203449034001141d507081031300e02400f100b40201c1007100e14140344c811600390070b0082009110308000100041c1c1c3c00c8690480d0f0104103c602000304003480c4041182c00060101d1400f83c038000312007a07500800680359908034000090428000c42c41a0900005c0d041c2e040090390200c42c541810850400b0280d4130003526030381080351070100741c8845c00482012600a83c01e08501080f0030b407400704d0500c00c0000400035065021b90400c01000180e9801031a1400c540b02c0d40442c804215031504890b00504440110948613400001d4410801c004003004080d08240c80d1076000712034980041d114221000002c00802c3c3d040b402440540400078400300460f8108140360109800c41c07203002071803c0d50410340b00d1381c1208145002113820041990800d4000e4001004207480c404245040204440524060321003420360760702600711403510035011280040d0900c002640d10941da580c0013 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 786652041 1250 786650791 786650801
    0x6030506040b16080603070605090d1a1005060306090f040c0317030a05150307060522140306090f030a0815060a020d11011808181003020301300f02130e01 68
    0xe08460400c48182c05600d44c0070b03454030b5008000241c014144541030000595290744002c010a07400250307003600d240000d41484a030041c005001c81da0000c5400e108000ca00380210540001d07204000600400032161103113000113510480d407a0b00d010709900c46041c000144016604003402c003002031070188460060a400840c0a601d0b030f81c60400456460103400b584600c1c002c1d954650603004000208902440b9101600c0703928000c104218003070b0300c0a0305602490b240d603072104a0510000744090024502804100d50000d940b00c041d105010100030388a4a130320034454174030b051001f4003010070405a01060002d40003a0003800b410b40c5c40750b94101c041e40e250903200040d40050302a03100b031823680c4410302511000d1510004003101107091a0f84030a19034100000111043c100408918031a5685181021f007002d2140c60041c0d88dd41042004030890300e0071032081c003800c5100800000c5401240700e1014546401090303504240440c1d200007901840c918ce281c50705c9a00b084142c6591b40419885 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 786653291 1250 786652041 786652051
    0x140913060f17070906060c060f0b0406140405010f030314030a021b151f140d020a030b070305060a030b16031e0c0908161721030103031d060f0d06030506040b 69
    0x8030f8900f2913032500201c09440710703406800d000801d94240240091600e030441c042c44104442d011400d000000041801c07925198001540c50f0800c5444458074141445401c0c00342900704480d08050342941c07005401d070500c144c041d010804e8000b0006503070840550503102501d5108a040010701c00185400303554182d0003440d0703598003140301301040d07500100c41010891200d09610300c070142883c04022a83e00d42034a0314050704042d5071140000140d85e0000c048000c1d51140001180310b0401840040480f10014000d40c001d01c00d114051003c00c0580100c030b0b0340807141e514141c981d540500c008030040c182c0c0c0500c4240b04225540151030140094202c0701401c41517544045c80156600c02c016519045c0550003000d22541d46400d201c842d1070000c0c801c6800c0b110780211040c49249052400c0005071010384c0c9128000080010300070103a020114044400100c55206564402c3c44001200307403007407008503882c03a540000c89040040203900580c00464002081d102c403441e1074142441d802c071007110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 786654541 1250 786653291 786653293
    0xf0e0306180c01020a11010c30110303060f09061309230316110307080706050a0f02030a1d010c02030601030605070e0306010608061302071b0302040c140913060f17 72
    0x30780104a540f000070107407119500140c12007000d8010703600540c4d40c4543d001c003c0c0c0300e9141841c542745113025105e00401c4050b4590f486daa01000d660000144108419010500290000c105010b29661114010701c1c0d05501101e10641d82d0700c2f5400041ca0500c0317000c10405a0390300b000310020500500c0d02400c8289034004002c20700072a07070b58000e81e4580c80761004001003002602805000f1074403d5040d4404a40060102c070406500c40d21200d280c031240703071302440000d18000342d40051960300400c1c000c40194140019410007090078000790407144100000b070142c0700342d80c103000c1d0103a104821450040360094103841d4956140c0c1040c2e80541022116031022505c07540071402c43c0d00340020750074129020f80c1d070f032074032141c031028100110f8050120802515540912401011440035801c540454002107480d0034414a10b20610044d54a0340e103250040c00000003103600104c240e80116090301c1002c070740c0755031440503210b8060014a09900109a8079820100c0810700030f60310407091703850500c424 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 786655791 1250 786654541 786654553
    0x108010806361c0c081603052209060609030f1203023105060304021003050603030f0c0a0506100803090402130801060f03060506041e0506041b0c020a090507050a0f0e030618 76
    0x94050f01c0341c42d4000381c0249040170030805c02940c95000b00343c000603144280303005071420740388070f11002c10807600b140942c6900e0015441041000514440d04006014509184440703a18544503075003e00843c400c05071080e13000d078031683c407400d1081d03040f01c0c10364082d4911f00000c003001c005c0c20400500c41d000c0032110507990800118480c034112041d241b10f294020031600004040001c100d002c0c1c840644a690544014403c000c0341c00c4403200a40b58144d0803200400030202c1600b0160b1030070b000500302c0e4100304200b82c010701c0608400700071185140400c1c0c6016a0341d10301034207144001042544501036075440c004d0b021607600012a02c41d802c49028100c1400641c454008010071243c800c000555800f00c6201c40e4015104260400c50f4050001000020b2804070104a10641003920315840c001036000c4402404520b41108664050b06101204220310310740312802070154403c088540060090b0a000d10108910a00d505085c1d400c0103801d81d8818184401c01e0122804160040740f1503000344 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 786657041 1250 786655791 786655843
    0x30207080f250e0f09061b1b0307080c0c1905060a08060d02040606031d071406130315021e030915060a050303030f0603010b010801080636 61
    0x34140c504440544054208912610510041c0e005805880219061221400034190031400f100c0c5125440d400f20781d5543e884c04403022801d1000c002c003141c28000d20b560b031104c00001080c0a41c0c0d460307000903187e80c0814000000452a50142820003440c0010002d015480700201040c20703403144c0ca0554000600c5000b40b00c048032900441d01400760001c1081c8114031071070b0f00c03540b0352641240c005404000c5111050f00824203596850300b03c10003090b2290b05070580c000020b0544d40a00301242c015010321400c1c60700c010840805c824030300c1d200c0c02c00440e401320312000c0d0220050041d944505800f030800030801000000e274028241900140400c9000c1404c620f080500b202d04c00c042c102c020342008225420002004d5002501450700b0104081c80490a508c00300002c601030300a42c2603151051134150101070a48006803482d5042141d51b00040065803400150940c0203408000c80603208600404600071442e81402c001c600c1040b5603100c0c0d110030b40046114680c41c101601c20741c003000c1039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 786658291 1250 786657041 786657043
    0xc010e01022a1302070f0b010504020412080c030906030718050105040e181009051609021204080a020328030e0f03091903022e0c020f010302090f060d0903020708 71
    0x1d10001c0c42c012044021400041e071590301c03848a90300c80010301c2060200c005100620803a005040101d8a41e0301d1120700000f4072190030811401031000300d0382940b03824284035011100c40d500c11401000354202065208000b0340c1031090741c042d00c82c0a172170f030f98403803a110384010451050813009820303c90540c6404903031940305a040318183c482c04008640c1c1c50b00c400700864000300390240c144046003d2078a001155000601920404901810003420020b078103000d02c0900040c4d5034058404944104200c0c40c4102c0761070100c5074040d800070001500c882141400340c2c110b00c03400c80021503011528400c100c40c0d0001d1000060b009185607410000700c814101c4056440d982e4001d0081c4a40c0103020301c0e44546020f40d503030300c1141039141c14400c5960fa640d001c40c2d01c038030000d040c40918048501072109002000040010303030300458948440c0f410380580104e9000070030280e459040540028101240c2c1c1c451002c88c80a50f040627141650712041000f000c801042649011001809090b20010341e04c18 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 786659541 1250 786658291 786658303
    0x1e0f05040b07080916060e09010b1204260d06060e040b0f100201150b030412030b0108010e0c090d05011e0603080d1e02040902121e2d090c010e0102 65
    0x1d07000c8011102502d8203041654911801840e036246442280c903c4024070880c00701c000010b007040d40381c212004080c00100070816105801c9000e010105110a45607121445044c0e90419004400c9501709440f008a810300c4160207020b004010000050303c46460556074050740072144a5074904d01c080d4110b10030001030ba030900540c2a800762404404e09203901d0031903aa24a135060500000402d0b0424000c02c030f4100c150b0b64807010b203182000c000c10090040c7c400c4943d4041d00c0320716040011495003070001e44015010f02441061075116000a074400c0074070821902581d83c000c2205400c80c0907850054064003c80003030000d40160314007003003214900c5009080559900c04d207a2810490001100f1000f40b012082400c4001d118286103e803007500352004102400e8407850143c0e0b1140d8003c00088034dd04090030f181a943c01c110300000d9000f11420703000b40c00c600d50400721401c030751084d070401d50180b941e082c9491250702c90400b8800c0e02c020004035216020401c2c1c0300c2c006401d01726001661640 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 786660791 1250 786659541 786659543
    0x60e0a0506060903070e19050108070302031204031505060105041e030318030203190c05090108070911030108060412110d090e07030903050304080a020703080c1501080c0105070807060605041e0f0504 87
    0x25102c10340a002d14a1b07a81d00050344110b2100b641900d2209100701c0320b0030f84500b07900144003500b0080007807095060a00c80445280020a20149024907580c2c1d03101c400d0540140e9149141c0d5940040781d180d0b032003171007141e00900501c00606d440c010000c8002c110040e4a01c4201c000c41c420380440b0038a102c903102c0a0b8116900180940003041c1040304602034000180710840791040030000109960b644d03420784a01800030800100405400c00c02c499041f10f40c102c1c04210900010300c01001740200000301c844e407140d030140d402c58540d007400b0700030341c0d4034030701a0901442070040100d80e080c0154000c1c642c608446081040bc1144d4440c14402c0c1c007155244078016001a2081000070f000ca52400b00600b00d0031198411290425600d4440c141d0b19040b5040d07000280d0031140c51943e09412800c5950301602500780604115281c031400a00315110f01d80004103c004041160001e2002d80c3c3d02c480000e14000c4c20034400302d0350486c410000d8440c50760710080b0061030040302e40bd02d1021482424855 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 786662041 1250 786660791 786660793
    0x509010816020d0e0a0302031e01050601050721020a060c1812030903080714030a05030f1807060309060b030708030c071d060906061b03090f010c170f0706060e0a0506060903 76
    0x455840c03000c442d6115100c4c2696000500c40500000603102044032400003025812401080c5a9110140b425a880607010504022061020201103280e10b61140c04150080349600003400d12400c3c01d03414134401800140969181038000381400741c100c00a24034000341c074020064409d46807c000095101e00d43d1000e800034494103402e000050103500280407180c010b02c400220b540d504500f882c95035000410f1500054004030030320a8209488203615040040c03820a11134080110f640c40d030b61040c01e0b200d078208158a6200510510000d94800340390080c0c040d040c1d40071181c41303c90f03050380c0340e01011600b980d0340b1580000258804580601e000c0340085c01041c90341540719001040042600941800d40c40721040003412042d0008030454000404014040c50f00d54203010104004459041c1c03d450500040091000018034100002540f4803403048806440e6404021682118060007a00520003450060003140c1c07480700d5900c4070701ca41004403090000360380c0e003804c1c003a050150303031202505 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 786663291 1250 786662041 786662053
    0x50a061b020c12061f0b0307030b0f04141f090e07031208070806010c0204022712010207030c060c030b03060a090c05041e05063601120b040308130f03050901081602 72
    0x46000c802c00307610301c52100480c8846102e07840c6c115007000b075031050381d0a10200c0c3d5600f0150585003883d150910b80400122000c220350800c000a0f45801c820060040d02c80d981c0f2041c448050204100c801c83c080d04920108011a444d980403181e60340103036004c113a8210078851401181c02d842900d14500c114001e5682c44056100c000056070656030200c81240d002d5000c1c4040d5058680c00110b02070000682c48803581c0d82500c1d03400340b04610401c0d1017254100e90040081901182d080300951f240554040c0000030090303a140011802042c4030b51000c2d603d4001d4505200d944511500610180390095100b0018280e8800802c0103c44a540038200e0440710030080d01c5c8502c486500c0303a0b500600145c00c417403050441c11a0520390840c403a90102440358a80e000d03803024031381401081d024142030f41010501c00c4141c4c46016400b03000410043c20800c4150000c0c00d00106e510215940e554001054409907030103160140c103603000011420f000070440340000304044035008050213a100e441d00a045 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 786664541 1250 786663291 786663301
    0x30403050d0f020307141e06060a0324021611030c0a05060a0207150203250b01030b0c0c03070b2202010818120a0807080106030e07050d050a061b020c1206 68
    0x480240b44107021007980418003910010070078030070034100850b84520103884458042d0011410040384540c0c001c0d016413025042000070780b182d69111741039a03001580b102128220341100604181c1010112002e280041650104903130303101e00b50301d492441400c0321011031060009042d6038480040c286540420541d408102c40d00701800200b0141885106072103201f034403000d19508491642c0c00303a00040c2d200241c2c0340c00c02d8010a41085569107043c0005d1204001034a484d0050b0f2410301014154007058004030360700720355100444541407403a006994030381e1982e00f0000412142290344e404848021080e19611a1305040c03800070003035058654a40f10b840b1031a90710100c060f0400085164421440f41c1281131118001513b4185c100c6e0b543c0004074981100000c1950304180e0046040c14200105104850004034101c0140c3e40140c606a1145140b8100746181110400018192514016400340302d030724070740c503841000c07082038003150400703402c000a01c4801119910038204039003121000c03c13 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 786665791 1250 786664541 786664547
    0xc0f040b03030c01091a060310051e040809121c0f020f100b04060803070221010b19060e030703082b05040b0609070c03020a0215070b190506150d0c1404061d03030403050d 75
    0x62f42040031441100100e480303005451801c00c0046d942a5140c0e10040750a41d4a460003440501da05068000a401c0c101540400004c50b51814a60442400441c4214080c214800c01c182440b400c1d1b55800c80b41e00058020016006000340e4403201c5c0218103000c030110f079402000045a102540c003034051200044c0010901c0e005400070703c1c1d4003415548072400c0d40587d40e10850301d024007184080c00300760b04a240246c0981761103403000206009801c54482040461003650a807402240440342e0411081c500a03020508202460b040380c0c121072400b028002800040c92800d8800d038030543d45440151180401621003682c840300080040c0d000112090060400441c00c0d45011584e204040c1001e005607070f4030440c540100c0392404851803101d25504030400701e0041a400c0501038510040c0f1200ca0300742c086251090b0041480c0140d103690ba000c5015209500030840001c810302e000d521103841d100f0044c08080100e00d005940d00328070030804130510b004421102100d40c00320040c030512688040079 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 786667041 1250 786665791 786665801
    0xf0204080a1515081c0c031b0c090507020c010215010b1c091a0403082d18010f0b090c04051c1407091b030903020c0f040b03030c01091a060310 63
    0x684482c0c1d8540031000a14040d0340581c80180c018140944800da030003c002c1404103845105039002c00640480d14000b00e0740000c440a0f00207903011852440d4025402c121403150180c0c4d00c151501031030501003010450f80400c28000141090742030792030701c051409254075074003400c0c0190209000304004400b01d1030700307803040b5458005402c0c00c0410a4450f40d120342040000380782200b08100364280402c401c055001e00c2040e070041c2102c1c001d00d0352001450403031805e41100d2400002d81c10a9001040315440300030640000e80d03069000038081e00340342540c180080c20729180c001e8003646031180403d9a503041030303054030291000a01400380d01000d81540280c800001c040035141f800c03500000c2220403105201d1040900803e40d4040f510404210305000715031203504a250400d40740c04044000240d02160020b160304084a20f1243c240b4402d0001c0d00400281c2602a814400015001c10040b0190424802c59004800c4245061250524002c0344002100c841c4e5058000d40c5011901811035400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 786668291 1250 786667041 786667073
    0x10b090c07290601030906060b040b0910050a080601200d0207081519020f070b041a060d021e1518010219050c15090319050c0a123e040f0204080a 64
    0x401c02c00d650707001030307501032b840364121052207040051540b440b0706000c85403005800e45c1b4038040786000c0000000a007503c030041d00b4203040000700c00010b42e0003c008070003840d901b0101d03001e071010b10241040c081e58541c4280b041c11883c0c000c08045070013145003002c0a9210f08904164400b4500c1d101b0047e0009500202502c114001c0030b221117001302d10036061080c40f50344610a06d200030302c8012268401614020305440c811549081c4001c0142c0345c580c82c24440d00d0743d2860100340d40b010740c0000b07030880000b42d0240e00c081d41c010900c0c0041c1b0307000100c0185012404c1e001d45480051a444072020652101d0340070300598425001c0b1003850500640300d00340315511451003400d042e510390000e8105134190500340440280e400b80c50741408014451081c2c00d481c201e60142103d460040c80c40718030854584090f040c0d60050300030341c4150061141e180c00720700000305543e60019526041151210f810000d0300c0c01140b500011800d412498401c540030b5520482c000c240d424110340d40c0d80304070b07155404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 786669541 1250 786668291 786668303
    0x8100e01060e07030e010f020f0d0c02120a18050f060f03220302061e131104020702040606080f060402030c0f03071403010906030b09150103020909010b090c072906010309 75
    0x7802c2d032840300c100d4000e020030b98000c2140c0644904003400c0d100180700381c0304681c1c0304000032191071213020201c1d50104912032010590721403401044c0e04010301900b100454210020f01412030580c0100c50209140d00321240e070300c0382030b00c8005014914190a0700c1c41e0300817008001003201115204040c6a00c200a07102402000c0d8107100b081c1d072044d10030340044015910000c180507092100a60404089110340c0c101180c81c900780e032105420440000010300302c5030114881140310b86580d0100c66138690041c1041c09010790b5260014a403203403c849404401c0741c0071000c165a8079040c000c07203003c0e5108170f9080c2d0800c0c94015400030700d030b40094072920601044401d2142c0c1c0080c880007640c002c0440007400100b040c0703107040c010f80c000d07001801c0141c1030f0003401d9403400415101d00e855055035010344034801217550384802e0703500500802c040e40394400020b4040041d0314540d100180f25203885103042c0040014001580403843c00c00d200c0c1101784102040003e00f40303521903400320489038011b003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 786670791 1250 786669541 786669551
    0xa03020d0f0c050a0813020a09020c0105150619021504111c110f1804050c01030b0d0803070507080d02040b07140316080d15180605150406120b09070215070908100e01 73
    0x150001c8c02a8101b45c0c819480c060b000302e08060020700030305c1156400341615400010708110031002842c94843e903016400c410034042c0800005c20b20820810b90003c84c019041903243c04c160a00e440303803240d2402ea031440f92003205400310103414054601880198041031a10b55101d17070008000044214619054121030003801406034030702d4001459003d90b00603005080c010b00d1820004080d10741c659111401040402c032074000080d5041c04031399010320389160003504e41225103008907c602c00d81d103007440c04500125010611000002c02416594400c0c0880445400040c0300d10741c40340249807403075044a004a1030318020a003c14000e00c0340c3c224080c40011382d91003041c5610034001c00c0341c205a80010312503c103200044d0040c424a40585022100009103410104030000030340700f0350192404200149a14420749a0541c0040c810394000a00c0c0300500e10745000d00964a0179201d070072000040014021810380c5016002180c142e07161074020300142c0c42959424800342c1010b249041c050342d612 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 786672041 1250 786670791 786670793
    0x20607111905031b01170702070f06020f010c080c1605101415030610120609060f09020109050f03071710050c03041b0e04060902010e060a03020d0f0c050a0813 70
    0x1100103032400c0e100004101c038086040c01c00780b510b40b1901040050599403120204681a0707042160722034401e0000041d01200e03135a1400c12428880f450344100030400c01c044002c505030b40c0105c0d041c171180d14034600130000441d10200c1140c020b8000d0768603a001c4201000301c41000c944406020074a24002c10455040220311b140c140200d0f0300c001c60301e0350024644410f202440e981100b03405c000e407004800074591400c041401d402c0c0410203100f82445e0148a50160042007229001440042d82099041207d188003106000280583c444203c2c00101c0300b9401196500c1c05d80700702c50115502800070900e95080141d103000071a0342c100e8203200c038415014501e4040c01d081c0111840780d50b9440c0843d80b60300306440c2401111007005034441101380c214806008c0790021403001c55210780c0011010410200500040ea03406800221464200750000384c4894155003680061002800744c030020400003003115900341c01c0748c8008940d4400180100b00c81c500c01886032914030f4018488070300400c2e40d6085 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 786673291 1250 786672041 786672049
    0x50609010e0a0e270c030606120c1003050108190809130b060307051e041508280e0f0c030703020f030f0a12080718260a050a060b010f0c02060711 64
    0x42207130310101a1035540c0801d10a50620328151421655040c000c2020943ca0f00000ba12000000c0c9842e00074600307418001c29001042200c4400480003406801c0045510078000300540000d001e904414841d40c81071206605412196071081c0d60003501483c01c016410040000750b0b440a90703500102d540720501030000356540c00c019130181000c1e4403a00e80e50004103082d04030300c0e4030780c02130195180c4041c4020000c2c04441210450200c03154038000321542c1d503600400791070400010200d0003220702c1d00b030282c040424a07031010120782d4490003120180790030000d21a503110079455820741c05400585040005050035175014900150041c00d0fa02d1026441e1070040c64040900001c0e511065092089a8096000004a50044503a01d801120303909030301640c10b030259191149030311040e0034500540200003001c0300200c00002c80300564041e94240d040541d80d8440200c015a0968a0000495281e41c003c80c0e58100078000703034803282c12141c0c482d02041704c0c61300b0a003400d5440c107500c10915036050f55 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 786674541 1250 786673291 786673319
    0x50601030225020f010c05070605030c070f30050921030c160506090618040f18140102040807092301270c0c14070f081b010504050609010e0a 62
    0x210401e00c102c402d010741c1c010072418140d40c1328194140619400101c0200340c000c43d2040c152102814410364030340700d03200481c2d00f51190140140084c428920040100f15011002426004000d83c0b203120480c610090380140c03900c0d940801021a204000401d014140b008501910446961030203c1c0000228001803c5510100100e80260402460310b500318054000003070141c102940e0850401d203007000454158890142141084031203100c00b0f40d084d640f260403038140c80324101e4091003426807030003030090481c4048004481100f080d215205031001d0501c20340c4e00302c0c1c02d100700030b02445203002150710003812821803a014400b5500703481c0394014650822039008221544c01e011007040c100d41c120704014103441e0a40000c0707040c1509210007607801409201615000070f0729020b01c40425480764a0840c042d030210006a1400000007100100403803440c0c1026042e40c0e07142d0104080c180110703000c1c802c1e07005165000d141800064680c2d48100010115404041e2a1a030f00d9030b210b1070f04414804d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 786675791 1250 786674541 786674587
    0x40b0a0b0c0f010501060509090a0b0f100e0301050906040b01030201080c0c030f0403021003050714160c03231504080705010b130e010b010219021c061b1116090506010302 75
    0x1034014150002c0e00d01007446110f0041100d0700e001e904000014000558007a809028001065220320461815545901c801104400c0080c00700401d0302070200c01418000c0081c002510032b51902000031040540072841921881d8001c00c4040640c0c2140c3c01540c4198000e00040c04520060205204401080000b0084100100140b035241c7d4918410041c4608141c0b4480082504100621215540082401c0c0740741400c0d194803a00d4499500d02855403500003000030f00011b00301035002092155a010591302c144008400e8441000304061880d0383e0004000348840200841c00003a021a0b0f503540506401885140040b669140a400007803d4020068550100543e00d480451415000b485070001c0301da020b0010340207142c100c4074004007182402002030302451502c107480c400001405440b40080c0d038000c0f02005017403042c4d4014141e030254150444042400e103610b6100b01480001c40c001c244510752140149070b03050140c15800b4106c0078040324141a02441841051010016408103103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 786677041 1250 786675791 786675793
    0xf080c0c0901090c1409031204091a030607020c010f0e0d05060105270406090203070b040303090e060a0e180718050405070501031104060807020a0206030a0207110f0a05040b0a0b0c 79
    0x36000081040780d203810382c48124402d01d00f414510503150400e5140146400c1441a10740f54000c5002290500401ca400c5800d6040c001502161015242d800355014980b0744428240b0401d2500034036580d00010b03222200540d1114216185c2580b01741c03442004019645000039a00003510b001c40c540314a070f08401c58550b0010710042c0400e044c15200c18441c10b401e055051851400c84441c808502d03405800a80603580713601c803100554030200481001040b5520f4203d0b61a0f40e81c1c10010801c5c01a401000c60414080011503e02c0c90403900d0031058a00e401020300183e110045680383c071050b512403180d058042d5800c0000d1860560490714081031902401007040c0c6450703c0d1141c10940c0340c0c2c00c038070706162510443d0040d42c0041d07803c0d20240e444900300085580c64041044e80382541580e030080d4070003400002c0103602c10640e00071b0031040f40301d0700b030342030600032854100701501e52690f4007140c01c00c000c0e070702c00c0001b40780c030343c11000c800180a815207105036250516400340e9441501e4494803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 786678291 1250 786677041 786677053
    0x10090c050304050607020105011203081e0f090706050f0d020903070e070215011d16030b030d050d0b010f0813060207140106050a120503030c030a020c250f051c0f080c 73
    0x6010050051301c3d8030581510003003100c1e606210f880f50350388016840140801c10391200203521200c10241800c400028250724124504e01442007401444088646401c94081e441c0001641e9000d03409460148901e21007140c1007241007850b00d8001c4d00002001360b4148101100050402d02c2c500300d0303071b025110300d038050101d444039410341c0b400503030b010fa0095142c2c00042c80c07860b40014505050541050914140c10710b45050030001700d002e4030400341c070300d81c0c14016030820303c88140e0440c00400f2150085d40f030034001c009108005440b880310413002000861611000141580d2102010b800050710800b070040c144203c0341c450881700006203901d02000d80d56080300384994501103a1700b40041ca80d80c107540800e070803983c0c1c41c603850340006001c581e1070705804000300d480f0403d9034040d1030f802031140c400c58241c601801c0c3c82519a40c060f0528460244007000d0104050b2141c0740c03074006407100500041c0d500000c03d040001415100d2a040c2d0f026a044020480000c4003080148034180c1c883c8000d0007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 786679541 1250 786678291 786678293
    0x120503041404150b1803061006050f120c09100813031407150209031903050d4206021b060304111c1e02030a020123040b1801210510090c050304 63
    0x5000045c580c00240b080d44203030104003602088420b0309003500c94525059813a0140ba044991442c000c18031a22526820a010801c00d520b198000e884a03c00840b40841d6081d030b946025114110140c92282c0403491440340940481c0c0905405801900b0300794686141290645840b4030582c181c080c8811641d4000520301040d2a0400c41800c046411040070b40d070101e895540034004d407241e25868142241c444800703460001071000340c003d2200d03e02c06541030300e541840089024040c8940003054008903c1e10204425200050000e2042c0a2880303401c811195141048016007000b082190010b90802000d500d580b990740540c401c5000340030000322a44006d01c1c002c8a01111080039580b0403000c3c40d4440c01690740020480d603029020308051070801c12103c41600d4120310442100400980081d0005600100308002d1240c0940710a03800f03a805001001103440107540300d40070b0b8000c4105002c1c0e403086201d6a000300d405c085140b50070511035964400200556140f00c5480c40490000f0007000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 786680791 1250 786679541 786679567
    0x6080c030705030706051b07030f0b0f090705060702010c080903030a020a050d020a0305031906051f02010e03032e03050a0c090b0916030b010c0b011e120503041404150b 74
    0xd4090b000c1200984211070078880002c0c800c0c01181031810300e09658100340b0a85c00d40601000d005540c000c2a1031490b4101c504120451000c02e03200c03490040c11410010f46994401b1420b00c00b9542c0003003070545806000e40044a03020502202680d07140d4003006400400d55040000f040307032550340e8000c4c0011030303083d080c02400c00000c07071002c1003950400e14000740000d6004088079802900301101602480340b00c1180c4005004542000e80c0203501d0107290402c03002c000310a000c0602d900d80c001e204503801c0d0b0240c15180d0105940000c15440220701d0959051a0040104400c400f0101205610343d6a500d40600c0c0108148060302e81d80e1082100340b000c4441c0d409000610102641c0245507806d01514807450303440030a52100825588900d0100d00c1d130b21910b52851041d8004a05045658590314040445031a52001c81084404c2840003d003404103800b0a041c1a81c010000c0d41c03e003442c001c01d0308a200900003030640d01a60b41d80c5000f405040a00122014040c0c0c1c2c11810740b10b000f14000381d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 786682041 1250 786680791 786680803
    0x311010b0f0d060213080f16080c120a052e0e0d0c0203120304030801090b0603070c030813023f0a1113020d0b0a050103060803091003060e07030207061803020d080403050d06080c03 79
    0x15001994540d030007802790f0383d000140501174000503940260310009607000c640c200013240b440186907014114103e5040d1802d41b80e80648803c0406101a0082d8202d080b0011180740440da0f91041c1c00229140881901840c4c1c1c400301c1d18005005d80c0c1002c1c03015180c2d0307040c41d030007201d040340030604410050110642d18441c080680c2d100343c1e5441c0c610308044034041c04801588600800304010314001400701d02c0107178080c1280395406400d000280130300070f00c00c5407048084481a10381801d4016034050302d5910b03403100c00d01e006091004e010320114a481d0080050060003520f60003440300390500892510502c014004042d440600084001000b03041119000e01035000030304050402c802407106000100844400c190b08030352401200c0040401038014123210703072104c001d107100e241c100400550190000c0c1010340c8111307006c01118505068040c40283c10f40009001640400f01c2c000c012402010704030f80250003410164200b060000c0100150b50103030300001800d410200700d02005060030050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 786683291 1250 786682041 786682063
    0xc060305090303160e030d0507060506030d0c080c01021b03090f120706030f110c070602150115050702040f0218090901020a0503061504090f090311010b0f0d060213080f 74
    0x60006003803001e085662400090540c013040310a0305903100044e0700136091060009030181c1603c1311402850001b07041900440c00c15545a4203010010703e25250101d2000d100920b651600000c41c01652556042d83e0840c082c02001990308000da01c2c86064606102c50032811200300840e81e5403540d6080c08400340f8020209030103441c0486480c1c11513000800c1c0c40098419900d40000c200032904102c402601504400c0d4a19070740c000f41202c164140498a80c050341c40c590200e48081c12080a08412100c0910030984000c20100300c3c040500e210704d00900d10b880c0018000304038080c0749629201280d0001a1a1140f0180d40c0d5842d0b0701410443c2c181940040700c007008504100d060200a0b250b4031008000501c908941900b20042d41c07140004c2d0f80260000c3c800c1044042681d82c503c1c0d008140118094001c112500c0341c200844a05004071040d80348050240040418020148881c081c200081214031907000d12420b06902aa281410000c0c89801d005200941210f02c00d135041010500c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 786684541 1250 786683291 786683297
    0x1a0a0509040603150e0c062514030a02190f0b0403030f0e0c0411090307061b120306180903020a060c0504170607030b06070b0412051c0b10020f070308030919030c0c06 73
    0x106c8084140c5d900800c1d00d605030306884256003406003d401d516005c07102c03c400205417503000d5400440e0709070300001404503980c2c19000c50360307024404207000c070703024010381d800801e1a4010b2400307000240e020b01415403c0f6100742008921341b000190584195107869441c0c1860394400440d1211601d010302410401c6020014014548030160b40841d4488819020303500c00d014000c000b04000c2c07590307207219100030342d00200c840e11b40c1c0a004a0050180009100c0d40d4040020440c0c41d11240e15284030307118909906070010f14100b07465540d9103000c1c09814007034000b84142400001440c07a03150506074003900002b806000d03645420314024045403048107003140914024400d031070016a445c001c440d08990000820401c0807008403085460f40b1450252890a20401b60040c078682c4054200c815120000c50f0502144106017000f240d48040100b1008100d80c071110b810408030700440000c50700581100103854803400303500181404030441d400e04500141c0007035010f2052150200c0c00074041e103640c1c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 786685791 1250 786684541 786684553
    0xc2715090c04060503011a0f031905010605090d060f110a0305010e18100b0609040c0309050c22050405011b091e0e0c030703151e09061a0a0509040603150e 68
    0x5009089000501490059820b607041031f0f00c0121402c0144e410070302840401503941d1800b05400d0840d1b4143d0504480403034240000411200e009900b5100f090f90082d04000c1c00700711607101c04000c0c0060b8044501c1551b5122010340c80e1510000042c0780e1195030703440c0490954504040c6c001c01c6c1c44010005100d03220990312140c0d0210f404100700740300d001c0c0c0030004038640e0b0265002810620848001c07a074420b1400c41504516500340e0008108070703000c1d0081da0850746050051040705240381c640a180210701685454000480f50302c419041405000001a4125003035802074208003201410b0001c9107c3d0304003041607203c104900c0c2102c000c2d030003886882502d40b00c06018490030142644940e9072003c00021000f51290784880400310500d145045500c0e41c0381c13044094007220402a81540c08000e00118280c003490065104803065000d00c80240e180004038580c641e04410181d80801000300817041650b5191300074007001e9400789204c1e481490058082c8012035820480410150b0080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 786687041 1250 786685791 786685799
    0x31806090d02031b1204180506040504020105030a110910081006050c07050d240203060f030f061501111015050f151c0204080109230c2715090c04 64
    0x4010345000c10070208400c8130000703030514118240403002240086024020800007083e102840105031440405a41040a500c4240520003501d41c00c4a000c0c2c0801d03000c00c003003156408558041c924501e00101a54140303800140000c1042162524400c0060340c100b06010034030b0203c041c00401441d15050891070284c00101d01a121a56407254512850758588403800b03120700360303240384500d01c210040044005129202c0c40700a400c20707541240640000340b400d00c1c16040000701e541032145010010444d544d2280c950a002d0398107156400d040081d100350681420600308200324039180880804148080c101308032242744101640660310410a940c038240d15030b1141c40e60a086078800041c41955000010300c5410b41d280c43c803071401c255500c006000a40c44070117512424034684611fa800f40e03200030140317901141d500c4410203110f0540048a0607103251500c0100814500f0704418035095414080703030740352a80c803000c070b40d42e01026001c43c20810300c034944007a5403503000325001a114245810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 786688291 1250 786687041 786687043
    0x131e05060f040b0c0a051b060a0c030b030303220209070c05191218080703050a150203010509182d0d05031323031c050109140403081b031806090d02 65
    0x101134030064140070300152411400b403284d01107036800550401c1c000c440380c0c2000304e1300d81e4a01d821500000303034a01d401138020220f44a8010703200c40440c003c005500f551035110740ca00070705030145c1d00220b42c5c1003003400420058a64181c458450078464a8103185c1440a09049080170000c88450200400000030311000406081c500301019202e40385c1141c0f4078410340324411281c60690040a054071840200004200c2d0028914100c28271aa0040e600b40c9140d032205d0081e40405c1c06800c1d0701201e12800100c0c1c03416000c00701507075003010310b088882036002d130307030000002d0340b0607134030215124500d000c6c8605607503402c1080c206902e0f40307480c000703242d45080000790240311200000107117880e0b0b1046650181450b64030720204800614419a42d4604906580d440b01c0e001440c442c503004c0c0d0400c000040e040c3c3e0b103072003101d0039200c41010310002e5595558080b607a014000b410a5000041c6640e60a141080e60b8080e51080c860381540001070020560114603000009114a03841e50021145a2800303138 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 786689541 1250 786688291 786688313
    0x1112011203020c092a1603140403060501060306080c10320a111515210a060b04060504061d0c0d09061d060717131e05060f04 55
    0x45004146503503038045180890a103441c442015078007a605500f406024000070b8840200401c0220701d40030012030841c24205c40b07000b24000715031442c855107400400b184c02a0b40828074506207900082c03070292a5076860b42151420b0308500c00090f80d40009103c1818200603400c2c080ca4121181b101c4ca00d03091500800c440070840100800c1ca918000e107058104a8130b965450002843e01125100c500300348000b0300f80d03460f40b507891a05128840d240103020042c0c1c800f05016001d0780c1e00515015100009004034500c2d11002a00c1d1650400712080303100c0b200744917100400c0d02c54000842d2102005040009071251500010b115900e000401c100c220b8517201800030761000b2150284159580c4080c1250074003030074030007503201030906030b444080209541c04446082c4d0b0180c81d440c02e4248000300c041e5100340840b00c40d8007280004842104c900f107444803640d40011000240001c43d10f480d41d60381c2030709a50b080c80122440701c2490200400c8000e011007036001c0310341894a400c600c1c050300d800780510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 786690647 1106 786689541 786689549
    0x515090c0a030f1d120c12130815060a05040209030601230a060806090c030105060703030b06040503031303022b0b090a02090705071407060e01030506280603111201 72
    0x955010242c40790020b1b900c0041c482c3c2c1d0030b4841c40e03030b81d50703440250401940961078000180c044d03401c00035010f5902003500201940d040c10410301c40ca070542500402e2155005012009003170302c001234081d0444010f103025851070721146250311500001e000309690003102d4040c000c80c51a4201c6480c40c002e18046d01e101c0742940d2000d0500406000038083c40b94407020411852000c05c1c403030303040304840c00c2c0000d101a103015601d50002e495580411540034900d10070311400c1065141590601c1c2182c0b00c8078015900701c0145021000d0034212110009004114400210750070140402132901c180354060103412a501b08007078054900d40142d038007100c010308850b88404540001080d250100e8203e81c0b100344104000800540c05081e004002c2e82e00003600c00251070805092032140b0000e421103550100301d00d4100b040042c1a03e49030b00140560b030804004000443c081b685001d4115 = true := by decide +kernel

theorem cover : BRFrame.Cov 786510791 786690647 := by
  have h0 := BRFrame.cov_init 786510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 786510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 786510791 ≤ n) (h2 : n < 786690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
