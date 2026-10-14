-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2481
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:50:10.559169+00:00
-- url     : https://prove2.me/submissions/5c30ea5f-f745-4d80-a3c4-aa9d1e41c44b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 446043165 ≤ n < 446223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 446044415 1250 446043165 446043179
    0xf04060501060e210102160b0610050c1f0e011803020c0402210402150a0201140c040605030402040506060405033a0801062a0809150418180807030801 66
    0x508160040401c105041159109680354051400f41a1034040c913400f841d1512140410f0080c040c01c9000d4034401305200045d002e01c180c2200c454062902568010b0b05401948030a031000d1248160011684c0d00001c41d1404111301000b01d00d6034a08419804500c07228200b13130321802d4070386580034a101d48014800c9001010340400c80e4076880d1400f0f640030b50411010406140510400b04a5517100804540000d82159544000341c0701900720490159110711200a000780201004450404814607210110703044440d20760646d4100c40081d17481a25555480c1c0c00c2c80302520001d0b110a400490901012034140e406200c004100c0c0480e041e9a440d07019610120141804524404888045040001822075601c034a9950646602e030420320102d0a1400320401000501d82040f0f01038440c8440c00c408004190300105031090044034491000d8801800040e2244110700c03038039100c10351905500903046441d40049005021010600345031150546403110707143c0c0503000440c0043c0308034006001c03407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 446045665 1250 446044415 446044421
    0x40f080c0d030b120d2f03040f090603020a051309170c010f09030c02090403091a0a0e0a150e1207060f0908011107080705031b0c010908011104030204021308060f0406 73
    0x43c140845002503845240800152075900c40d850f000201b000c84104000e41e526a000703851440c54062500a18100a01c01e0342ca4070b07038001d40140113595182c071800007141e5584d40039800075641c008148031802864003082214010070382c0c07500182c107522400c441012580181c0030f43c484145541c2d00c59510100e824886084428504201c4141440d10402c240880e070700910800c201a41510421421344441c02c01360384810180e40200101c00b41821841c46680409020f8054a40342d078032040a8809407804201031189035004488005000a45540000d84a080c400c00500000741c01c0032200741880c09010b051407455005103004c83c1c4004290049580e0220700c500c0202310080003086002c01d800e1044407244100d403000b424010000c5044006c1c03010038012240310f40e54507a0302007840201e110300c00da126180712400c81e001c100c4020000440060602441d403080184800252400d41150b01f040002e400074100007540035043e03180807070310b2103041005030b01600c04041e80140703514251030900c003070b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 446046915 1250 446045665 446045681
    0xa120e01020c04060e0a05190e010c0813030806010f0905030a0b01031a04120e010509100806010f1403011e050901090f06050d02010c260d0603110301060f06030203040f080c0d03 78
    0xc3e91802c141005074030f50403402550003001400c4003150740c0e100c0220900010760703282c0760801c005280800f40d0b40890b405611100e10302c00191585071b038540c1c5102c0c500400d608503400180c0490b004500140e80d640c460321002d040041241000031440b9180d80c082032405041c40000c0302c01c014988014424410000b4501c090500419100d000c2490f05035119000c2004500c0c41e00144404540100807583c040c8082e20380c50007000c0c3c003092201c5d04144000f803d9003000e5403800c2c04a20620602842c19200d0700c03d64500140000003985036900e0041ca2032401f108004c889150102100fa010a0380d0703403401101c40c002c00d400074002c9202150400707104100c072400e600c882d00c10180d2209000040c0d8020500300c5c0038980105e040d14103000300750078003000c1078071000800060007000100300814107829441601924042d0b503001103919a501c0c240740c221140c6000f0034000446510082100c180710303400465016100e40040c1c0c41410300e0f40d540380309a070864a1031404030703046520000b54441d41440ba03128 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 446048165 1250 446046915 446046919
    0xf0c0301020f18010909051608060a060e091e01060c0c05180402060702040b060c010e010f06060818010b04060b180a0605090d05031b03070b10030503040e090a120e01020c 75
    0x1c0b42060038103554400d88a0061000d515000e411486041030380140d100a0040040d8501408107240c21017401d010603040030104404101007802040311802d100c6610001c1c0d60160315004240b11a00c070400c4003d100041c40b14400301302400d2101042405580880d00038152615020b12150407450024031070000c980019014016050f210341581148507200c68000c1e8040e550245e8601c83c600204000e0504410510303040540003c03418980081580615048124100200004d1741500d860009072038145c403840000a2840003c101c41d04540c3c000c2001603003818000080364022003010405aa41c04d50116208080c041903070142045444401c1c2400300d801c03101e4504850a00d00064410b000b01e1042c1405901d13954111b20030000c0400444203450215440c0064944094419a0303a960144da022207a0841d00804030308d100e130f0b0100c550415a83e100c40958181410f09105c4000744c18000c1459815110f010b401c0008a49240c3d07801d0300620555982d0000c4030400800a480c00d03241c081001c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 446049415 1250 446048165 446048167
    0x1080d020a0b0105040903020a050d080604060e0f070e0102071a0406030e0606030706050c0a02060d020315030a2a0e040606060306050f03150a1122091b030c021e0f0c030102 76
    0x40020030812155044d11021240000c101041741000c80c0f5124140800401354440d60355941000c0380c00a008500c516400c6906202d02c5484600e0056003000075200440501032050104501034040c042c505001d140c10301c11202055542c2e080c110383c200d4559000914004001000d104059050180200e001c59000c0200031604100b0040b0380e4403030300f903c901c00810030042158410580e06000c2e40aa2a4000b0300458a513081694218025072090300c9100010408018500c51411701082000e5095007082c04095402c80c100c2c0500019090011211200f900c0e5040205030441c051880754002e030b0007004001501030800b4000b07000c607101e40d0130152007115950110031403a64001090460010500421050381d145c201d00f843c040c28902040c000345090104d0212074503040d2451080902549807803110656136a010600c040715051032170b42c04240381032802c2d4000c90b0b001c0d8010a00f8601e1510443d440400148541081c07142c114100302281c0d04a102600c821050408c00c007065101c08900031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 446050665 1250 446049415 446049433
    0x70f05070809061926043f090f050d031d03070f0602010504050d080105031e03311e050d030c0b1503160e0103031d1c0201032921010c0801080d02 64
    0x14039403119003040e140c1030075840780000c401a21190079103024000c80d131240b0007400d440414015046e023041d80642c20410f07003c08400141c510340004041280ba0301511242e510081020f00840e8500401540b1505441405030005401c3c40c0c4c0b0308244000c0c83d0300d90001805040c07602c1c4c0310f030a10303840162400400901d640140901d43d408600d03041d400b80e020103a21203510ad01d0740c20303a0543c040e02c180a580b0014903111002003909041d045200c05510358004039005403104803001c00041c1c402c0150b10352611021051060342881e02c1031504190090900d0003400d200ba41d50200d05500864144003182000c03801c1455a003010003403414210704041ca605126030400340303030050083d014400a020072401080c41c5128031a414100c0c410402d001e0728107903442e034110b26a5a003050300c003041280000d141c5070040c048a40c00c80007018231030818515004491318504200521440d007501d41c9448142e40c0d107030811050740240704040d84030400c4d4543c8080c030f614091149040600010440c0295003060f07540c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 446051915 1250 446050665 446050673
    0x12251203090209090d0813030c0c080601030c0605030c030103020d08070605040311100506030d0309020111060907031e0c03060c030b090a06050f03060c030106081810060806070f0507080906192604 86
    0x3174603480b0f40f580c6007d0b030440055040489148e000048064039001000c1000b0600800114a0605a0780a8070302070704100d90f2030304221102c1c07200b11591a0f00300400d0005200518080710a00e0103d4080e41040b0b08000d425140c0c0011644143c40c21800300e08101c40f50076503198144907903210480000c2c0100100d00e020300109031248042c014240815968454030811607000d05d089001006201080f10003510f03085000c155a800c0a00050741c0d00c85200c0e10b240048403604411424850344400c14400c02031860784c404000d00b03d0b515041c000c0c1611500649901e0302c8041c036440c426007820002050841c600820700210f0701c0407043e000e00980082040040c1101650101c0303046541c3c80c9801c2c144c0c0e0382d0344144251213100d5039444d01c0071070162604a09030031031503801c0744090b5045002941d10b252921442074580504004035031012400601101c2c000c91914030180c401500080c0c011407406002c111038850298001003030001042c403c3d444812151003000c402211320311207215490090030a138913 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 446053165 1250 446051915 446051927
    0x6090c0103020c19020420030702100606050a0807020f250b0a05180a090515010e06090a03032312040605010b0306130b030a1509110312251203090209090d 68
    0x41e8a1300b0403008840040c210f407160303480f40500880c0c00c5e50000340c00080b0b03038046e02d06906c02e03541c03c00107201e80d081036400b0850342e01c0b49000300c0c0d00c20f8a80c03e1800c03249503400e81300918001e040380b095000701f0038a4103028000344406000c0c0684112301504408540804014629164008401f5035409001607054107402204072030b181890f24604403001c010742000602c030003049230003400403542803078184110b8a00b01165420141d0003600c802c3c4144401c01c040c05000e0180d120415404003581d4401c101003405140460211007104200e41010300000780018466800400e0060895110804010a004840c810207014240d6241c440e440c2d410900000f41c120740f1070b0086100c4a0341d49180340c4030250381c208403801e0907581c0b1240c000c61000024880400030003c110080d286501c019070060881c0ca00401d0311541403509090840c2080440182000b000741c00c20000300c41000790355485070210719100407540c090343c480ea60202d1503085a1050246030180031301400300725407285c05070b145043d81140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 446054415 1250 446053165 446053183
    0x2102130506160c1d0a0e0d0c0f0206070813060c02030d030f02160b16110a030309050703060e062202010903060203101a040608070203040e0408032706090c0103020c 72
    0x40700a52541019044036002e0342960100070084a60f48400044142d07404250081101080070260741c0350b03071409000c0c402c4c0ca4069002c5041078000e105071140c80ca000302501c0c03500c980030321100303800b908059000ca00c1640c402c031070640301c0c10700110b01c492820b003030700c0c0001c0301600003450590784d000c40f264046a07540d000c24201f407080c1a2290b1034aa071a4045a043c3c80049050840c1c1042204403828081c0d61410255140381106803485c1801191134054040f61044450032002800500050f031011030091500c0481180e4a01a5001c00400b00d02180075034444c0d01c0805d000b030402400e00c810f000c10a41c0401203d08680864a4101e0340983c3e0020b0309081100c0c0c00c15009680c030341d1142c00301201c40840b604120f00603900e0440a0300c1880c402c0018209550b03840e1a0a52140c440c140b060360f40e8082c2e0700ca03d11941d000103000500240e00c002c09181c20000c83d80c921f0310400c3c565402000b07586601600a191076200004008040004000d1020300c8207081c20f04603d00490304000940310480070f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 446055665 1250 446054415 446054419
    0x1090e060d080c1006060206100b16021815010f111f18030e0907090f030807080904050a050f010501081902070503070b0108031c020a08010e0a0b1021021305 69
    0x440720144640031044a40074030601c800c1e11104083c2d404100020002d41c06200c0051240b200020001c00c2140d800340d003a12054040a810a161748601c60b282d0181400101d0700100103560001d04000000c00c0d031b5000303110801c8140907541201000400910851900d982007000c03d14030116908804900e0101011240d00c280351202d1038a15403501405003e212207044100b4801c03540700b030503804034030750b441c10104440c4912183c4070361500322440c4109004203ca00031214604000142c240c030001c02000c0d02c1049000d040031036500000d002c0354000c50f0403070007036070b1104d007088000c48507042c002d40500b10909041d01a4200010344903056052190707807130405c950018080c07003070140c07c100307a588543c0d2281c2c1e0f070704440d03031900c8045849801c2004401441d100030a0380c80e0000d510350090741c0c00c503d01642c1d020016882c00c54070144419028040709103030350351020150324075180c4a94801400c20b01c0c0c8ca0f041502d140e5404000e880000308a040880c0c1441400207042801855000904503442 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 446056915 1250 446055665 446055679
    0x30c0e0f0c030714070c03050f010c0e0301020301060e1e0d0b0603010e0d08070c0804030c030c05090a110a03020304030302070f051b0d02091602070801050a091403070b040201031a0414040b0601090e06 88
    0x21910300401b505400b42c10241891082e50141c00302c101054100014000046d624810860f400c641410700740c0c0000e024000114907210354160f000d0a01c40303046900804050368486008401d400440e00d0590170b00c400380d401d00b07105020807001d0300b024019404040780b80130040c991410500b800510b00e03440a0035910400c001075414109005d101000d50b000765401c0081020716a54174940305200100703a104440c09000210b000402c0000c0c80d2090100100c0b14907079491411011704ca04500035440100201d003816401e00500000c5080c4039101c1404920980080402e0f071083c80c0d80f840154602101d21b4421017041c640280142c0328811f509400459250215410082e40441641440300c1504542010f600c1c2c9820080c542c05690400c0b081c003401681001c03175074445041420b840c1c3c405c0f1103000d8400e0000d58007003001035209500c5040038441407400c0b4490500d00800117016501c2190412031800c0501003400203100f03100b20f100f9002882401c2040780149408280922014002d020700c1c82010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 446058165 1250 446056915 446056927
    0x3080c030703061a0c010e0a0b01060810090c02010b040b0402160b0406090206160309050105041d07031b050318070602071a0d0c0206100b0a020a140106030c0e0f0c030714 75
    0x40680c2025001c0c08003801a120024500003e110007a040030f0415005582848080041e0007804152231032115044503064501d6070810303030241d44403403018220b503c440d40801b1000a2200743c500c18040315002550002c940d0704e14903410001030f1040354240302c0c400d910401c0451000780850050101e0194480400d14043da664203000004000d007905c0070b900468002804145800c000307001c015001d101ba01c3e2103403040d81b1440110390354010b0340038100f030f000080c07803882c0b803500031034104254402661318001c50000d444074a0401344c20030741d14480700812408803d10401032403450340c03039000c4041c0d54014140701d464040000d40d1480144500c2c2c071180003500102c0302d854200c3d811949100369001091240044104000307603a00412900d03d810440c0c42d40d00842c4c1201b1000c11210444019802401c8048841c2c0318040c5401500711002c3c0c0c10740d40c460b000800551041842d0300101340c109104031107443c1c03640c00400351140c01020300119803020010880c65940004201c1290804008040d483e00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 446059415 1250 446058165 446058167
    0x50405031b0f10020f0c0f031f0b19060809011b08100b0c010209090124120204050a0e09010c02011406060c10060f15050307050a050903010f090524041101030c0219200d03080c0307 79
    0x4ad449030440d40008181e034056001643c46103584040b40c109569a03c1180d0f1484001c0d422200c0209540b0136049540c02c1c01701c2003520400089030000d80b0500d0b810591661010f154001341e20080d407007840c070b0b5004a9170f14154500800c0c51401441524001c000001450050410b60190182400309020702038501104d1411a9815103001d02006003213005159152002ca0742e54503030445a06030158244990f80240700d02c103004000440620000b010801e4507841c0801c0180d801c211103998062041c0c8006a8100e038a60040000a01d0001131502c05036050194200600c034640d000101441b47c2002801582a0b000044585c03600551424585031100c100c0040d01406d94107151105a40c00c00101740180440491200e845422400b140c0b01c0d40410491445a910707011a0081c10100303009940e46002e50081c1c20440701d81c0c0c0d8510548070410041000668012807003101070f0380c02d80b00040c0d0311900881000e0720000540080f200ba9004c0c401030369004003000c000a1985810040100c081071600d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 446060665 1250 446059415 446059421
    0x140a180e07090f320c0d090b010e06010f050a02060606070303180c052805060a0203040f151403010509130606080a0b16050405031b0f10020f0c0f031f 66
    0xa030010903003d0003522003203141d0001920707144407000c103158040a6a600d600009400e0070b0701d03824034140c501c002035070745050481064020f0444e0100e89500c8040650003e0000d610f01d42c040c00525a03114000d040000006208200c1201d0400a000040007221001500010a5640a00c08680d6160365280f1494110b004c0c00d108198100c0b0080d21902c510708001103080c000041da0300c183c84840c0c102640040310581c100c51030100b922100a40f440c24401c6040420060000c0d0445004803407401e43d80341179844c4000303a40c0e40148a18076800e8041442c0550000015414160440c3c1440c00d650600c00020600f240c050103816801920000349400c011080d0440b0004000308020f03240700f00d140b4103210042c0c500417101c0740e101c1d1040494450b64035001e030040d24180d0328090020201c115540801140150821080301c0e4482c001c20800140c0343e662290070038007008103038068803a0040000d0507618240070070030442d1048100d140900026180003e00d14040c0131000c501e400e0b01c5401203035480c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 446061915 1250 446060665 446060669
    0x90f06060d110309011506050405012a080a0f0315051017010b090310060806010e0405010f0609020c010b040c0f050a030f0504030c0b090114040809011b060501140a180e07 75
    0x51581008902e4242c0744003a40610f21400c8a58024000f401c1c107981e44c0c651100890090001041d002e000038000380d481122402c0c40e280005481c0d541250044060300747e202c000e08002c0740c9060000a10007010b903440308035100003c103e8201070000616403000c00152102d213008503070182d00a036021b0800b41e8428480e2000d007100c12119440656128000b07442c160b0b00c68684e20b402071103541c165407003d8045200301d83c22501154082c10345079003840310400c4000c4015000361225901c802220107a8400d40c4110303030060680300c071300580e40c40a60038018252040304000034800c0f4500700007840c115400203c1c010914105140407076841c0b410b90019070081014141d1603888515000810080541150340240c07214041c0030303113001e107544025005003a1907000c0c84d1701d0140c0840201140014a1041c082c04210030141403140c2029100c0040d40e0600080960903600c00b602c2d000100312a02d01801803a80c0d90320140d2f035407100c550074003503040c4280c210f080011001c640e690308c404010620138404000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 446063165 1250 446061915 446061937
    0xb0c03070c080106060207061412100b0c07090b040e06040201030b0a1205070915080a110a05091e07021912110304230603040210030506060921010605030309090f0606 73
    0x1c1081c1d21200102d000304014041d01d800361040c0d003008603400b03010b10340c410440e1408070402c0b490f00008007408003030b825001c0c00220581c0c2c458180405e000c07110601400200c21080020402949030000000555040c004000d002342d25100f40031840c110302054a6601c00d8083c2004281ea541c1c040c04950301140980c040000401401103100401101181106c211a0074210600002d5100e0b00000d442e0000791007544566481014442c0005d006c5980390800110b0041441d600750b5941c00104080032400c45d5071003400c80c1c010720382c00140e03400741881c41c1d0031402e140b004003e840e44108031441e032040400c0380640085e50706100c942d5074034810140403128210150540e42c4880c0e0740d080107840700c000e1800310035604082c0200701415081c07140035244915001804002d901c122588158024031f00909003540001d010000c5151076141c0d410b490141c404e40c00002400c4821038884642110185d40146200340c0040144030401e944014060303408c04081489900e040e2607606c002440b42c031856091074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 446064415 1250 446063165 446063183
    0x903020d20031b0105100503071701020d020301240f0906051303020a0b07063603030b030102040f0314010504032c030a0f020f0306010302030d030f0b030a050a1a0103020a0b0c0307 79
    0x800420300d18035603c00c01c18450000c1c02151109000c400080480d800745a42592040314100020300318040404414509035000619115020b400c16050380d04c240c0016501d00b5041025031034009a44030b401d08040c00320300c5d01800c43e0054800007003081c00c407440303020200000490707000e080b142c070600403c0083d9401080914a15a80c0c1095aa40e821001060301c400c0d152941c1d01400d06a6000ca003541210300701242611080c41c8a04500c1040324144d0a0b0205560349440c50102c1d10240b00600c042c0528048a5140b213103146800d280d400c486078154070041c1d0500d030034840041d410000d005504c0e000a00b01e003039498220130261f071030120b00d28491603140c4500544071007482031001e400800b0718000d881112a04412200741940d4810a00c4001d415a000b146101c51480c405d42c07084124101500c004101c40c000500040c0c078010008005840e4bc0d003281000340100f0071480440d406464407480a0400356142d9000981491980d104220f020701c00000d01120512050040b20001c0b41d02500074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 446065665 1250 446064415 446064427
    0x5091207080331060c1401090606060207080120070f0f1718090f06040b0307050a030c08150702030706150b03090703020f1c0204110c0a030f0807030903020d2003 71
    0x284400c4582c00890303044800d48030b0f0f000b0040d0107180612a080d226182c9070000c024100760703a003541000b100042200a5544d81454100044040c01440011b0000740d00403d800d500b880300c110b0854203c0301d03e24180304d442e1408129141003940603290390315000b00c81c030004c80510341400404d40c2240400200108040c41031038046183e00400b5010340c2c0c510b807002c1c0c142c07201140700f4400e03114010340f01a24600450f000003030741d515203070300311207440240501030399607840da80c030f000c1644403070399410032104030514020501898004111954829180c10071048850820305e4010b5124031480c200600060b80701e12065180c1c0c1c0c41900424000c2c58003a01480e52464150003464455003e400224401c07101c10424600b140382c1488100c0303a5070101c940000e583c0d000c039420000180050240010b1040c0140b0044014400074001c1c02c5076030f1b01a80764041c0c0da0203014001021228010001002e01d031402200700b0102c0c2c2c0c00500400308402c1402d01c0164180051801c800091a1000d00c0c0b11070f00c00080e003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 446066915 1250 446065665 446065687
    0x31b0c030307030f0501060e19050a080114092b090506030403030e0d03021e0d090204020c0a05120a120209150a02070306111e0d0e0d030c0e03010507050912070803 72
    0x1144102c080d0740d02004003044001a036802c0e00d40038810790700000c0c40140c17035401e249000602c0840000018011507080ca40c0e5502103401c030380b683d6200d0f55103030b5910101300e1024900508565880b038000b074003030031151000a032034860407030250504105190490120a142501580304a4050000100407039228074007490001c01605003c00c07021703000c0c014500a450913600038000d0b600721480d130864080707458000210105aa820100701c207542a500c1352081400340e15284020501c070020341c80907111624550400e1840c10080c03941c00b81491344108007180760386910601c3c1640c07000542d400541c1d62030500e0002115425100301802040e440041d0880129130000f541c401103d200d0b603022301c140601d60140c2c03034043c050766605c0704800b0081c1c0d004509000c07400008122102e502c00c0001090000203002524040040d4440c2000c20ba1303c001c034041d03460f0040e140d80c03011070045000344003910701040c00400d94000c03000500e025000a101e1030040c0c02080c82198081c12001d81100d803514941c01c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 446068165 1250 446066915 446066917
    0x908071203180e07050901090306051503060709050d030c0201110709051b04030203031206221a030c0d2003010f0f0c0908030f03310201020d02010b0d08031b0c03 71
    0x10440210341c90481242c5405100c46585044400b0003600100c2583e43c0751080c3c032158010700180b810041c1b601700110008500348603a03401112003090501c0306000600505141c280301400540c18042201010031042d581d0000c1101041e078546000c2c614000c052005a92109601641c4461405245000301c1e01c0315281d80080d20541c08562030031b0f07400d1014003150309540709e1800081c0d09038208002084105500300f050980141000d81494520a481c3c0d05410300f803244210381006c8a500c0d6080300b951409403c0c13a05560980440203880070510072000603030300c020448002440b00703660079051203001c5072918645001c0d4002400038040c00300f02e500d49900401c0880700c1c0000c9586030070522160341d4480c00b42801600c170024021441c0c5003e0880d01207054000900541d84480807100243d020b802400c803032104c204036401c500c04098007034800682454011040c0d0f400716850300c1c540f01d410380e40d5404a5102ea46d0082050b03607036910384030504c1403d1a590b101000140780001241411604008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 446069415 1250 446068165 446068199
    0x4030803130c050a030f120e0d0c14010503011d06030c130501050411070b0103060b0a170a031211090105090f040c0c110102060f0712090213020a0306080a02011e090807 74
    0x2c4518240c843d010409101d959000c040d000c6204100540c000504074600321100f4030a0703080108002e41000001040c9510245040b01c1980380300404011240d601d07643da003070345442401e0183c1158108041008141d8900c6518801c140301c900114045440500c282550544040c1030700300c2c66040804d44001a010a03c15503000d145055200e030200802101550b100c0f9030300c22030b0350900b41d185480d110042c001007154540d0101700340304002031124156050302060206600a4603090351941809803550345032812040c0c00700e0400b41f010303a440c01c003441181d880c0c2e13400342011500c80b426a004940c0507000c1e1040e440e0014909050605215080a0030504c003910458209103024000001240ca420342540d44005c1301c0940b501190940b4080c440214100d403103580c001404c1d150316000200b003910419601e00e91581d000480305001985805448064211a00104042442036000030034910112103030481c0000560721071806c07103108552600c02007584200b00c0384015258a0b001e941a0800703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 446070665 1250 446069415 446069423
    0xe0121110403021203070b0403390b0f07120f061e0317070b06040b0f130501090b0a05030a0b060111030c010204150f02060c0307030e1e070515090112020403080313 72
    0x10f04d441465141c000308a034000769111505e540943c640e0380d000c0c0e4084900c130030704d03104142d8002c0c40000350f00701d0168a9202d07030800c901700c0d0041d8642c03424401074550000c0d20120f00e17402c1c110204a42c0301c1d00b181802180c401c1300440081e45004000c1710380010565600024540e050b0603e40c003440303041009a5000380d0f400303007240800c1402038a03a60300103489043d000810069000000400910341903001501e1150040c242c01d80b010020000200910544a00c4090190f41d8000501044040b441614540841950030003207007810040080d0741e45907403540080c0404484000122607034424061910400c40c03d100316900c2e0b0010804d0036010390002d00508841401207080d002c0c1461103045803c6417140d05801800d200d46915101800e203510040c80c00c2d0070700d40c445146900c0791b4410010901905540c03ca510710025004085600307200c0721b540002c0c03094030401070811a080440303007107031184002402c04840000390522800040d024651028104007004006c0000810845086aa81501c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 446071915 1250 446070665 446070679
    0x80703030b0d0b011806030609050a030e0d081209030c0d020120041d040201110f332406041508011e050910080609030408070e01060e012111040302 65
    0x211014051081c400801c0030f0161486200100409241a81c0c4484550301042c4045800c03138407500e40505603020020304407140e5000d11301c81c0d001c1c5a07000040c0000074404803454440761300f582d15a50b0042c013664070500600703440720001c01c529000030000c5400c2140d0f80c03815115030a05100002c0d008042c2c4040d50011040a00030021458800750125403c1d58001d4480c00d249071998050702100c0b2200400484c18415200b11803581c60b1400c125000c414003d0b04018a400d80000001400c00c40310109203104584885001c0349960020f01030f919408029840385c5007a40c00503100c13502821001400c0d9070382004e00014007198101a048880300c0e459000d450b000d4090340c0e83c4000b01c42885c020703807166058200403001400640740090302e15030044011402c099100361901000b50400c002a290404540d0000070104044201401514001c00c1e032400314131020f40c50980c01a1000c010410b0a90400410107140303101661049594050307410040400c12641e10b02944410007541300340000d901c210a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 446073165 1250 446071915 446071931
    0x709080105060109031b0e2d090304030b1e0c0d0b1e060702060f1b120316351f0807050d080c1f0b190b030a020d0908070303 55
    0x4414000c1c03a00039481a500c0d4908949162200e0541e00b0881d101c80800c01d0b400d00c00056072901101c40603001e46005441c421811030b5200c4402d01c0c0d916444640c818413940c150070000c0c00c0c80c000c03065a04072504005d0062003550303000c9841d007440012071416030040c0c010ba010701404010520180c80c0711f40f0641820407030350440d03034100312600600c1000640400c5000400400ca818801c0c05814a50301c0a00000d0928070640007910382c0d5003040340e00403564002e80c051001c0da00010091004180c55081509142d4205003e441200203440c90841003841034004041d03540560740c040c1e14241081c1104d50303503d40408001114a10303141a00c8800007000700d03488c558443e00080a686084600d19001008044c1c68642030200d00c020b000b1050701c8161080c002c0101262043c4a03030000c0070f06000800b8020216880081d00700d030448030302980500c3d2a20b4032010785801a155500c20b0b0b8010f254250344a545040710040603104a0054203485400d16242004000224015026081c46a1410300c0303000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 446074415 1250 446073165 446073179
    0x8030705031b03070c2108040e07020105130f080f0705010509070e0603070b16050a0b010b070303150501200f0f03030126030d1107290703050105031203090c030706080709 75
    0x40584c54015040b00e00645041103580410390450001c116100f804075003902286d01c4403006500282c3c02807155040001c20001700036030a1040b1035009000b003410019142d0f007138403516005841d5031002018031304002042001d02e4101002d540c2c1540d4800000e010601d0b11001e01da84038404e80c898100d1218842000c00e4603803402107020801da40e038a400365810248680003100f01d9242180f803d86035801000c00f1003020680c00c0c08400d02900c0c0e040c072015a182468500101200e0b100310440e04e418602240c1030050b6a407081002840600700c1d5a4000b0403c2040310003070a0141382c0c40001c1140c400d80981154003100400954100d400d01440349405d0384402d07111103803201e4042c90361b003002d810400ca0706415071411703441000000710822030503050800c159200800b0720f03c44000319080b00e2400195880079610210b22960046443c034062100303501d0000400da8a03100030600484030388020001030941c0000f0407882c2c1c0a0b80e00181121641c0b030387d9040240444100b82c40000000c0c01e40c8001069030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 446075665 1250 446074415 446074417
    0x60903090f0103050c0906131a07031d040f0c0914030d02060f092401090b01030902030615030f0106090509061b090603150a080c0112090c0b0f0408030705031b03 71
    0x1030a005000e0291215020004500600c0014180d0090301024440800d26840e400b01402c4128038030442c00046a08004042421840c101a1b00d0000c41d0100082c4002070350180d60321000b00c1030444e00105042117100000c000d040280303403082c5141c0c034007070b01080c1465002030345008490403440401d0b008524441030580b500315140080340941d0000020950b00800a405103a005003004280c0d441080001c080c2145074408098032018140c1d060b006021a500900c245040380d0000d007420006400030b580401c2e1183d10007454184200c0b4441409486502c0600948881205140c000c200d00c075241d980000050109580c00707003091081c080014420b5090380000701d6203000703104040341012800b10400009520007003803181040d1440100a1003911484600b10140070680003030403230250075800061210003800302c2c62003007908007000c000220303d50304841c40640e26083c03005580c1d21420003010b2842c0c40385502001041c44001071280a0000c080b0141100d203803035201000810b503c400c180c0e552 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 446076915 1250 446075665 446075677
    0x15041a012007121403190809010e0d1112070b04140a0302031804230906091504060b0102011e0209090a020406050d1d070305010e0610120b10030b130302060903 70
    0x203a0000c003040c4000b40d0f60100c01c0755607034401e95104040c004c804440784d045400c583c0480c1e01009588040d036240c1c6c0d800001641c0d2015010b0000c20074480c40440a99490036007100c08003d10041141032528444144244039040b0b002d08021079903a6102d15018407280001c4405071014075280d40b00650541012580381100f0380c042e4000e506256400c0c12102022070800302240e401907032000c250f000e14929021501c4814030744424180369207010000d007801c0031802084001c2541051469200c500a030320f0040b50031a81140c00062015100b100613401041c80503941100454200709182d50709170b85400030000c00e0381c292280002c640702c1004403400d81c003d0b809400045401440b020306044c140e80e00008a650220045184030710800d5030710b80c1040556001551a070351920803010441c1d03010080c1c02c0d08011085404199249000d04c0043c903021440002803840400c0b8021480c0800c1a20000340555040a107030b00042c00d10202c099074102c5a0403089025000c2c502c0080c101000210503111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 446078165 1250 446076915 446076977
    0x3180301050c070804031203090f08030405010b030706090e100801020f03041104060b0306060d14090c0405061e0d0c080d0903050c0102010506010504360e07080a170315041a01 77
    0x1003403034159558190980098105a800c05279a403039a9004207043d144a45141c0d8080c030741c100e03600d0a081c00c00c542511900d5940c1c40c001d52000900300302641d400420300045030540c80f4064060344903698212120051940028403543c008100c81001018520003907024501c10040c800500c0e803140d041c0004d4440c20311620300780d4101840007820f80e080c07107401401d90304000350700011080e5040e102d51680ca03205543c0c2d8905070780204988406424544102900700e0402c980d8603601d044a21107000410701c40078861030140e6030300510301c020021b65940600107841304500361101101c000a0080c80c0080d41c0c802610103114613400800d0950041c800c090264206940b03c81c6081d0401c2e403a41000c6903c031400c41142d0800c031b00001c495060000c45085840c4071440080380d00b0b400d00384510f10313158660b0407c0c2d40c980c000c2d131501000254005202c0313506614040300c0540380c1c0e450303080d440b4405401640b1281c01c141007140c8400381c0da180f00351342050604240c841020f02e1a11030394008800d4000c240001e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 446079415 1250 446078165 446078167
    0x201061d0408090d02120105070302180405090d05070807120810140f04020c120d0603050c09010803030609040611070b010e070302130308090409080c010f0c0c02280803180301050c0708 81
    0x9103c5003410b9041074000c0380068401c8411a01c0003c0f10b03030849a0488441001035808642e00c44244204260914200305c111424041414100003180e11056925007040c01d000c000503030700003042001420790350348681080c00042c00740003a44020b810441c04582c15038062050750004941c50350a203940c4010260043c240b56100d118800c00d01c00294080c0c14000800d101d0014480e94220b01c01d0b00500c01150b0103840070800c03a16500e0958038110110900703610a0400318014054003d0000c02d0b01c1c0c0c00b080c210317182b61041d111401e12500800c00d2041ca1b20340c0c50000284801031000d00c01c08141220000c0780c2d9001039640e034080860481c02038818140c0c44541b061810070115400030098412204000c0c0000713480d490558401815a00800240395940d46503011102d140070070348038074142c40340303d030800300c52852305540084d001c60020a440f560740b114020310b448090400404030005800601d040300e985403110400da0010118440c3d03000d20a60170100084c0c08040c0d0207090700c000d9035200002c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 446080665 1250 446079415 446079427
    0x9010207030e2b150c03020705010b0303030f0705160c063902010311090a030c0303110106031509150c031a0a0e16030f0c050903061515070f0c03030201061d0408 71
    0x11040c03404611091310714000340302c0d00d420a002c1611401d903040c151902c00503981e0301185803040c203483c1c41e061664401d401c1030042141d840010114240c1c0082c0b145001581d8aa10420507110a14a2000540306c01095200890301c5900902440090340b800849004404640d05c41c0c54010114034400400c0307004030001150040d40240c00c80315084ca01492000e0a100c08d4202140400d615540183c9000c82560810400e064008401c88004055900240b085504503110340c2d000d03000c3c10310303100ba0751039441e02103000f84903500e00741c03a000b441c243c40f060240b8451460f005000d401c20b5054134141186602c0d41460314a080b200d860211110914040d8055580059036142a02013602080c107150310b80a98001d8200c031442043d013554501d4032840d48407905141498a000402060410003551498100d0040d5031002d00c0c40104507240e012041e80c0700c0382071400c04a8418001401040002111404010940c0640001060b95a61040c02e4420b50024507401c12410382581c010f4070b4141e0030405 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 446081915 1250 446080665 446080729
    0xc2309100e040e0c01120225020d060f1e0203040203060c030405070b0a050a030c0e030c04050c091305070e010513092a11010b0102011401120c030b09010207030e 71
    0x244114035655080c1030304256048008101a64050010700ba00303504000d0401e8000d6030403942e41079512454910840c20304c00380106c017041e084240304860302e540695640542c11507a52030340c4001c4c65540840c041c0855046030342003101074514002d05c00c0715203030341c0110700c908a80c4910a0f24030841d0001e00600c26515945101001540064070641d214060881c0110786041600014000364616940b0306230b850f20940070090440e08085860340030055003264409090f0707000500c817071050710210750009454a418941382202c0c880e210240307800080700c8642500b86162607025903c40e1505481d00840806400011907592280c840310780c0080c294030303070144134a110541c0654002e2801c803040340e15000071007030410400d2a145846500054001d60100e215800a00510319502e5080c0000d00899024401c9104050030500845a10001c00161071081c0502d95503058001c68105030010304070f01b403400c0b60074080d43c03110b1802e80220311800c00c80662410b001d8403901c030310901c840c520302a075900144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 446083165 1250 446081915 446081929
    0x230402070501020c030c0607030605010c08031803130602010b031b0607081305060c0309030d0915080a021b030c0c0a030809010e031e0a0b0604021305060a11010f0c2309 74
    0x40e00369100d40d42031012001548040004100518005006008a281c80700340101035030016040241000a0a0000c90001d000c11050701d03003000c0b80503250000c0b406d110a00e5071542c007501c1d019004d103440c0301c80001a2642c040d403106421070303800c1e0242e8601c080c038132016102c24030300c25880350740007441000b5203008101903602400c86002e000e20444112540c43d00003a115420940884001c1d8100007284180751400300200003d214072401c00304001c902c0c2c00b280008040144802e0340901200d40300285003d15583e0443e94a002e0b40070f101d602880c400c0c15042c3e601e800c904000078651060708481d584038a00740c4844401c895100d500c0d10318085071400110707101d55209601c0354042c418660004440c0b44110028024442c00e83e004010000241c101640030010140c03245024601c10002c55060094060004040d540140d45c0a65a01442c0104880000d4440300a490b15460861485044400c075040034084480c240d450306070924013010781204ca001c00880c1602c412000b040000c5550074808 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 446084415 1250 446083165 446083177
    0x806070c030c08070501050705030105090f040203060c1608070f050d09081c02010b120607030f091e1b0303080f0108010b010207050f0406050348130f02130609230402 73
    0x50084d0503c41e05079162400d540c415105000490400f04c014406410300542c00c550041c0d1078000b0040c41d0a05402090b141d0300080c0c42d02c100c070140066920401c601041c7d1801c01980e0216060381e968215040041011190039030072101409107070b00d00e05025106070b26980546d01080d000d403501600006a071321039107480400500c2036548800c1024010354680f5580350100c03214601410035460072840040c1124015640607260034505040400420034009074a407020f0780d8110940c40c5a90705080220310000b05d12001c4203000d551800100070154401d101e240100e04100140e0030603602c07000d4071400c0e5465540781500680c803900e020826868154410014403070702601c0040e0054517240130030b052100602d21803c240003003028241041269590018050040034008030f1588254455012824140d65000c4d00c10714030040017100415680c6d11607030202c80f03440c80466031941c20030340c0389200c105c40c4e120b2440400d1300440b0001b400c0c0140341d03201c21010b150310198140c80c4004000c22000313402c0a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 446085665 1250 446084415 446084423
    0x15100f03020a03180c0e0a0c14070507081b01020c01080106050304060f0605060c06160e0901270515010f09060f0503180111040315020a0801140f04051f0806070c030c 73
    0x44100703820384c2030038190350810980694000a0a541000f03021156460040c4c0a0300d0031350f10781010082030030382c0580039030b030f62081d42080c03e40e40e244a03041a614200160f00115914000c00c00f00140200c00a6451507403600280c0035161004242001590382d041e007480f40c000030650410009000500b03d40c00150380d144544000070b40d0b80c1c0ca1714040385581d0000010000d0651048080c80502503c1e00030101d511202d0303280605072400300b02c0121b05d1002e01803045e039039118a55440f026000b24001040307040d0b9841c4003010000da2a040d001c00070392012258070940403400c0c0b0111018036a106420348402e48a8135140d006000c54400000c460300c0e400103241501c0400303008a200c010000071b0203400c882c8408030a00c0740d141c80c00c60501104c4444581e08456002c0e10400841015a40055810741100d208003d00b904281c2c4000108020707d40501e01981d200b0714050404c0b00801d4400025030703005055280008803a900c03882c1d501d40c0c5c1c41d01500d08070089840c2250b98030001c1d1103080d10040003442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 446086915 1250 446085665 446085671
    0x200a140c061e1e0f04030c0821010504061d0709050d0c050414040506070f0504080604062c07300302011e020c3a03060303110d0c0b18030301080615100f03020a03 71
    0xd0b2342c6802d4050b801c014010002e14080e40d4890b481d6102c07581005002d81001c89040103100e142c03c000003407403030b56402a90a1440d040c0006280035015040b20340c018103014040d0b026121003460025a01a03503801444e201d10315182c101958000c400310428071aa40c031800030049921254811758010016502c0b04007040410000491058018890035005a11684000c540c8100002159040800c41e400356080d41c051404058800e80000440384201c0b5108151210f003c00130701d100110760240710858103211030105035501e003010740c15071000c400c00103102007031001001c85e1034a06d002c2c2d210b12103a6540d683e0010b94a800100308190038003407100e04020714211110010204032501070444001c05000c80e5982c1810000c1c9070704000d17000ea5500b041c04c040c1c8a07001c00440050311529081e00042d01c480d1100001842801582c0303140440402c02401f10394496960303400ca00d0755040c084a440c81010f11741e20403100141040b0741c0d02198059030b5100d10040c40701e51074084000b900804000030416403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 446088165 1250 446086915 446086937
    0x5041b1d0310021b0606060f0d0b0a031e051902060301030809010513060e0102060c120f040203191506091e0902030c0919200a140c061e1e0f0403 64
    0x125510083c200e0784101307101c840007011000459410800c00500640c0a040c080042c842488082c00071104162a13206000408803c00000300e1240781040c1c000400c0c0030300c80d0402c0c1155400d2589004100340c030400840e0001c888208403008008071440c0d000b0340000c0c040c0014000140c10710080c1602c5a010301d080c605100c20001010040021603001c00d007c0b80602c0d80c44001c80d681402402d521100d0300060600c2c0c4000a0070060360707880018500515103401d200410708541d020701245202084880e00042025154101000303401c0380c8800c03a20341540b90040c000307000501805040040001004041c2c04103490200304c0d00030305a9007504030f0f458083c901c4580c205e681c0320700b201401a160548290b40c0081d00c880040220340f4a03103200c0b0f110703143d8248074241c080001811036102c486a413a18105288091482003000d00076104102e5040c01184200010900c000b41c195160b07548804a541658079a0402c0581e14114080f4010b5410240e1000030340c44a071880d14550450310918204040d80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 446089415 1250 446088165 446088193
    0x50d031107030c151d1002030c040e061f05040f120308070c0c0f180b01090e010b13030804060e1504060210020f0d1d0d110a24060b0405041b1d03 64
    0x101c60100951405c1404a44c0d4502c1d48400c004801c81419039100c00c6185050043c00a42107001c1e6200b60308040c101403001407165110b003030200700d081c9003030900c140a03041001005061600540118508003050010000e265800083e041d150309800d512562800e40b0b803020211a860300d803a0043d42d009010902c00a03070170b811a8840c3d40100310381c18034101c180080100314400d5884e55000c0c1070400c00086024000300d1401849a81182c041800155403448040c46040482903180d0000e04002c002203030002d682500110303041c1d08100e044404012902c140c508269103405180149001603004c541c038140f51249523802007952458042d981424030741c0a83d00d44e025506000072501c1d14800390504002460b0081040c0407800c4c102c0e0510584c0b400907040c196940c0c0605d00006020800e69804500c00792650000f09407002c1c03500c4109220042e1100c1072507465034040c0c1309090099250001010200741d084203091550882c40d600c1140e1454820f0303403151100c8421580a61500915142c28100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 446090665 1250 446089415 446089421
    0x150f1a15092704030e06030f01150e06030906010509010f14040513020402071a06040603030203030406020310080d0906020d05030705161502070b04020a090209180a180f050d031107030c15 82
    0x100c21500c072055182c3c5000d14000f000649040300540c0900c07001d0080c000c50190702800b050548404059074500070110b910100e41c01090708401540004002050140c0443c02184180c103075107069555107080d9030f036600200340c6081d032489140003c107080d181c46900c500c0c0681040b80c01804401140d000c6240c1500020101e902c102411a0051240740194014000780c51680c2c2d40000308440030403140f03146441c042d403207100040005006540c0000010312096840104402a211410442d440d4064804014160541c00d014000c054815800002d920a00c90340459205080c0c82e0740b410b081a0308140d1860101c040c1031012202c2e070a140804800d40382080c4040e1075507070701640200c0114140350041c00406a415004040c04500405c070701d58068031800c030107405110b4420034041072652100410001441c070300796040c3c40144610030b0b100a0007050360301020314038040d1003a210a40313403192050b41200c071521840c800c450401d0140c6000300f0301840074458114003440019040340302003007014080b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 446091915 1250 446090665 446090719
    0x3120c13080c010809070b040504021c15030510020301031a0402240904140402030a0201120902061911010b15070501020408030a03060e090303061c0f150f1a1509 71
    0x1050b030262540005540c1e20861441d00310540ca006004000d04100000e001881a4007899005640009a80f40c404000f510f4038026910132010410005e0008ad000c0b00711140140320a031410b00c40c444403031138081500c1c400c0701e04980e8807440842d62034288800705609101c000304181c1c0d0110007030140c11469411f004040e00c203260711514240e60f40540004010885849030003030500046127808000040e1000100d410b1700c1078090810502014003c1190000360032020703c001d4100303034081500810062410b00040c000741c09503d0b64142c250440744190300301d44410004586c030020603492290b820000c01c00802c039040c00341c800503240540f50450710386181c0c0000310501c0007075070703a01e401c00504000001468120f0b040a01861441c101400014001e00f80c05d040c0340c841030145642401004003400100740999440380792900c1131545052fa45000f13248125101000c58240b6a020025610b080455010311900a0000b8110413041d072002c50150441c07942c243e001881c0d100328190030341000c070f000e0f05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 446093165 1250 446091915 446091929
    0x30b0a0219020c130603051905210403062d15050901080303060102010e0d020c060a030b13140a0b0d0f020d080301030605010602011406030d0309030e060708040806071103120c13 78
    0x598a20910500c130281d840910704264503441c0c994180000f5102040320003481819400c09039110700c1d50b040c541c2c00c048040d0f03c5000c01c1c0384401c0d1f41d903101b082c1400140048a00666040284c18202c0c13000043c1c610b41e1562180d82c412a141c13032621090642e602004820111030382440c421500e03000032130880402a0814840741d403020003000003e40c1d0901400c01480b0440c4050b00d41c81207004c2d4065a50414800000d22640011400c900c049210b0b038450b140082000b440c00078100d030950f0400b8010a40000300c2030011042e8000a442d170314581c054050072a5020308506803041454075003c1d00c000c10714800302d91049a030500702c00840c4101014501841c002c200026041d45041c0002c2e007100c5040400021494403038040107125640401c18800c00c0100e0f0502140504103407404803a200348100c0741c0c80e4008400f085c2842402056006441990304050031550307592a00e0000703a0308204150a1031650340d1082100c140c641c90b000c07800c1c68000000b03800e01e03424071040142c03c00c0174146a0700860 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 446094415 1250 446093165 446093173
    0x3011404110109060c080a12061503110315090c0c060103050303070206010f0302060409050a0e160812030f0103120e1503090d0840030906120b0901030b0a021902 71
    0x30500094868200740403400742000d855940c90402d010b03010303000e402409402e81c0400310785098103501504400c102c0c2290b00b201000b0b208c0d201c0340d092041d002034503089000a86800e0750400030f00300712000c803400388003140180c00c0d000d40030704100b0880794001130040d032903040c0170b00c034407803040e0420090b080c042c40c4104040c648034940340000074640310f8140c0c0251646200020100090303100c00b002c0f00e060315103890002c41d0903036452a544000e0300146201804038850060554240444e6480d5a0281e49450054906858140c94001001c2c002955000c9031007100c5001080010340180440c80025643e0601c18004440040045d42c158800c02c50082c50140010400520420500004c4001c1c031080c24900302d142440800081003d00f046000f0a01030505100c1c00300420f884800600714405240b0b410140301c90310702c7d00900d40341c8640303d01e201095100054082d841e41d50f004110070208050b060035020f07861a250600350510107000d07003000d26800c012851110288424460106107907030014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 446095665 1250 446094415 446094421
    0x8061909050906062b060905030c0703050709060b120a0b031203070503010f080a0b0601030f090219090c020a050d050304020a170109030908240601140301030b151215070e030114 78
    0x480380203003240070b018010f201400e0f064214054800e01a0704000e400900001d80007803d490450322710311903040c4140c242d102d01000001044400991001540e8811005000e107030394555514020380a689010040c00c44c10070002400c00180764000d4410380401030480b070f040149080790201c00d90090355510009500000103104589502140390000c08650009040064030381d00d42c0700c1c80da0005002030381059194034520120359541d4001d440115002000446080d070b060078a000301c16200d10441c00c555042c0082006041d0011031604012600301025000c4070000300c8040f521680000c004030b0b84070007421004108000300701014400311034014000210000a81000390152410b940041000d9004d9880f000d04100305c86900103850754591340b5038248e500d988006940c4045148480f0101e25004800041404038247e100b038000d10441c0710114145481d44107004c0c00040300d070f9079028a9402010120b0f1003500c2c551006030712000514001e00709024410009007901c10b582c0c10750000800c1d00041c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 446096915 1250 446095665 446095669
    0x3010b04080d0f050a03240801020c060604050601090303050a0315121716080706020403080c210a08010b09040902061b12090306160507060f1d010c0806190905090606 73
    0xc1914600b150f03007400f0a4591200c00001d00e035110302c1025004160b1a000c15140d411188088240341c540f02d40c0340000740750303190320300c80b4002d4000d07403240851445002c010a070075042600c561401a40c041c1c2d44d0b00311850441d101600d0982c040300c880820075030394a1040c0e002c0444e8030100000b9200c6821001501e840900384145803404090b42100600001c21012600400854030041c040e1f80c45483e0342d4032180c00d400e04000a0180380e10243c00c1407800244690040c03000304050400301d040d403440030030041c100040d043d824091800741d000801c51080042c0000031525000d4540038a0080c00484e41200950104a0540041e0202c41d01c4244c030503003100c1031810034040d00c2c0c0034044043c003a500b0300d00884002a03540c0b07009000d0299510300d02007044182c600c41d03c200c1e40416044842404110600082034000346199a075110451241c2441c920745010180503001203042c03181e0f607800d201e49442c1c0800c41514444101c0100700906000c000600c49654040c06208070010f1020b0603080c642001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 446098165 1250 446096915 446096923
    0x17130f03021003141b04030602040e040b01060806060a080a0e0a0309081513020609010c06020309031c05041104180507030c090b06070507090b060c0a12021014012903010b0408 77
    0x340ca1410303d0f090400c01201c1d1014019040d902c03040342c4a907840691049a000d008610031900050302c01c600004003c642c0c00c2c54216014051485a41010a5aa0390315001c503075514007a540d81c0e0b8016020010108060310a1450b29041901c18000103550a210b107002c5261580711f00e02140460441e2804000b07400007404460506c0d40000e1082d0344901d400622088100b903030410080c818003011072101344c1c9910800d8507050f2164041d00865484c10f0010b1000c0d940d40002000301003040b01d4020001401e030160042a0003640c3c00b140c0c052400360200104000f608800d110519071410305100f070004104108401002540248581645c903410541c840040d12050301d00540140020054440002c40c00200c450445500030400034181103c0300c009409446024011029445104a1364081c405100d6110f00301031b0b044c6c0c08480c0110221181c2000b9292241c122860566000c40104401888a101070a10b4034103034990391040c80b0461554040c1d07800a03003061102d51070114081c496004100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 446099415 1250 446098165 446098189
    0x92d05160501050d0c020309030303040c0e01050a030807120509130504020a0b0c030316020c13150603060b1c110304050a0b10030b130212030d0218120a17130f0302 72
    0x8100a80c4290030180040d18522940c03011203d1159546101e5003001d03c2841a103281203c02010f50755241494102213000711304a01401d0418000b03500001003500e0140202011070364450140350500a507600d5501c4a039442c280b900c01801410801030311035544110780d111110840100015450405e40140b0220044a4021909003131040091500c0e417800002980d6000c4030168403150b0758008040201e0030024ad041da4603801a48007000c0d4050480903405c46000b10f914680f1b0301790140c3d0f40d402c0440c00c0d202c040c40b07007801c1841c00f006142402118070030318a42c000b0907004041215444045e000d200c1e5401142c003951590015074542040018401c5104c0e00501c0e010310b800e00583c1161202000d4003000780143d40112040e41c030325021911070350701c0c20218030b403113009030317a220041d910700302000e54460b00d012010305000014002c0285002000c000d402850940109013101c1e80741d071004c914038900d0701c00c14040c07941800285c110307003c4034480c00c1c0030309412410f1030800c0e131071481840031030280c030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 446100665 1250 446099415 446099443
    0xb060904080f0c0705130c020f0111040504020d02070b1302031506060d05280b04061d0705090a080105042904020d110d060204170d050a080406092d05 66
    0x50500021414041c00e5840c40c50280c0140e0350f075405000e490038501507081d4045500040001410348800070b141d444180003030141e4087e6910448122503c3d4201e41852081681080c0c05120074000741c103165005c0c0c0042107e000780140f038100c081e203445142040c200d0f0030031441150044070720214141070003040803601000d042800181010800502c0724041e0400c0c40c402c096440c000903100305c40b2078030801c2e100d11b1404043c3c1000100311242d0300c0900220700c0028001c0b42080d80c00144002500703000e03169205c0504406516449444040760154860f070800342d800b01c00108045041242849030030300442c81241c50385607082d1802d041c96404881951004042ca0b507000c10400940c540c0450110901d5228401401e02600c801c00205409003d03400a01110310209000c074032404001e18241104155000b1076483c04010f0104695521500d08008001200d040104001074015017007007000306e00c110007940c40840302401c00301100b162107141d000f02400c9081c9030350502901303010100c559031175 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 446101915 1250 446100665 446100679
    0x1802071b1206150b0a020a03020d05120a0b0301060816080105070912020405060103021909141002070902030a180503034203010605031f2406050a0c060f090b06 70
    0x1d01a51455015030300381d0301609060320755450b941e101000300f6416010b0400100c21030780300c1901402c0250781e00c801c002c0450251081d966100d5100d40a502074481e50a40c0aa003081d035941e6490350900902002c50000785c256480d841c020903000c0007480040100d8051200c41118145010b16003400c1d030b1009030820060008001c8144040f07030044140c407285540594010031036841d0880120002e204100e4140d03492122500e140c4036455010b04084204d500e14500406055152802c00218125034141400036a100e400c0070041a0000d4003e56031200054000164881802140843c0d0728461401158160030010801820f164540d920104509110f40682001c0140c41081564450600c945015048140c0501c21103a60250041005400d0140239a007003900303001c0c041004641c129841650081c10300030b0903041a10705010042a0300403031741e0403440c0c80780b602000351425484440804104040602c03050007217003042c05900483c0b0544200007400410504044c40e045601030f10041c03080d25 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 446103165 1250 446101915 446101919
    0x209010e04210905042301090605010908010b0f120a05061006120e0c06090609060c061603090c03080c0a0c081e030f091c05010504030e09150904080a091802071b 71
    0x15206032a0415113005980008540c00354803842d500260301106c8450000035808004528000b06421803002c440e800e80714900110740b00c0b20160300b60342140f200250025818400a800ca10f494089040d1140480060300c114400d03e44409080c0001101c080c2a032003084c020070070a42c3c0e400020000410040c00041083e102c112602e107880d90a03e00c01c00e4481e600c007040c20f0b0400c0d5070300e800300c60452800400740c595580900400a40300ca40803100084d6038060008140310290103801265102a4010041c228043c103507174031100c0e15040008030348070781c1c82000070303142c0080c90101c0f080015040d0350000f8a00611a0900324070480f40300d1a0000040c0c0090080b2201c070031162059038811501110f4001c2d04800c0d0860a01c10242031071005080f660a100902061540100540c2c10611080d41c42c180196504032030702180b030313042602035a0019030031000503001c180d10030080d0003103e646141510b0306030b6460080440900c0880449044180c6c0000d02204002c00035a5034518034103002c952520040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 446104415 1250 446103165 446103167
    0x7020607021507090f140420040b0319050a0b09010603020f03010e13050a0b060915060a03051012081215010203030106030f15031a01060305160c0f0209010e0421 71
    0x40c10310810056070450030b40210729030034080c0341940c01034403520304a03d428550b00c01005451a00d24811340b1b0040e41b8000d000c100381c02114100c00c10108852002e5072806c1c0c0707840d0030340d98580e000615030080250a00301405491019004440c010b020410001c140005180c0400240700b03c1a44004145807040007800c0041c0e00101c1622f04440c2c0d540c100318100d03aa04460104072805c5100000e2090065540366020003412285050042c0801d465441040d62694070307078002e54120720b10407503001d0b1081c026105120312070342000781d100031000e10041240703a8032040741c0d40f2250744040c211210305000c41c1c004502c550a07000654041e0450712401c0c000015000003030740324070041c02188101a1180e0014000a985800801d10881103502a04089030389040003141d00c40745203c00c04043d4610000000d40134484c4c01100d00500890f44c2c9070b1542c4000000030b4130a80000c1408490008499203001c0c050394485001a000700500c1c00381d080300e0314044c5410110000c1001e852507001e0481d803400406a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 446105665 1250 446104415 446104423
    0xb040e01020c0f012313061d0c010921030c0804080f01050c090901030807060219080a29120f0601030b0402090f01031a09150c0a260402150c01020d05040b0702060702 73
    0x100658104c204d0158070740c09100340160884540c06040c0c7c5007448a8501c0420080c08a56104503040d0281d40340050361000445900d0243d202e8a01c15000c3c03003071005040144541d24941032803107030501c0d501900706507440040030780003680520981e0308017060030001441e0038081d0540c00500c4c0c400c0c003403825a0050004c0c1038881c045c080500141000704900301000340d03560440300d44d070782405c800340141c0e03000640003001e10358110749003015035040c680404441c409843d8910f00e1a128a40c0e43c0d8981036903207042c004503080c10b0109240502c240e0307528a411503018040140a1030040c29055001d2030f0a005108521402070256003003080d10000400110b5401c00302d102d0a4104e10314a49910340703c40050074540564a11480c2c0084c02c05018468a0780190004000144090701c07000072071642c144c09599900c080d5040004c02e148010001801850280c2c03400c05803044400955091041042001e400c907046060a0604243d1712400e02c01030006c0030100ca42c4c80709980c4020300c3c0314a0003540094403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 446106915 1250 446105665 446105711
    0x120403020d1e0c1e0503010c02062d090307110d08040605180907090320060714070e10092007110109080d020102070c0e0709060c05010b040e01020c0f01 67
    0x2031000c600c2041c4416840d0540710b41c180581201401401540300c0302e505000300c5154190030300c20400c4040c00030303031801d0600a6442e40c21803038001e80055075515190210607102180482c0b141d25641241c91142c51000345410b003d42c1900d00115192444c030310701102c00241d02d4070140d2242d0380386401800000e074007a00701c90541c3c0c198541540c65030340c2141c225480c40141e614041d4044252020004c0407a407008820702128041c1010740d1503001e024012501c00240c807001d041c0c00c00800c10961004c01c01d40061929825484800c03190159076840c0c0084940c0b009450b1b40100d1503e000c41009a54081d0250f07402080000c080c8140e2208880e4661481d0320400a0041010a60500b4114585c2c001d00c0d0000c000c040e031034299200e0000300b5400038000c0d80003038004c0780c000c0740a01c0b020624440720f6101c00c0c032820035500d0b0720000a0a00200356000d01154070112540c1d0748440620b60700e80c4540c024016107a10070400035072512003102a9a0904045a4041600c0c0e031401022001c0b02d0507414040c08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 446108165 1250 446106915 446106923
    0x110a0c1701063c080a211d030703050708030316030c120504050111030c12090a0b0403111002040b07050606090606090f06090d0803010f0f0609091d10020c120403020d 73
    0xa00144020710682e00f600e0100c100110840c6050710000c0c0b00c0c140424281e0405200b800c51428003800d49611003100701206502c0c40001d0011224240340d00801e80388084001c01c02002c5650046c3c3d40c3d6156494a80c203170304402d0b015000481800b440894035200050313412420b0400380441c50b98444018904044441c04041607034a035000714060280a6204007200050700b2031a07070340ca10f04107401e00342d503501200c0041c8220901000044200c60081051644c80742d010000d000e840d01d40d52812120713081d00101c40324082c0982400d0710007240700380c80100020b00c0498182919008182012410001d000f070500340508040d00410140d03980e039008035141e04030125203825400e210740c1c000c250503019400705590032001ca1030a10080c000b00d60040d42c1280c8040710b400348559103c0c40301c940400c480d03110780c801007003101005204580e80d039004000e1400d40008941c6c80c00501c0c1c044036203030040d0a12600c42c0203900050403030b460b41c0700b844010018a450004d05182c28030303681c0825228051f00030050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 446109415 1250 446108165 446108219
    0x11205060604051e04030504050109080a0809040b0a080703121103191103160f110d0b07030914061602010f060501020705040f0b0603040b01090501060806010f0f110a0c170106 77
    0x1100c500c05904000c1c0201500301d01c2884c1c07440e10b40341c080d020f1360041c095503005c1111410009040c400c0007502d0b240c599402613841c0e0500315001c06110241105542159200350100008220b440041000034019400742c035403a08546c400713030009010102110001c1d41c07170390010482141c0400c08001601c080880030314210740c5000031101040d0550140c03490b00c0000c03403140d00071783c0c6c24002d501d01c403101a9405044010500300c002c87c00c000300c000c91f03004010700d075070840400121454066808268460301500c0112008622000164181081110300e58002d014200300c6001d100ea092184a07640d24100b2010031555080100103560f0b140c0e0303480381ca80b08948031101e50f0150740a81c0c2140c450314601400007901c034102880e015100d45001d016001950340307030000000d6118841c80d6030600402040e1a45545800d810340e040315440e4020310100e05205c0c02c150f6441d80804100140b448203402060000d006a0411080040420800c01031005c640c0c1000014441651030310306500c032800c1d62401d54 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 446110665 1250 446109415 446109421
    0x100c030f0c06021e0c0106080105040b0f130b1801050105100905061c09051b060f0d051302030313081501080312130204060308071104151809020613060801120506060405 74
    0x92003e0300c40c140c4040202c00d0144188149000100050403c540b1014000e2250b203840d2024a0b007241c20458000e0081c24060317011174100701c94a00c805400120301151003081180315124080f110b0000e44162000c1e0300c3c28101a041040c00317108036400341604039003c1a00364250300c001000c000481c011503124500000f9401400c3e0400c00c900740e6800109182848a41d025040c01d82d1510352a0607410900a0000e0400d280343c68040d0403204034030201c616180c01c01d03200c1a0050002e242c02000b814001c0c900c204141c000da41c08002500c12001d01403200e556050514100320b04118015030100e9000301d80c02c3c014410300d180841a91070320000c0ca05102000c0e40c0301d0860148503800e0303401c00ba400c2850004003205200d205001040201d02403c0c1c240c8804402d0b0342408201c070440c0c1030404080707030700303010506c0b8050001d1802e1005030000400030541c0356031600011541d0f0700c09800001200060003003049056007001d4882c1c01048000d56588102c400d079180c103621072000400040c0304a07568000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 446111915 1250 446110665 446110673
    0x1110703032f0715120204050607060b01031821030608060411282d0509090c120705010e011106010e180a030306050a050d0c0b03060f1e100c030f0c 65
    0x2030407001c1d0106000312440a0f42e1113840e4610b070012585110001060082d0300c0603003410038001c84044820107040d061070034600b912000000c010104042d410944c8034820700640d0340d42030041200c0a4001d041418211401d1482441100050245d090516050120400000c4d50110324554840e8104002000e0100c00d40d0028007031072512422003250440b0551500350910030b458008043d28071810014400308202d0000d9680301a07410100c1c00c6126400030700b8890360800c065040c2d0400e00420454012040c0040003507a184c08030990700140382e2081004101e03070740c1d00064000c1100000e007019056a006141c032251900414045c03031a1144010300032850341390450700b2000c44400003005540c2a5200341c03400401509081c81100d10940300c001c000f00e0145021034601070700991000192500c0341c9800c45520058100801082d803090807140b00301c0b00354440c52612800d56030240d1032021601108400c10072210f141000900403c80c803001c01a00194010b94000000710103804c1044d0499000d12f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 446113165 1250 446111915 446111987
    0x20a03060b0d02030706170f042102030c031c0513080d020306150307030f140720010b10020708011416030911040c09032a0e0705120c090111070303 65
    0x80004d402d4820004c000800e564001d40a01581009080d80700c03141e00c03080b003903100101050b90050414a500300a26000130028800507031140014016a13041c074010031031581c1140c01a100c203601c18100c1018078503079060288111a44042401225041613081d6250007403540034050006417602d500101042c100d07038501440d1a4140c1e051840503a0303074540742070020301400001858109642c141800064220840c0840620410442e640c50840c48081461010074002500700d0072025540c50802c40c806454003a00078031245050740042160750715050119085602c10205c4281a1401d0028030001c16414040140f000c469490301265119003410030b00e4051807614001e039486458100c040c000540c010900d82c04a81c01000c000350754070f84614401c2c2a0a03184481e41c08002c1c8012410301000c0303c0b003c0d01c250404502e04c0c00c033b800d18501d9000c41d14412030540d01100c0302200414501c94a6070306c40740d094140302124000e004014a155070240600344036001610104009410012078000c9a00b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 446114415 1250 446113165 446113189
    0x6050a020a050307061a0108011410030e2b020303060d1119030b0717040c031205040f080105010510050903060106050307030f0227100e010f1202130f06020703020a03060b 75
    0x2c02926965210b0385001c9000b001d40d250032540300076400d500d204440d0f00428403a4121024180400226a80942003040c20076400390303540c0030f2540d5030b2044111031b08100314240070728249a0f460205500710790703c10304511b20030003150400c5500c02c100b0000a0b80f5038050101066510503aa000c15118810018100400b40c030425481950104400000d00c0050003065014210b1512204070b01084088083c00e823a00481d000380400c0001c0a00300006480c3c4040304100c0c940c81d2030314034245a200c80e841290080f144e4002c0015079129030040c4214549402e400e0041c5005003001483c000c40d0402007a11800144111001e0101c080000740d4401c0c02074016201d0451040b07011075032a000400c0040c0320090b0142c1c6104c90840c42101100903043c890b04c2549080000c1d2110100f50038200c004441c02e910408908080001001509604000070b0026001411400e880b505840e42040c0014060b041140d1000b405c6600c0303104200091f0721150400c0b4140c0c2d030800d0011980041000209484603611 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 446115665 1250 446114415 446114423
    0x904140609160f05090103020d1410020406020c06030103030f030c03020d020706021206010311030c0711120d021002130b0d090b010815061f0f020a1b0303120c0203030106050a020a 79
    0x220070007000d0400800c05844011107402210b65503501e500002c4041c1e0454041d80350420700c4076005101600d0084071004826108540035891005040750b564200310144000b10521500450188209a0180101100b070081612080e0842d85142c03030051000ca00015000c0505646081142d245c41c400e40440c2c00c500c2007101c0640d61081a031501c4c40080d0302104a15100800001c0070807103540c40381c080c0c0444070001d00079031401c503100c00c20340d00701541c4a820101e0f800403415a070b87e01c490700c0b400d200a42010134100074154000440001a080c1104064222650383c410004282e40c5140302110782c1c25100712030011a100e601c9400d01c0c1005000c29403006d001c5080340800000e281d0780014160b1070319400300c50103c0450f1100c40074000c1402c071803a010715140c0030210002d28824415541d0408000880c03040fa03e40aa031500c0384000189440c01005418410310018018560400801009418807000c100401140c24600075141d0006000b244200b040004076444040d10802c0201c61441d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 446116915 1250 446115665 446115673
    0xc08011803140912060c07110a0303022509050c030108010b031c0c050c03120c0d0507080412030c060504050705011403011a0c0a050313090f1e02030a140a0b0108010e0c040302090414 80
    0x6e45441042d80002c0d40441d0380c0103203070124103001d00301003c01604482d0716400400d64450410218000a00c100c403007003030800000700c6c0010b2007407454001c46000c0c2a0300c19401e40e503541042e41319400d40e002104000d000780d00c101381040c404803000d00c00d0002c0d19503520382200026400c5c81c081e0b0801d01d02e1600203a062050b482400e590140410003805003105032403c550038000d03925015250341c041d100380a425114103010420045c5105103100c41128800d183c1074100c641c0554031071044580903103080e02c29501070302c0705000f0f550300058050f1403801d10302166415917243c0044058212801c40130b00e1801000491038100c10001040082401c0da07008040d00c1d11400000181d21500b40d0a100700071280e418140c0c103404c0c40f03840e441944100d201c002449047c4004010104001e98400f40c0034003640e0f40d582c1c40e00740c0b0f8806c400b45e80a00402c0c00740400300b5200d40c0c5000051280006802c0100c000821030207104107400072004540c201c80d41520f111140380d84605007060448000011b600707141c00303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 446118165 1250 446116915 446116921
    0x902161b1805090f120703210c020f0c0111060a0b12030703020c010f030204080c1207170c0405150a120c170d02121806070501020702030102070c0801180314091206 72
    0x41500014480d9034608112510200f0007012035035104117550b80260051001c101c000c3c0031038884d40981c14000d0880540c100301c540c2c0000c102044078810414100140c10040c0240354100d401e0200809213a002d203000726004d8440ea210f03d8a07080081c0214404982c0c0b00d00441e010740311405013141c00c96560060329102d0485040c0030751104050b4181500007002c0da01806440c500a20980d400d0318036910082c0490b0b00c4070400d1109481e512011440184100000003800810b909102400800003d001e03143e03d5201d442403105640c03002d0070a181c0c080c07421580b4210350700c40d5003864044a01d900e540c900401150b0401a80d42d00d150340104001038031002d11304114510000c1d004c90390b0707450f0342d089495010b00b9000266103405641c40d01e8042c00c984ce410080c09142038009464003d0081c00018a4524181d00090890f80300702811a03040b602c6030410130200c40284107441441c65401c0c1c2030315004034103580060003152040400818148041003e88883d00c03a144502d01c400301c42030445105003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 446119415 1250 446118165 446118209
    0x504060c2625030e0409031106191104050d03050d0b0a03030c021215070c141b180c0a03020c0c0a170d020f030403020121050403030b04060902161b 65
    0x9800444907019104003161070140d920060081d0301d0500c2d07015070790f444d6060808820000a411444402d600b04072414821001c05481801414050801c0a001514440014900509486904d0410382801405110400250b2601c8a106200a5152405603500c40700c001144006200e0300085d65000300d21420040201500540d41e080703414000c1f41c02000f950403651945564841c0000f000003401102808502020b000796018000d16118011200108003001103c0d07181c110b06e220b92911128001c44910003609081c2003c8109850140340c0c401c1d9032601d14010041071091b07610030b00c01c0680c006441d0710301d4441802415515140140220303505641e03a00341c0744000712240e0440845020300703000d03844000d00000b0410b0722411b8043c017541c1003514580054403a440031450002e8072451102200360a4801031081034400c80c0319440004694461800b400111360a0360090145148108844140502031811030010309a05c00702da56100a107d280640c00703481c540d80708000e99103160352002d2f010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 446120665 1250 446119415 446119417
    0x151206080709050c19030f020c1b15190e01030f152103020718140c19090e1b0904180b0702190f030318200108070504060c26 55
    0x40b540c402041c401502d03490345280d1941702c0c03466600c65409035500704000c583d010b41c0103000036840c02e0000504001c40250940d081c2800030000d00680d078040b9a02542a20385504d0003003049118041941c1420100c003041581025a00010400d002826620410980c0310780c00c50b84c548800c0c090184000500d2441c0068070600e00e018200807018510f8896080080800110640c1500b660082c07001c00d2400e10380620740c42a016402070302c640c88408410b400d0310900c078032901800344a040c569440c12076102646440101004d00d008100301180100f00b0307a1619040f498015450680c01c00c00c60381d81c101e1000c80c074800c82c0d000c280c206d41460140c0c0c40d404440c1c900407007010f02071003d12006942d0741170100d8642003880829000d903c40c182c00700012a60120340c41034150f00c00c0c103000501013050305421070b00142c1000d00711182100e114104000a002c04140c085150013801c1180d458100208090402d000f540200800c0004110b88401400001c8a207030b2540720a4281500748140300229007082 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 446121915 1250 446120665 446120669
    0x20403150b0f10081b2b06050f090a0e010e0a02031c0203030106050d020708120618060306190f0f020903070b0403210e1e01020c0114041512060807 65
    0x200352900c8008103003424100000303050440010000181040301843c2942c229001500c0c0c00300407456403d0382d00207001d1150007003070305404407102c02001d40ca1500d020100c1c080c03450302c03010149050a40400c166190901c2c14044000215140c03c0580d4940c0900401032a89450b01403d03582022003c0e00c020300007040140c0d80790b0080d0f0607901e1200d010030780304a035038270400b0b002c9005a000b0001001035900c02c401074803c030549007801500d401700c6030711059029000036000d941415106018007190b4600008012901146000140300c1c1c5d1915100007511244002c00c00d001c5070501580b9803012564560240150509103401008040c44441e640802034200001c828004c0c03150b00d5010031404040c10a83d0222588020020a031030200e400e903100a12801011805001552000b80714a585913850382d8101004c02da1082d00504070640020f01d06014880b519041c02220440080403845020880c0c05a03610340402c1102c62011000c00c807400f022011503d125685020f0021440c9040480e400f01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 446123165 1250 446121915 446121953
    0x50a090203070323031c050c04180203071d03120d0b04060e010906170d051e030403180902040308030c03040c0b0a0801090501091109100203130e0108060a020f1209030409020403 78
    0x7010390001c4c051242e0b64030841c420b082100f00807417820940c44160307810243d4040c9002d5441414160f5405007408101c0010b129091400d80202c02c2005042d0310192455a0100002c0400c03541e4452501007500c0f2a6000d044c181c517500001440401454150090b051201025104003e01561440d48001184c428052a0452030405130000346882075410300100350003c9502501c0e020364001d1094440d0b40c000c0aa00b45041c01a2110b240803030343c1c0704040e41c441c601940710f80355002d0712000c0c0010031950540100c2ca403e8414442440810060026070f81e000100d2480103640c0c0e01c49081400c0030141c41e134012883c6410004405c080740b44c0c0801603604942d20843d0500071030b600c0301c1200c400c2e100e05504003000284240900302c4503113480c5940e0b02c4100f0150041d41d18015007022105110001070f0011501307501c2080042101980800986a002c5160b0f0400c505003004488008485e00c0340103c002d8402c500300000c03480030f100600440300203100c50f500840da03d40d520318200082c0c6545841d07142c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 446124415 1250 446123165 446123213
    0xc110a080a030804022e350415050106020a081305040504051524060a030b120318041a100302190306050f030705060418110a02010608060c090d0303050a0902030703 72
    0x312401012003800d40c1b910780010040301d400300000000f1203003040c5880c0780840050304c051000e0112015040c1e06110581000300440e540d1402d03040c08040c82001c0c410500c12146407600401c0301643c0450f1070304d130041c0e105d03080e281c0d250f0050309811442c41c0315401440d4014a05424482040000602490544030a41054445a403640b190f4510803902c400f0801800c10000a20310b001e1030598002e10341031815050004401c0308000200c2d9002ca885000105d80d40e00000d00f0042c070340314400001c900800c04603424480c86003c2d00c107420310600b400b40c401d4015402e14001ca404a40a130301a076a583c0d80c00c944042e80c4010303100c40180034000d05d2141a015030030160000f40541008078114096400c090540752030107113402c502c05d120150b001420320661b50307540008101c02d02207000604017900c03a540042003503418034102906140c005448103040150030480c0101c1c40e141c0020b11001c15405040018840c2e44074a01d050150248400082d894019070802004000d03405907055160404100c0c15 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 446125665 1250 446124415 446124439
    0x708061504051e011404051e0d0609030503010513060b190c0b0f011d070806090714040f080d0c030c080702040b061309051b07140a02060a02030d1107030c110a080a03080402 76
    0x1a481b450281541000c00f42c2c221943c08010f2580c01202e1072800ba0082a00c4080b1b40c480c1c0e0102c0701074450442c001003000004000030700c0c011155000010400b403007001101d282c04240c04291145400000b94501010a11800103008408505009401032070b200c1c2c40d46007101d20880c0f08042409021034608081036004041c2c0e028803441c80c0300302c13100d486c0c04016860b010100a004c0200a00306010003a40510014040841303101520003401070183d00816181010800c6003404900c41c1c0c1c000800c01c0e2141c024012981c003084801c0480c1c4c02001059a841060011801529940351226000a0b0020349205982d40401da1743c3c04a0318540070400180c1c45405507040070304080c450104003500140241004128000c42e043e000407501307000c880301201c69a020404640000c510700c005a007004c20545041c040501030191150751007484607180c00751641e0003a10203560b40fa00907010348600c2203100d03203e4a0708803540010f40340d4041151021b47c41c0b4900100300c801d0489081b80605132903400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 446126915 1250 446125665 446125697
    0x6100801060608060306040b0405031c1d0f1c0201060b0315010809031e03101a03010e011e060809010e0708070812120105150f0409230708061504051e01 67
    0x3441340905001070141c0540e46030b07038032440c1755024003030025100c901080000c054050003546074100150340d0001c021850f60007507410360720302c0106080b1041054004d034052403400300d0080b580c41c0701c3c00d010400a540d00b08800000300d00501003074016606000c0d0010500203c0000d21010b903958013800d0341c1d4542c266482c240c4d032a80344c0c0988104410301a4030f100003c4091b45040b4090741d80806178041d10078190340c1d201101001c2022500f416030b40c103c00000140403400d1000e0006014026000001701d04011449008800020320f1090740d041065a0001c56590305003034103c0021440c4080c1114031150701c8080d840c1d100c1032107203e00c079880c0c815000020201e03003030342099920100c4200d080240507840c11090001d60201201c1da07440c0000708100350100030000001070005056040f80010b00e03c21445800c501d001029140d00c001c20440e0810000055131000d2103e9103d8070580d9684507144000c185070180380607503000580d1060300d17408088803801c070000c1c0e5241d00c004260f85448600440080b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 446128165 1250 446126915 446126927
    0xe1609051c03030905161e060509040c0c051c11070312050309160f030b0106050903100b0a0806011d06120c010c03050702031f0b030102040e0105090403030e061008010606 75
    0x1003155006200100340d0020381c9503101c2501d0344580a41070215403148240d0392141000c281c90000005400304040500c070b10346001903607022100144036524a003909000024040e8064a40f906105a44030504100240d1144200841d03032a4450112808103e002e408081840d06400d8a00001440048440d070380141c005401421650041c0d2040070300f40d86608121015800189681c80707501c644004085038180c041c101c540206900741c80311020074154503085240e00c00690190040080600c00d250b920f80d0b0204102c2c0300c111140740001051922040031502c0d000882c0c3c0000c00c14001c1900020b2480c4115044c41403040b0744501ca510190b46d080f00700310769800e00d00303011145c1d9804866021515405150001c0085009007401410420300d540002c0c6014100341501c2540004140d007a907508016004200c0c0724001200203508207070820820042071381c01485024810501d690100302490301a03400141c1e8494840191031080c64149113800c00b0415030321400324290300c3d002002541620400b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 446129415 1250 446128165 446128169
    0xd061e0f0b011d0d03270305060c0403020603061323060316030f0605091c0f18050607110d050102071a0f0103110402071b0609170102031303120b04060e1609 69
    0x85064910f902d048103000501c80c1d00401103040c002c201404c0319001c940030403018940800143e103480682d080d031400b9030503d0006480130520b58001d01c000d0005030f4400c010307241c0c0320b0010b4071707081c0480c50000c80c4003000e04207110301003501c88039040e1843ca201c400c1400e43d82c0301d0241a82101e142120403001d1001e10b142a201c00b50110340c984802500203116900035680001e50b1004684008190407140c1d98440701d03406189020a01e00d0744504401c540016602c41070b920802d800e410361a00c0c180103d2590300c1001402450502d040d541d180d241e5960188101003c0c0c0c00500131034841041e0315001400480c01c0807020b00941a1600148019100510fd10f040c3c076072000002503451188010302003e500903d408840b4201508a41c0180307174904505c0d08024262070707441003652442c0400404441046a110a171543d004104004411958101d120082c550506d03041860525903620301005041106803694054142720b00020441480e800050113580515a084488198020280e814090703074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 446130665 1250 446129415 446129447
    0x21e030a0209040c05130c02100c020706140f03040f15150311010c0510050105011206080d08071407050304031202060403020706051c0216141b0d061e0f0b01 69
    0xa4011001420b10840c03075034200c0c0c8200110562140c6030400151101030b405180e00155983d0341c441ca010030750400c6680946141803404001300d90403e00001d480d911240074240602c054008049031803001c11080b01d4203001a548815241d0a0034074125503861840c0c4000e85444200d007410111602c080e101d28414442901309070400c441c1b940d40c480c1404210110b06e1030600c100c1313030082400f041080c0314030314484000c41400200c9604180002d8604020040c0c0081c881d0b14141c8180011340c0000b403000c00741d40042c200101166a198400c482c145c0d2824021034581002080755401c0010010117802524030425104203101c4d01120120b03520907003240e014005038800441003040d103010300c008041142d1142902220b42a0024051060340d00c0041042141c01c2e420300c0c0b04050040400a91078030384510000f608480c05c104400c2c500c610310607100e15224210714494442041125400340c4550350300000304080c00b50710440c80e280204140011011101e0801d0a4070382d9035032203450301c203a580d448 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 446131915 1250 446130665 446130673
    0x180310020c0f030a08191b030506010908031606180212070303020c0405041211010b030a14060702070305030a1d040504080d05010503070b0403033e1002040e0103031b120507021e03 79
    0x200c0f610740908003506c40518883d503580715038401c1c03802011211802140ca69840101d400e050040c00140740c03441550000b035858000b880300c1c45030400800441012a500b262001c00c011074048000100d8140004000790300801c1441c001031007010202e03c03207040b2030003030b0240c0c2c009000400900041d1042190000d01d2100207140c001e00c014020510030303184190440001540f002c81c000401d141019410040d074207100024034016000c0c0081103032551101c21880501021440c50751842d90702d0103081d4440081c0641c5c4031035000403411002c03514404402c01403043c0106e040a0030041d000b503010104120429040800100c0c40b4140022800200c404100d116407070681303992421a5180407090304a04100f0120500c0300414081c043e82700d040343d480c4000148580000d15001d40f030150707000c1401341101e0061000300046051401001c6c1125010f00713001d41115624250060441c684040c024244207800b000c0440941c3e012000d0425148251540d60008040ba8000549882909299070741540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 446133165 1250 446131915 446131921
    0x30106060e06070f290604020705060708040503070501060e070e1002070b1c0204060905012a02010509060c0106091e0915111c09020a06030c0f05180310020c0f030a08 73
    0x74610b004000c2d032801000200240c080541e00c20304001c4040c1008061118400b00381180c000c140368580d0b400545c1190218070b0304200d956841c0e21f407140148a803042c44a00d0380080c0074410248201d0300c4a59000340200050b989500700340381508001c1d10060000364905441c0080e03401d1004000c80c418140d0b030014180603245c498a0311540d400f450114840c02c898100506108440f030002c2c001405490b15030600e41d030b0038880014006981481c182021072481840c1000b8507004402044000e50280b800c140d03075000d2030001c10361030301c1000fa1140d02d561a055000035890810360292442c02800d8040c00c03001c011352406c11081d10481c0e0009015100344a006032002602580070010000000c180581400080740d401d25900522640c8080310b99200c0ca4403074214540f8039010f4014000508040080c00002040100070030b8210301c44609004000400010000b0126141000314400408982100400c64059000f94114150f0814103101d0004060081c280202c11b1702d102d9400351390340c0b0045076 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 446134415 1250 446133165 446133169
    0x90e1902060a23041d091c1b0503071b0f05010302211509072c01090f0312080c030c0d0e01200d140108190c050402030a020315090610030b12150103060b030106060e 72
    0x301103489031092100b82c03050b24071769080360600742c02d248e8000c20185880b1011802c2282c4c2c07861007800005c041300c10b03005041c03280300e60301080782040d60b0081c07030f0040c1c8540340c1c03d02d2403003541c200f020441201c1c250603080180c10354482540240c0e0180c20385610b2000e89032154180c0342d000d062041100c60500c00f8180740079412005402d4401030f1014035001c41700c544e4a601590303081c0910b82055410502144240c0802c61300842c2c0b0f2500308030000e00640c610725094003969440d014480ca0300c95202d4541076a40c0d80b48100b5041000c040b00305080301c002d0008402440103507580003104140c26181058007052080005910a9049802c0b050251200444c0030003c0f251801ca4400200c80810002501140c2a15244040c40c42078601f49001a0340741410014034003c0c070280902280300d0540b0b5020070203991158000070803442403508011580c0c000800028001610001820465125409203445509403080c00941264080c80c03040043e5411b9206150076903543d400350b00c010809544c0b1444180c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 446135665 1250 446134415 446134453
    0x1050324030c10020609070b09090c0310030206042705070207050904060e0102040e0a150506090103090507051e120606030a02061b070906090e1902060a23041d09 71
    0x10800400b0b03506090621800a0070f124200d60604005910a0303040103030403581084110060320b0462540c6041880240020b8002040104020b0312900003201058a500c102d542503405550b0080c0100d4480d5141d90300801900e0300c0011811035008a10304400804143e40302d218003e4040741d010b000e040d81000d0038410394140141088030000c1d900c44c0c00c00310b400710a1004d4030291140b2681c4c00070078102400b0007030a0300c2040c04416101d0314444002c101d903681e00421100c40c2c40003802c0215052480c0d042840c00c04078258005904400c20500b411201011030b8504424000300b00c0700240741d114040846903845104076903071a01580103000200242c43d10350090641451040c01004d4000c00f40300c14641010f401d42c3c0b1811006880c0c21041c44503154900900e42c0d070043c02001088524040c03c00800e5502d041b84019018032400038051088500c501c21002c1c410b9140544208103034501030220840d54001e103d040750000c40c4130b80c4071089008065041c0c0c01090242c00600c0410411030030b1a00d2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 446136915 1250 446135665 446135731
    0x9030d0e130506010c0b040303090201080108060f011a04030215070303140c03040f02060d0905060105150f041a120c1207030603050d030f06080a08040f0501020a1a09010b0a1205010605010503 84
    0x50000c0c80391200001b41c1000c044070b100e40d10a41d0301042034040c52001520100781a00b10801c0ca40009040220022801c00300c1e5046516541c040702032095414080c440d0f5101ea80c1003c3c1d0402102c4500030810f4884800404660348259410131810b901e12a840881e00001d88055074058000c10205001c6003a04403040c1a00c0d00081c4082c2c0f1300711903d0310740710032200e5070b601c2120150428401008980790231004008203034000741800b45001e0310250f003500c280c41140103400c001c00e42102c0b40c21b0b850540809482448200011100803410b010491014a40044a039600e030481c07104001901c1d240b00340500c00c1281e034040c0090820304681c880030b80107450300c00813030340c44981e4074540040d0fa20401c0000d80091809072200c5592141458801003040100381c21090556011100c540001148602c01d80c00918a5041d81e9009886050240b40589010200c1d20781c000c031078000c0030600740d4140c000c10030a540308000802420b95110015500d80c0411510340340201900e8070f203030400303406203001829 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 446138165 1250 446136915 446136917
    0x3020a060f050904140405100507020d12060b0c07031103070513020d09060c2d0207060f1b1101260a0e0f0a0c0807061418030319030209030d0e13050601 67
    0x30603ca5040d01140485a2550800240c40075880c280b2040c0201031004260791801400140401d14041d40b01940e01c02e0580250010800d09240d10041e150302070388034a01424050030a640d8422100ea0b00310365400080c082582d85810501c462906850f00243d11001c9640c0a404940400c01d8034840c070000750002e810b5500b416490359007040000350719118244240d6000d4461210500491030a480344240c40408400051404003208420540000e0f40c0411101c02e81380800c2565030328402101c240c0f0071940840f58508550009000700003400080045140080e40c0e41c801c0340c0300030b039065642c1003013114000042e48002004189910f055411410201100004a1b0781c40c102001c2030030f140100443c1c0548840c0c040a1080c810740300c2c00d0020700b009240515003036000e80e035582d50058040c440c1c45641007551190558070b1000fa00c0034030607a41c881e0310f000e00080085a000d00d016010303500000c2954401d0107405d8070350007518002c45d10703402520f83c09840d003d042001c10380342900a15001d40114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 446139415 1250 446138165 446138167
    0x405070e2809060e10060905040f06051312050306090a0203070906050a1103040308120708010b0d0506010c080d091209061b3206060621063606030703020a060f05 71
    0x400b141007409440031a034004030080601a9254a0f000701b10368094220300e88460038003040c40f0200362010013072240070350810000a41500c40c80000b104801701201c0041c103071500c03950070300c820301d03000006540300700c2050742c01e083c26030b84401d888000c0380300c112184404205000320071310074bd034410070180405440504000c0401c00c464185245103402030350003150504000a60750305401050b58100780c0007043c81c10500c05550400b4204090f5000d03180040501ca81d440380003444e682c1c0302d00401800240c10070142982c03803104140900240054010a44031461201e03165045544540140812140c81e655072181c244040d13100032011030480c030001d691a10801600e41e114986c0054080038400080500324110600d500c1c0e885d007826401401c0922500c8280b1040c50092010600e20a0510b003400401e41030785d0382e04000614014601c114220001c440c280c101c1150070000c0348850040d8500d0b103106019a03203a0080560b15100f86c04002e4000343e02c03a0007040400d02a108200803c00c09040c15 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 446140665 1250 446139415 446139431
    0x51e030f0102040b041703040614070204140405030904200a0518030d0903051501030b04060203072c01080c040f1802090d0303140a0911270a050405070e28 68
    0x2207080e40c11940010100c00b00000381000366803486110a4181c9a90030080c41c141b40c54000084c00354400c01b41001c103a820300240b80700c11507941340d000c940c03035a201d411010000e05260810554a800c4007036614000c3c1c0c98900032008000c0d004024a4114403402d00461034180100c0044400c1e80102901030054640c140da00925683c1c14401c404010f10300307a0b529906c0c249541881c3e4070b08880d058250101500c000c0052000c00d5000311041c1d4841c0d009800981c0d03985a5400899010140e040d503544c881c0340100018503101825a07903c1c4250304241c4c0e5602c141e4548014400f128411441200e140320622101082040f02c44007010b00341c2d5504ca0310050030402c00c440400d1491200203800c40010390364a50440f854410030541c0358100c00c4e416800c11a40a440d65811900345180c4007442c4940210000503d40754030212a14040b000e40d0019400682010801d41015000c2541e08139000e001d80c20000c110082c0505c102440341c0c2e04003204004080b40c24401d000d4080d049071805039225210049 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 446141915 1250 446140665 446140693
    0x50a020d120f05090d021c0b0a0e0d030b0904032f0a120305060d0201050c030d020403080901020d11061b0c1b040506030a050c09100f0906031b051e03 66
    0x800d0240201c6981040c140070350700060072521000d881005018003408280351584501100300d01c4203174107465580003209410100c49901c143d1080003010a00290100007075080c490300311450443c0281d080b81e01d03121080c00d0903000d0320814562580c22802c0640081c022030320034010840a10f065459403040401410200d41d54140f4030950300b8465404650180200007036901c03e840d8884440c0390401040c1021000503d12172056030001c4d041120100788924500028011180e0014403944119074450b0790303240c040701907040000840d026005aa2441c86d42274002c054001c424035070607019006541e10090400340106c514400803403540000d100340d9250031402c110b102510394007040007020200d0790600b04010341c0c1005203031b140203421a850704400100000707280c01c80c001e002c48194440d5035071141e0794207070005154050000e0b1912080001045031195102c0b80560340981e988405001c640c0e40c8030381e07240d8500d1083d140c01440d010300b642c1680540c54400c16690700f00805030f454501c140300d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 446143165 1250 446141915 446141929
    0x6070b0108030a0801090e0307020103380f010c02090103060c0507060509030306030105160c030e0411072004051e0a0905060a0b18010305121e2a0a020f0409050a02 72
    0xc1a00d0030b50001607401007407900b0030005401131001041c20311081010040792030700c071f000351000241859160161034501148101056665a408509403280740b01c6006010311010300300500c032801542c0c0c001210300306510609007503401c150047d15003651a480d5a4804004094480b446010070030140300c0c500001780c1c01d0050a0084611900541c2c503409c248041508540d40a00503121015131200740c803036826000030320710307520580600b00b880c0c000d25040c01081c05020031003503101921500044c0003082248445941c403854078070340141d200c6081440144000c4480030f1b1180c0300a0121481c46103204501c80d1501036022924090214000040c2d5032a5880d040061f1343c032000c07441d198410110a400c0120030540403044400c1c000c05203515684411fa2694020f050a10344003500080410000700b8000d5640d6103101c0da0080c00da6200e2040c005081c0809030644a5455401c800504000802c400210011140d0300100b2004060505504100c001d0480080440703450003181004000340e61008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 446144415 1250 446143165 446143169
    0x915131b0f0306080d110c100e040c09210317011206050603012405150708090f0319150c1e0518040906020a08070206130b040204020d0e070f1703120606070b01 70
    0x91901038440c01e64090031030402c0c1540320b9290141c05050b500d03005062780052001070903c0241d0380056003207803010301264500c1c1e142e04411103035031015030081d05490b44001c96086060090343c0304072180d403500eaa0382c01e00310700c01c0c40303090350040020182c000815001e038043d58010000400010301c2c0c40a80c09800e80052510f041d10100c0c8070055010401d6052501d0049250700c40740781081d160024981c1d540d04507006000705a8000c9103009980350840d1030070844880fa040380f035240002c4000c41031a2801ea000d0a0101b50f0722154189115450740500458808582181181203414455403421003114a50013402c0c1e04101501007a85110440d1034a101d903c541c035024100140e030b030b26010480030b80000409455001154001020400b00c030602040504103da401700c1240d40d151100d00010b4068040ca8aa030780b07440e46007040d100200d1340002540011100c24494648409a8440c2d01c02100c40040025440d0f54108008048400362000c0c8515444900208102d091001a88403c0d03013100b000d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 446145665 1250 446144415 446144417
    0x70306051c020a060e0105030c0a020c03060f0a060e131106040f0b04030c1a0315062a0705031b04020d14101a03130305031003020915131b0f0306080d 66
    0x8207100e00305506102d0f0000300580040d003410b08200c0e02690001304148001442c0121200000c5120174030303180b003400300d08031080b8020b0488015040085002d8020341c000e544245015150542c001808454246554851036100c0105060344165890b808a0800030300030340b46d03210b03104000c08540d8012100d50b4102404c9042111a121820b42c41c00000038106604000c0e0091a540440102d04620b201100c0d4061b00001d0701c1c8107508800030203e0300c10f0140d90010980c1d041818161100c01e0904022152600046411200620b41da5070906460382000d00400724842c005420b030b8030550426400400c040780031300f040065092030bc07110101c072800040d512068141841c43c0c1c10803c484d07058400d02d6101031030302c0f00c0c0d43c40d5040040c0a0100884a414020244000840065103010069a00c9401103401030800702c01c0c0d240c20216600b00156200f041446014904128a00600c95120304000343c2004450001d0781d0000c0c00f02034940032a04141c2900f0541c55820100d0900c205021003691031800d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 446146915 1250 446145665 446145709
    0x130513020703031d031902011e0c08060108061c0510050403090e0c04060f0e040b180a0c02010b03150907080708010f0b0301150e1504020301080a050d0206041a07030605 74
    0x651a009060351084204201041ca2510002264001c08000c880210319821b4a00e6803510880905902601c0512100d6500b043c50b03030308040c0c49940a0700f0040701c2040b2a038440300940e4130f0703000542d1b2003d0140d580d1600441d811111040d603401015410441c94001d40840d1110042c2003030b04801d852040700c044000540c1c0c14170410941c500ba000c040d8004e100d0b0200c85041504106004040e40060a54541013090070a260036107a1281d40c41401d200304043d2004142802d00e803030039282c440b0180c031a414418504100221a6071061286000c580300007005041480c94828000441020113003d0a0071070043c40c1000800700000c02881c0300804540c000420700d000d843c0420f00413a4810b6000a01990401c21359198036005002207000781d42280920704c801d61141d82d03070032070707078020013040141c11074400000480c94400014012510510070811603801592030401240c8852040e50002c0016a01149103520045403c109136400348081c5800610075a13074100180c0100c0c1202018a10b17000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 446148165 1250 446146915 446146927
    0x2040b0c0109021002060702030a080c16060b030c0103061a0d1803110c1f030e16080106181401060507050102190c0c080d0c020114210a0507021c030213051302 70
    0x80130003654020407000d0010300420f14000c6c1c40a501c91140000c40c00401001d400080c01d88c480030026030b5a0362040e81d1018010184510380b0100408045181c10700ca0322441c01c0d40d040b10341c86400703602c3c19070301090403000d410f0602d640d06c0105e035000170030f220245a0700c5500c58000c0c039990220b000f28140c041da5030105220656807480d030138200680701003401203482c05c050901d05080a002200305200914000402c9003180071805d0504849417049040b001e1b480f5000940c81c04150084800d40d08003d038011140c802d07021345001121180c62002c0d2502904000400405000703d02810032280940005407070030546130b8101c400c101d128059900807650120340c08050160007600800504102c00044c0071544401304058051a6100e000074100071550341c1c0741907140315603804d481c84c840301c1b210300380310620303182060300315189044400000c418a03110002c0c0a542c80000c0c801c1035941182d52500b00c0082748241100603601c803030341070100b0f00f400d108002441d844e9120101640d64001c0c1c001600c0b52 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 446149415 1250 446148165 446148169
    0x60902030916090207120c150204080f0105091b09071407150f09020f0f030f01110a1211030403080c09090f1906030507121401050408040f08031204080d02040b0c010902 74
    0x181c03240c11180043d80705124035070008600e08600e0040d2038050030007104040483c5803980054032442581d032000341c0045000181003000042c04081000b441c0024001c3d40da81d0103d6590340c0c045500c0c10400990b8030301e20b085042c20011440d903040740b420318040700a4090300c45020701581c05490125041d004140310b850141e0428030030080811a5420305000b450804e4000601510300550054800c2205660351150b551f030421045800207940c4009010305a181c2c000071187d6080480e4401c04a641c1e105504006d00b140c0c403402980840038001c1c103046071201d0710100c0303070004000c1c000809a04100032900e46642e900a200f445800684a1020f50307181c8000140049009402e00c0c5803214146401400000c1e404140c030b0060710301d5011140c1c0e503410346052207a4159042002403c0030351900045c401407004840043c019541c1e40f1076181000c55039155103554910464040e0340c2c11003480000b0500143c289001015100b060907030242c1001d40711421506198480c00c008000c2e80e5403990303401c0c114 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 446150665 1250 446149415 446149453
    0x61a10030509060402040e1014101203230c0105151c050a080d060e04030c0203120301050d0314090a0b042408160c0f120306050609060d050a0609020309 67
    0x102a1860240a1420410441c5940e480d0140009100c0e6460340d070018612101005060f820303542100c02444000c00340c0075400742204003034071584070700104180b0100f0050461942c00e26400e505965080340d0000d6490044001050948018028076082000455647c024094540203109074048886c40319038074030800559403441107113041000d111080d1100481d40c003180f00e20740d894103e100f0300ea407031a4403001d0800070110b0341c001040c44c100354002d100070300d42c5c401405941c0b03038800d5040352080c481d0400091110b0000340f1515602103160042e040010340b00d025050840c1707910510050a005090002480e80141a0070a2030568000b081c00c000c21416411080074003d100340e03e21501108a4070010640c1a005207100d00140c0908066203485105401401e0000d810414281c1c03070300010724100480d01e03101c07004d5800190405230049864078120048892140d4001c001c3e51900e40f80b8824003014042c01030480044580d24a00010100b00c240000c41c81171580701d000c9c0c4501401c000640301d0b4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 446151915 1250 446150665 446150689
    0x6110c130e060603070609060806060c07080d020d0e0f01121b0c05120901090b071509030e09100e07030903120f150801020a0905131808040501030b0105031902090d061a 74
    0x1080e88178503020458150002d035600c040d10100d240c01340d00340c1e0351000801d5180c4500c2221001c68402c0600c00291680040340c5012481d28543c01d0300d803018280502118030241c0c802c00182e0040030b90400d041c5641c0501c6049186000c5c280c00840d408208003621082e000f4941c034110b000c42e00c20404001006801d0116001445040d0790f031504066014000800d80c00d42030084201000d00001d03c0380501c07050260011300d8124450007070069058030303d4004d01c49000c072200701d80240903c6001c111301d8050f1000780c109072004a03195003002d64418a0031000f0384116402074041c0300d000c0c1a0108414954001d010310b10540ea00c0101d10701c0c1c10750050701c1884509a0100b0381c1350b48144006054942d012410004680b0100c891103104038903500a6801800c00d651004030601c00100d1140c00c00000d03001500807a04241c17800c100301d809010054a4500c4101c404a40a003000d12700700741c1003036042c0c0c050070031248058030008000b141a91140201c441c0000400303c1d044242400e41110b14040703200e041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 446153165 1250 446151915 446151919
    0x1b230d030915110706060303180b071502250b060109060801120f02180f19090f060e070803130e01121a1b0d06030c0801090c06110c130e0606 62
    0x51949142c54072800e80e0409841c00a40c16150507280c208540e001d41564191900404c003002203665900d03010b400c20600a20f07440b0035500e140300001d03028203c00b098030401f503040200b008070700e5110540480258010b20f0031154001c405001461854080001800541e2051040c0740860070070b94005040d160855000108002c1801c005204164041e8200420a0fa101481f052602c183d88006031140141100c10030005102008008400d03201d0705505000305110080c541e403642e40082d2030b00a032151000094069800c503202c01002840715072010f9148900301041d81d207400e4a40c1450b9055910520745501d164400b035200b44802d0317071002c2d0590b0041011000c01880420b0994861005100070038800c1500703d88000000d4044071040c0a8248000180304103d59801d11005600300803c42c034002038a078110112030105102070148109036815400005400c0c8075441d0075400c88607041c0c032815480160040f014003641c903485010708034a2101a0703a40100f03200c011003100c540b40000082044d8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 446154415 1250 446153165 446153171
    0x2b26040e060405100b070302150a201e21011706070c0308070f140a0201020a09050904020f0d0501060e0f04261c090503071a011a0a1b230d03 62
    0x801c01c0e044c00e10440080b00c0132100c0058440255080590800002d01c031304c2000562002d007000b1050f2030603031203a601da81c40d240c40c811310035402c00c440c803405015a6442d104154030940750f822180305810302824022081a100304000203400ca12040e00030f001fa4032144480149107115800914144007156000d0040d1420601624090b03c0050010001130514001c0c410580364041c5d5091041070803903c20032140c02407a0f60f848060000900030743c001902c1c1e0303000072022940031441789880044940190713002001000b02d41c1c0d003441040751500114004503103030340da034440c00502c0c454034800c0e46114212819060145250600b01000103004c2440011320380144201c1042e25066100d0682d11071149880c0c110004458182d262802069120340142191002003130910801c096518022000424502c1000c00c1d40da9605019184066007846c007041941c0074440e005038075200c0d801c08200d40c1c1c0c0420b140150341140307031201c0205541540f075003807861100d44055940d800b070410030f604038412545020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 446155665 1250 446154415 446154421
    0x209010e040c0e0603010f1a030f0609030f0c0a0b07031401080c01020a03110a0f06090303060e09030706151701060302040501142d030615010e2b26040e060405 70
    0x8034850124502824500c43c4583c4003044145e2002d500c000c00c0100001d001f0080c52041d00000c9103080007604504d4441c2c0309085510200f80c3d000b043c0280036542901c0118101480d0985d082d40a41010122920354803c26071070a0110f02100d40c3c890280c025500c2c00140d007011105604281d8005070042c800b05c2d0300c000c18520301c69070b0000759000d0b082e07054602008040b440000660412040d1200902003d0043d6406d1083c0714042c0d03c440c0026200e03803002c104156807401a0b04a02404071110003098009104140115002d80c0101c03c80c2d00100042c102c401b503c80c0300305c14400e1102c02e1031400c80c0c1c1d9291400e00850a251058a0250641c81000000581380000060840d081042c4003004a401c20f960310110300c0ca03105031061190780c01000c3d584075151a40103600003400d0b00c0b41e2280001d603524007101c0c40f814015441e611441c91f421061071444207810500810540c040d804032400c01d8102d00c041c68102d100743c0301c03030400c91114070306603a2180780c1a51009051000b5100c1ea201d2481e00c0c00b4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 446156915 1250 446155665 446155673
    0x7120603111306360506011704150203010b090a09050c0f0708040503010504140714010503040308071202040b0706060902040803070f14012d1512150c0c0209010e04 72
    0x24891101089444640103010300c0384240c050f1005600c03000140c103070500c1049007109880050301c400440ca500360784000c044036690100b0b8039002e0b903403035022559440440c160403400c1328150364000c2c001c0903280401c02d1411501000c1b640260301030260700320b0100310030300d807480c0000799a03000b404111820300c80f5042c8180014420f21607400b114001c11030008092080084440c261002407100070020001d0b458a400c2c0040c04090444c0300915038090010041591210020000c0c2d40544c1070f034605055075a1541c040d00c2888011300080280010401d55104c0302c4400d0004001400e50300d110681c0368801860410195800341c2c001040450040c4020702456074000140c6100c0f5411070300b4424442c125043c02648000c01e9607000d1050350070000304044c01e40c56208480c5c18080100a400b008806606000341181c4840545403201c1e074414008029000110210781300d12402903100341c44492500030b400c5c04459045247c4000302c3c2a42c070030f40c070652a00b003003080d006003007800f030f2400d031882d01e955 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 446158165 1250 446156915 446156933
    0x3071220010b130e01090609060603140d02030906030402030a02090702030a0e09040f0807020a0b0705060117030c0d0e120303040b061f050a050d020d1e0c0504230301020f1207120603 80
    0x20f207003601c80e0341d00c41c1c4d1401004400d400c040c40e4a50012004c1000030114284030000c2d041a00086e1501012050703c420040c0000824000c03214555024600700308001e81005a2544060b00980e818880e64042c100540c0c0c50f401c1050155509800843d039401d038402e00071300012401d004143c4201210800c001c0810310a107401e840c0a940860300741c2e96915a4400035a10903401e8100702550036011802c5820810000341c210305841c0e01da90241d0b01048007a01d569aa40719a0352040d104d6000b0006602c5c50a014588004510000400121803102003040c0349207160821a03050300c07403608038003d0100600b4130801c056224103140885075601c070103c10001c1c01900c100f80a02d4100900011141144185903050f100100140e54003032206414068006040e01d1101c5d001d101d03802d103003606402807240954100c9040314494641d4042c1a01007405c050043c8000c245030a8055400f0400074072243c107101c0081000780c1c4103030040c04040c203041000802c4500c00314107810b00c0702d242070020b0010407038401e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 446159415 1250 446158165 446158189
    0xe010e0105070204111207020304051311070609110d08070606050901050a0e0709030c090b0901060503130305030402040b0913031209030e06090a0b040803250b13030203071220010b 79
    0x14501081217400381640c0380451040da20b00e0071000200005104010380d01000a20844070100c0d15011620007a1101404941c1e561407089000c2e14200001000261650030010405000c1e011240e410382041000c034003004001401142c90f480b00040ad9010002075219403000392805176200034003981003d0115100c100a80034140703d20942c040020092172140040702c01035035118101c2c210950f078604009004d04140f080ba40d00c00c00f192000460214844c5040d02d1040d03002451340c00307014809840c281c40ba030740083c0040c0d030000d407074400c0001a6160302103041c0c002e07003041e0500786004446090060051500d903400300c0d1800c0c104550034012030f510844c2400e00c10011503500341d9401d40c0034001405050943c0c0070140002c0c020900040f4010040301410540c800c4c00f00200b0010314084240600b00d007074070b8000b8440b0743c0c40004552646540000008561f210380100d07407030074859458924880c4005000780c0c000401d004011610590810002118001e0f40c4c0001e2007044081000180884140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 446160665 1250 446159415 446159419
    0xd051302101b150609200f07020301180807050f16031e0c030b060109080a0b0f0c0d02070b07030b030f0c100c140102130b1c09020607021c030e010e01050702 69
    0x1034444507010b40b15464036807000990240c42c41d9a0b041121401c08080c00661042c0301807185010020400048461408200d200c603a8521a1828080060410707081c0c100f81d0050360550b603105460099613407101195100c00e8058140d040d02c4d984d032031070100d24018005050b09451340101d001450110204500d070030903680d2041d080c021a605ea02c035080e44480040401801c2e20011103400000c1c001b4000303006001e00001c0e42c2d14100039441e05a555904c0c0c911000060803c1c2c075060005500d378a12103446a00f10508040e42440e000040c0c001da8141d070498041a5140d9100721700344940c032030f054442c12000020540c0070300f00602081104c20784984100182a0164611440c1641d4840c4911880200307903911110510032801c81d845054002d4002160103c2d071840d0003000480c42d404450161400c0780d80d0310403020028a00716681c540a4080900126004031040c08000010307520320310000c1600403140b804256030343e09420003c10050a14081c181480103c41002c1c0c81641d000c0c040f502c3c05501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 446161915 1250 446160665 446160677
    0x120206031b03070801061b020a15020a0c08061009060b030402040902012006011d040b0a180807050a11060f04050603130c0b120f06011b0201030e030409020d05130210 73
    0x44522940c1849076000500425600020402c15100c0d04040a603050350740ba50344190319003010010889140f00441400303588050700000822a4a010440b026401409407041d6403a1b5861540d0304603003000c1030380100c00c2c203410040030058540741c6104100010051380505000b11440c1290341d04840c0300c0500b01a0180d5225015101503900800031048152540e81201d005074404600143c5c884900b805117078408031160401d11070f002c00d5002d0403801240c00c40d01811243c1c480603840380c01002c02c40208100400a01d44a0001c05c503000007400d01c21f07008030080c2c005010301d031078035107001e199003080d540c0705d06810302844024090400568007540c1c015140d1543c0c98450000d40c48004c481203100820651502c0d01c0802c0312900382c0050252003261803240810340d20348150004000e00112071040c0010001c40c0c505060402e90200da4241d14018100001c1051080c480d2606680c40303030300800701880d00001c4024004000c1d204443e40024010084050603045500081c3d244803540914400c00407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 446163165 1250 446161915 446161921
    0x60405011d13090b0a0506010f08091f0606021e100f11040b0406020d020105010635270a0f020613080a11040605010c15050c040f08070e06060412020603 67
    0x551007541d103108401c010984041e440b81050b081014080c5035500b110103041481c04150300c6800703402994050701050719607414403500080201c990000050820649102e165640d101881508800345c0003020101c2c0c0100c0c10b5414010f010349044188040c60210b0005541d0b41400c01c072021410205402c51600041014007518514030f0141086881070072aa0000081c0001e03481111001001124000c0d0203480b03441101d0034069080360007d109820201d003ca44112000040d240801580782103000b2000314110b00d4040307000005003088900d0f41c0852451800c120850b00701e8607001d0040d0546d003000f00240a072540e142c8918017450107009014102c0840c000c10603c0042c0040c00140c00403004450f24075945040102940303c83c80c0c2c00c1c80c0254586807011503035500c96006104aa80c0110003052204588001500101001031800d0b12002003800003048048600840100500410f4001e2a2030750800082c94031048028250502c10740c0c080204110300c84034034001f040c074550111041c944a0f0303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 446164415 1250 446163165 446163197
    0xc01121104051201020706050f0f040803040609060504050c0108160509060c0c030a11011e05180406150e040608010c0906030c0905040914070603061202040203041b0b041a0906040501 80
    0x40550740000354080c018283e40d11070154154080c0644501a0205106076244d0b803000382c288140c10760744485201114000980441d001c0401960400c0c450400052020322076140e80c0100c030410780781141c1c2c9811aa8001050390385c85500c56410565a001c80700c00c0c131800000c09030541c81850314181c0200e00100d0800b1070f1900c140420000803f025060318507441c81c62406116807d40f4800700342c003140490361032080d485c0314940750005411250322481d143c00200395a5815000b828800f9962280c3c99580110f210b00c02c0c07590746054170603c2e40380d00a62808000410058030311039000041c481e0324211a14a0059106d038140342228001c0c20001809002d5480443c0d00382d0036900030540050130241042d003081880314507910008101e5040e80d2240c0e40301d0501700d0647d84e1600c03a59403200c02d903c0042c00540703842d13401035400c03900c510b03600b581d0440c01480c0c4041d030a980d580000044c44022508011900f010304e005948111032000c0549420509000070715507010f0ba00440b4104094407520400b81 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 446165665 1250 446164415 446164417
    0x1e0705030f030c010e0313060e130c020d0e0607020109030f1712150117151c14062a071505180d020703080d050702100e1605030c011211 60
    0x180002605582030880200d400355078a03031007030510100541c6408459450340d0300200541e0030743c070030541e80703418421700c1c00e00100c5858501011040d0312107840014441c0034402032081090850803030f00601140f90003244003900c1e01507e01615070190404019001c0140e0b0b12070007403c15242d002c041360740c00420340d00381900b1a044181c8104003048001502e04c02841c80c0e81211442044500c803a160600442c000440c3c18010301c400302e600801d00c85020a400e001c41250440c44030038003038520021031030f4075680c405480d0340b4100709540041000109916000c0c0c1803081541c4041c1c0807901d60f40207850300c5c1d60800381d01e24030369010350303001800704000742082082e8811078a40c0021090510a43c10648900b01b601c00706800034100c1403207100c000048440c00490000112500046403600f010000107940014010040c00340003180500300001c10100928825000c221485000170000d1138034030303601010305c0002034111b01d1003a402200f500c2000d82c0c0c84000f8030780c040681c040c04601c0300c080c0002c02110b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 446166915 1250 446165665 446165669
    0x5010318082a03040320031c03111201230a060804020f01030902220f2d0207050a0312060e060607110103110715180804030b04150f140c0c1e07 63
    0x550000043c0003040c81b16086216040c1250445281c000a0400081581e030304055100c40e18080500080d12107a58081d50200c5030f07441074020014a48101d00c3d0901c007404900360400c0c1c50f403015001d0802c900740d806105400c1d44c40740c156041c01d201d9041500140c686e0350000c100034490007041d0000125a44250400d01c40981d0291070000700e5201441b0f000141c084400440402610307141d900307580c0642a000d602c080600142c015641081c14010300101340c8001039886407800d400700881c10000d2420881107182901a540d031b04052105a40b0300000d5403203d0340040e1014a150702813162554494080703d000c0c0e1340c4902a0101e20f281e2500680c06003003000c107040c054100c04102071045c4040021414288001ca00d0301300500080c2a4407103040003103d02c00501001c030b040c0410700000b090b8001460304503004812102108100350803280645107140740b9400321607100c001200700c44c20360500344c1e50400000080300381009041d102260b07032a4400088541c02c079030056500750000606000b4400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 446168165 1250 446166915 446166997
    0xd0e0108190f18020910050d0209060301060e1306060f0b030711151815010b04060f11100207030807090303051c0b040f0c110606010f030c030e070f0501031808 70
    0x34241420f540142000290302c050f401400f948001420520100340f2400036208010243d00b550a01c5070240f01030820020b11030394240d0750328840072900c40001280d4903c540300c662a0b40e50300860300d01d00a002e0f511f6552180d401207000e04030502c070401030b14013a00e07030001072403a101c40c5e8500e40400851a1000070041c001e03030190701c6018806280a411aa40c5e07800c100501181c400540094940e002c94409210f41410ba60080c0014041c0a10804010b02c030008a4500040c80c010302c80c02070f60a2801e07900c041060700d5400a010380400d60000083c603481842824002006071031510702901d248034804a052440b240c0c2011840785500c1e99000940703024014104120905014100d24010030883b01810041044a411640c04c4500003c0c0c080c481d480c1039698001c0458030316007e0300508405c105100170301d615600207070401c034030401a04004040c002031445140d8a0a0005811280f07041c5000d00078900c0e104899002c1090107040316258001c2007100c040300c0f103d10340015501001e05480720 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 446169415 1250 446168165 446168171
    0x50c04110a1706060a050c0f070b2106010206040212121201050406080304270e2e06060c0b0903091e090c0313020409080f0406020303090d0e0108190f 66
    0x106203810540c007070204035555498020341d10124102000034003404030b030100ea201504000b4a00214070950103002c0282c40c2d41b048a07640c480010006060121503005504182e50200d1044081c000c1e0305500411100d200c0c2c00e010003420200c00003074540c0002000603004045010503054910b1003040303154083c1c8211805661600f0f10450551400c100a2003801e201c2d9050107004036007079802004550449020000c40901c0c246942da8414160711000d202d541710950303440615031414014404010740f800c01a0f58503010341c1e14007061141040e0b03440408400c692030030100348100b82c4c211184885040e00b0007130910082c0e031288102481d41c46295070b9503400041c540000310854100808141d0300030001c40300c404d00b660740c54180c074020b408211313183c142c0100142a401e000d814150b100c654102d01443c800c86c58030a049003441902c0e4000e40c09400103074000410800c40d06005e11228445104914242600a41500c0024803c500c080c6c910b80348408041e0b150500c031102c0c3d40c0400b1460400c00014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 446170665 1250 446169415 446169431
    0x20f090c0d020a18092717190f03050702070611010e030f13080d0e090601020f0303090f120309060117010204031203090308071e0e040920031c020304060309050c04 72
    0x80c0440c001c50819044d01060a101150b81c211a000700250201216040c86c1c0c1500e500c640d4001c444141041a01e9001414040f60700c119000c9000b0904100001e043c1505184070b040004d2200b00c1a0b24072508241c60310041c0220716a002c118501241d034180350091051002e12111401051049004145071100040d42c04940100750040d02460080c4150807860940d11140d60361210744182c00c110000d440c440e41c02d0424901040e003180c000708103104035031341610f2002c0005c0c1746070310654940324039030f101d001e140142410400c02640041c00c2c00e02400e0450601210196643c0e4041c0220300c0c05200070b18201003409802d40c183d40085802040032160038040c000090000c1003c3c19047d80064040e03c0051041401a5600f9481e000741c0750742c00d004207801c881c0c100c0c0d0b50241880000e03070050b02d50004c0340c08500d0901552a41c906d02044280300e2041c0c1c0800c140c541019500d901c80707036081c202c010000b02034010007558100c0b0800e0801058172802807504a0601c02400c1ca581d52051804000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 446171915 1250 446170665 446170667
    0x306060d060b0414061908060a0c050715150501031107061d060c03150405100e0613060b13150c0f02130c0806010f0302043020040b0607020f090c0d020a 67
    0x4c07060081000756800040c000d00c103249541c642407940120301566003c6400724444110a41c0590079140c040c2c6030807401d1000799070310805555100700300781040507151030394072040c00d4a00d1003030401040b013405c04000030240ca000f490044d00940a001e0045651812104120880320a0880c062600c2109480c89444c102c1001001600150761016590a001d02054420f0420384601e034001d4584d0741c80c8074091844c060412a041c80000c0c09140c03c0340c101c0318122860f9919002d40310141030041700990300d42c030318220045103551240c0d100001403095520107403070041d00035540301c0000350016003507402a540741c0040f400c0680703640c211341d02e00c6240c0003003d58065800704240f030141009903148400d812003440100d0aa008501804480b00d062071102d6803980107000f40740030007120001d0700d014440119101e085100005440c0040340d06198400f000d900e152610130040301000403900346051070419008608030030088030403c1d01841417070022807040900d0b4010784107801d2201106565403400d40c80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 446173165 1250 446171915 446171951
    0x60405180a1d0d030b0d02010813031101110d0b040207170306150a031401060504050a21050109030804050c2e210b0112091a04110904030822020306060d060b04 70
    0x1000380c0000b0b10f0483d85c0003052505803003007401c0c160140d5451100307841c0da54034055140c103842070071010f1002010b145592058280945440c4501d480700070368486034841c0c40c540c00e0350381c1400030301e220368810826a00040c00b140b0308032180e40444a40a0b4580ea01e8401040007204c0b52480352400c2d880c0401d59481561b0f042d08200041101c440074001c26980c2c610064035140520300a150340900c942c1010f10022220341d017208026000e0030780c121143c0b80e50ba02e4941c219105450194001191a02007009000c0108101e2004a00981d00e102a80907110b24140310001c2c04008509032070145d4000b1080a442400b0f04580f6081a0f0750741c2c4901d101810352071000707180485040380480c0c64083c00441d66941c038414882495000350300a00c8500c0071070400c0c611401c00038000c82c5c10740a0311512820a0302c0791502c507807017035219440d041240d0804184208202c64036400400c00c110401c0249030040e01c000c1407894100c00706545007002000c85190040103446543c0126400503d0103442602c20340c9400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 446174415 1250 446173165 446173183
    0x1b29160c20040f23091c030603081209070b0f0711130608100b01050903030301140102150a0203010e06120d03050c0d020f181801030209041a0a09020a05060405180a1d 73
    0x182c90044604c0492581d00044100b241c410000b0b41000f541c41b0180001c038081c5001001c0c883c40d000074055203903a1041e070030390040381800d82c040701c4110401c50b1054007080010090b02040e90858180114490494074900c01d20b940148188203080c1e40745a1071700c4058850418100c1c802050003400d8454051594400c2103001941d0242e080c8000034007254018402c031542e0901c0078018525580c20b203800065031000c00707030389103046100702e2100107448100d4181003405114600e002595a514007100e003052000041e2020307224410034550210800e00c001200099814542070200e02641c034134180100c1360050a16003203d950001231503280760340b01c0d00300070705280500c098031000580690061001070301d9510055004400c040c4010b0001d40760580c0c14592080c82040043c40d43d030005100d10142d01019201000610744492655003145000c8140d94060300d0181d0382241003924110015804601440e080c030000b4500001064040b2284c0d00100c0b5170030384811100140041002c03540381d0741d002003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 446175665 1250 446174415 446174441
    0x30607120b0a050a031b0b0a050304052103072703050a1209031a06030a120c110103020c030405090a0b0a061710030f031b29160c20040f 60
    0x10200c0e11401e0710b0400d81c0c04043e2840074103a004074078115680c403200701c0d12414103101c046042d4000003a528845d04000d00c1d02c0c1c10b00303039070f0f45490381130502c2d0840c0303840904c4000c1c000481400040d01001101e280036258400040d2030440101400b0780440e83c960340691880c85000c00d1054004400e0010004100c207802e44180b0b9807003004201500e00303d9440c031290000600240d010328071080b260581c1ca11180c0c000900905030345180301c41e5522198003104e03040455012a0003c10200103120b000c41c0308400043e001c0c2415480c20491001c1c0350741764480c03401000d11920101c0007240b029a015400303100d030120043c0138940c3c615202c04c1c0c0078101c441c21060560301034001900107146c2081c1000c2e1031007166803100c0c008002080b87c2d179041c1c1d020051011121021030005072004041080d9511a81c02a0711180004440c0450b200c12185818001440c01e811180c8035011040055072001a44c100340b03030880d03421079600682e000c0c40580d4040444405a20505004150090005135030144110b0070403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 446176915 1250 446175665 446175671
    0x15020f060603030301060903080711130c030c08092104050907050405130606021b0f030604030305070f0503091b060705070b09011205070e041104050a030602070b131203021803060712 80
    0x1190700305550382c40240501d800044107504204000740e00d03280500b100a10684040444507001e9012a100001c466204020300c0d460302014602c1039054420407004041c02c1c84d11490a2034002207142da20010600d086810b40c154400551203000001c00ba1030183c0707001400030303c0605044500a00e2504940039040c4140e50300480c0d48105030b010705c0303240d08503841e540180c584010840f03082c107485071507441095037101b240806210300b07950500485208074482d0300c0000f800d04014100401129502020b1018000204240440e40000183d4907580210f0030108071148072440300490350a000300e0748010641d01c81c3d0140464912401d402511591000303a1f9120141043d00f40c100b02500c02c00c0da0804042814261280342508254010200d04403008181520740781d80c7e03001107038601704917600581d00c840d400314119040111070380c0740c560803803100d00f40c00003101003a46a4030040380e9034086420503d13030300044100418010594181c0d01300801002d443c0b040c501034102a2031010540510490a8a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 446178165 1250 446176915 446176921
    0x12020309160506210c0405030a24111606091a07020c100509090405190602091305060603070c0f0b0c121f03060e010603080f070b090309090a0b01030615020f06 70
    0x5000d001d030307140c0014a031104113030005800402558500060412185110200008120358800300418070007a4490348400c90685502c60035580e910b45507005150303140d0b017803441000201d940401924122604020000080080d070319021008144a0388018a4101d484444c5a01070b15a00c07102849001c00b80c00340c40724141d400040040319161841c200c404501d0900c007001c050f041407500554000e1182c01261054000503009030140f440400007110825000101c0303141c141480422000d9040c4410b07000c0c001ca090060000f100c6000090940c01040083c02c00070060014010f04000c00c4e60304100804103501b04503c4895069021024000100b003030180840c1d06081440c0c048840d00034858500c241c01030841d5681006403a0402c1c440f0555900c40c2ca01001080800d001004064004c0080e81c0d640c805a143c810000100102111416002405640503035202d242480d5801240341380d000034621111801600204059003059003501c003070400c9200d8607900042e05030a0b901c82e03034044a045503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 446179415 1250 446178165 446178169
    0x705060603010c080708090a05070f140303120f040807020603010306061e06080115090f080616080108070504020c1f0b0406050a0b0f070503041e0e0903031015120203091605 76
    0x41000070781d078001901c0003001a4520b4811b14140b070308504d0340d0007914a100750740c1c1c58031844c00e6900c4c3c11900ca1500891820029040c40400000300c0f08000d030051130a104440d22440100c050040900480c007030900005010031a0640880304150b50003000280c0381d58503410a040107001c1400380c01b20f600903102035900448204c0841400701c4445940b4280c0580c00c01e03410341d069401c0800e4040c03e11400c1c0d0f001003114512a189d00d0040d01d9604000d1503180f6091500c00c940b00404407803082031194405c01030100e04e0000c0390480a4440a8a000d42e07507484100c541413525409078402d42c25071012000090620070150817100420104071814440a40c0714010859001007511034803c0e003200400220005a20b45409041964003603019241010344d9114000c806400101740d9200e0481c164a0500002010845803900002e1820040d42180762031342c3c035a140310080b400b40f040054140e50601011314800c14031082d188031404004d41d140d0610800340c0c2e40d102c4001c1ca480b081030441103808078181c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 446180665 1250 446179415 446179421
    0x4290108100608092a0108011e0603110f04080c0118080d14041d10091401090c0903050a0b010f060801290903030d02090405060d03140a032c06012102092a070506060301 74
    0x274803503220342d0754401c2e1420340309500800100420560440003032004005102a01c2c2c050402003100e90301402c41600d91a0005280820403116002442803400091100034030004441d0340b6000c490030001482c2c040713448204114000c070b91026500700c4614000c1c2090000e09d9070504e0081c444829203141031034452403440c00f520701c10141c0822420400004001224a039044003030141c4c0f003400c0009040b07440e500c0320741c144a440f440a4410b09001401003048088400c2000018142441c08004c1035050081c228100c1400800c510f0020164030303d0a003a00d03000070f04690041d0401011240e5070182442240c020f904900c1404c1c3c8a6440c180009035142001400b50205540c5a40c0d10014540180300000d910340011718100100b580d90004410500d061119608120b2000c3c00b0394410b2400c07400240b49480f0341608400b00c0e0f1001c99849084505000c07410b84a21a41180c0088440d5200205c100205030200d2900300380004171505c401520382c1800040804034090001d55040c1d03500c101c14503080e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 446181915 1250 446180665 446180699
    0x2100c020c031002190c02120607020a0b0c09011706010306090c021b0a0b090108090a08070317070e060901050a02010e07030f02011205060108010312050904290108100608092a010801 80
    0xd149034400b10707500e1a40306e6401c1c503111910044c0b6001203152002501e901c0c00004403038020160344522600028808401c807020360003110007503414580b20035007000812108841c0aa4140f0400d40e001040c940c1e070007900240003074402d81c0420809840080700096403903105805601d915181400d00704a54108000b160082e1125840307010b02d001150001115600b00041800b1485e01038001ca0000080e0501c0041a01a02a40d2600c00301c80b08449085100d840280c01c907403d100000c01c001035103481d00ca00703442640c002402d2207030300c0c0c6d000100203a0240490600c00394880c0036100c80401003011000030f041210b8000c1c0e0390241b5a48122100c1d0040380c1c2d0a0744c2640c04a03900200400000d031411440980903803040c50b10600700f404800124003a550101c020004030b036103150300403400e8810191405074120b8246030070902400c10180070700c480340c1180544020040c00c0750000d09220400c1210344192140c14101c6c40014142c6c11003501c500c01880e04a50000300304d0000011f43c03038a6001c0b0b08130 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 446183165 1250 446181915 446181937
    0x10f1a04050f01050f1c0501020306010329010318140d180b091302040513060905060301092021070f12033002040b0c010b0103050405030a030c02100c020c031002 71
    0x800c0d909001c2005546040440155807080960116041a01d0086c091701c040d68030034400540c0720300740b200000d000d4400c803840080c040d481840802c0d4400b82c143c05125101e8401303013030010b0100722040e0860400020024050320341d480d62004800c024000103503449030b034946170341c410091003220b5080302c803003409910500c075109009200d00c04507840c01f013101d2050041c0c400d10040c502035844003c51490f014034025504803030f81e60321082280d20118010954800301c00c038020046416242d6030070728183d03500c0c40800f40c00d2100022028440e120151300403581065401920303202d602c049420b90382c400d0140612551344a036120005021200781d0044500183c0c941c03280640c003821514042404e100d0141d4100460901c0b0b414070698400a100601c06003056410440e618012004200e007592030000415040600d40000c00000c60004010384a8004803032a0120b00360304801c0003240b1301084010100741c11440d01025000e040e4000542080c0b102064080d207010501440301d40b000c038000d0701c91040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 446184415 1250 446183165 446183191
    0x1d0f010612030e13050a020d060603020c030d09060603051207030f03060b0304030302130e13060608030a0806060d06031707030816090902220e010303080f01030f081b010f1a0405 78
    0x41c002038001d43d0404109880a4450f001914424290b0703010380e5815107101c00815400216030300003c0c2c3d03502446000e0304c0c05003419854408a1070940355684521501050515500c81e4120104525500300800854220f0700719135401d81c00200300d102c2d5500c1180c04030301240b071080e02d02c01500d000780206021240515501403d5030740d19201a00694015403841004084c80d03103001c02c20012034000c99002c0c48506a1a401881c03031481c0040032259150480010ba41c130a10143d908a07138858002503000100b92012034440740c0046440303000e408190070050041c020500500c1040d20b4a1000d4200d1600a5481e004c10f03031140400b503450f00b4813041c804400541c0000043c415a8241e40041c01d42440d00d0341000a056031000c008880c811080c0c1180c0c0700ca115030b1004000b459130040d011500045595211141540745a035525070402ca4a00014844240425201041162540118401060a4024003c07a5401c442d014010030003903c0b020500c00107501702586078201485014131034541e1000d01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 446185665 1250 446184415 446184449
    0x61101060506030c04211e050c09071101061e030f030903050a030e090c120402061608121512031608041e0812070209150f1305070909020f0304060b12011d0f0106 71
    0x8070f107c1103504800b505d6030b10900300034080c00e455000d08c0398415a05035071807800a130b808008007801e56071a94401e440300b14039081d80b05524a01c0400315030451b42c6c8800001010051031a090741c0e011191740c009021401204d042100b4141c0100c54a80c094030110341d42e031030641d1015070701f01032401030402e05a9101076400010740103050120061400c02d07100c80700000b03600c48550790808285c1c03044002e00200201030043c002200c021441c04191120212a4103100443c62001030f40d807402070b0000304100007081c1800d601030040003000c0701d02074121188465200003400c1802d18102030701e0301c10515035100b554008220281d503201624102c0d9801020840b44e52182506c003110345140c41141c681c0100790030b031203610b9580c403480240512010010041924a030051020705507a0340c540c00102880e00401001c2802e064590842e503102d980404009480304110010804a080310f8020f916a076281882c1c440901c0c4c801c40d1032100c0c0315070b0301d41200c0c0c2440311212040c0c00d850840c030581050607205000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 446186915 1250 446185665 446185703
    0x1b02030a0f0521041e060f0e0a12120b060f0a08010801050705090f1c0308011a07030903081602150c060c0f0405061c05040b180610061101060506030c0421 68
    0x200540140c041d242d40c408031641300080701c0d001c50b212030088500d02e58840341c03c5010421f6002c1d04c410020707180054808039a407034455240c018003100c001030070004401d02c0916035065a0b404807581c07281c094121034030362162014003001039018550740004181948000900d4000502409102d8030b6030f80e803594100035000062180b000c654010f61170b8041205085801d68041840452000e07034020f070b442d80d0455250941c5100c004244042c606081e403400c21008010a400400b124101c0e0fa024020039a07440e100b1002030300803051b4840007076015042c204030b400c40b040e80c40003400a041d8244d00750f41c919200d8880820705445954410b03503121106000400a510744240601010040c05072140d1001101961410480300b0442d01101c0d8003086000b82b01950749254801c0b100c4802e000c00511190a003040540044d5915210700d40401402c8443e40790400400e4211100400380607242c2612802c007600300c001c1c076401a014900100c5208044408251002462585543e4101c131200c000d41240e021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 446188165 1250 446186915 446186977
    0x16080a0b060a0e0103021c0219050403111002010b1f0201060501030902240d050109020a0f0215010e0c1204050c0f100f081e070e010e030102070c181b02030a0f05 71
    0x142044c14194240600100b0003080c5182c20001c0580c820700594400c200c0c0da034900c4505210142404025092101b84005060411004184042142c1e800188245201c04a024014041905401c10012441c100030b1100e81014030b01c0c41451074000344442c54850004408507103019001a5010b0744800811800c4089a141038032181c03001c2c0416442c0c00c04c2411128150750f07081c1d1160140741d900054103d8626404400082901000d102508a002e00c10590b072400c01018000c1541851941c0040f80a443c0038600b02d5550101e00d100c0030100346028140307a5128000c01c1480d40c00748281c80c0240b142841c0c1b4003007152881a04ea19090864943c0800485400300c00070950410790f6208a007445940c00c048000c540709030840d950311250070905400060000d03e010208030300130b070300500850300081e1031148010195415000f00052049860301c120002c0c0c030400c48010310341001a0f0078800340ea5404001020122030a40f2004c11219015200311041c0c880c2c01001006007161401c00340031007140714 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 446189415 1250 446188165 446188187
    0x40c02061321021b0105040b090907230306190503120a12091407060e150304020402162303070c170f030406180909050c0d081216080a0b060a 62
    0xe0125180c201041410000300ba00a841c407a026a0002d43c01404c0380e82015a0410410801c0c0780030350400341313004020f02040c003529020510800c0c1000008400c94031a184100c52060b02c04090901700d02840c0c0380358220360094403498014410100303414608100c3c1d149420480710080d0043c94003404079540640c16800065280040103005211084981c0003402801720391802644402c81240d010640c0c82c0c5042c41c070798000010311001120401c516558110103c186205804a40e6503a90700c910000e00280716500008540390001c0c02d142051002c2020002040c0c0600e80080c075103160408090390f0340380541e110080003445490030500450003d00d0400c0103440d56102122421401c0501c042e0641e00a90800e000041054490044184000d000308004001c00b502c01c0200070059150113490740b01a885150003405a5007440c420060f16008a920340d001c400c1901c489420b00704180000f03504640c1c880000112135102140502d8654410810300d0000200260324114a114041d600d1100c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 446190665 1250 446189415 446189423
    0x209041403030717181902030309040612050f1216050307021315060908030d15090f0b3f07031704060201201e0d020a0e030c040c020613 60
    0x50038000300303428003000698040c2ca4261074040702c000314184001c2080d40000e0070003c0c100c3c69007a80c445854804140703418108035124040c04240d1032400400d10b0740c41881c0c0c203107070000c0c94880000746a002000112280d1841103040c5c501d2415903000483e5101c500146041e00c0b110b00b00094000c8200710100014804c0c8a502a80d007003103840d4000075892110107201c442c070191180c8042c003680e0301e8003400b100600114180425900e0800414aa46c1e01a409240025a035108030841c02500d10104110040400b880240420f9508824941c0546010401c01303010310900d90b00000c60700812209410210605055190a4035050041c3c072420030408102c200e01c0d0041d0f41d40800424440c100e0030f80c5095803000410340c3c483c50040700074216985005010390041709040c1c2c0c640350500741411240b510340642d48071000c0c40640849692144203081046c1d00051000841d5513480d60041e0006031303030381d400320103032070782d44410000380402d540007104104016005580066001d5218071455040540a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 446191915 1250 446190665 446190683
    0x140702010e04050a060510021518031c0221010b12040201050d0f05010503120309030a0c020f060307020a02090108012c0a0507030b01090f1b3207060e010207020d020904 74
    0x26401c04203040b6141581c0c1000455103459091040d0700b801717003c25542414901c02402201040e44540c84070341800341c0001c001c10640e0fa408901180204150740d80030390544401c050031a00c940d1110700941c04400840d0200391090343c000e03004a0b12038901070480d5550200145040c40003038418102c440b0080040741030000900010b030141003140309001c03600d0000d400004a9505003000c05160000c03561282410060400400c00440d001006a40b1400d000713003860901040c3d1031000450b01902c2400c8980c115038080200811143d00040c1c95a0050083d5400c04550f6204c905103801c2e20840d04889450b40e034500d050284594070b124841c0d60000c1008141d6080007403e56445080c00c2190744161400c3d5204001803040720402c0c4560b441c080c031b05190030000a403002d00590f50018455403402c0130312906001e080020600d10603042c100d0304503c0e0303c0000c1851107107401d8415030803042040e12010701c8c0010030b00400005208841d604e54005102d41c00c84007203542040285c0800a1084a190711 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 446193165 1250 446191915 446191937
    0x11011101060902222102091513060e16020601140f04060b0a11010b09040b130c0603020a020f0120090a08060106020d2607031a0a0308070c0602030a14070201 69
    0x41c9a10103040d084551466185200c4c0201c6103460b0f015100d50015201c00603c0c2803048a10b1500312800c070b81055040d40c4a1105540e18045003015500800c4000d40082c0024080100203c0e140d000070141e1704101818a100c5e02e4a034580d22200c510742c80c0c41c82c00340e44800014000030240982003680d0703c500a041c280301100c50b00105003030350185d030301a40b80140c0118254071003c3c0c10800c40010070a18034001c0200e00748110000d003c0700700141014200e0b0741444082000c200310010049003241e00038960240003580d81c40014020b501c00050900140101c01003d45405010301845100c51440101d00300bd8205d40c000c15a05a03000c2c04006a011981a00019400c0ca051144600800d020780250409640c5039602901504045c98014542500110741c1008400c10940d1180c05c031044c0d20340094484001e0340101c03c078520402e00e25600c111014000001c01c45440000c0400b248244048001075603100da0503a960300440701c070745c800700302402000c3ca12148a04050f0551500504d0301100083c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 446194415 1250 446193165 446193179
    0x12020f0d0f050403030c0c050a15020c030304140d020313090c05071a06040b04050106080415061d090106080706020a12021606030504060c050313080c070b0a050301090c0c1101110106 80
    0xc1c0450440301c021603141d504001c00d15405201c0c2c43c180c81d8840c241102e004011b9a01e40c0d44864404d400100001da030131a46407014102c0d941610f10405690b0200d039a41c0c1007604000340310498912008035544280149414103e10200603907c09800390b44604803d40d080c81c030301001400f1010381c4c03001003040a00100b4041003202c041050f400311f50002500490400c10140000d0300c40c91000140900e00b02401046aa5801501507622030f40081c50300d442c5404c0b40061302c003c1c0909a110504a924000d9a0701c01010581140340c0115400802040a241c3c3c540a0340e4450740d0905c110409600190310603004a55007143e00d0820803040d00c1580d411480a400c0c2c40c5c2c61450700c1e0400e0f000a6520010402002103500c60b0018419240c10202d044d40b5084041415802d02108020b103405404038001592210410440f00074184100c0b02e540c4402c29031900130002d80003441000c10803402c09030410490b50140d10176480c540c0d0003121070050b410000f4015546543c0c01140b0300050766983c4c400003401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 446195665 1250 446194415 446194421
    0xc011b0501060b0c010b04090b06060d06030c0f0e25200106090e19080a0c021c1a0709030807230604050d0909021c0504050708061005040e0a020112020f0d 68
    0x64110407a80f66290011000002d086600858881d0b0140303203040c2c1214085030400012a61051084801d1a603403544051400c010b09015030006040c120862400300b0b10321054400c1c0820342d1460030341c2000700c1e40c400c518014070010107240700071220450401264100d00c80c40303000c4003811030180c0d22050307405210005400c4074100c0d4041c601c140c0e039985150030f540109021101000703601464440c19515640c4643c0d90394801c1c016141c0c180b0202c10340307410464603000340400040c034007031541000344000c0d81444803840c0c0a0814a00121208000145440d40680469400d8a400c08100c6051003c513944040d01e044030011140c256502c1814050b01101d42004680d216903c100003030f002c4030701d8200010740030304415003005084074010700070322a01a2080b100b5900043c0ca000010480e5201e50802c00d08107040760b000440180107110401070440b1881500e0000c03101d0075101000300704090724040f6114010200000e0000328184100c2d0001301107600506a0580d031a0b9549241182c603800c05011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 446196915 1250 446195665 446195669
    0xb030411210105060a090c021b0a031e1115030705030709170a0b1b030a090c1203030501080d0e1c020f060a020a170c0a0b040602040302061b0d030b030c011b050106 72
    0x740c0e034407079081002c9401d040c40301a000b002402e0f000e00c41c2000c1c2400203920340840050300c003200809009100d00e25a640c01e85000256001601030b000a184000021090304100e1000e80d007038281c40c03ca0701030a080c420250000725042080a0307046032a070b500c0c102c9031a0702c0a0000810003000e1480440c0300d000c4000c24040c440002401043d81003d60319041484100040040380810f5a1100141c140e42c00c003000c895000480300c10000f145c9503079107040c000c60b4400b508502e4100200300303804002c243d0141c0c00b50b41030300d0aa50480c1c0b1707001c1012404880b2600701c007900b0341c0c000b980c18051989003200d10490568051005000d400030850340b4001c1246c60700204101c00040c0c0c04504150b00303104124015940300f90124030b00368034100f007901101780da03190410b4008110444a10008050007890f60655002d158020105035030b503001204074000010070f40e045c503150f45c068401d00e00c00c0f060282c410011041d80150240448c0d403500401902d521f0000c8500011008202c010400020320071310036400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 446198165 1250 446196915 446196979
    0x40509010e0f0a021e030901110423060403030c060e120a0c061a1c03020c0a030f0212010c1b060603050109050105040c0f0303081528090b040203010b030411 69
    0x10107450b1100d00c0314030050024250041c414410040e07511000c40c0c50744804491422080116501c1d20744211541c010288038a590320286008900415400c02c0c10103460500030045e1089038a5400a008001e810b110700d00c8001e01241b0301da440c483c005507140c2c001142c645804000d850303000b0700f1202014015880f04000c00c00046c1c121044004109041c800d60100a203a9a03400d402d00c400d12010444c4115142420070b00c5c81ca03220500e004140c070030800308200b200047d09a00001d65649861105400d40d40f074124400c0308040c18001c0210320511130b41c1c00c0c00078995100d21880c581d030f5103142001c5511681c2078805613203030720303021001c078009008980c0c145120702c0000409280a08144044181c2c0780c0203a4400046001c0410200e03903c6041160000b1541d040c0e2150480288005041c95074920040e0000490417031070f0541d0121310301c1007103080f1162081d05202c543c40c20000c02c0100d100901800403281818400301c0c012070034281a00c42118005041182a036030003403455110501c41c1d640c545 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 446199415 1250 446198165 446198189
    0x2040b0307140114031009050c07050d020307020a0b18041107020301141f062f0618070501052104080702190501030b0108060607032a05150108072904050901 69
    0x361a07540c1c040c06840c0c4610045545a04504042500042030306c4280300386508152900040b07948140ea0390201c807035242d030250454681070400103000e9200d4000e1201603120f006040c2000824002c00300496070030b0600e24250a000d4440c550030440103128003040c40314842410b100f0b040040e1001d200c3c1c0e600008030414003c409251140300e656444003281124520a2806201000001d0f000300740b20003907a58089594950750600d02c411052003102c8410740003584114802c0c404103010604000521740425403d840c14241c41e1001543e05101381100c0d902d4800e41e19000d110b00306110240141c1140c8280062468000107400040c1441d030100d80c0000081103140c01009a580c061148804992081c28540f1a92910b0000103503a80214000682441035010b00c03480303c810045c0300000310080700e1085080700b10f406e042c601d03510b080031b2000c45080303451100042101c24000422204071219621050010900a03141d60b20405400f034810300501c1d405d10000c101603441c541014041e1000c801d600c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 446200665 1250 446199415 446199449
    0x40231051902040506040b090609181015020a06020d020f070c080601050306040c05040b0a03060e0f151611030c12030712060803190216081f02120a0902040b0307 71
    0x210040001e8248101c401481080100800e0303c500303056170200c0b101050b41075212840c280c0480c88030301c0348070a00340c0d04c07840c05030404080a00c01c6192502480c90052100c00c2a41c4403110340d101c101190000707401503031108988c5400680781da00100143d02e0640301c094200788003460264520b800070202112040903000040c001108100607981c010304044004180c0e84c180750715910b8035041c55020309070003541c0b81d160009094445a10740d4000710340c0401e040050003103d480c90780d01d070210100c0402c05401900d80b03003480800c84041031405540410703070452420110403001c0d1048021442d076106140800c0c00100d050381400e00603240b44119181d0b4980e0b0705d01c0c4c03403030000b03090007807a0072030002c07244c68140184004030f000400d85075800c6e07a16140200800c005402039103031080300702d41320f0300781c804501d80400d540c200410074464206ca010010014140305281d51000e034016581614000f0204c500058104800d5401025041340064000600400341101080c10041c4680108520000385001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 446201915 1250 446200665 446200681
    0x306080610033309020d020907081b03091002090d0503030f0a0b0301020307090b0a14070807030e1c0210171503070503010b0105040b070201050c0706020105061c030804023105 77
    0x3d0040c410906040030329100c80302240c0808080e070000c1d1076207030042d5078000000c111b4880c146d01d580002c3e0000c0c083c00341c500d41404000d00000c800c03241d00011750358050101790000f0340501501d003d00014409840d6a00240810900940200c00d42c568441d0b040e01203000451014001503000ba4080e0925000300d141c000403c100f5500045204d9000360700c100100401d030b42e842603050041d100d042002039500d14013030100311408440c45070f0344542a04000ba2110810041d01e0040841078425140c0081504191040003103c5a142c808200600c2828045e0001803810701010000c614107400c007151100910600854206012940780000304c3e01210310020b20b207000c101d4903009047c02c070000c0c81448c0c0070100080c081d0107503204080045c600481d500c0d0441e8000e405607070181000c0c1045801d003d954800090203004280e42681c0035610040300080c454440d18080010142c2685604950340c540da8240f041d0360400e9405001004000300700d10060f006a188078808200d9482d101156500706440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 446203165 1250 446201915 446201933
    0x40e15130b01091202010509090403030e010e100f1e0903050f07030c0b15180a2403060c080c09130921080109091109070912420b01030608061003 64
    0x300052a201300c40d09400141c0c2d0220480c4c0003124250b1b450b1071182c80d2458190302500c0c0040c2c5100e415420004907120700304000641038196081c0441c14818160000c00d0007080794000194581c0800b000c41442d12050507a40104540500c40c2c5404c6283c4001c60503221041c3c0c02180d002c40c0004d407006146002c0c0400c000403e6088845040042980060310000955071800240c801c032400e014200018540c800c82c0d442400c00d4100100758a082a01081002e16868014001218140d281400580100e0f100300e40f003d11403190030301d815280c0030800041007000180200d003001000d444140000000709001c0d2809a50904c104c40c0300e05240d00c0c0100a400044141c01002d141450b20b840e0340081640100c40081da01d8042c0c8600c119500c49003801c40d800034a58100003042c1110318954810000303210242e080380d01004299002d18214610880403000e010303144400005901800f04600c05015401860080b405050018411750313a02686400c00c003044603042c02d01d140404003001031044080c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 446204415 1250 446203165 446203169
    0xc0e1809031909050a03060905210403030309261306020f0303010e07050d062301030e0c01030b0402070b040501020c060c04150804240b24040e15130b0109 68
    0x20415600038a4012040d980d20b00540c0d4280380701a03014690148043e01441c0403001030003010b452400d4860716410004050968400221002c0c490308910017420080404980035101107104038501c2d01e86180c400710054680c1348000c2c1c800030f20488401071100f04034411000300304000d4040c151120030211403003108240903440303c01035400c00107076000700b140c0c00320459040d00c030b04131658070103500c03040c0c1e045819000345010313594035611f40701012035840001c00040f074001d10844102095920520011416a1100088590154801d40301c200c025030207500034210403480a040141403142c5074031110030b0380c81c00fa01d0945441e50700041004202c00240701c4282d01400c8560054a064a8011800400540340070741404000d1048089410002d18209101620224a0184460502c1c81c840b4000811107030301e119104007801c18148440310780302001d118031105101c0d1001d0034281b03080b0500341300e0070006045280084500203d040e0030f035201751060701da440c41404000b850800080016001c5809a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 446205665 1250 446204415 446204449
    0x60310082107060c0e0303030703020c070501050a020607030b1f090f0e0c04090f0207320d05090d0c080106030507091401050a0306020901030e01180501050c040e04140f010c0e 77
    0x307508029510031808458031140d01140020759018241d00880f4a90345134a02c095041c0000803d000c610313a816009001c1e0319041c5c60030394210566440040d20903120708640840584c001e500000d44041c001c2e4810310300b100c005000d1090501c4c0011041d9000c0000b40b6403440441d419030804d0000040050340000078100810929001d03080c0605c200d0a10300403440f07902c0c0d030151550a01e00b2002e6054055440d19944061562002d8005405000480340c6004040c0170f00c0040504014002c1000103400c18080ca858a49501c3c0c94400c0087c07100c01e9145c47d0081c0c45003845d0b1080002e4580c403d1044400860003200980320040c10b000c1d40c2c50980d580d400b00908115160001400070703603200714602c41100d82c03101005030745100100050300940b00d800b00464081d483c04000340c07581040284815509072292000700075a54030a2814001805070307004405420079407100080c001881174003980760b6900034104072072080824041307407800c1d184407082007000078258200202180c20400300d00030307000c040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 446206915 1250 446205665 446205703
    0x70203040905100302061b120d0b011106040818010507080a0e1c05060604020a17041101020f060f0403080c070c08030415081915180509060f090a060f0b06031008 71
    0x1139a00001e02034040d5924040e400f580d02e0640c0c8003084410000c00341c84648005140d1380700c01d51000341e03030001c21a68069074042442400d54034014500401c65a22981d44010380c4c07428516994a00b11181010303c07006418003004121100c080350780f6034041c0c881c07a5415910303001c42c100300300284040420501080003281c05480e43d68000264045200b03540510156001610b0b41400c3c2c1c4d08a076064000c800c48012819140140b009000450a00102d452020703000c491070400c11030380b50390303481004481c4000207e504801290009205000d0b50760020341c1c0302c440c1420520241c94180525880d58400180340d440050100a5804820a50800c607182400d04100501c0e01d11039603020403242c203644000f0280d0703a12480015980044040300505005030040705d0030305224040e580141011789801000344070b56070010300072a02401c55144600a1023010b400468059501c200140030580d9442c1411034681c031001c00c480c2c584401652040e418003050441d214580b8100600300b105c17155603070b104164 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 446208165 1250 446206915 446206919
    0x10c03180b040305030a02040b13050312070c0509040218010e04020306070f0e0409080d11090901050a0b070b220305071505131103070905040305071e0b040b07031407020304090510 79
    0x12040da0b40c480c0c0c240c1000c0341c0d260b40b4600a08001c0c45150042502c080c00400c000309290035240001c4159682501210454203d400c00c1d040d00c0d01840300000c10a401c404d4081c48242425101150802d20203418031241390034a564402051409800001c0755164410800c03055183c20082c00d5085000b5061000c002914184020000084840740d81d00558486010008200b82e0404950301c034404068100407180721850091126400761413110301c90101e000011883e03117041e40c0d8140440701307020340c540e25081150f5100b088907040100f5451035203490000c00c24484000c40c4072811414404d5403107030383d581d0702c1c0c2c640003810303c80c604a01c1000034507090800405603907181c0e0700040c880c0c101c114568811032400c006032528403960070a8848508120a110415401c0406080f00c544120010320340d4248210712814140224540940541c1080c070114010984001d8210b030803c803949804600d1044c2000b01c255400410341e00c96005038800a000c101f002cbc9140b0806401c03118150506122174 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 446209415 1250 446208165 446208173
    0x13507140f0d0e07080f0d080109140402220504080712020d02060c09042406200705010e0d0c0b25051c0216090c26011403031b010c0318 60
    0xc021440740d090310b69518242e118100004100c080000c0442e070301220283c8805002c02620340105408800124220400206a01c00e1500031225400d01d0040034000d15a00c90302000a1502c0c0c3e9899a010481e00d1401d00005c80d041d4000c980c0b0490086041d80d40e10892841c0031900074540541c01400c40d00318072250031229a02081c607c0e01b10900c0300d0701c540c5806403000002d00800387c0e01c07048260a440f00b006c0030a4401000301c50300840b449501c4a06a03610f050450215802043c80b40082c96048060b041c4000d6010704e0700803040320809404a540312902e980c918460b80741c0f980102e5468034020030840703429502d081c030071291501401200305000003a603175040c0e41d0781400102040000c0154001c140300074401c01131012406155480c82c50403903541d180c59401010090700100001c1c0c1000704180903241c1c4038841c0501c540c81c11200c50708507031800301c420703039400040622207a042c00704001c07114003904085607003071504014800002c1c12600e8220050300720707003803008100e1511344109030350030110b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 446210665 1250 446209415 446209417
    0x90b0609061806030c030610060801150503071805060c100e03120c0901030b030d050403050706110c011409062106031203070e01020106050a0305031806090a05013507140f 75
    0x4202c00e105603440d80c0e11804002400c110010403450303010310400d0100240521001c0900080740e500341ca910034140d0302c1d00e1442c3d003a5501c1034084c9001c14020000b00d40c031584200c2e030b102540a881c0c40c600884503101c5c00090415401020762195580c090040408003500b2482400c00118140f8000c502c0d0220000c00b480d05e00d20010144030703110342c0100318440e00742d01075000305401444c020143c5455480119016246800a0200340c4042c8250200400d8080c080c1c6003044204020310000c0444124043c011500c5400001841022803014032409801e5203411001d4641c01000710b005480f1160394001048088100824092107035020051115140c145c50701140c0c1c010841e85400d80b15008844010303400340200b503100a4124000f2a0b000040c00004405401112401620141404c1c007910401005001c1c040740e0b1a48102000c0e01040a507010f071025241c01c41c441840001400c442800002c440c0041c0783e142c51605d0340803410091381f0b5034809240700802892803129800c05903400016012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 446211915 1250 446210665 446210689
    0x30405030c011b0203010221060402070218040203070305070b0a02150115110304030203330601210f050103050a0201080c040b121e150a0609080a03050a090810090b060906 75
    0x10f000e0a02e9000b440c090b00750b0045040e06030054001d5580e481e00d2040781d2042e801902440e4803000c81100802d0151402e80200c1c0c51f03680e0010500350404041c00c407441e02c220005030040381d041c41040c4000000807018031801c0c004200c2c003190641c4510303031043c01a040c0f07400312640300c40c00f19000c0b00520100e10260024400c41d0007034503020082c040c4150005207544500e402c0658140b246034820710702d40c0300d5900403450031a5a0122904035046600e48807071000401e890840c00719441444034a40066081510380301040d00080103d441254100500d080b980e081c1c000f950030341c00401c1d01e4401d40d600b0503030958111506880c554501440d0600d0503509006440191414074510404110010000e001d004548103d1001c503100c42d0504400044529162241c030360f000c0c0180c080e00158803401000040d00f101c11a0b0085d001e4440107680407940341c0c0c41041d0f00800d01868503808600603a041004100724819220001181d03803580c2052244800c0040000e8880c107400d82c1044280e440c1d403409040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 446213165 1250 446211915 446211917
    0x61404060e01020304170714030c03100506061e0a03060b030f130f06050a060503011109090a0914070e010305010609020a0c1113140a0501050105131e15080f09030405030c01 76
    0x2a2070110800100c0c250b220f203a000046681042c81c140b90311100102d100700403102494040d4035135500d18010715440e540441840c40c0d1507000710343c0d009003403046600002d5010702c005100601d004c0042500ca65210020704101c1802e41011612a00050700b5214501c0601039044031242185000c1c00700400210001b020f8003820010500c41c00104141402c9580d00300340d0041041c03001c2e00e800380c44880204064401d40380309608044074416034901100441d46035200c05804180d10340e8031241c6000141c00030386c3c0c080324100900c4942104041d01481090051b000404000440d9451800d00c00c1c00d6400c55045107105500c100081c0f88505e410960b030200e580c2e40b0074a040d01d0100c2400000b00302107400555a900542800c000c0e5455035a010f03102c610800c0300c08002c01c0140d80b11070044400c0d004141d00d604601c0c00c00340080c00381c8086080700da140c40480c1c05405c1d0055807500b8030b400c0034410303000d02d8a0100b40d0030030500020400e0200c1482c0d01c10300f05001103050620b80740020f90344d1040440d40038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 446214415 1250 446213165 446213177
    0x60a1815060f0e1b160f080c010207050609101802221e0e12090616080d0609202704151a03060d02040b041d061006140406 54
    0x140e41004581000300189a4921107800c1035940300c0b64080451003c9450207680b00c80c07042e001d8135007180c003815259440b410f19041d003c0c0785444c5c0c0d16400c0c0a00491000e660410052000e201100d42c05d00040541c244564003402d0035007003101c28585412030b812002105507081030402d80d400b50701d1a00c642c6204c1d030102e40d034440c1c520990000700c0680003202c20711540d580c01d1903030070030b030810038500c0c42c201240951000b008041c0c00c0107512600c41c0300a19640e088840100b18064203881d04202400130610a041c064000349516515128140d00071004540740d0be85500041090a8042c4500d0403242c07240b50001c0658580002001024402c918075050704801d00710164801000c01c0d02030411258016000f003140c5c4c4110101a4400d6a00c2c0c880c400114000c111200022110318055034040c036070142401c00002440d500300000b0340704000c0d4840d00203555110f0352181d0f8542e0881580500d040401410b4242480c3c0000b070103c3d40b40d50426014403072050080000491040116800c41d50245014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 446215665 1250 446214415 446214443
    0x3070203210c0106060e0109080715050c1603060605090604020909040201230d06031101020a050a02010c030509040f0b01030c0c08070f050c0612070909090213050c0f0d020903060a18 80
    0x940082c02045140d80386580381c24070104942c0e070003200c18685140244c82d00b8503440e03940d140c0943d80d4125030003600d140038080c11681070407500a00203000c4040328042982c1c64094441195407645906034000e07108140c5504080049040c101002074120509643c20351a006481010920103000500000e04110400010100000c025500c036600c154000c00703459034030015055150701030301d487c2c0800e035842501c28440004640c00007441c441c0d5a68804c4c090020411690010740d4036034202030080c0c5c203003e420485406907a0faa8440c0141d000000d00e0000340310207070f400004048070800c8103014103200c103100441e40400ca2042c25a43c41e10b500c00d0b01c0010500c610b1501d1402c0c6281c044985400c0140825203009030900074050512404081e519810382036503d0021320107880f4800c00194000010308881d000034034280c3c0199911024010010380b0785820640b040200380e110701c2c020301c000e035804280021a4982800300a400c801202d80c01d1004502c4201140e0142803c40001482c1e40000c480c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 446216915 1250 446215665 446215723
    0x5040b01081306020f04090b120601030213200319140705120402030f010207030503040b0f13110102120d1a121914101418030a1202300903070203 64
    0x417154a41c1d64045e060f0345a5942c0c06071000540034144180d032080044a505100c410300001d1181e04882e001800d00c00b009a02d49a00700007010301e040c07074600c4000c0306800072040f044804002c502070206181c0380c4e0080d20062044000700c6149821070525a040c4409100c442980a01610041c007282000d8039550f48072071000900c0c1c039182850085e540d50000c1040020b058101c0e001d1803246004403180704171592a0200101040022591040300c855a9850300000c5400d0815000040c64180101e40018605040c809060707009104046800d87e2100326032a00014014140700d50300606807501c3d8210b05103032124548071201d0f946800c000500a258802c2030242c4a14800107240c3d9134004d0320401c0380d252808501170000350341801c0312030b40120081280c7c007102e910496411034156001d9400c040c800340084483c8032400c0d640c0040c15409001b10302c1810025030003a8801d042070fa664400345102c500c5103072034440d03000703140c240b0f01e8000380030306009070f01e012403c00c541c40044c0d0f009004541305180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 446218165 1250 446216915 446216917
    0x6061605010c0c05060108120706020a0e09091c03051303110709020d1b110a0201180503060a1b0203040b180d0503030906011a0405152a030304020a05040b0108130602 73
    0x1002829540c20022142c8019403c01000301807107000c1c4068480c03581c1c803818600e580d41e61031f1080869811003007004001195140e405010200e06911307021060031050740024202c0e01c1e007903c251190707030061007401b4050031916883d07020155590509226500e00104d41300039810340e112002c1c2c2444071024206442e0141400500007070403031840210b449034181100c520007480801035444000258058174542c0720b0080d040c0f004604007480041100005590045400080b001600200c5c010044c80218a03079074140081e511680c10500f0004507209059516622410782c81c854000390740080100340701071030015007201c04110115081d0045c1c040f07200302041c44441c0301d4001070401d000c04418484282d0010031030504a500c5004d50b1900c40d540c42e0320148092089100710340e482000117480c01ca011480c040a00013820b901c5800541d03107054000c5070803448002005002045c1c000108010451403c52400c00140c041510100500c2454100107070006d1000390034103080c140c1401020301009001c5e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 446219415 1250 446218165 446218207
    0x3020603091617070e2802040b16060507090f140d0c030b040b010905060f040e010b21190803061e10020307021305040b06010507060603060c0507060c03060b030606 72
    0x85003041841d030349008070942d5802c00340b450445406140000144441d0001c5c3ea1030080c0c5185180841c048402c40c07421601c9210a04002c200030303001e1000288041204001e07102a80c504d4220440d00243d40c40c1c00b0b811180c00410550a1040e400c50038072010340c2c00002a001d480c82d40c1c28007044100c502d8001040c0c60540d0f0700c000e006c22102d400100400c5610084c0724000c3d8420351190000340d803500e80325015940225040d680003d00b4802500c028a820340001e0048035418000180030440080411145c20030341d80458400c0f4a0b00444101d001c00801040400000002c200c85403010b0560710030005100c003402c1503204482c40c400e8040c0c1003c81c9076811100000c0100a0100c044008002030340781e40100b08240e10581050002005925290150354819070388204500341c140c1c1c074038006444540001c4e0702a00c04580d10b400220003c0c40c988070b10043c1c0040d94a40b43d44402d60b40c50b2a0003501c0c2c0750503d000070181050030070401c8028050540383c001904803025038035030004280208210b2220 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 446220665 1250 446219415 446219443
    0xf0f0803182b080c15071d01120504060212090a0809280801051b070c050d0c0806070e040f0212010e0a140a0b010905010215010b030a0b030d0e030f0d090302060309 72
    0x4002e01c0402816200800701320a86030152050060882c003d040e0016044445801041c44442c00400142081024400104050510880040481c0c04640403030b8003c46d012649540d000500c1102101c0e0310550540c000245d90051900038482c1c0d4030362400303004071100c150144038441a40c0c0068504003c4e421101d0342d052114080e86e41d41c0f160041c1c0a040300351071030040300101340040320034065805c00315510141c022010500c154900010300c0301c2120741d4581a103003100d03603410100b041c2d103040c45110f0040c1c42c83d68500690780141c108000c11501c1a01042d103400d8410041113117030f001401013140c1144d43e05441c1c0708455807201854405020341c1074807011071403515000c10402d101d80da400800ea580e403e0ba00c108a8036100c0d0016650750701c4100900000e12104801008116004c4001b503a0004004902241c3c1c41c5042012070324181c02d103100c81001c102c8205c800c0046060030021201003808220082900018551002e0104105404068007403913000000800128080103000c0b412216 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 446221915 1250 446220665 446220739
    0x20f040e04030804060b0105070308160507080f040e060d0f03030506120703050f0c06030702030414040603061406010332061219050607090506042d0f0f080318 70
    0x3103842c0090000d44101e0301119442d14100c0e1204c2e5951058080d60031841e419101d564058492804206110709400241e81c10854100308200024400c04060b0802e00050081c080e00c95050200d50080c024008149a000c0d40390740c200000800c81e40740440c045583c141c200015540c440602180001d4440c4000d49054481c2000003c100000000c441c081c8240030002c0d0740505510000b0004c99100c1a222080140d00901c024400c000e0203842d41c162010b8001c100159540e640e641725410369460a22950840b0041030402c8800d58250007165144e890404030b1300c40307449000305d0305103844400c4122405d01549603400103030540ca5021091201100031001c6807840501400303c5a84a000006c0c11501c6000d004d0115100601884450007545c400402041c101401d140c224414102565801e081e89070030044090710030360782c81d12920054440380a000301c1075403d0030400c100070304003030b844107005510401c8040300d480d40070900c25180f00021681c0800d07400c105842149908151050f152152030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 446223021 1106 446221915 446221921
    0x306091602030705010903050d0b04091e0309050915030d0207120b040303140c04170703080d0b030a140a142407020f0609030c0111070c0306020f040e 66
    0x512407045900780031082d162103003501d2100c41c3c280d01141c0b000909400303c4286006641c2105016a404e100c14955a0340d800380f80641200ca0458050306000c03030400305485040d0903c0140741c000d00e074450b2070900100e07031010f4962120495219214074050030010a002151410072540034009084100d003003506c610b510080028012410140c3d01d00c4680c48002c2e01c440d0f114020040054a03d84403401c0904c40003150449100e0241d079580140020000a80700030704403900020307105800f042000c02d2001003490800d03c0c4074020000204250810418400002e2401e40c0b40c2c09891030041c0c4001d50441c4645405000380003607117400340c0c9550740c0c04d1040705810450b00515280304945c0d0f9002c0c0340074400d0400e0401e940304500340c2c100062504006d607090040e0f070014460078900d50302c0d1000c6c1e0b94a0b000035072018840201020740100c0c100007160501001e88008003800600000285 = true := by decide +kernel

theorem cover : BRFrame.Cov 446043165 446223021 := by
  have h0 := BRFrame.cov_init 446043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 446043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 446043165 ≤ n) (h2 : n < 446223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
