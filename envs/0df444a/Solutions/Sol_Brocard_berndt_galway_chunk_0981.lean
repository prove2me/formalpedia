-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0981
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:38:15.391311+00:00
-- url     : https://prove2.me/submissions/8886c97f-5f43-4cd9-8902-de18d0435b89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 176258992 ≤ n < 176438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 176260242 1250 176258992 176259001
    0x5090f0c0702100507020103140c0a0e0f040501060905011101020f0d1a120c01030e160311130501030c4202070f09060504050f090d0309020d05060f010e130305070b 72
    0x41000c0700e00640e03004040c160340da42c00400240080d0060303102a0701003460051030b1804000d4400c0c8051083d030f0340300400d519101507440b055640c1c00040c0703201c5070080522100c00100307464922405004c1c1c601da484140c50140346c400010410b40c140240ca4800340d0051058821200da80700c1a1526007031782c9035003c116000201450307072041000094047c0c1c07080b184140000041c0010810b9466100213036000e204007002103590b1507640c0c8030070f00c05041c4580c802780104003103138800039010704000000700002d119484e680c0b880d00541c0c40c03e0b0004c1e109110010740411000c0d14031f4a211b084511070101c5121401649007001c952070b40c0b1010510401401090b100d900513200340700e914080c280441000c85240c2d00c80e242c1d00c000700100c0c0a413034010703031800000c00c051600040400740b09892230401400301c00c82c40c5004402500383c40c034040360032100f00d095600000384180704c400d00c070f1107000400001a40c9000c03481404494080c220601d200030256211000c25404000c884a05070007075920302c10380c1c96 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 176261492 1250 176260242 176260261
    0x2901141203070614010f030506010b0904090c0b0306180f1b040801020406031a04060302090a090614010605070507090b01050703181e0303080703181b0504020d09060e0705090f 77
    0x81110180c0c805000000354502048940d52100380041030502a10640ba0380784ca0080314204507a0201800756441100100400c1390264010002140301074408540c15055a032801e024001d15005004100c2010040180604240c00b14252116800c00922003c2c04d00c4400c5942e020000b504c022070b01110000e041a00f00c0031403044034000c0945000171175a46595070401401080c0182861850348504c1604a442d0710700b500030741d0140e80c3c0040c280c1c9990348030040c030440107018000040720020b86561108802d450003009141c020080e907209e2030740e182c1c030514140741441100c3d004402114500241a50503076030050035282d0855241c2002e8240484034085241810b0280d480544400a10200c803900c0010f280480300132244a13464104a90729243c00590030b680044047d0041c440320100000003298450803603030b0101c10105000007010f0344075404641681c1c003411454101d40d869076180740c101f15041c0706030072500301020003a04c240c07801c2c01c0000306000005000b03880c01090410100b00001d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 176262742 1250 176261492 176261509
    0xb0705070501140711070b04031208150301090c141e040b0a080a050f06070503060112090f0c23010914061e070501150510170709030816290114 63
    0xf120000c150010f458081e4000780f481c4d02107100ca203454041d0740d0001512440e034030151016a5805403c02c810311900780d1017201e084200078081101420001d1142003192001c0c85404402400f4101c00401282094500c640c04210001000d0146010118498070510301c5000c00300400c46c101c60100b046040784000170000c200507001000d2a009600c0c1c4c0b0801c011000134017209442040c415250f0503034800400399200d0104071129800b1030000000d500c0b0900c2e0030351050480503c0389001303c0410b08030f5203944040340c41d6030300603d002806103608800c407070a0200d0036100b820380920301003111034204001d0000e047c0b00b07016950300070710b0701141000c6509030700b80740300c4880d85e0503000b91622000d80c0d003007950280a1103140b100444000040215003414030020094502c00c0d02d407a900440e1084100403103418600a281c1c5040108002000c80015140c070000e065512000c2040c5101c001c030750501281101030003008150078030000c9900041621118187c50440d03082c003101081c9801110081040310 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 176263992 1250 176262742 176262761
    0x3030301080601080606010206090a030c080c1903030e0703020a03060b04110a02010c0306060e0603040f03090510020a0c0501020105040c0905070201021c0c030515010518040f0603030503040302190b0705070501 92
    0x1404048008980c60340d00042e075078121104102100c000b03889100c016030716050241e0f01d25602e900702d02d458501190007245040c0c405032040e008540b405140c6000c05051444150349020008058001c517000e2540c1401290b14030007407240500011840e40e130000e0400f0130241300c01403006407120305042c5103966980c8441c5401142d160007590f20003085900a000b041c8440c0c2000102c0d2500350040f9500303104d081540d00300c0001404203440c5884030f40f20345e84140c401038021000c0110640020a42c0c0d100c44084014403012500107004005c52f5150801c5064195004141160b2510003044041000007103030508613004641c00050580342d01c80203d0280c0f280c00b95112016141c654407902078412039000096a008556040049844401a50b0030b8180c400d017980780020001d122030500403000d1078500407090001480015081e1160b40c102003662441d50050f004614040100018550140403280c26194500d806046108042c0c0d1101541c03c3e01a003000b04006020414104000095100e007a05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 176265242 1250 176263992 176263999
    0xc0103062105010f141b09010f0804020d050d020c03010e150c0d06051e0405090606030c04020a1806020304030311010b0a06081e010305070906080a08031501090306050f0604050c0a08160e 82
    0xa0301e4408400d008a20041c0c0d1000488038240103110043c0c00086c064541861050b034500010001d104411519200d014000340d074007500c8440404005a0104241003070b000294002d00036641c82c41003010300b129408039034644950840031641044801d01c4070625842070018260940f1100ca5000100c0144420b411540d0440c01d000850310244060b81843c0c10101c1007110184030740d039500c40b0140c0c4c076140152451070705a4400e240301d0707640386403e4001c0c01d0764502629100d075080070000d00101210302d075944a0301c05600002002d205144d03200e61403211004490009010003500c40010a03000c0368144248030070000c00b0380200306c00c4980c6100c0004100311003004525a035071241001601c40104d07101d201211450800009443d00f004034281c17120f035805c44003203800c56407081c04855401c802c651406040000d2068040009101c0d807003040c0c0107030048420703214680307400713400d20040300d8000d04202040c0c1c806001250b4141c1e440300403e503109400f00070000d42e02905942c1500c1c61520441d11079803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 176266492 1250 176265242 176265251
    0x1401031112030d14150f0108040803090f19030207270507050f13060e010315170f0f0105062e030b0303160f02030c15181302040e07020c0103062105010f 67
    0x5805440ca54458010f40741c014141d040c0018240170003d1b107038044403d40b804030b40e45200013008503942c080510360040440c5d00395840c02c0903d0001074103000c00a000d070040031414102d0101495410031400000d001e0308900030305840d000c200c03a00f4860b410b01d01c8086020780c507440050304007846001a14034140d041680c10391030f1600081450400d1500d8080c1c400021603119030106650b01c42d00509051018060385030703500c141800d070300d1807000c104044c103505144202400150441400c006c0740b6010b01d100c00c00014981000c80401c1010b03098081a011200314518029824400c600403d40262600d03040c001400c036010000300c6d05502442c00e4070b60015000030956024009862154054a031085017940c01070750082c8100243ea2828140083c10703401c040c80000746c0b0381c41601c50700d55012801810000345461305844042a80c1c05500030a00408102d0b0074003245c19010041c09090360024202404031074149500354545402214145425404c1c031032205040c03000030b52010881d83c00701c810601 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 176267742 1250 176266492 176266511
    0x2060406020903010b151210060e13090822060503011d07030b10050c06060306040c1502010f020f0a300b1f0e09011e051011010f0f1401031112030d 65
    0x4240c0111a40c9a00300500c503000603c0320813248014419107005499800041c403000050bc11000058881380700e855645039816400714100c00081e0280c1e0660241419010031021546000355203aa44108107114090005010311000a002c0600c644061400d4807515a00c41e0382c120003078070f6800040c136002210b42d4050707540141e102d030050418134044411a10140c580e9414980e4a020844001d018104000001c2c4405070a985010360b81c105948004190710300314004660881c1d2005101e4181e41d03200150f049941a00306104000d58a240d001d03019854a140ea40514002034168060307504079038600354519640d4880c010401840048081d48080e0a01030101403c0c0d82204d00700701c1e104a408400024400180c5205c403e0721300005150705a040e0314100500844007400000b8209001206980070f509031400d106030145009003907004515904404049000c507009248400c150320001401400400e01c007101040404405948507608025003180362401d6001e12101040d480f0f0502c4860b4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 176268992 1250 176267742 176267779
    0xd1403042a080d090f030203030301060c050f03030705040e0114010e240d05010501140c031804060305010e0a02010e0a05060f03040807050609010e1515010c0303020915042402060406020903010b 85
    0x69103c08119200c1c0c1e2200c60b16240c1c1e200e56101c01d0310000398158020401480303424414135600c0da120b48075200b00c0c0e8101e00101c1a00741107810840b9028002440450304029950b00005054010b01c0100740d01e600401c40350300000d06801d415607020340a003440c1c106212000c090082d51800c103000b02c9411a0701c3d82c204101c50801b4010a02c034450015500c0c620030340759021000704890819007101c0045140c41c0131a280b50f02040c034240d104c40d078880e60300c050000c041f800038081c491200c04100e000d00001c00d440e00c005445880002c038440e000e000681001d000645402e01107642c01c2c06060621030b00c0e680c136481c02d54210709c00d201000b41240210028480c55403015000380c03482034415415148000f0702ca6400c0c005030344080f01c00e08010380c00c0c400c10030910b50041d04010222800381c030340545415581000b042003c8145180c0512a041c000f80800841d00150340015103601e006400000d070010044009603142c01c09480601429400192000e05a409510000b803851001d403a0142010003e00c1c2c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 176270242 1250 176268992 176269003
    0x10509040609060e1005030a030807230307140901020c0d060b04090804030c120b0f1b04080c030709022d0d09060b09070801150c0f0804090c020d1403042a08 69
    0x407084a1541c4e00302241190002d6030203903082d528054000e124101441c0c0301141c80817400b8140c03c003481a0340c2800a03032100213803140c4c3c000307060080e01c0f156641404e00000b04590144c25030b204000303006124081c6503aa001c610301c40c0460742205c19a03a22070450030650010f000030716400754014030b8412040108400100a402100c0c0140700d000381c0c499640c2422070403c40c15040c0100040a4040003480e03802400070390f29008100030914929270300724080c49610a90154000e401c203980410720b4103400b460f003008000d02400b01694254208040904241c10280c010345901c44c00c07400342051001c0b104420015245540442c0d9011b02a4114a08001e0300074003948021500419082002903075450007608250304a070850700c090405250142c40c2102c800c19582402c6030b8000307070715010740041620301c0044e1016040c1700d80c000030626081c0401038075000e1100c8100c81400102581d00d0300d1440d003d0182c80d803103900710700d4646442403400144004403079456500c0407082e620b0740c004541401d0002d013 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 176271492 1250 176270242 176270249
    0xa11100e21040b120a0b130209120f031e0c0111030411091302010318060213140312040e0601030902040207050c1e0307090c03060e01150201050f13020d0201050904060906 75
    0x2503a10444804510650a44a80c3c002c4102e03c40301048025203940750154071640c801060100040c443c6820000520903840082089090030b40115a42010389050354030381d070150301790a0040c9a402030040704207071030380559600c140d022090030300c44005d00110070341180c0c814800300f4004c0084000108070060707107400a840a5422403c0f02d180d40790726040c000d190601440c0008a0290300e1740441c0c3c01100a414111405081185645007100008441d800507201403881d510810086908020381710300000381585983d48240d0140760750008201d00502140c0c266002c00d1003600c02d5695010058018056051000350810b01c0011032405020011540c070b000010201e607001401140ca071181105949407501e0103500d03801c04c0108121440003657201d400f00941030309000c2440f41d69079100303c2c41108240d0000206009000d103400300300394288075240c0d00150300e078000980c40c1030500c2e91000513002c01c01e00a02070701001c2214019680104280c812842004009100003510381d03a100d0090407480c0f1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 176272742 1250 176271492 176271523
    0xb0d030909060b0a0203070b060411070803011d16110c0a03050f06010501030e0304090f060e07081b03040b010e04140609010b1809030f0d110d0219090303050a11100e 73
    0xb0004a0307205109021104010b000794021414044d140e15520b41c0c0301d0002d080035610036910705000703440324910380240051071f000711701c00307520384d172400c240d202921403206503014004042004000041e0714070384110b041c01c46249000c00044c1ca00500c0c0615101800080c0359105803110000002c00c0f00000d001103135000340005a03000b030b0341e0b10360064059907242100840c064105210900104044d9030040741c607184042d00c003060301c035900c0c51050032008043d54180000f072600c100300000f404d5030f024000520407490395101e03c0d51801c2e46403100c00c0030341801008030703d44d40c41021a05010311a0100046840b10b48180e45841c20409056402010803450881c001c0d00c60307007020445c080785070850030700c03405403d405103103001d2280c403d00f01030358028205c250615540d0001402550141000780071440510440140c0d610000e05200b166520a14100c404202d04503105000080d84003095907072544007403d203129144030203501b140c1442120b0050480661510390308903014140007030300c900c8100310300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 176273992 1250 176272742 176272751
    0x703050318030f0606060409020a02120a0810060503100e0402041b09050312130909140d0215010e15120102160819050406020604230a030e0306060f030c040e010b0d030909 75
    0x480c484e490701011240942d0240041c80108039a4107141c0041c20307242e0300c0d441035420707c021004200000d41c000500040c006542801041000c18400300810060001c1e400d00300d04510f0b0100803c00d22002500400c15000046000b00301152036580103480c00040c0d01d50030410700071203010002c04042540c41400d210344910500c8004100f6400120f400c3e40c410f01d0b4100030100e0604403450050f0a01c01d0003261100b0210281040300d0000740030304454982c0690250041004103004d0b1001c03090180c204c0b0050881c08018010046404d11540807400400c3e50404c001c62900011203009010720031a100c20406508800020410003d00401e00020244040f190701c880320a02200c540c0660f00501e03004d0303480032000c07401040c4619800780c0c00001d8106800400d40c6000b24650a08035244421800704480000000c0710f440c0601010f64098800d6400880242681d80000d5489042252036400366990745085813000e5000e4000d207005a1014100a070f80e901a8600288140d80030300c1221001440c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 176275242 1250 176273992 176274013
    0xd06050a0b0d0b0f040305130b0306040b0a080d030c050d110405040c0942030e010e0309030304050909100c0807081e0f09010b0a0b040311060901090e0405070305031803 74
    0x10942d0010110f8114000e51100c0d81c0d01200a00b91a501410950500030144102d15814010390107850103072441da10b00e83c1e281d0520714140001d031030441d85058825a0f55800900c80500700040c002080030b803d00c5e02043c41c02004038151014070401c0c0c0f044402c1e6003403035159540150700030300900c00c40e02c0613a001c02c03600b000600200c1d0030040ca40556000040d503c11800025000c0c40d020020100c1411020522018144031004910800315505004242c4440d9800744c0142c00f80b013154410090351f0082c40c41d105102e40000e480348568011b85120703e0380c401c0450401c1004110004151408002c20003c99102c100054880ca004075440720000b00c030800014201e842500d02c0180701e0300703d481981d40540303075040c1d142a440710003054034a0640d601c00195142e60340320b24400740103219035039a00d80d41b541141842c0c42c80354402c20707003d4064202001401816640444620115680301801c1c1c0c00d103481d60319100e414120503a00c007a000707110114071490a294140e4003a81034210440480300701e80f05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 176276492 1250 176275242 176275249
    0x60210050c040b0304080f0412030e030d0f030e0304030b0f10080c100309150c0503091605030a060902120619060806040201020a030f02150f1008070305030f070c03020d06050a0b 78
    0x4046070344a8a16509200412054401c02c026542183c032641c55581007084130b41c0140034540155105125540c100c291361000c0c180c101e03944552a4500303070050003140c5101c9001404e80052850310341d041656424243c3c40005061050b1006594480b2003000d507810034200d002c5041006890444030030151400014500360300091a542840c3c0150921564148941080e0010001c101c2c0559040711000360f1505070581d244500c441c105030f00d48a01d5264101041c031103140c80789080c40400d01d41c5030000b00348403541d0001901039100b6442074000c6111103592010800300031140c4204091445140d0503c85144900c400c070f09501e00042000b000400c0c0d03601d1000f42c0e942c0c4107440190141c0c00510081010074810111483c0c20300c07090044808801e1031481080c81c030541180e00c40ca50002c2d00e418070180001a1180c88010680200188001130840c0c440b9038580c40b13014120003070743c0700005041c803c0101030441074004640090100d00d84403918102203000d003008650001000d840e214079000b0924 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 176277742 1250 176276492 176276501
    0x10b010311120103060b041d060f130f0803040c031a06040b06040302010c020906060f040e0402090112051504030e09070f020705040c0905060c0102090607050d110316110a080f0106060210 82
    0x842c08003010207580d00c0c6481d480010450110b0580d08903440301024000362001c00c007014404c52400c0000d100c2403030201d203c051506c0d00036000da00c909030407070401e10101c0d01a002007203d40d60403071901c0381e90b81c0716071409078000c82c100d90004010703088080300800b000240e481040d114201c240c505201004865040100782c3c4218000280030a08090418015003031604009074444006000b40b0700e0170181c01d110400a400c5540200400c0006a08000850820030502401001f00800d10300c1001146c0c0d80c2c20341c40d020030350743c070701d21450f608130006041c944121070262050901525100c20b5050410000b0108064642d207100580714114000440f404d00f031041c3c005200e4251760742c0c0d81c46400c0c01c040016a510280c0c007050075640a00141a841eaa040d00900d51207208100910590941020103441c40c1049491896541c2051064103006500450400140c1c0d0380004810404919440043c0d940e501e00c0d08202e0302c0c0d01c40c00c01d010300c1c2c1300b00562102064480c66001c0b40c0d039a034014a11441903e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 176278992 1250 176277742 176277757
    0xf07050a0e0f0a06030206030123030a0c2315040e100501050f090a08240f04050d0323010905090c0a030f03110316050c01030606110c010e0a09020c010b010311 70
    0x1400c00e81c001402811251041c07a0014000600420382c1a56600007035a150404e0b002071040c1507078002d40398110294411100da01e03480540140004c841d090b110209038150a108900c03c03001c401500c2c000d40c0c01001072803034a0311002040c0c3c403640034402070032141c25000b501038541c0b21880200440e0212400e461038a045402c1650386500c1c0c1140d80394400d0641c1c01841c840c6030401080400031401080c1070290070500c034114801e088420030076103005c1c00c203480041e001094000c11041888040f440101b80d0341083c00d0b56060108101003d000351200c44800c520802054425000002c104c41e15160007a40c00b0307100c514225801d4496800800c04144820310005114113030020325640003038002c00400d158001404140ca04060005400c0c1358030710610b61084039680c0210203180e6282da094851080039103418500030310b06107034400b155940ca90204034040d0621064049140d035036500c1a004001404101c1c500350f4582e880106200c1c043c010100e40c05000c02c0c101506004180e85643c141d4806 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 176280242 1250 176278992 176279009
    0xe010204093b030c060f090d0c0b01120c05090a151505040e0c041502070303120c05091509031002120c09010804060c020109020d05030c0105010b1314030c09090f07050a 74
    0x44103440d0001c1035803011803201d140080c001444000b0302500e0070b0041500c294010001e1109510b071a5400f6400c040642007401c8c24460200111004280302c101614196200c00c0f40580c54039a035070a011a01725241e5004551217050300041007400c1031076800069500c614081820075a036280c05c18040c40a180212900008005000c1000340e825010340243c0c100003220302c0c1c0c1c2e2406440392014018402e40c42851000b41e4000e05040042603032111024001f44240d801c00c200045c00404c000307209100c3e07040e215120b003005007441180800e000c001c64403c00c0c001400ca034442d0300c5011800001e50841e50b139198641c01040d00154801c1c031400e040316010b4005035261003039541d8503501c2c60700801111207030b40b007190350b50340500006884502c0c602010307031700030720007182c445410b1102582500d8050304030300d030369207414020521611581060351003960007410460b01d611440324046480c00c50310200e20b540c09240102841903000c0040380100020003007100740c1d09055294010300c610001c8601c200380300d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 176281492 1250 176280242 176280311
    0x60501080721080705070f15020705130207020406080607120f09050a1b050613081606021c052205010813050c09040f120503060a081204050603100305010e01020409 72
    0x80350518541c801c548144203030f01c0c890500c1c02a4035006d1800d241c5401048080020034020b0001d01240308580041104902c02030502506210120301060200442e00880d00d0b000b049078000c540c0c564109801270887c110442c0c4052816200007843c61001d030680151071882c04035000a00d00690140c1400340c0d4012005201c0b4000e2070b034805a090200c00c4030100015801c12011a11765203210090501010140c0700c1d0401c01c1c140102581448126560b48c0b003200c400c05c0703040221035004034440c1950380342e22060580190a03030304180da9038480d0a4801c1007040f801d0f0300818a0080c101e18510550305d007a40c980d9815611a0706019110030100005441c50303000300348000c80d0303150405420b54003501c540340010030307445d0039958104040108460880401c0004c0700704222410490a03000041c905007005000c1d1031080760400f42288100d02940d402500e002001944031000846c0c0040150f41c40402007015111000c580d40c002d402c2801204034042c286802c05407014100d6060002001e10000b0020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 176282742 1250 176281492 176281529
    0xe010308070318080f01150e1e070908191b06140a05071a01090e03070213020a0c1a04060614060a030b040e0f0f06010f030c140a120f0605010807 64
    0x1d8800b45101414082040ca00c10013240034035080c408100310b00c010318004038542080703000e0003c0c41901900000d030b03441c000c0c1c030402182445a04240440a40c9091510f4003901c80440840d0814040e411061a80c030407a51600088031100101c044400d0103485212240361102d50072180340303811403091400245944104080301c81c101d1004040008031828000e10f880c3c0540d0701d180400120814860301c008084004020552550048014076483d030409540b4140c4a940091010f50f0307000a0404256800700345103400e107000d0348114145540040601c1e003903400b12081348000b8202150122050740c102400022883d080101c6018106802409641040404e00b01240100f201c180d4180e4803035241c82962080d4103090084e50484120b54001e84400187c00040c5403400c0e006920100640c9508a4100041008501024280c0326040040203045e0701c02000a05a06941c2d084200c10300c502070100000c2240c09102c1c000b0042c881c40082c0003903a6141011521900e5500c00d05008003003500303011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 176283992 1250 176282742 176282747
    0xf0417030d06030818010212070b06121e0d020a080406120b040f0b010306150203040512030f03010e180a0b070f0c1e0516031a071707030b04060e0103080703 69
    0x1154104a84226820582030031040030a550440d80240c1d050680040c050820401070303c4003030106030081c0000c0c030343e890764441400500e100390000902600c60a83c0480d0490b92190709292110b440f600c1102c403050400c9601c00c6d114280e1840005041c0f1460310b001884c02d001081208090b50002ca540303050924052055401101c00ea650200856039089443c070181da03503204100e1114188840051041050000501200c1054001342c20100d900810b07400c0f4107074000112001d480081d201109031811080d40039255000d151150360703103c4c40200c00421210250300c813071442104005c84010000342c00001042d103500700d034040030b00040207410006402038060720002110400328a001c0e0300444403a240c042c4018a17030324540001c0036811070a003051080400c1040c440181e2100d041202a01e555554950a0010010b0243d01800c1c1740020320081e01030710038800302e81e4410b034406c401c1d07192042e401401041c1059005100f185130403404904e95044241c9141a6644641c1c50381c40e04044e92000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 176285242 1250 176283992 176284019
    0x14010918150209040504030504050a0f05062b050903130b0c0d030b12030c0606030706080c19030e0a03080403020706090602070e040533062b0203030d060e04060e01020f04 75
    0x50480d81c2c080001c00c09036195440341c0c07403003640240d07a01c4c1d4580d8100300820250802c03da010395914500701d042032099135202d0f000c98400207201507404982502c3c0da422601013400301c030540e86001e850304041000007800880180290307035a189960502c2d41d101e81d1048240d000e0582c0445403030380924054031803540070381c0c00f0f0381840b20010700c0d402e0500c0100f1030385840d42c2d100e02c880704056000402881014242000014003610050803c0c0400380b038a05010282409000450045201301803420072455002c1d500c400d4001d02c1480c00ea03018003030076050240002034261012801031042040006d83c980c81106c5100a031342907a8041e100140c0b90098107810241c001d40155270a0245c880c144c0082d01f00c4104401ca200d5581e41b00d29800c0200050401129100401c01401075059000168171051007150b010003202609908403200ba020b400071916501501e58400c44880c500200881c60f851045102880b5038424403047c042c03800c16551403400e0703000c0c0c20662102c14409200c28499548103550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 176286492 1250 176285242 176285273
    0x22d0a030b0a120501140a110a080a060f080a2102210c0703050d09090209060f1606020307210b03120706200304030e0d030203030c090a15020114010918 67
    0x814020309071900318121020040783e00442d440e030740d200e882c90303048500003400c01e81c4900c3c41e003001c00ca0081e000007824000e110ba070303803240108444c020000e0240d0649a000101501c0c02c4c080c000c81041d168043c1d48d58803100801c4c25101e0526440aa0085a503508491003031016203901500040000c0382140524001c1102da6100c000828131042d00555000c1102000841c0203000800d40341c0712030080a091210700ea0030615569004015802c000c0d00c40c0c04c112401940d15119581da5071918030011440301e0401c0e14020406800002030000d07090384450b002c080260448100d00c40c40031100040700440b0f50303401900d501a08100004c00202c0da940000d400da0034001c0001095103440030381055125130b5580c400c010428004070500082c158032482c08800703000203407803101241c1c0c52034030080d599000c0144801c2a808000446031540c2c1c543d202d03244002d0008904070ba2810b4603010010b03001c0d281d00ca800c2403025542c40d000041101c2c0074041c8690f05000030f00d003110a100c00341c03603200c0712920414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 176287742 1250 176286492 176286499
    0x60a210204110a0302070b01141809030c0a0813060809070506070503070b01081c05120604150914060f1512061825032009041806022d0a030b 62
    0x41454429a0800c020f040400c0c86640043c1d5440d40b07450000d40b86c61060f00640c1c03201c0480825030b401501c031603200356060101c5824961080e40c4500d804e034614403e0250f050020700645029104209800700074101900b2075080111800b40c50b51030844051104640340d031095032105101300001d0030503800402c0d000c1d0049042c0c03441d0005503240c0d508030420a030b0045e80250f001d18071311040307030b5510138403139a5080c0b8034034000e40f500b8194132803102003080191005101d0346c1d035403541d0f010181e995841c1000420080030f0a0050041c0c8000030000140215002d40c0540c100307060552041c540030311248480d13454203520600b4131240002c2d0964030400100100c1d040f1195040c0c40f0044c0300302c0141d042c42184421410000004494001e4000c03584c2c500840051600b004400c0420b44103030303080c510343c1d9034034145096183c4c034000700020044d00303d210010244c203500440c02001e100258004055066050701c2d01c0d215104007001524105000541001e502c0005001c0c5d001c0c140e20a4002000c64000203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 176288992 1250 176287742 176287751
    0x70b09060f0f04030b0604110304110a120303050a110f0313111e01030f060807120c030c170c01050a08010504090c0305120a030b0f1018210b060a210204 67
    0x1d0540040d40442401c00a208020604108210024003c9907015106039810301c01c20f08a4200007001c2d01000d003004000210280d0040781545a81c10000010680c90514a00208003414042d006040c16559000c02a0801d13014080304810715040304c0c3c0640c0608000791450751520010408090800c42c216903016294540d0768295a5032800c015040f044601401d2007006000c00140480d4824049102d800341800c034200144c481c0461003d084802c5500c28540907d11407400e8034001d01503410090410569200100300d4440e04021a8080c510f507008690fa03480600005640c2c41c0160303d0302c42c0004100310010b21590800d070b00300a020512806c070401210b9104e9641a00f404030120442001410101b09070070607503850300448001074001d51302e03034070f8410180000c43c0f079452610721044203200d500916091500c0501b01030b10000d19680c515482c010a0301078030003c000045403420740d041103012021564034074101840c0750072107901006d00c51503502c14054039075103100c0b802016684243c0c0c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 176290242 1250 176288992 176289007
    0x61e060f01050a0f031503210c110d02030f0706020d0212040b04050607060905120306010e0402030f04080306010903051209150c0705100c020409081905031303030b0a05060d06031202010905070b0906 87
    0x1b946038000a1071007011890000700c03003c242c00350165500110380c0c3c1003082e0402c011003c030b0381c0044450f403500000d13100190a0360365400800c0c80c1ca0260a0818a00c2c030565600041440e404286521038170007030350a0301c20030700d108200d040311801a8001c0f6135444c02c04120800c41ca1403c08000e10390507104004c0880e0940154991711705200f101c0440444a40c000400c02403150390110300d20102000c11a02103055080501714405051401480102002c8001011610b03da006104820045030700400b203c3c3c9a144048a10f96290084c00986019011017982d08103901c000d8829203804010501c002c0202c2840c0204200e1030a0410004905108442c0d000c1c10241e1034030300610381000c1c029040f4030750f80c8030714502c461886582020b146040050610912603580d2041c1480c4032070b180c00d494042a036130302c92000112507034030b03a070b02107a0f001c0c3e400501c1143c8146142c10400c110780c001c0b007400c01100c4c208101a8244e0783c80203001005d03038004610502007031404801a003000302c0007910740c5080c00e0a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 176291492 1250 176290242 176290271
    0x709120311060405070504060f030b010e0a0e0708030403020405061e0f01140c031b0607081506040909030e0102010b010813030c1a0c04140301090f020f01020f061e060f01050a0f03 79
    0x1000d0f00e0507036240c0c2200b0410b00c1070741030600170301004014400038811800d2070f585491000c0901070040604014880011800c44034031034005525003000c0809540c18165616003003566a03000d480101d00880c1410001a040d24002c0d2100e94009044040511103190b940c0c100440034030900a4603040c0080c8545180240c0300c410040c1844582600c011981d071080d09400e00034492900000d1a5035620281c104040c40c1d0340001d21035000f00d2000040a600007030400040c010380140c1d004081458941516201419484010724451715000e80003044940d06141c011110410215020b1807016000032010000030b1250030070085a5000e80801c0422210050200c01800c0b000e5400c02958900890140050368082c4828401c41004a00030800f40c40d07181da8040c1c110a2160000c0c1c0716415502076402503900a1140000001000741526145c2c0340480d082107000000503d080401e0002c1000501a420500d100380c0d0300500585510307003480d40705441103601d10100000c0500301030f01c0e200325006040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 176292742 1250 176291492 176291503
    0x2010e010609200c120703120f020318011a12030d090506070206011d06011103120106030218030304300f0c14010305150402090a030206070606060e090709120311 71
    0x21100b840841c46400700032201c0c0d0000f0040e401d0416010041041c00855040001c2c00c144404803d00f900e0f0b211401818252061088100e039051001c0c200180743d00c0e00f01865000350710562104039440005a480402d0a0803111a02801484d0703210310700213070b1700300d103030604003040d2440035102141c0c500f841c0c0f84600000d17990f100b841101c0e21361014040c00882601407001a000d0805d2152005a445054480016440010b80654107015404807141e41c280e1050088445c03910544010400c1541d51b00c40040007988001e2f1822201c180e40300344401d0034600841110200c036041810203072425000b444000580703903030442c900c9850b024118000700040080308000d5403240a18500141e59180c0010195605140301c2d0090405180c50100300b40c100da402c486114031a019180180c0300e03010784c40800c140e40d9094001a51000020452004020098000200303a840325640c0001070785054090108441c400d031004808510010000d01c4100707a400c4100d244d66002e49040f10400034504159030405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 176293992 1250 176292742 176292749
    0xa02090a270b07020c1207030305090d0b070c050c22050a021219050708220c080102270402042301090e0703050601090e1902030c0903070608040c050414061002010e0106 74
    0x103001c040c00c1003810364061203920517954055030101821510209440e4881c401804001d0501c080450705401c01d44072001d103510a50351042d406d00c224209507030301034208240c683d0121158443e50b078250802e824020000030308005182c0c0c2d0180148409036241010342002402104129030901400c41004070301120540114000e0114200ac0c4201c44488019240024140004d104e0040c0030300c1080c03240b50b0790441c4c903040301052004243e1124039200490000d240e100101e0341d800880c0125a01c0010314501100b00d021070403080103d1035210600c003d0780102d01c0340d002800080407440f5001e418182d0410783c02501407408910a60701c030000b806080d2415601d1400190b030315000c10226503004051a4003038100ca442e500521714181c00d10009049400021b00e484a4010000c2a440280102510b00c40000101175401103605c1f4a0300500b88a0116025240700740030100001d5a42420301c01c0c00303000364a800498103141d81e03040500c203516072032946e40f0045651790042075203040c0c1e082c0302c2c02c4080d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 176295242 1250 176293992 176294003
    0x1813090227090303060a12030e12031201080625050702090403030b0f04050103120c060b03030a050309070915091a041416081012020303120f01060f020a02090a27 71
    0x488003101d84040c103000405000ca00d500c2002404910381c0c130074401404441c1503003403100c2911a289000c80301d80c4403154249402c040c9800d80c10799650304c01300141c42d40396145051001c1d1070303a0350141e040d038581055540100c0b030321016103134032683d132038050b0181c81c09106030414a1501070298041a01d2050440e4140c0000799074481c0303d16149443e40d040d42c5d000741e080301c0501c81541103031035024111555203521410300c19210902c10030813009070441c40080c03074010700741c944a070002440074000e17602c00c40700c6c007945004142010848503450312600044980e001c4040c2c52807420314802400a0840b58010034217088071501ea0301e0240d481e40102c284c2c00131a404540881c0c10b2801181759404a40008c4009004611040149404500c505001101e200c00c9260b0238030002800400c0c00c5d803040c6191074515117100010410b030400750302e41031412601c0540d903103024107042d1030040361181c80780e01d0000d501c004e054002c594011003e400200020700d4040824403448018012076460000c502007c0350b0703 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 176296492 1250 176295242 176295289
    0xc0a02100f170613110901030e0f120d1d1c02010c1e0903080d05010e0c160605100503010903090801050705090303070b090a08120402100518130902 65
    0x440c2840c512440391010903003803265a40051600181a80500014650500791400c0016119545a00b403800c0d031800f29140c100b14100c807580103140541e002c0040580131900741144101d48074000199421842850340242183c0302c030400045d03c6641c041c100b0010095121503c00551403c00681001d01002d00f0008020805a8000103001c0e5058101b0784020759240032410300c4c50130b8103e0309290101000c0c40d1614410019140305482c1d1407400c1d08050240480843e0f0210801110f505c124145d40c1e103050004000d603151a08165148500c4400d54201001c84034401c0c005241c50f00000c0d00240c07610b8400312100d84680102c0d007103500105050700002d40305c1d181001804c5007842032541081c481c1c50882d28010102c008a90350b481200401044140004000b5208030300c18001c00e08910392290030240e03218046442c480c0c0944065500703900c28400340c0381480300540104112408400050020761885000000f040001c1000300e10196500d5259030001006a540510041164250808403270 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 176297742 1250 176296492 176296513
    0x608031803030f0f03060f1008040c14060f0903030d0c211a06030901061509092a0c110918060906101401020717011d0307110d02040e01090305030a0c020c100c08040b0c 74
    0x2038040465407150469000000302008cc1c1d0312202c084524a082040c90540e803900244042499841380780c5802c0f41c02840d2200c80740d01580d007c2d8a080c0d290303801c5460620152031a01e40300301210b00d0300d074008900c00650100302d820307401d1a501440d40700f5216000015400d54683e040c480070342700c500e0440d00160030f010090180003080e104d102c040e80342c0300070030804004240c07440420031007218081c80305100301c2081102c20800c900e154595401005804042c146c00e001c0d5000c6403450040500301440d0103032400090703032120001540741c401c0b10a02844100145810000000030304c520500c10304500424101068010850305004003003001b10000040d0f0002c0c03100824004041715025126582041002001007480c0168030b0915600840c1d60540c40162840010700030080740001c08103a5080005400c14140c100010314481c00014070203000c440e580e1b22040b030301e40840c1e511035548000c00c580c04a2005105517224001c051086441724585610760098050540206050300a151b100d0003902 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 176298992 1250 176297742 176297753
    0xc0c07180606020c090402150d0c09050f0303130302061e0705031b0303070207090f0e0a051005060420070201032a0906090602060a050c09040608031803030f0f03060f100804 76
    0x1000240b440c1d10140c40410500070010711051009030020740b1950b0400c01900420b050741d400c5070f445464044003007104465001c0701a24103005803141500c9200826400000c0d41004002c0710b15094000400e03034421070941d8200001ca03049400d022003880c0176110f07010320103900c010080c48420700403c015074689a0340f070300440301980404a4010560020300501600d140c000480e0b03015940e00c920301151064045c420b00004290f45407042e10b880c440e202c42c00040c00b02c081490320241d1018141400281e64000c103001c1070381d10001410700750082d25190381c035840f0482c0002d041014414035012464403403496881030000603028030944000d41600010b02c905800028030001000c090401d4041c091a00c0d42c00f82d200d10b0002c08020149840d82c0009100501040880b480b81000a204114894461070101d40c0c039044900144030a240e1400c00035401d2600200392030030030010042c0d8030701d4030306a06400d09458101800580d0409050003914285940d40115001c03148842d40e1449102c1c074050812 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 176300242 1250 176298992 176299001
    0xa0b04050d0903050d0807180e070906030c05120c1b1b0102150403110a050f070608130816140a06020702040f090c060c0c080303011707060305060907080c0c0718 71
    0x5042c4440040c04000144000c2456940c255240c244007560360ba50300426245c00706d84401949242c03064010206131304848850640c050100303956500310031512a0000e0301102c02c0880340c02c001c40c4061103a9100a01140c85072580240201051410040940c0c07990b50a01e1008000440d50340003480c0310500000d080e5406003808600344001c080058141c2d2625140c440d02400c0541044504000444a06820010802c4050340102220910109000a1a251851400354000085480d408254000d0884800540d5650807281e035906d40100a100d0010000d8104021903410141c0f11400700582e8040c0400ba5a00c0c0c02606d025036240544e104000c1116030540c1360300461840d240c041c030081450100108240d41c0d150520b180450003a042c0140c00c407c44d07500c242c0c0710780b00000002c82d2202c00d4a00001c4e090b0402c1084411960304c0d0801a0162002252000d4100031450300043c003007803040e003200d900160006030461400e00d4100a032030900245802c01d03140c13408020f40d280c0701c21049104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 176301492 1250 176300242 176300263
    0x1f080705151b0a1401020a080406020c010921030624030506030a0c06051c0e06070807020c090108011a0a06020c0409030e032d030f0301030f02180411010320030a0f0e0a0b0405 77
    0x310301c0c00f1603500d809090b603040544050b101075804100308100033001d501c6444030782c1d00418400642d0207010207d04442e01c01c00c0d91b2000003420444c0010340640c0070000420070407084503081c003050305408021802040e0061407594140300758003010f000704000a00a40c05403d413545c80310390b1014a0901c00000e2801440520783d60752502150411110010500ca5001015440c00c074540ba00c802204a117402c05942265501158010001851034415230000300c03e001e0034020303180700c40f00d030104115088846100b12030242c0c12006030b401040c505540410309040c400d042c84c00300c1e0320140c40400e20701503690700b80107000340b864440c60b50420080b103400602980700360700462408500c85031854542c0010310004092412044000c0110b50b41c56030610021070304901e02040741c0c94941408034201c51412605170100e480c1c280700c184a2039402300250901c500c40c03660546951642000d01c0c000b041c0c1d20f02440d0300517640b0784610141d00c80c24024021018007540e50b8481a08017410200d003440e01c0e041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 176302742 1250 176301492 176301533
    0x302070501090b19020c0a1e060c030c06050907090501090b010818030d0b27070e01090f0302101202040f030201020c0406260c1005031f080705151b0a 66
    0xc007041014054011504d00114100342660300d5441c07410181d01d0542600c903115401030701180c01003044214004010300e20b0446845014405c1e03651201910301c1d08000d003016000a49108140e8003055481d0080c0390841c1c0002d0485503840ea9034625101180d000f0b82180c1400b586034100000750350b03404450941c015210034164440c1051401000b940e9102e01502000029141c881c040308644d80d458048582d6094901d4664848210301c0c01c140300914119014408100b8042400c0c0c1c0710f522401800b020354400803459207800f81143c00b00945200401055020000d08100e03582000d803d41c0082c0000302109a458078040b4110701c00a4204014a030a01d07006500d03286082008049406503c0c2560322400c0941c01c100403c0750441d81800849000b09820604084d150f002e55548400114400d603043c0314038030044060395181b407030305814901c90286075074403010080c001480c2503888100c407082c401480501e44000c00fa48040c0c403821096074440d05070056280401400104002c61018900c801c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 176303992 1250 176302742 176302757
    0x30a11040506010e0108240d0c050109060302070503041703130f1503050f060d0312050907050906040905060105060a050417030c01060b03010b0a031a1c020a1710180f08070302070501 80
    0xc0006c048560050101c05182c11010400080d8040b5011040c2600c001601850422446040070ba10b00b094911806000490384031002034180e10074820f540100d980032000c1e500d800d00c4d01c3d030903074685401c25640e02e035a800300300031040c103031614803803450014090162201c03000e07403400c80e000f220204418111024503041c5801c0000110318032400c1c580c003000850b500381500c01d41c0d080c01c8402c1c000540c1c0d810b112901d4103050118a020000782503013141d204171055441e40d0780300010301060700c070001b0340240711364841300041c001890900c0c0078001c0403015140071402c03e541e07402c0c070440034211001070784078981002810300d21156080c003611015090b0a40d10030710319450107494108a124099102d010169941c0c2a50983e02c3c00e040f8032080048001c154a1081c8108005480e000d07080110403403041d2006d03a80007540f4561443c5092560f148040036020004140c0e00c241c02603c1a11101c2c96000c046003c4c02e170000d82107600b1898002c0c0610882610b80c00d080c0344c0a850091a81c03c00760501203030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 176305242 1250 176303992 176304017
    0x30307030207030f0816060b090a020f1819090204081002120c0903031207020d110105070203040605030c04050603070203030f070801030b0112110603010b0d0615080f040c05030a1104050601 83
    0x4070b02c02126809442420141c0740c5080c499014002d1050005003c0c6010f004103040c00301a8010300c603d000b04440e00159900e07001c440d00e04034480e10f40840308886e0240102c01c41009440e80c00c011020700600850004041c1440300b602016094106060b0650301040501c18840108400b29040e0001241180ba0000310300386400502c0004001d12144007000940b0700ca5510b05100303940c0b22004c60424491207041c20480071f9250203402d02d41c440021021440c01c004160b0500800380607080e142c011314501410f01d1022980ca0340024090a002142004006003585941e00158800e0301141e025584a040c50103212524050181448040010540042c0041891008403030b044881010b0061082a11882c29141400707a8840980e40901e020000150164003103004242070915000100a036644800103800130180a400140c001910500040c55440b00e481700325230424054454660641e558800082c68036100000450310042400340d015103e0515000d516042042401c0c428500e020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 176306492 1250 176305242 176305247
    0xa2c06060705031c09120c1a010e070302070602091201060e011a040509041a010e070909110412050f06070e0414041106210f04030806061c0209010504050d2003030703 73
    0x70030510700b600d90719154104811344280c0d0b00c4090319682c840d00b19054040c1800c8040c0ca4070725910020f5981c81110b6890702d2502003d80c0b0385a0503220300035042032942c1c46a0000320f009401c0303480c0841e0308950802050155940310364008441c9071b081c01c00414a50f003010103611039144181e0040d140c200401c00700034400508036003070f101500c000341d1b500007241e501c03414400c44d400ca044d820b10220740c4541c40041400280344410501c030749115210074801d99070325098881184e5074109400c1260f1010710050081c022000085c990f07140c001c0d003c652007440c2c180019030900700151010404111025a4812a0308240c05080d651624040004050740340a407079080d418040703080941d22400d000140300d51001c440410350725000e002008603641340d20b8013a83c400c0041c1426142a404607611500051462030403074222590301c0600001c0d100c0320303440000044040e41045400c2814058103210204250304d400288107445406901e48440398400441c03800b40c10790107500c409009400401000000c81d8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 176307742 1250 176306492 176306497
    0x131d07030f030e0a03020d14060907030b040b060d05030a0509010f0302030601021e120a21050c070605090304230405010608130f020a030215031e070c030e0a2c0606070503 75
    0x70b81600b0507401407001000090b00141d92030300b0096100340d401c802e04050101641c0b00400c1c0c0c1030b15200b21a6242c403000d201307070b554810030b1000910010035140080c0008400381c04440c4c00003006402d20841807401c1c0d481e9419600402e603075100089010800441c07035070f80000031020000b45801c04514605003500002d450302c940501c00005010051720544240108000740100700c038100003129121301c01040b0051000e000e00c075a241c16a50074402003150f11005200c1d09000d803002030070541c50f220280c1c0d0b410b0054200205100150700050000003629551820310480495200c400e048101110314104400c849060704080d04003e691070412116422155a5034801500200004101000ca20003c0c4040c1d00613040250000c070b0315021100b1000303580e4040d40c0500b0601e50708400b109044864540e84801c129080d2000400010441021a002d0941d030410400050f0a2915154a0380c2c1c0f81d990b035440481c40303480814021603803c516100040706440d004002220b9a5180405e141c43d0181c0d01e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 176308992 1250 176307742 176307773
    0x414070b0f0d0b0310020406090509010b04080601050d03020f01051005010f081b18041104030203210f0918040b010602190218190e010f14040b0a0b010c02131d0703 72
    0x100d07903c070300c9030a09560030080d40e40200103009095541d80d46642e00100240700c41d00c1201c1c01104580004071720718480704250b5054600403002010f10340e107010104140101d0501003074040d4050f01d01e01c4801c0c8082802910711a010284480203081d20b410f000610f502d0310100b89101300035005040c0005140e4001c4014400312000ca07440391030b100903008100040c2e031041d10080e405450070000100100300e06000e032007102d00032016603541d03080301c071080a20303800411040859040708100300c5e01815480000740800450142080d004900c100d5540f0307a0040041e00e080c5c800000740001005000d0b41045040315501140d030480c1c0480415601161030503180700202000881341c0d80c0006c5840b041d0420b800ca00300304202d410300c00c142c551404103000307110850000031a5414002421001c0c440c841d55603003d558801410310541e074491040384010155556183d040080201e0700d0000b503660040c0442c1150721100c0006903007503000020440c0c04000300a140c0b0243c120003020004070b0030508500034207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 176310242 1250 176308992 176309017
    0x402070c141203120702070b0c070504090f05010e010e0c030c010507121413140108190b041b08060405010509070203190e04061502010b0603060a061209020402030414070b0f 76
    0x2408120000a00a00080c031403140c140c44042101d1160408051440b401034601b40c003520001c9850313002085c114420713201060090360041a0410150038664001e40c0818003c00b4034030340000c81503941c242515091804100941c1d1182150b249051003886408a4200100c0c014010031103c000040c00c14050301401800402d0b02c1100002068007a410b20640a4070b1405916a6504580181c0e03840e07030b0043c0a484948c008180e994070300d0394002c40c2c4c41809420f0752000c500c881c0004081c1e202c0648481988a9000f9848403e1802800c3c44801005100011619403050b285045030510040b01c90590109200304000010301800c1c0f41c0120844da0300e03900c0c000e88042e91149181c410b586170442d0b12441c0c0d41003890710304001031010320b11034a540c44250950007440b803000d0180c00c2207260f0000344d420940c0200c165a08206550083c4192121107000c1000818130501c00d8001404036041240e003a9208160301c03007011030340402846070401138241181c09a0030302d1580d4030400302c00c0c014036592020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 176311492 1250 176310242 176310269
    0x2031006080c09250c0f0b070207060807080f010b0a0e1003022101050609060a032018030105010b0a050d060b03040c0315050c1905120406020415020a2a030b070314060402070c 77
    0x2c1c1b1011030f036540d0f0241c0d000b40ca213034500d060045009683d0004c51003042700003080140815012803064500c43e000e40c02c82d1404030354590811000707040c1d55000d11070764400e1110000c1703501c100340c5402d0f50f02c8181d0103c42d01d0043c9c8600d00040c1d8100642001110005209411401800160345200c1030340d9034844181c0d101c6841d007856841c19002020406607103503a4000020582c01040002001460340515001035180d80440642c1418260f64080c040c26625000500410141912500181050742d543c600041504c0340d8950408441d0380c070a440558200d144a1401d10034804900040595001001800c00030391410141c1c0c0034a501400c3c41c4d104039501e002c0240002d66220710240c603800c0c001e512044140d42000d1800100039400361044554204690004141d600e001054110307260b5000050f00c1004000c2e8018020440c0050402030010160404044080707800544801e205504a071400928403110b03000d0017024100003094640b0990042008200040c04c18a804048a0ba40f058110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 176312742 1250 176311492 176311517
    0x22505070311060c0303090115090903090317041e03120801030803061c15090215070203060c0d020712020d08061c0b0901020c0f0105010509250c02031006080c0925 72
    0x21818860810300b113045200100911020300410760144410b004c0048494030b52595034400e0805a6054030000340126003c15401c0010480d00a8400418482031311400e280540301c200000e101010040caa1554900100040c4200300701180495111280c90820341100e6155984403030140c480280041c2c019000035103078030381000c0500f02d44446194402961180d04513540802c00c010091074074141c4c4030f40c2600c0002244280010b0131206035580140241c0102d80d102540324002d5440500d5401070660700b0094040411000c0403039034102400c0e94042c103e00310f0003c20041410b807015001910803c6400c80b099108955a212891555400b106040c102e0340c03084986030090080c1d02944c84240503c0d08180d000b01d10650000b810380d01c0407541d1045c0c2d610750b01c0740504040c00003112491003107181951045a10700414041002c1c40c8020220344120000f9014042070310389c103500901c01c603401007101c8452841c0c000300d00d80c0c2c40001ca0340084c52001c1c441d00f140095101083c0400305101d10120400d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 176313992 1250 176312742 176312749
    0x501140d060b04060e010603020712050307200f0607020303150406120201080702010f110403050708060f0f130507060e040b01020a0203101515050c060705071205091306060201022505070311 83
    0x100020b0002402840c142d42c1e45180148c007a5100c6281140c1d8030140300586038060b4010000c0d00e0242071140d9408a0b1550000619401c2c01441c0e06002070340c0c828001d4a40036180c0800c08144501d00030b9015589a080c60383c2c0d0300401e041032005041c421401c00301c6c01d100908200f48107500c11502481c0a00c40c40e1240c3d00241d006110107a03070f840f19141446071110190088400138002c485c807400c11a182c1c555610802500d803c4c041d80c5080185810f0804035000e100015040768018000301c021307007180c0020ba545d2510f1300c00da9510007404110b90050602aa05c1c00d0b2042189481081c00036001000f01540040e4481c0c040c2e00e41141380690350120742840c205003071004409000e03040070381c4441d1807071200003500ca40c111348080c056500c680710000e0007040c443d409444a16910052641304c002960074150b8030b40d01720401c1d80d900091103445e034150099071401288010720107070300010781d01d0301e2412034900c1040a00c5e122108066403100454005200001e200d4100ca4004c07481140d0f040089001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 176315242 1250 176313992 176314001
    0xc030e040c030e0f1c0e0f0d05120a09090e0a02090f13060908131d1b0904050f0907090e03040b0a0215040c0e0a05070219020f0301060305100501140d060b04 69
    0x2d49050b11035800340c5200ca160004c0d030030014000480d05002c1c0d20381d0714841260754403c80c16805400001f2100306000d2401c1a003040d50300c061054003038540d4500c01a40c00c15141c0c00c0182c2ca000012a0f4075002c000c40d040511a5114084407003014000c0c1e034a040e00421481c99002d049030f2000f00305140050704481594010302e480907070010092003942c060741080c1c503a0350441c03480740661f00720594000500703400c4800c80e48600c40c204807131020160340d450207503000310400c00041260000c08201d00c00c1d0315522480348512403a4520000e4645003840d0300740300e1802030b40340c101c0004140b6180741c03416440303400019101200e4002c090166a803e80500490408000b1461010454603800c00d01c0104851440064140e03080300284a04d20341d80c402c020300c15142d050b100c039030150300007400d40b00b20482e902441210700350018146d004450003a401290031142180e1003501e50303400c141c40ca0310f000442405118014155160032900554807900002c1a101c00365200134080390342d6403099216503c6a400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 176316492 1250 176315242 176315261
    0x12031104090501030b090d020d0302030a0209090123030d0905120a0c0312110307030504050607020f1003060302010e0f1503100308030c190306030c14030307060e0312070c030e040c03 80
    0x115803200d5658880102608081c002111000181000110101d400040903900c407520360b8000c0032000e403000030580007580054041080d00c1e03020007072403e054480071441c50081043c00700e0001c1d08a023403070914803104681c207a81d504ca600003c0703200f00b04591061102e01558004c440e0701710b00d00b04509400f440c080818900900c14005000d00000b07101480e0342418504c0c80d1a1503d980001e40598015203030310030000d00401041091005120a060200c003405140f48040c10105104e00818001044c0c40b01050340c100c0005e80760201802103580c0a82c1011096001b130760031100300d000500c00a41c0c8080c540c0103000042e80080b0020345440d010701320000096401c0b0585075075038200320380d10350307159401205828042c10028500441142c82440382d0400c0305d4100042c040550b007000380e001d0b040800c00800b07a51604c800d20030180820398521074050116420b000a690b07401c140310001c040007100034050410701102101300f6000c03940080b00c0c1500d0174800c44000843c1401e001003078000b400400c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 176317742 1250 176316492 176316521
    0x60a0c0b0a0b09070507080a050a030f0e0d0f030e15041509030306050f0618090c0f0f07140f0601090207022805030f010c120c0212030403090e0112020d1203 69
    0x3414000710310348030703446190b0614003640d00400300da5401c0e006450794816288000e10180003000743e2807089101d84043c15650b46a8a004580c18080d550b400741501d15002a092040c1c105142142e09a90007003080500b0804505044c00340c0f0b19500c003440d4035100689a05148218268002400c105640b089a040400c03130b400b041000c41100c2c10700400a04503800f60f58020b000201d03030304500c0e00d064829a055000c074410080310043d030310800c3c08003038003008d0f1a103070000078244014401c0200e074102510743c16500310b1a09d91510128205220ba003e010724130840d451300b00b03407070308104588041501815515034003030159541c2000e202242c1914510310054011018900312441d804010520340c40444004030102c0781d4002d08003092508131504900c809000c90002c101102c46502e098012100300585401640c4042901079180317220f07648101d80c02c078005003154409100f12240012090b0250a110350750000d10b0f0f90f591b01003111070005a4026248085200203805d00038400e41000402c0003201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 176318992 1250 176317742 176317763
    0x905131115131707051f0c02061603031a060c0a080f07080d0506040c02011517010603060203091e0601030c1815060f020c030c10080a0b03030403080a0e030105070806060a0c 76
    0x12a01c12110030115610f1440500132a01c000075103140144800e00a01d202208600041d90040c0e0305480d8101103480882e08124240190140e0041d000d5514030254029140801c1481c5413865008000d080300840e035105003001e01800010380b02c001011030501d9440b0000316070ba840303031a41d59030013405400c0005000b40c20001d4076440f1a0072a810031801070f0030079242403000c01c1c0700d1304080c0e0030f0361008282070100c1ca256620401c0b4820070004402007c039054000061005c0d201d48a640581c1e200320b90001c42e580c00074610011050300003203103003107178101000500915410f40da1400344558883c460124204448644842042615400b45110703100078a80b1b025501da541402602203161003012202602a00c000002e25040109900e10640e0b4010020812008103110640720020040c062a40c0d881e40d401c0c0000442d2010001800590700800940c0e80703440500d0b0000340100c0400e140140a41d040106220600c0e070080c1e111504850111100e540310030f210103040b82d1441d40002d000e003084151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 176320242 1250 176318992 176318999
    0xc0d020405190303030f0b100302360a0608040c051302090a06030b0a0e041109090304032a1502070614070213090605070207030b040609061e06090513111513 69
    0x300c1c142c903030031070380709403005c3c0018500c0c203810701e04481c403540200ea04100171406043d00603109a000340482140c10b10302040620140c580404409001d02010304401d1780c5d0b260240301d6141984a0030024007541ca0110302c18a440d98030302c82c014040c1d204090286c924554107001c621401d8060700d2007034001402802645030303038020080142a15500c101d005610749140400d001d40f014039542c0c0306580264400e03404070840820710041c010002c00f60030641c04144808000111080d0962005242c22180c1d20501c140401a8401401c0c440d40300b11380401500d003c51282d02e0300810f25a0446e0210f0810300003182091202031000c2c411248025070061151480003681c030440ea008000b09800f840e07041246580b41807041c0c6e542c06660201500c290300d1600001c000a540d900590300c043e100e8480031030407005134040884001d80048600007030f940c85943c18442d5550910603d41d1007981f60b05e0890b966101034896000002ca203c00c1680120f0340d80854402e40032041c011208a03034001107205284940c6d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 176321492 1250 176320242 176320279
    0x1b050a03092a0e06010e0906060a180e06090705030402090615040f1206180201090311030705060f0703020c031c18081c02100b1509220f060b03040503030c0d020405 72
    0x4a40a02583d0a40c480085000ea500c20019031903520703070250088072151619070810000e500005564401c2060044180084040445010300200845003a5181c0c2d42842401c20000080c01000001001b8090003000003580e81d04010b030b82c20072002e461070141c18100c0b030f00740c0207188190b0304a6121203800f1880004c1039425001c404000d03500039142000664069600110910810354010380021645107042c004912007103240c14982d4070042c11540c800e80c1d20004210720703402c070300340388034585502050580601da010722180300c41c0b05081313004d040c004008035556604c200302900e810b0100310b04040c1d0460804208a400800761144008841582c41500c02c0200c000400e0074040c8010300941078480e00c0aa03440c01040d038500c0300204117945140081d0105401a001014500d601202c1412000040c4a009440170901818070402003100000c0119240070340340c15510520000c40c04000f00004244080107a9800800a1b02d07141c3c1c3e51562420294007a00494000c1a44403200e0f10500d01c0010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 176322742 1250 176321492 176321573
    0xf020a0f08010f150809070806040b0f0f160e040209030114010510030209030607030b0607020d03050c0706080402060f0a110d080a06060e0109151709060a1b050a0309 73
    0x507507201a40381c1e803291000440f06a50307120b00f03070080d03074076a29001c0054040c15a0781d43c00071810003203610040d51604100d02c1d24006a501756440b01c0602e09124142c1c040903401d95211108590030421414007090b214203e00c4030000d01000c2004040e0a10050b0352142c0480d000d0500050003440b412280c010790381043c20080c071540b441780c1c0e04190809000c600074000e940702580010050314884d5a4842c00790040d0481c602e00c2c2d035025400708203000041c1e9030000e2200200f402581e503039032141050b950a521340152900300d081480030759020400160343da24215003881c014a60f0098861070080d60585034141c4448041c2400c2c0103107000e00d038030035a004a1041c420101280c7c1400607a95812041d0b500d1906000c7c010700080c4040c1091212011900e00340042043c1841e00880345581401c030314240d0750090326848104e1b00101d06001844086015030300f107160b810b241602d204140c1000c05081440f40d03030f02483c10325840d00ca030361041c040d04402481003c0c00040d0381c001a81008240c100000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 176323992 1250 176322742 176322767
    0x305010507021c0c150609050a290a0308071e050a0302010506010801080d2012040306050c031003140a080703080618100603020306190611010c0e1509040f020a 70
    0x14400c0030800103800b804a08100341d242c0ca0784c1c075a40c18181054507a48405c0d8810003080841340d40318640020221920f1041d140f041e802c000c0001072a1440c11211101e001d5503070007102d665191000014003030754801c0c2c0040100c0354821032140e9620040c3c50220700003441c00242601141c00007503d082401404102d00041600c298020003c80c0d075500c00540704d610702070244042d40e52092445910841c05807040080080d0355010380d01485003035444192604004c0d07440111410800306081041100500480d900101c031025650b095150181540320720f4402ca100140c04221414501220000140107549a85405c80380c0282c1c0c5507120f08018003c42c400381c0da101d000d0440c103031f0b031070000403500000fa60103101120290702c0c0d910f29104085019410103400947d024084012610741e004001818400130034258403090629445041e00300d0031100e04c122200240031314407122131011356550400d600311301c22506403281c9502410300440c00a0040303800e000115440003410754075942d00302c41e4503a40e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 176325242 1250 176323992 176323997
    0x22030803010603151805100801060b0c01050c0f07031805090f01140405151014030a0e07060305060a06030507030b120f010e0a0804450b03010e0607050a11070305010507 74
    0x2004280c01c0012085040344603034001180717405203601c484020764019075007100d0f81182c2d91041e592202c10443c21240d00c0d5200090400700000c0e40d00700d010080c0180f561000104141a0034114980300c0b0008510039800c1c018100091500111041c004407000d51000c1d00c409489090245064030100b07400800c00e001340304401144003150300b40c41c80c0c00c0c0074ac03500c20f01e8544000c10b40406044184030340c1403001d05052045c4182145014034144402010350702c507039403440300412003030310b001c440d00c0c1001082d401540826081c442001404e8580d00f6100084900c54907000869689002c0210001c02ca2044229070107890000d80c028848170004079002c0b1a811400200704410381400201c3e90740041c4a801000f50030144800c0107441c0302100220640c0fa01c2d00e1100c0e1100743c8048945072002c54140d003081c22152449115020701e8210300c41c0c00388144094008002000356041001c1e03450ba001082c505c100310300000c403403000d40d100d0b54600700d180414008a454950703ca26010f80039007070032a0365200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 176326492 1250 176325242 176325251
    0x60c02040b090603070e1302040e010507031b0203030c131205010c0905180a0e030f0c030705010c05030108030d0b041e1e02161103150103120206101a22030803010603 73
    0xd0610381400500c3c05500028010148076103002001c0703010820003040303e84007603034104141d005a1110300546c0754190480c0000112031030041c4026088a20300100c0c840300c0102ca0344802c446540010883e41c00c01d0305510016200c08042c0c01700442c0d006150000d40211030382c80e80c00e00801c8815000f00b01c0c680d540707464607007000b501c580901c04001c04030250340c003004090b640031032042e060650007140300195003070540c0d2808050401d99038403603100034041b00180e0320018403a03007801800e00c120700e408039651421034690751500c00346990341d000d615913030340e0781a603500751001e6180d40c0d0f9400303101d00c061034028000d41c420403011a900142000316801d407511154440c0c0340800c90584c0b00b1100c0f180000d118442d1b400e04581c079801e04c5207010707080700d5405200741c400e0a820b582c00c014165008502c5916410281c092029000b82446805003882c40020b84041c82030100080703a9100e43c0444044c843e00a84231401c40300c940d004555005a0b8a10190755540003200303002c6040019030586e03070217031020701 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 176327742 1250 176326492 176326511
    0x60403060c210c051b162301050f03240307060507141c0c0501020f030c040603180c05010e0f090f090f0c0f060306041d0f0111130501080403050c07060c0204 69
    0x2415918008120f4001510803c40140075509041c040e80d04002000111200704501c0c2c09038103d201075035045040c0d44c869211781070304107042c02d0340f059a100e0000e20300142032901801c1c2d1314090380405006031910009414815280ea0b55034404010068401000c40d165141d172624050311582c840355040e41e550342146401a58618009592407082106484280610280c0c2c20b0841b00810703144011141c41d5003c000c2c0c051400c0690015500800c41c0115240ea0746103403e00c00380403601d4590180403034a04402e400310100b607102260908884003803c00c00c400400060000341004654640181e02c0351200c01403083e080b2150038201d210341c4a070000c5501d19044085042e50b40d41411059a5100b4541c00d008503e40c14018041e681109024202203032100b03051800c034040d1140005800b400303034080300c54000c400400340140c040ea2452500040c4c9810310745604110034014a008003414001c041c0302107020140300f4001c90300d070002d4200079114103d84036440100480c000c50020381c41142041820f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 176328992 1250 176327742 176327807
    0x507020f06010b19050d051504180c05041a190306050106020a0b150a030203011a010f180b07050a021206090c1516031b050102091c020901060509060403060c 69
    0x16410f0302c40c42081141000001d4071010030284c468540038003080070a00410107280242c0c01540e00603c400d001060001c07041c00140022100e291a03c004241110b6604801150385c10611f002500d00503500030684111020038200c3d980400016250002e01800c20882d6585c110120a4181d91080070140080d9985070b0080740d44800081e001341080c400b01001c01c0038010030806c10000c940380a4501070106549800003821646001241c01c103103040d1244400f2190303031113012641041024200451100c044018289150506014038000100c0016100e130a0107000c100082010b507005080f13214003003900400c139444003401e40b0014410710880351400c0c51468507041d0003039040711950045052030844012105403110441341038050104c2c1890480d0884040c44007440102c0c01400056607a0000c1ca041c00b94005401050b00041e40c021207800c00142e0b24078600718111816881d2651b112a140d900240c00c0d07220356440149160f1600441d54102a005407100c0d9900f141c91140c02911034111200c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 176330242 1250 176328992 176329003
    0x60403140c0111032502150307022104030b060301060b0408030a11011803200d02010b01020705040b03030f0a1115220222060801020a080603160e01061b0b0106030507020f 75
    0x3e00160700700b4040340b40b45406059001414510001d441d1100d2641500481c1a00c071308a00c1642c0602800810404847c1d01040f4500ca040d00c075182040c08403041c014420f4841c011400002c0208032007030007054182e5803d420007070103480303800e000c00d41c3e42e0390303420040e5541c1d4022000d0001003030103000494210352040c8940f1801e800510305007200d80030315030b504940c40c11070005245c084404407000c40120382e00801c0381c5400c080254000103504200300f070019140980bd40d200d41d11560800e41e43d0101a10048240e4500c0d004018403551100101c00060b5220481040c1c501910b1080003446400d0a030141c031310341d00a00380c8110489030f180c012440da4400c2003c002005c0e4000c0c0ca004014450801c003011880800c02000100040d03803500c915a00b420790f0b02c840040800206038009101e0700b46000d120302440d07500744013002c80029180c0501c2c0f074440081407098034240320b007040050000b18070110071050760303d911440f440c000b0360711050090018102964071100510903501038a1007400300261 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 176331492 1250 176330242 176330267
    0xa060305010b0301030f030c060c021b091e07140c0c090a02070210112a090106020d0e01050a0e0d0c140607050a08070201020309180603060a020307052205060403140c01 74
    0xb00d5882d5070b01310b4540d000c02c0900c81130100e00b003103446502407011036420b10540340000e410390b001d0703c2c81421400041c010303040240703a02446022480d0900820b544401030481c0c440711404c0b00c4a200d65280b001c280e5840071a5450300c1000400095129134951000c030390541c818800300d8003104191680c20501c07080f40603076800250001c07004010b981c0c00d42d00a440240324070000204489403c101401c0034803240003110182c03108a003458201b82410f141100c0d10b00d0242c2013601c000c020010000000414810030303001c0d26814060005028000310788114441000d40c540a00188480001480c21001c1106070388500317041c404034030810f001245400000c807280550464020000502c2646400c0c9c21030f401084100c1c158403041210804984403d039911580000400644803545004000c0c181019001418500304500c10410440f404d900901070700d400c20080c2050710808003885012840b00c810035040282d000f0000b19000042024040d502c441c49003a410984400f4107400b0015101140c02e6507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 176332742 1250 176331492 176331509
    0xf0708101b0c020f0604090e0d0216030b04030c080406020c150c0d030f0f0519052a0304050a050f01020d060e1612060e01060503160e03330c04050a06030501 69
    0x65400001c41c4160b090209541c0010b004402e422044000222035900a81c44103120b01d40b07468080615000038805201d480c5c00600281c4041046c48051801c0480c41c0d00000700317421404c0b4003180c10316200d181201485540180d80710740d0385841b0340f0065070381c40c801d1030b0f003510030340242c2d4030303540700c48120700c141c1d002040c0003402402e01041a040960292640041107003107540c0c0c41d80d0401e07840400c4c0c00789038062100348684500108600704584151540240400181c140c0785101400040c002490883c40c0c0da007200da56038880d100c0780780c09400d285007000040d12500c5401009038000310194010301d08400c40320320800c58103980d169181e890150481c1c030042c00d01080504102d07101d001e05801100980881d20000b400e136181d0f103403284c400100780c011500080010040015510040c0b5071803500708100d003802c84022140314000390756407400c0360710494900b0000110040f401c007001e440300311082d402d9100c0c000301e241021290415400a10034248075410041000541601a110301410380d990788 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 176333992 1250 176332742 176332781
    0xf0b0c03240a0b09010201020f070c0501021501080a0303050712090b2a0a03020c100e060a0605030307051c02102a18090c0509040203040303050f100e150109080f070810 74
    0x72480514030f400c2811383d00c0c190354003000980c00401c280302c01010080d104a440b12091410107000a01e00070071421101c4d10001200c0c014010600d0015000c001160b0510300469241c0e00c12800300c4c0e620400420051007142840980810820074180380e62240381c96403001000d03c884e50504560101c00d0424044001e20304000e40661396200760010030b003031592082190302c08e407000e000791400c40c1c3c0e04204000c0547c00c604140b00c0c0300f01150003008018103080f001541001019201d082c1c4402c104113120454100007482000d510340280815803100003c401d0410584d8500d10f0b1020141074200b140a400b071940324612043d4900802c01c0051640b540000e02c02e5107400c02c69503038000d28500b414141849003d101d0403030941d41e00d0001710f110302d10079070700407032142400e00201c040315002400401c12100044400e2280c040900c1d4140d034484410385501c001003889000589503183e03990860b00460060500d00c07001d00c040051903804a400071011503001240c06801c0c04100c0784084640c24030407000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 176335242 1250 176333992 176333999
    0xa0c02040509030c0312070f030e19020406090e0a1101021504080d140a0b0a050301021801050702040b0d03051c0615030f060803030a0b01020c18040f0f0b0c03240a 72
    0x10392006a002c008041260b00e85002e07444151720b980c0210000c080001e040c402003200719680b110103456912603034142440b01a90008203030b911069650a040c0d5070010402541095582c0c0e074000d40020200780c50f04104460200701c0e05901c884682e40c06031404081d1480e074a030607510004650214a80c0008011000d880d0f40d903c80415601c80b00c05003a406881c2d40b20030015669180c181801861540b0000030078001110610034002c88942c0120301c00c0e44140284102d00b1107011101d400c0b92800d1030125564580ba00c0060010035484038130a03003022034010321800b0503411038010184547c0000c4240b2900b0004458441900c140b07001d603035400042e14041445c264025084080313120320100021503800c0d00d98404525682044905100c055200c00105140d56018811000e400c2015038581e401c0c82c640d01244e4a811101400007004620015000f2040c400150310340f40714240d101c5c481300020b0178a81040041c036081500c9182401481098104104400720585c50070540c0103404607418500c0e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 176336492 1250 176335242 176335249
    0x5280e150c060f0a021207030b03060f040803070c05100207060209120f100b0402070b0702060a0c0e0913030915050310080a0201020c0f0307050a09060e07090605091c14070306110a0c02 81
    0x2c1c044d01541c0c01c181c00384210b01c0f03481c0418a0240c81107140c0d82d8009030440303d0000701032505502030410305103044100c0500001c210310800300d0750712540d03500340034107840d030341e4603000b0302c1e080108141c00391161000c90031904000c05a0010411103001300d407882851511901c0c450740f1001105002c4802d0b0b031203800e90000c1c0518ee0780080e03c107010001c00041c14000326840d107031544c0307004690010060304102c1c10411a0b401510507100042440d203021209940e0850200f07003416006040b0740b120231858100300003010701ca070b11200041c0c0144944c0203890f07680c114000d041d9420545202d2101c19200001040e00c0d50001400714081380c0581c01021030f9011801844841d0303a00002154150103205008282c1d0303180d1001c107a006000c096000541ca81c5000d920b018002006050386040180d070641c00c006090380300c8291500075a0443d50502c104066040034844402000c03402494246810a1019011400b00d81c1d101101d005600030b00448008084205c20303032040d41124004070300c071004554050305 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 176337742 1250 176336492 176336521
    0xa0f060e0112050403020d02100b01170a1d030706180b04110a1208030603060603010507020a080c01060906170708030a17090f12040f0f06090605280e150c06 69
    0x40c010304142c00c4054680080c00c003a03410844050b000760744081c2008040300e6040200b40f403100b500000420060035030360002000b00d10318000340c4141d00309140100d10084840c0e0b00980f1030410840b001510202c0341c4036000d449412800c000e03112145401e174901005002c40d1101890300d580a0003020382c43d80d49658a010189175255000d80000035030342c001c00d001914020030005607004401103a01c0307141c46820145090b00090240c0e01a9040c0700c14821a030707070005080c02d10207903c004550317204c6142a03502c2c0c1c0100215480911814103020f800500020710951140100c0244002d80c0c00d101c0d141c40c0c0f6555284241d0f5101d9000980020024026007040103007960051000000e0381c00c03a0701c030030450b9860301c083c00c4c8441e149814002000c025980c4001c0030640104a61110700048925146c0302410b84032441c4968001c0c011700003a1130b40c01440f1050031004241c00c01da036800b5491032f00580201442034070769100e8001e00c0b1103012158840b8408040d40c6076082508028141a176030301080700e4981 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 176338992 1250 176337742 176337767
    0x105060a0c060501081015050102061b09180103020103051f050d030507020604060e030d030e0a1e02030607030507022107080a020a06060b1206060c0706030c090e0c0406020c0a0f06 79
    0x806041e5000001c1c040f801038500a14005008150203a2907041a07000c480951108821440090030100640d03600480e055500503800c000400c0d10b44005800100c06206140760707a03900c40b11204454081440959115059a000b81d82c1040150390f981a1241d9542c1151603040190100407020002c920f0250090003d45200b40340581c01c0c00d40641c04206540c009802140c0840d9408441e44801e0504010b29904e000c03580c074062004d1b00069080503269200c001c0302904628501081c020244c901020b0401700d40c0d4007070704a8500d072401d114024003c1c40103a0303000c401400b5101e01c2c2e0711030302d8181c2c4201e07a0109a031544c0500d403a44c40c0d919002c460b44100110b00c00d501030387c4444c1001c24070340e104080042000400c0c1580d6400c4001103040518401410140300381c106205000d0044070028418003590207500b0009004590104182e40d41540b07540032801c0e1480329001c00005000d8030001e80110385403074080b1800d44c01038074100b140305040c41c09070308180805403508110b0f017071044d41081c130752 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 176340242 1250 176338992 176338997
    0x309150203070b0a0608012a030216051e070614090d0c080303091c210510050402070602071202030405031f1b0206040201090b04050f13020906120f0f0c030105060a 72
    0x7071602c2540c0701102500c0444110020307a0340c0d0941040411401c1c00b84690071801d0480d0b2440d2a0710083c45555864043c61403502016804141c1030000c2d0040301301070078070541000c01c54006802440060000901400099200d405201000180c035400b03120709900400003200c40600707000003a0300f4069411107a000950700602100000180e081092004500031520000a410300c1440444334101100010a40d1030030000d8240303a010403c032288500402c40c001d21400401c1d940c41d56214510070401e2038003c9540648002403403010410b0f154028107600d442043c0030451400001b00980c0c8034000c0b4400e564058200f10804074485000b1100c514105500380070002d8210405040c0348580e000030682007015130b0080c01807006641c1c102d0780d078030000d21804a03400c1c500f40c180004203100d80700b01d030146401142001010b18106000f0b4056685036200940800e0b01e825600d540d51448800c150307202204e020513000458912010014a6827003801034a005500c1c0d64039200038007003e41c2c0100780000c01c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 176341492 1250 176340242 176340247
    0x201030f0b180a18050703030f02061003110d081c0e0a17070507031205070b0f0702280f050304051309020303273001020c060a0b19060305160201090309150203 70
    0x13841d000c900c001c440100d0182d4010910343d4254503016280001d4401381f102990f00c400f08210b400d071050241d0505a0b948001204076084280300170908800f2070541c024481040415030302c9602c2542c03d94407c5401c0280301c02e00c2896007008605496000200b005091b0919510301e9800104600e0001d05000381f0500c22981c0c0c3d25a01d807070340758014003110f209400040300051280c06204031004210307005002c1c40c00b42c1d16142003898010b55640903a84480d80c41c2111075a403803600da5840300c40301c503c1a03003001c4004605002440c040d900da50017401014840c100d00e40000000e0140d601c54100143c0e4058010b40c80d140f0744081c0f587c1c95402e802043c0000320203e1945000c1529010b048440c480c241004005440c82e680c100c20801c050300010004a0b42e2040c41040490500061840c4d00043c005000048404115000c600402d114103040e0f040c07400441000034030139502d40c1c4542e1140010102540058079032280c101d003a44e800c80d0000d0700241300b91070188281c90040000540f070030b40d6170040341e2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 176342742 1250 176341492 176341511
    0x4060203060a0f030f03110613031809061205010c020a111e04020c150705211003020d0f06050c0c0d030c051b0a111002100b0a030614040201030f0b180a 67
    0x181c616080d400c21940d0050980310320b0105508401f19130407100703603c0c010303024a00e046001c003c040401800003404102001048100641c0d0103005603016207d40f4405102c0316859045420b402da11103a801c5515602c0c040116222a00c0030640700e0071507900040810441e40da20040100030341d80e82cbc845c0b00c00d41407040d00d280400e690701d100400c1044030140c09483c0450003d4043e84030641d00800b54000e10404004a644030151403d402144280001020401742c8070301e028010701405a800c0290407854281001c410303c10f0b01c0d42d284a6152081d07609002954458443c88554054990b0008550307101e14106900240690810300c116901454628200040d120030304200d443c00c180c03015201e40000d4031560a1000705003c403404108240d44085d100151640005e5582c50110941a8015a640d01e800e11070364500d0821001590800024841020f1001076200c12500554080380400e01d403240110300016180107683e9101402030030441e800b402c805009089010007004155410781e2280e000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 176343992 1250 176342742 176342759
    0x20c030d152303070503060105100309060e0609070f060302090a0302010302030a0b040f15090c09050915030a03080a0f060608010b0d0e03030c0301150504052101092102011802060304060203060a 85
    0x200c408048868805a04031803209050034400145c00040c025005003005000544681e40b016104407600e00e8001100c801604200740240f621a003103100c5401800b0070700c0201c0341e00050680a0b141e00351319034200750350740c0c0d08107400300c1c40380181058104218400400141d8000d6020315400781c070840002c036031003003444005012550703548109042a41e03070300740750003e004640300414050050260708010003c1e0036480034001407418400d09100302000c4000800082c440b440e0180d03400706c06011500515031760315003c3c10b0150100c84415a20749007006801c01d00c1d000b4044d1004a40003900d85101d180d0030032002c65026400040100803c980380d408140d0030313500400c0110701c50224030650603165414105069010348080a032441004024041801640c0d91407602940c14401915030341c01e9490032a181c180134201080b400340405805980480317114061022240100031182d00030051450a070754214005807081c80041d4000405100180014440ba401940c04c01002002000c0b600e5841025 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 176345242 1250 176343992 176344019
    0x3100b1804061e020a1205100909021513051017041211030409020901020106230d11030a0c0510030218040b010905130209190302130b04020904091b09020c030d15 71
    0x100c000703540007a2806400c0d86c84080010114200320342032160707041103540160420342d5801041895581c40e074060045660307120302c41046c00300840b03400e41c4548019080082c1d0310124829280140a401e1084c08014481d80c030080900c1001d0440031055241c1c3e4984070050700d40b028150090000c00c080201c800e220410113000181907681740076175100d240300002401c1d03c0ea254440daa1082c54200700d0350f403030080141c074000c00304020359600c1c1c4514500c0c10082d001c4032581e442c1a815010b0402000f091040c1c0e1280c00c003d4441c00e0300ca20030500e088000481c101c2c40b0700603007018554000302e06610302d07141c190403030401d80c81c051400480017500d81c0005000010b00000fa083c40c1075001540280d1b40c00c04112034041d01c0300303540301400c8680c5140c002c100b0141444a600124540d28071580c44c0c01da0f11340d03054500e0004050020460ba011601c1c140050514107000780440700070394000002d4003001c0d070007210402034000010354100b800a02c02c19028112001d418151281024004035861407050030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 176346492 1250 176345242 176345291
    0x80916030803100902030610050a140403060c080601050c0c040e03130e1618030b19110d1406031c0908060a0b040b01081b090303040815040203100b180406 68
    0xc41d65807400e00349209100c1000c694401d01c0081d00500400c005580e60f110252051030316814100d50b41c0f41021000c81d40800c1c00114001903450206001c0240100ca62140d0541200c0da21030320166210a00152040e0103004901079150780f000c0c0110405d41822340200340c03406810004c590501d4400da20100c076100c0e0796003122070002480d83c10400304004404038520703000309500b003080004080250300801441035001c054000039611011604a0002030741c6150b8600c00070604101821000e0a105801e900c01c00404442d14100003c1d508050003070200107004090040061032a05c030a4000c0d0ba5448200f050745a09000c6240d07800580f903142840000d2141d140d820000409803645010042110713a0f01001d0303810043c42707104000b44160400e03001e541e10900400820388582c08a40001c0ca18402d03900300c3c203002c1c05074000407082034000700c400320b019034401c0b819617041c0079000c1c00c43c100b00e88141120f01d600001030311011740020807160340f241d0464014180882d041c807801001c036036140d02014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 176347742 1250 176346492 176346503
    0x3020402160201080106090303050318030c0d030c120509060708091203090601151809020c03040506071a010806040c120204060503060f103204140103140c06071208091603 75
    0x80700c800442da84070120502400c1d060401014507401e544004141c0d0100400340a00e0141c03d07042065501c10820640b40b4290f000e0044035094207101c08000c0203004483c0102e80441c1600032011032109080c002c0501c00c01c512802080181c2d90303610b003240c0966015044840e540101482c2d56509913041004602c1400850002c16007940361101c05ca00e4448800b5054041240f00711114150b910002c01c80800c58085240c090307283c541d02c5c0343c041d00703512a540c8200e602180000c0d10304100404003e030603019599180410314541c2c0e036041c0540c4c99950484000303046940c1c120041c401940c2440711040c0303507030000d003001800b561902e000c203140400a54000c00015081010012019858440180608090741c0040083c04140c000c010038014100c03800d0703400300003000c0c4014264545a1040030390341c01e900204ca000f540d490610007000418000102c0e03240c041c082154405003052001c54034041d030f0000d00b01d0050004078104650044005d0002e103150702803007020009800740300d030b031290117103001e00c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 176348992 1250 176347742 176347777
    0xb040611070b06030c010309030807080402060c07061110020703050712030b09070507141902011209080406090801110306011d0d060e0f0708070b0f0307020309030a03030903030b0f130e0703020402 86
    0x303078100740c0f170002200d194034101070421012000080d8003d102030740001181c00c1941068449100003842c0b03010310b00911425100340d900010340703280e00030400054081d020050300c410307110280c03014080e4410b5041c080d001c50001c1000350000b0300319508485400c09103241c001500e00303440700011800c507025102d9800040c404140f00e014000c41400ca01c0003028010000c10780e040e26100106907602c0f100d00045e041c44480f111000500c1065040000c03c55807288000c0c3c5d03140e0320380310083c1141b10b060090300b40341d40c82d01108524514121048a016040503110b0303d071101d001b10300d920410506c991403250041c01c0c60700c02900043e4140101c401c4907000c000030b01146004001e00600d40840342d440071220381d111030000c110301c6203e40107d41407a000f000b0840d5403a5124041a469481800d2160360135110359055078007419416400080f04500c2581c042c4000d040c014108401180c0031644c0302e50040401ca5103140e045203139031011602c0300254060318070700c903a241c000904036088102c0e10070f401c0004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 176350242 1250 176348992 176349001
    0xa030c050c090411040f020d060e0403020f0604080f0306030307211d0a152303010306060b03090607120906050415140f0c030a0b0d060c0201050601020f0a0b040611070b 74
    0x140980007400005451003032031031801c1d0300d41c444a02c5031103c81a008a988041813031001045404580842d1400039040c0050781d50343c001c1e0b1030b0480c004c0f6401e40040c00740c491041228203001c11031a02482d00844d500e401e04c18000d1040c8d030541d1000d031801350b040c8000c20440b8006120801c40050410700d1070001d811020710b0700e401514480010002882c0711070003030341c0c0040c0d0b40e444168482c143c03002d0107424a000d01440c0400da400364020240c09440311143c071090b02554150300011416030f4820700e001d0041990740c0025038118001a1401c2e01a604007100117480d2511074030f400a04103000c071001003215100342d110002150015101a10032045540f500c1004984a00603d05c894180120300052880c2019901c0c5031110098898a8445000404242141640d0708940d8815000610300c59071003415180140080c000d02c10041d026508100005100758008261014921506000f070142100300742d841441c1410003d00803559288d0303030706070303d04400444006807903440d00c02e5416200a050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 176351492 1250 176350242 176350253
    0x503011b02011a031f0902090103060614013023041b0803030118020f0f030402042007030503041e05030a1e0c0206030a060503030a02011d0601030503041e0302030a030c 74
    0x1441880e009041401000b1190f1514009050141d0f100ea1184405580d01d040d41e000010700100c0c500070b5800345082c0000300502ca05030380200e04440c05a410b13104020031210054442d4065090081001020042c0034014a0700c0d1100c0d400050a44800c0081e91510490000403136581400c40e100c00c04130090100010003480c0c806c002d4070170301d407481c840031440d207403024042d982d21050240e0581c01080113812a045d40ca1501510820890303aa40152101d05044aa64060708112800da20903070500d0112000d030300f40d40001c0c42c071080043c20781030f107006055201500e040d8009001184c205001d8102e0210351000f61801e158520f1162018503034950b0300c48002090220380141c3d0002d1000060110031065400c03410304102150f040d48e1154403a903c0c050320000410841c1d0042d41c1600000612840031070303040d0301500c101100c000c0c03442c00075044005e00039522070003408014200e920030082403000031090107044a484c41040358002115841e54082400d08049038070440c0801c2401441204202 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 176352742 1250 176351492 176351501
    0xe060d062d060b040b07060e030415270603020711090c0a090806070e01030b0303160b060319120c24090605060303030415050901020d09140d1704110a0503011b0201 72
    0x220a0310705001043c142035034800c06203d948103d04408500050f5201042604d0b000001002600070949e6201c90365a2000114100611215000658a441c45035600014020300d44160107000e20700c2124142054000c0c0e0082d4000302c0300703079030741d170300310515540d1716a41c801d8032a11500707007940842d49800301f5140c0900303250103d810000ea250842006c1040742c540c40040c9803a0030f402441e01003440c10070170003c241544100000e041e844540d03041d0240c280801c140c5003034000c28007a8100e907140315085640c3c0f0002c8a00580080000d1036400d4141a0b0510440501130300c14015401d4074103007411100c6000e044103490403400c8a0f42c2d00c43c0718607000e0094501c9119400242680558075601e01a5109168505640c15131805156500d010070907101003541a81ea0090090804000c20106414140121491004900b5041c45841c1148100070311802c0000025501541c0420711a140c0b82e503440314401400c2c420940155900c034002905540034003607000c800f00c404001d5940e00405410003400e58 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 176353992 1250 176352742 176352821
    0x2120307051903020c060703050705100606090801060506030a02030901060e2401030515040906150b09040c0e0a0b07080702101e021609110405030322050d0b010e060d06 74
    0x380081e85080109070042658404580206e60680d91062189401e0311580248040a080c0784030300310b407004840e401c1c0c1d4840406d495058072504030459503030010318282c4125000c3d103500210140042a44500b103500038541114030100049266503e91000030807405040780e50058400701002e07180413100c04100c5402000d1402c3c607084c130252900342c400d1803440d00b888108500940e580c0031400240020b6612190441c80d10600c0d146403540d90750a40455504415091840fa40c034088030f601c039881c05800e9140c1c2c810350203803540305528903100c0512015040f0820690300f03042c0401641c8010307a240f40407003444440d1501c1e201140310100e600354600c032080da8a0002958025a414000c409088484101b162072219000c02c540120b10040c1482c4d00079644069007501c800700da0400159170400640049607110030075042241c0d910740410840300002e1402400301607071000140144500211b41581c4200d019010244140481d910b00c411035031981000319541c200c101d18042040a100c90b800201c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 176355242 1250 176353992 176354023
    0x914031201170303010b0304320f0f010204051c210903060507020a03080c0d060308030a24030c03020907030207021305160c02060409050702121810050a09140d0212030705 75
    0x131981400200c0c040b0340706c0540040c0c290b00f41060880b0301c20550034110286862110755055000c0ba500d2181640c40d0960b0146a08500a902c509011b00405100381c800310340d0010441c8030010510204e400b00104200400ea030048900b44180c040805d060b00400c2e5075110590300d0030699031a40c20720710100c900140c244000c40d0800d221b21004240e0080c0481d03044406590069551241915410024001644001e18002002c001c0002c1c001140c1e100c0c50003581440e445207a295200c110044860045000007004c82d0700e0b8010500240c2420341c0a0750340301d01c250800603e44005030700000c21607120410800140c40d103440030405d10600b40b02c1d0413010000c0500342180080303515030018005000b01d000c0e4501180d940c6000902d0345c0e1081010108031211840700c907503a03551030594902d00401c14203045024901d400703141c600e6140b003a8201d44040d0995601d09a5242c14a0703200c403004002c0c03c240303650050400309224003680d1141c0310030014800000c000c540d184c40d2840e08034104400e60440148 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 176356492 1250 176355242 176355247
    0x2812020f0604080f0405090c070506102405040b130f0503010c0e0909030702100c020102072c09010f1a09060619050f16030201090203060f01060f0309140312011703 72
    0xd5288001610a400030703400480c05849119180d0142400c0c06141c0c0000d51004580c8144500450504020002a40100c00b41c0f42030340c0e54003801440c124840d208000c15802d072542d244c1c8501c2c0c201500c0d554a040c46d45401460603a550a440101d9005100d41c00211a004001044070550307900c5000005c08040c0c0013030084903007400380a09803d18106005014071103450028281e60004c1c001caa03500c940c0100b0903403414500b510010052211550201d001d8030560a0100301c2400c3c07040302c5c80020b0f41000254083c038290030703015130240002070125282036480d149051150003190140003110180e5011100000d1030040801ca003c082c09059640245400c0026600614000301482c06089240c1040c039940c091024002030300d07114144004640c46240a0350404041d410b40041045a000300c08075203ea0311a0141021612000c1c883c1c0340100340c000b070403a401c0d130b40650080355501d4090310044025146060b100c03400d640c06090f0410a12061304014450b0b451600800008400d112000f0360 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 176357742 1250 176356492 176356513
    0xa02040f0b0d0e07063203040f05010b18060f0103060b310b09060703020304050604030b01171c0c030221040e1006020a0609140d030f0f0506031e281202 67
    0xe200200550200c20203206c400150400180300f441480402c00c02034102d50794900d0a802e10b60f80514407800304885950a00740c11010910f0888403000b28800d9070810990191a528100864102d55410043c1850380f10000011201a8240684011030207010f0315003614001c030490010040000d0400d600048100d030f014000c40d818003055400420050b14a59a620540d04003a450741c061544001c0c1c0c0240001008010003131036112a80c100c0e07a82d00d803c9099100c107402030f962902c014040015039039aa141000f00c10500c500b14202426019005440c1011040c428051000b0f51050600000340c800060410036104280d071900e074040320601540d2521414864001e40740c01e10941c0140941c2d86030034814003440b5900120240303400e01d400c12501016403401c0301402600b60020640861031910320100d02c10b05caa07010340d900c00ca100070017030144201c6c00380080410011422412002c2c0c45400080f40c4040d006d901380000301c0855440620340c0188516084502500800100003103401c5a0004c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 176358992 1250 176357742 176357747
    0x1409221506120804170319021e060411100509041407080c03070903170405040c020c03010b010504030f06050a11041202090601030908121504020a08010306050f01080d05030a02040f0b0d0e0706 84
    0x31405d07541c00c00300303030300c21107a04001c4180345015001d608440b11040c2c50616000e46c0e00003550b030070202c0219003404080304410700c807541c840c02c0440703001e405880707020358a01031071414404000b0080d8442c1000303400d12040e80f022034104c1d20ba50303a100d81608880e005025429800801181c1c1c03000407903030000d140d441d010354020425101072000070410403440410740341005411040c0c40c058a0040d008015020310660b00964940741c00d00b005000307518180a440350395200328220f0703096941010301407078581100d5541000900d4000c0000080719543c17200421000c3c5444014002080f4052005e0901e11050040208600f00074200c14140f51420b1001c000041e0188207030f90503090307a000d001c2420b41d80c6005814290b046058180e5000b440050142c8030241c100800d039058900075001002545d644007014001914280510712440d40090802c3d030b603a0740300e9002541d11130b000314400740c10980c0e1007010600c17544540c0c00c00440b421000c00c50f081c825495100b418030690060000f0203c051418402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 176360242 1250 176358992 176358997
    0x90f06051b0109030512072303040c0603060503030f0309031608070507060513031103070f0f170f060103020910030b0703020910020105251e02061f14092215061208 72
    0x2211520f5040d10001600a0700403080303a04c0440e1000c00941c95411103001230140c3d07a004860442d898100070740b012801c54801e200d240300fa2800030300190718101c0224021f840c941c20040140d0220f10081084902906400d88400c014a106e112400d8a5058525000f0b0030849a600120200941800640034048500c851035013140d81006061007201302101c0400d0a00e280c03604001045412954002110486500e07524211928007088807400c0e610a1805034441c02c103840c2c50011a4003140051000d03281c1607422542044150f17441d48011580ca603503250900008540c01000f00b0341c049110340340341c02d002c050440f81c4205480208800e213071101e1140d0842600c1010894004021103c0b54401c600402451005122046c490b054040600400a550300e008035001006d183c0381144695030f00c0c44416180068900020809005140d10410f01020303400003419403054103c0503480356030700c0030340d5600d14484a0054021a1600d401c040507034090303c1642c0c0c001039940340c0c400b660002151301c0300107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 176361492 1250 176360242 176360257
    0x3060a020901050d05060102010e0a030207051005040803040312020a060c0e01030c0528050d0203010f0510050309070b070c030b040308071b0803061e0a082a03061501090f06051b01090305 82
    0x100050240c42d0303800105d005204880109804bc8142811202810380020f0490210b0350211180c61040110b0442215507014510442509a10520041c400560341011010200501d481217039500b000d1902d070007003542c01c8029000041b41c02042d0b074002550b17050040d05044000c1d401d1680c40c002d1360328241c4610104000c074200c44d51140b2042c40d041a44034004891050003401030954036541c64a8002840c04664400c00740700303109112481c040b140c041c2e0b0a480c0304012034000b8011417132810600b081c00340d00c09002264425910342e4040005103403100c0ca180924041da503025600d140041f40940004114142d00300d002c0e80040c0c41074001500081180c2d8064421f4402e40e03115075441c0510010200f407811042d0b884420002d020485060015004d201c00580400c104080142082c4c40c0d0340c1c20103039400701900740d000440095100351081003000541c1006144c14100140e0700c0e0040d045400d165080100050070000d0740031050340300c4009003110400b0300c0303000704525241a680078000b03100d00c0a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 176362742 1250 176361492 176361517
    0x8150f1c03031104030c0e010e040803160207090c050c060a1503030e060d0e06040b15090105060715020307180b1306081306050103032705011b0c08010e0c03060a02090105 75
    0x10300500800d8070980002001c00c8996541540702d40c0c50349070640350030300603001c0c404031071052000008070210011002800b9a40005401c1d02d103480e08c05003c140315030010754580c1588140c903c00158003482e403003455590803036a0383e420307160481234a40078240a000b80801d81c01c6403d00d68600d0609180c40c0c06d04040f6541400d01106214114000c24034500a085212540a19000d00010008004102d10f4803440c8a203040d048155100d1849224a9064040154004404000500c100e0400740d0080110300c1c043c250b400c01c0c0c0200e0007025003c0e03902c11030301240040c84080516a150150500b1100034051001c0d40e0340c200b8030f00400b8403200c9241031154404102410002c51001c0f1101e044031300c1c881d07070000c2090005607120704000d01030340044481001410300006900160b00068030b500700686105a403400c902036402c003203440c03910700081c0c0c09458503c080d40d800a4001024860b290f8401203910141a420950004143c200f140041c0805480e80c010000f0350320582e4410100c0c0c0d410301821 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 176363992 1250 176362742 176362789
    0x3010b0a02010905070e0405070e01030f020d06020d050a060f0902071a060a080601030f03081f090b03251502030f070312020c030304030c0c05010306030807020607050111040608150f 80
    0x3000490240070020700240c1603005803000480d4102c405090680709a0040c0c04030358025a56810907030300000240f10160401410080000040c500760150030340c2140505009401d05008c904000212141558021182955180f040025086049000004242040c411070a00115490b0b04124001092044c10100044000142d10341c4d40c00703e00c01c01519400d42195040c0d80c4a107024408a000102c054000c101e80d00d000541c5d501180d04044000c03100070b450b0282c0d941c030780307030005c805850100d0070180c3c0750003144d20707a50544240d580a9100403140300c0311112450702e0040b1180c07455045264503c00c641080040715130a8900c1000c441c4a140d142c076201100c02c058491080081c06052000780c590b020000610050551045011102a000750000324105540b1001541111003d1000409030001440100c0c0035180400103014100c1c0100008219100e8500b010b0303443d9032050300f241021415640c284800400460b4a90603a6032080e02d00840081410340000e42c0400080003068a00480 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 176365242 1250 176363992 176364007
    0x10c12050c041710050105040209030a231506100305090d0c030212160507051903020409020a120b0a0605190e07030605061801170402090c0708041212030c110303010b 73
    0x141c1d00b21002411180e02081c10303a08030100342d580321802c0c101c1003090300e800c0200104880c58140300311030411034010005c00300d4603c42d0703451311104110000031181d680548280c0b40c05501040c014244018640310740ca08540c075015042100800586880c0c81c2054640420800407030000118801588883d051024050b906860202d2400c508001a1201c485005c45c80e088030b12501c499a03840ca511800a03100c490b070b2104140300350442c2c030065582c40c1481d0b26108202600b4941d10100200c0c0c00030308490381c10b40d01c803000340040c1c0c580804200e130280140707010410000c03054030852001e1f21080320f4101e0042c86c0005103c40c848203500031501030400541c040f400043c001e0340003038002d01014007039544801109058003002040b0003100c5011400c900f80602078009401c074864400c0340d0003001d4102d182c507a80400754840d080f001c2c00721007412080001141c2c002000718541326603480395107148156540754030010203171543e07110720101380403003409031010340ca1000c002d982c151804141d1090700c41c5903 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 176366492 1250 176365242 176365261
    0x30601121214161a06100e06090301020f0703020607080a0204050108040b0603030705071e060809060a0b06040f09050a0b01020c0f01050306150706240602071a12180f010c1205 77
    0x40307801103101e40400c2d040000c1040300b1a11031040342c1c04040200b0000e0385c2d41d03a0505c1141c20300e0041d08030014840b0840520180340c4900600403440000e400141400e44031084240103034003070101640580d000c4003c100f4010b074071004c4960720422005065040ca441e000029001c000c010b000100341c2c0210b000081c085841c10815a05150b40210440d84103da8958003403101034003001c0c011144080340403020070310364043e4202c2d6002e000c1401c014800b907074801075800010703e100600d40c0d80c800410403000400c40300003d00c0401505819200054504043c0740d500704032100c890059042d5003101d50310912503561100503400c40c13602820034980d655900350010300b02418a4186641140000c203140d4288510782e403081342000c4004111028920b0b002e0100203a01e5a144501001039000d50020300c030032002d203400780750301d1040103103001e0510f540c00400b088494011030b8166000d5600e81c480d188080820030000300d4858030341000304410012072500400d0b002d00c030024044603603200c201040d240d10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 176367742 1250 176366492 176366497
    0x80a0e06070b040c0e0c09091f0312031e0c020606010c110d150b01110304090906060b0c0d030b0108310206120108060106021c1805150702030601121214 67
    0x294000b41100041c9004e02c0d121204c8819401110030360000e001c00240b00040306011640305510041007440540e03603100011200c070300fa035440203c2e180f18542000000a08060381e8070b8019110380c030045160101000c07102c0340b0100034040300140d1800c120700b4031031245c0c0114225802c03100c01e192602824000b0b0410f611036518103c084d60300400700e0842c01040c48100c65030400c11119060051144100030001190b40030340403d90483c86e504100020045222180c0c03080c0703a1281705050100700350340d4450003c41650803d40902440d9081607071810071a503030610a180d03040400342000d8600313042001c61610307040c0200704400c40c0306020f2210603035074491f20400c145d200e55006207010b5030b4a065041c141d0ba00303003082c4100c043d2442200000308200d400401d000300703e140131201e614401500810100da00c44030120310361488920803403000c56983c403481e13501d0541000048180d40d94100034414503142501c141d01095180404400721000228000d03086005030a85203080100b03d2485201500d5a2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 176368992 1250 176367742 176367757
    0x308012d060c02010e030109120f0207030f0c03020910060f031d0307110310020708070807030c0b01062c0d0f1e060606030614010e040c020c030618010501080a080a0e06 74
    0x9600a40007600da64000307501180603100382e85d6000107089800902d03080e1900705800811104020140070a828425496a98010341c03030310440f2206907894403403000319032500805842100d41178005000303606260000d00c0c2c011510b01c0c10030003540d00d810b1300240000b04440c1c40f13034205a158a40348911034000712030701c5800d960724800c1e203039642c44628200041d86403102e0090b01034044d0000300c121400941c030a4510103074001d08a140f8011040e900c1104961041d00d003201802502030084001c1181e0b140c001d4083c3c500c1384c90f02030100074003058480c03080b0700702c00d00b5030390500d81d40d080e0344895214886102d0000d42d00800402003130407a0300e0b0104000c00788154980c0800501c511403002d0041c43d4001f107007203c80d252000c02c0718580340d0401c46a06074082c0362890200d203404e285500d042c00c0c69840b0078491549031041d282c0202e6207000180c20000300340c5103000d800c0014000401441020320440c1d0050110400800802c0700c190b440050b00d01500343c1c900248124203800070b00726181c4004450701c4c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 176370242 1250 176368992 176369069
    0x20a180f0f06240e09060406080a050f1903021009050f120702011403010e06130b04090305041e030309090e030409060e070f11120c16150e0409030801 66
    0x4840140c8448001810240b0905012000486058183d1035400c02c03684032000103503072403c030900003100c10310100e420f010781841e801aa0310040020070410078403110021b14880c0300a00301c2c000003030224910745440078102c00c140158505a0f4000641c00044040b09031400f20400302d50f00200e41403440c206115500300a4035406000130920342801104000c00c840c41c400d88038641c040004801e040400c0c0402d00403060511640400304031149402d08603001c0e0038442e0358002c2035a080c500003103405e850982c01c00705c000c541c0100e01400020b5042743c800340344004918045244503e10785000b0708040d0f50f845120402d0b40d481e021808031400a104807005482c42050600803196102411581514102d524400140d81e0820a0004500c50303005801c0c501180402021500c40110f08501a584040101411485202448220390308403041440040c00301461121091102c8080907010050441103e88202c2c54182000000b0350003200301c5042d500a40010038100925010441c024400000314045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 176371492 1250 176370242 176370251
    0x9020a06050c0d0305010501050a0309020429090c09010f1808030a090905070e03030d0e010f1803120504021e0f0901090c020d050408070b0a050708030403020a1e020a180f 75
    0x2006074010004002003014001280c0700300101500441c2250f000f801004c0c0010410000a44a02d1003900447c003400c0c0020300006800b076000e100140d05882101c8a1803504203964641c400c0c40c83d08041456000611141442c9400300c6440000c000d0351003900e0301014002d1000c0d00b104130740e070008481000780481100300c1e940c840d046200681a00d00034411040c443d0f0800002031300703c0340700f501c00c0d01c03409001030011410081000b01c03040c040e16003200384590310b41da21400a50301e005580640c44000201011f4004011001c0c1401080c0808400c1c2c0726800030b0811041c88011b07101e12004840c035003e01200c42e103c0b03035a001e001442902c14600070b5a4441c0c80d080010a0482d800e0b0700000710004940c00301c0d401c41c190000709071181d0041d48501e0304650411001005810030440040c019007040703250041c07030b00c2c00c150340c3c3c040a904281e5050300183c2c0481e4466007000100044c038942c9004081d8184a03607007a50b40014030840007806015246208058105c0c000d00c1103410241c0c0c1c032008601e0501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 176372742 1250 176371492 176371499
    0x302130e042f0a05060f0f0301140a050324131406010e1b07200a0308040503070b090f0d230105150a0609230d03030b0111060603150a09020a 62
    0x745204180903400c081c0410102c03400d1070360807180c44040303900701030240b0404924210401c015908401ca28110300601001040018140000154068045940c04903402d50070380b0f042c01107082c03031608440d001e40d20034504a400d41c1035080071841040b0160740c100b50070b5642c00c280c0c009031000c15100142071305045800c1002c812808034019040e103543d10b0a4000c141d407034102d0126107003d0200c00240a0b0010083e01001c10401214404441008020f6080c05100c0703801040f040c44165005407440080420184958038042c8107600003030081d11300450412182e840096540c1003000d00c03443c402d0000382d03d09406c0002d00c80c2268010203e10080100c1e03d40c040c14018085d0500701c9001e80b000c021164855254030f040880c04058420325641d01000a0921508085014042d4030710b082c80f900600e1038030516075624109244a034803c3d9800b1a041010200243c00290314500c10146038014404000042d100014a600038000d0410780920544172220603100a295285010b07400504805010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 176373992 1250 176372742 176372753
    0x9030b0406050a0c020c0d0b04060b030303040f060e06010605040909030e04020d020409050f040b04032607200a0201050904020706020c0a050106060206070906080103020904052406040e030304050604030302130e04 93
    0x198420426207501307104041303284400b00d80740d04962003003e5020031500240f502007100710003103030b0380984240c00c00518001e81c140040e00d160001c6808950000b07500a80380108003541c0505488402d098001b49101e506041014015009038065800085c1e540d0a80000b80352003000301c504100c201074400c550351005100311101a50140c011003401a06102c042000e0a0108080dc0d00c610b403c012000070f1501e03280d50803501118007810940d58804024107203030310198a210264044d91142d211380c0c055410b50100c4200101141c2c4804c5010b4100c0d41d400c10260341c000c1c048032402c1204581c010b80d13412191074002c0080c001e001c400704051040322030001c1049815400982500d00c0c0d50201e40059880030400c40d07162a440c081c0000103100180100b00505203865040c1e00188944140c8100d90101e202320f1292110200e480d00c0d03851880401c3c07081c0c5090030301c42d80c400354500138080c51541c40e02e600c0f110365400010380010105680014400a00c0c03000c0c01c010806449800721094840c205420301 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 176375242 1250 176373992 176374001
    0xe040317010311010905030a021507080f0c07050a05010806030a08030612070b070303060f03080712140c060412030204030302070e0901091a060406050406140108091627060e01030f0309030b0406 85
    0x10f00d01149403620003103401c1c40d0020f01e0040c40ca43c0140280030102000100c5441608403d07000c4608010600c40c901d00280390001400f110b0300344400030031040d480c01041009001541d40a181800702400c02d106041d1008901300b00031982000000b50b807611000082040c442d003054000c00903008005021400f80e0b00c04006084160003070307805101c90360720ac004103c60713400b203803000619040c0300b00300d0a4000f0707501820300c0c02042c9640c10b02803200402109100380c25801220205403d030080b100f04400c100603501e0041961000d80341c02c6080606550780607696507000d000d0509201c41c1e0303400240280009410080800c1e40c4031524405c910203101c46140e1003d400d032480c2c4d10984c2044000f09039401e09100310011500c0401c0207900178200c030401940e0340040588040401c4c001e514000031141803041300140203103100c9600300001c410032803c00320a074800c041001503090038070204210350300c1107402550540b9004602c2003c0d00c0c0301413074159444502c0d64802003010001d07104010138041c00e0743c00b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 176376492 1250 176375242 176375273
    0x30b0109050a0e0703110409020607050a06050705210c0c0115151d010c14010c0512160801030b1f06080105010f08070f120902040204081e06040803010e0403170103 72
    0x1d0005465244038601507070b01200b041c25456004203002c0001c51480d00c004190aa006000052100f600350007040642c0c0c0402010b81c0c2c0ca80c0180381100800065202e1070303501c0350051900a05201c2030751080c000161804542c0f100130582c810200e8418410034049813500e440d000020460740c1440d003207185a4082610580c0303500901d240805001600805a007040040c500070003100341c0f440080103444817524410141c4030440b0032000c40712440424420714550103c140c660b55102c00e0251940120810020004044101c51141d00904144c1020101e0305595204004813200d5613080c52110714034600c105104205075000400040301034110945a040e20341c280c0e1070351085500c05805070750026040d650840000c202e0714400249600c110f08610041e0420407010420b010a90002026604141c00030070aa800c100145081c114807128038440c00781c0280054107113403070907448160f1240014801c0b54602c108000004041620034400400c0727180309031a8080a6586904009444452250 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 176377742 1250 176376492 176376509
    0x90201020f030f0403060c020f0d09050418150b011416020a05010518120304091401050109080f07140402220f1a04090c0c02131e0c0206040303090201090f030b01 71
    0x40d500c041c040c1e0200880f40081407800059207003502d5030395000b000342541081502180680960203036441400d2219010982080d5200300d000743c240002c1208552400c0c1417000c64007403059403040080e00425007000d41c440d64003400202002d803400140d40610070040020789258002840e214100c4250204043c03640c001d80f5017900305611400152018030072500c1d10802c0c41e07500c5016004134603054081c51482d1040070309488c20710360b8405690301651003070072111602d40c003030100520055034806401c03002002500010300340d03012900c0810f40c44131a10300401065a2402c004103600d40c843d0380487d1842e08400c40b09816454a2541d0304803020014019080380a051550004481401c05401c002d1119031001c2c05140920340700200c00100300d01140c001c06e01c00346110300c4000d6603030011940e0401c00d0040d40030070800c43e21089100300c2c3c11303040d048030101850312101c504415400030342d0f2035201d6418180040c0c50140c500040c4c2c1c4031074842d07101054600b200d203008002c00581c585020704880804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 176378992 1250 176377742 176377753
    0xb010e09010207111c020d12080708090c190902040602060a0b0f060d05101a030a050709081e01150b03041110270302030102031303020f0a02030613150c03060314070b03010b0d0e0303090109020102 86
    0x1c0cac0e821a0718070415100a142944510b03441e0441c2c1c075117103c00220071089030103095101962500844160703001036100b44090f801180402400807128040c1140d540011070303001c40490702c400d00180050085041d005030003503507007000070400c1c4a070791800e02c040e040400c00501804603d11030003080d60f0003100c4100202d401c1c00c0200381168000d05250b0b007529a0382014051620741130410039041030850b250303507a16640302c0025a001520260680003e0000d20900c0d60703907840c041c1411000300814506080c003503001d411080700c003580e20a00411401c2101c401c0030241700040b0030039103905110707a00040d616510000521800071400c00d1412a403901c82e0b02a00c20b011220108581c13541411f090194258205c00d00240003015403243e0711940d6441130009011000c0c0c0303001c00b00308441740301c1003c10100344c3c0d4034414410b010340940c4000d669021400289001401c00c40d00b56030a00061081075640c40021030200f00c3d80e10b01d50054425001c450307084076120f2905a03030300c901130301078000c080c2e015010b103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 176380242 1250 176378992 176379001
    0xb190303260106142701021e19020f040e06060918070e06040f0e0c01090b0405060706021303060908030712180204020d020c1b0f100804020f0d020d0b010e09010207111c020d1208 78
    0x320b507003070020b23072038520040c2030035000d140b445108000c1507200803a401615104003181a03a1148030700c1080981041c000d05241c604801400b0082002409080c1c80c41088844030420000010381801502c000101800c0c0e140c517440042800b6000c201c150f00150f40c01c0080d50149540d00198070010350ba400d0341c841d2490f41d50b6000d0410103200714007402c4c1d0409000c0000e80046009a0010b200680c0901d200081c52540c1b40c54005c1154500402100c1d051800800d1010207503024151800c40801d82c0400c00010354942101c40309200d1082000b4080e640100b1180c034020001e6041e00c20f82c0c0e03410415038180c0c0e0700c8400b0300c3c81c442b400448101c1c814842c4101c40c0c2c52500786200380319a044c2e07140d11041c0254813203408100d09241a0664194840350343d402d01c0c00107884680d407400c98984140401107003941014010400031500500c04402607205112070000314000500a1581c5c0e0402c1c2d4100d0044403a090511540403011031000e500700600116040c200a259107040c10003126950740c01499417030b03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 176381492 1250 176380242 176380273
    0xf1103060106260c0c030309030403050105060604050d11010504170f07060302031306090501150306020d1406032a03030c07030b0108030327010b19030326010614270102 74
    0x160b41d0355050307000310201c2c1045140822090b003079044006107800d2400c05c4480035000d465984111482d04407900040b84c01c0080107400d026480d0441d400b207441c1414079081c42c0205411a00b0854090100126680c0000840c1d0141d81250086c10105480282e141c8084071015039039286513400306001c4c454034000081c014031a100340c0740220001c1164802040390b589a44e8041c041c485c405807070399541c8465041c1380e01e8020007440010341c4030304000360301c0300c04ca4034810049440000140460a003000100583c940d030205100401c0c030796100080c80c410855413900700030b11150380c4405426210014050000180c0040e024046910480c00600641e0720341071055100c3c0000c2d00ca0503407a09103191038040b20550b07a030528501000d01000050741040e0180016800041c00f082c03402c0c2c0440c120014000d2641c0040c000002e08441140403031038442040d04800400b005114440400808220401c0c003042110222500f00c00105d10708280c080045c80360801310f10004207000c0c0588180c0c026020083c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 176382742 1250 176381492 176381507
    0x40e010e01061814191104030327141507020a0b0c100209010203091c020a140301110c030304030c1b030c0e0f070e01030f0b040608070329040f0f0f1103060106 70
    0x1000c5031a01404c0f515009440d248041107071010707480380f0751990011010301d0142e1001c0c0000714005c1d91075886103402411a0f41c10301d120040190300941860009100305000c000c00400c50b80d078191410314900007502907008403401002d0009501c0032601c68005a2004d41c40081e041c03440202e015142002a0086114120f00c070700340b40280035801c140f00811023490034820281802103001604a0501e0055001950b1400150820359580841c0703100298141024032400324050070140080e46800c82c04c01070155030b0b010081c801020040320020000412907040b0036030310130210900c00f601c800303502c9103032900702550140500b12500500d04001400040d03207080742030156a10b511050f034141c003000d0046001c1c00c03510f02100301d020f8030340100b0896038036544111001008a007000c1c200503411483d01d0b900c85140380c0b844100200300b00000140b56600c100c000c90f001036002c0142040d108080c50801c9040c0da400d40b002d418010171008040030710800c280a500e01840803002d03141140c0c0c9484060314041c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 176383992 1250 176382742 176382761
    0xd0e0604300c0c150305190c050904020903070f0801020304031707080714041703040f05030d1d0301110f03061810061107050a030f0507060c0b07030b040e010e010618 73
    0x400c40a039600e00c1c66019801014026009a80d0f004042c3c0e11110b0b4000507080e19000c071000640e50b03000300a000312211014540918180b5401d0010f0b103c4000000d0441c02114a854810fa90001d046a40c0c0d540c10400240204044040800714603600c50310f080c000d4004441c103074040703400c80e41014a50703610394405c3d910030f4601da15044040e8031800c0b0102d42442c000078041c410030300100004102518486001003c0c0d080e800007c3d03546605001c1c0e042042c00c11a48018065848031844400441e0030000f03103035407415140d035100c0c03004d814000000e01600c1841d0720f41c280900002030440f000c0c0c071400001c0d4403070101514040c3c25058408000d0301050422140500030072030045050046910400c041074000501d0f000315001b560300c400c001440800700e5441140c2c1d100c0301080310000c000d07083c4002c0e001003285081104481900d903c60818466004001e00b00f00341d070781c1c0a000034541c2c0e554000309603051048001c210585041d40d0150080c4441c0c00b0b1a02d00a000e80c48420040b9014010403200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 176385242 1250 176383992 176384063
    0x10203040803152d0301060f050f010f0306030b010306060905100602060c0a110f0d12020f040302221d0f0109050307030c02010519050306120c01080402060306060d0e0604 75
    0x641da1007010151522005020044d48000c8000c04201c1d90740c0c4900e0050707405040f411000300c00107042810036086500607444000f400005980070465662480351041200c0c4003030910315882c0c2d40c40c550440040c13031580c0004100300001d00020007403215030380c8090240d89003280d04203c0303510381c02440e0030b45282c04d00c0b40d0001a400000000d501d081043e0280c04004c000e401c14036810021100803500f4280080007410340c42c1c0c40303030381007540c00e592000441c41d03c03900c0000308501e0030b265588c401e062072003103020103800b4401c00f0450103034400c4a243c3c0344156002d4641c08112000303c02101c03000e819441601c800303003842540c3c10501e030107106115040304207a10000451404202e99002d589003080d11500707a040c0f00b070500042040025950801640320155554981d07289000f07001c00c248009c821a80c840c0c035612180c120110760f40c22210568001d901203607440d442e55102800603115110f41d110961943d03040c80b1440c03081800001e8a00e003e584140e842c0400541c080c4101046103190440d00303e003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 176386492 1250 176385242 176385247
    0x1080405070302060d09020604140405070c0515071b14010c0e0a031b03050303090f011b0210050c04090603240b18070e060304050c0a06180521060f07110102030408 72
    0x6141990040035040b9021700b010030240c0554001070015000703a40b15030f91102629402841e00e00e01403240a610070041d0501d1990030840d611040d6035020b1549000c01c3c0ca842050205080601070340020999403901d01c0e020b147e40001380360403c020b19008000030a10360924070103040603401601c0c1c01e800340601401000c90189145c440c0a04072503229202d0300c05240c00400840414402c0c0003c0d881402c0340c1004040741c40e8004102800c41308642004a40411140100540d2690115014045107801e02010403107843d401d550101e144220b0b440206100c1c40d00000200304138141610892a19a404281c0c2080b601c4024001c203841545858551010030228002d445c207109101d203070303088041440c1c1421507804d50000304807558402d803010b807425400310185030a249011080000a0015450f00e4000340246030341551401e811030040c0b0384510416404c8518100284036140862083c0c2c000b11902d50034003403074061f20707200c043e41d034000066011030081311582c005000300d0b030040c0d5119245c2d07807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 176387742 1250 176386492 176386499
    0x306010c020f1206010b13080703080a030b1f090305010b030d0512090c1801051e030705120a0803100e090304120803070513230108010e060906060d0c08060f0108040507 74
    0x1100d203540740c502d1680a01110014142035070f00300212030180c228682203030f035200c0c1c01c000c1d80300c004044c5510299850b03203c010140300080d0100300340ca12900305401c001c103101a03841c0000341407060080f5104c1005030707440e031110703900d6603c044a8030499010f0002000f005204d203041c151202002d84035240429002c00804001a0074001e60540c040080360544040c1020000003540300a5031005008030251800c0051000340381404001d91410668040e2149040306180440c2d25207031148180c921800800a48080c0d5038428400c2484c5164040d440329030703910b01f000415483e08241e0191600d404040c0c1c00080b06000000100d9003a15400c03060030242154640d034100b07255000400c0482081010b00855000c15000d070a8003015002541819076020841e19250120490700c51032103041003515001003145142590410360415815100d000c11590303039102164443c0b140640e140c803501d04e050101d1000a07405070641c2d000d0107044850242c0200150011543c01c130301524094a2908001402c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 176388992 1250 176387742 176387749
    0x4141302090414100909050c060c1c0906080105090f01030b06010507020607050d0201053d0b0a0309030323191d0a0201020625030f0e100501031407062705040c0512010b0306010c02 79
    0x7402c1c812101c4048505061915070303808103103180d41da19400030403d8cd8105000c40790300501c2740350142009542082c414540a41074403108641813001501c001095008210564420070442c1c281c15000340416540d140c4034035103155075594110115005520b82004240340300000001c03084000002e0200f501031240d400807449012241c0f403030305d2840c1255200c000a04c8212500900030044003504c00040803011410007030161110307000d080c0b2001c40d034840c075032001007410507a4a4005d030307540300400071004911880f20010010036040d4002642d03190180c401c1458002240e4500340d100b86c2c21b640854440c181641d8100342042c1400d020440c00c034001c0c403400d40c0b1075030040d043c1703048024002c112071049058890074400b00c0304190b030849441c2d03001030081c80b402d080d040c00c001c14008002e143c07076854400c000b40001d800100d01c855081c000348007030030070091404a5001610340104204035004d004140541164081c0c020114055207606c00060b1541d8440e041d03c0c421001a100e2802240c0c0c183c0c2003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 176390242 1250 176388992 176388997
    0x16210e031e0a0b04030809011a1302030a02040e0c0c010e030a0504060c050709050a0b01180e220b0c04050112090b010506130308030702060108070b04141302090414100909050c06 78
    0x8500c09441000d4101c0081014500c0ea02e00850290303c406c0a541800417000d030039078600344045480c0804155403212103840b10445014030a81071640103031a9210b02005070702a00c5160b0000da0046841028800701034608402402441011402003025039041c0300e0302c40d201c0c05051800d00c0498030500c4100401400f4a00501c17034948101c042e58520b544580b90402202d40944603204181c0c0d84d00700491075940c101c4c01210240c038100002d40340305898590032908480c40100bd20a4100f4000301c40741080d11220f000070b8600741d200706800c00b1860310400b04103a80c0c01c2403282c1c03030000d090a030300080b00038030600c500700341150091a00308040c0e003042c00b8030610b54031084141045070441c1100201150105c000341d0f0040c0e00d40c1d8090300c005d52519880d285040090303001072100d44c0b8108001c11401503480c4200c404000d00796086c207450305101d0f185070000c0c05102c40c00754006040c041c1240100b034600c11200e06c80c0f85103140b00140980c942e1410000c849000f40300407c0d0303610888000c241403501002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 176391492 1250 176390242 176390293
    0x20607120506180a0b030c030601082806090818040203100512030705240601082202010e040c0c02130b1c050a0c03030203040306060614030601110316210e03 69
    0x8150240c2209248603c51000c085400b9007125580d01031000b01498280034002150100300c0007017109505003041b150b200c0222101d9000c6184141e8841c45c0d80e005400c01b44125a030700030341e0400c610780f05801c000003142c0c03007103500710317030461200c08141034600e02403083e280550010b02c4175a42c0c0505003000c1c84001308102c82e0083d0395100500401d000a08108604000b403010143c0454050107454101d070805000541000d040c0203201040061301040c0d1405003c024620b42070f40340540005000681d111440c41101d80c0c0c0190034603490001d01a0040e2909096034402d40b064040c04180c0d030214011124071a100540c0b0025000f0380c910711031840c80c40401c001c0d008005841414400f5034a000032042075a00c11805600003080c00c00c1440102d00c174090040805003818954180d60100e030300c00d2840000c111605000319008044480c400c100240c6140707400c0011040300400c0f55003024190030b1221002d1181d007403152a0445180c92144108186441c0d024004240c41c411029030798511165101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 176392742 1250 176391492 176391499
    0xf08010b0a0312030515062109010b0d030e0f0a091a100e040b0604170a200f090a0905120c01060f0b040b07080c0a03110105090a0b0106120b0607140706020607120506 73
    0x80950141c1d40307c03030041502042c0c00c400340d900c504590703c07201c41929000384070076002d13450107030080d805890f8204414100b540c1480d003449500382c04000500c40d43c024550b42c039001494400f001c070b000f0380d40341c0c4042440d010b034085401c00400700c4402c000c61070104200110000e00d40d402a0382c480c2c01c0036041900c003040010b12a40c1099110914001c40e6400840030313a0740c03940855428000e0000040f001e005140c007400840c090041800e02042c00c07840980c0c00035000e0041000080c040311050360100e22242e90040913500180503080c0780c000a6000805155880e5107004400200c900c40310740050111400c038034051382410b180c5003141c1895045a90160f600d6034040042c4000c0100510042d0392407803213074680103100070000d4052403c59000030401002980130460a02c04100924841d03411186249007400440080c0b8652034041d14400c080e107a0007802c04580b4404200c402440c65484400b1401100c0e00d56a4a50040380e540d04161000d2001c14441200c00300c01000f950026a44550090b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 176393992 1250 176392742 176392771
    0x30506030a081815070302010203040c06090b03041419051c030203091b011101020705010c1b1112101d0609060c040306090c0302030a0b0105040b01021b0603090a05070f08010b0a03120305 82
    0x44081900c1c07175101050440050754000200002c0000c1a000000500600d2403ea4840381c18012420010f10000d030003d0b0081d404414a00030190342004045091b060800599600344000c0c50142da030303910310321240420500a50202d00348244203100b607070300c50b02d0388400811985a02180d03c050302e0f0024440c890410065003070084008509000a2041c83e21490001030b5500c290500180844000e003101c2d182d440c9268855404140c801e44200d0b030946003140c6003841c80f00143e60803883c044801848a00701c5080200e000f420818150700c21000002030f000303a540030358402e00f0080c1c94202c21a000c03405442d080c042440410b986030302400303501d84108012542285c03a500041e2416a0204044a005218074010700c80c07802e10f0b0080c00500391080c0000c18004200360075940c0008041024240100c0e008000102c0c003035003c00559494075048400c1c2d40001c1d4079084005050b0300c450094011640c00d02d0a0080541020f20001003100d4003e050b0034006182d00030100c0c0900009004e060211900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 176395242 1250 176393992 176394019
    0x105101d060906070803190905100c0306051c02030c030a170a05120c0901020c040b0609010e0a030c0806040b010608010e01060f0e2d0603040201051b15130201030506030a0818 77
    0xc2400070150030f40242061170b00c1c0c0c0b03025040c00c41f04041c07506020084c0c904001c44400003074400501402c0010400c1c6000c12508074001d02240182040d0344071907441002c003242200d40c0e5020b0206171880500960548502066400925075241020324005050464012142e0301d804803a0000d000e80c8445494944e103401c15210003a40010030589050b910361000182188080d07070108001d20b1810f2050b1000d02c0070701088000250107008040c0d02d54140140c4400d40355103070781d581030703003401441e03101c8007100b5140d032905191655800c0884048610700703515800400c043d4040c840542c102c031070443e010180390382003070811030700180e5848046040c0a801c00d030747c51941e924804c80036051150000d00c01c030030080809084d504501050350540c042d034420000c0c040541da020040340e032112030a5061140b0000004180c40c503061a01005101003050740091007102c070160108107205d14000d07a410f20070703a2501e40404d40c0311260342c040148120070800809c00411341804042b49034200003004040003560 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 176396492 1250 176395242 176395249
    0x20c0f0f1516030914040903050d090609080706020909090c060301090f0e1516050405030c04110c12031e06090a0c02160308190f09060c060b060c070503060105101d0609 74
    0x8524403c90200d20304500611815100340940802c40304102c0701400303801260b483c0a40785105011440f102c0035200c410840c10300403180c0041d15019805030f0300d81e5551100381403c40007500081c8010780709104403408180d0b6503000282d946101c100007421545540d2070508880000c1804800c46403200c0c4c0c98003d40910345000740200d201011b01e002c0e9006040c0781001c02010006014200d20082c0f00007440144036580340040d5000401500340c60018081c413502241030a640200130007450513108202c401d028091702100a0f50042c190410208016002c80c410780032105803c0314850380102c2c210b0700003000000f09800070204400140145c80d503400d598005003d0100d5960000e865944e4009411600312003400f50b8088469850719200355802050740000741000128070400c030410020000040601c4141e0b80540c0c04039a000b8009543c82d0841d0010035203600240c85200d100703010f2803000140508180c40320750381050300c3c1e58408041c2a03070902d6a40da4070107182503407030704285c1c1448100c92035203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 176397742 1250 176396492 176396527
    0x90d0204090209150f01030c08010308030711060702010606090905130b040206040906030803060a051504090207110d060f05010f061704060b090426071703060112110901020c0f0f15 79
    0x800700c3d5403e600d1001c4184500782d01795074449410140b61803801c42c4005d034080050703410342c1c1c7d101c1c507900e5403034550300030072101d18003042c102521a00030781c000c1c045041c0e0154002030850f100b5841e0041c50320f5036510100100c038030849400c00401244c8aa90780060b1030030300d1943d48248018082403e06072220100d01c11220242c00c01c07980144004103021b070700e242560049000f40003c4070164144004038400050a00441c0720315101c0c160041160010032005040280501202803c3c1012071000c40c10a540585290030100c9070123072601d000495104008540c0070b05858054440d0350140101e05e40c51210a04002c1c801d41d11035584441d5180b8641d04c6804450159004502d00f041c220000c0001c0d0301044844284d6904c80e017070030800c2c900081da41c00c2108071000890b9040c0c941307940e940c0005996540d1200c10b565200c03480d01d41814411542c0c00c0c0a080e80800030790031034100c601d6000a102c078680010041a6015041c0d03c0255628078282c42e5000398a912100994180501d80074800d1649 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 176398992 1250 176397742 176397751
    0x507021507021018120c030207081b04290d02040209040501140a0e160c0609050a08130e0112020f0604030f0c090e0303070c030f0e03060115020f0a08090d0204090209 73
    0x5030002d01d0b0b9400e1210a900800f05134140340e290040540145075034004c1280801241e10007072014900b040001d05009000c2400104480b405454025080c2c3c14131050400803403040e94070580c41c1881e4040740c82d15207643d04005034016880442002d06140c100003c802c0308500490340a03800304641401341d01d0701d0041500034600c1c540c00c10606110242000004103130b41e0401c0c1200c0d01c1917420003240c0c071900c902000781c1000a04103888071410a04100c0c002d00040880070f02680310f5600000c0c2000392040007409006c1b03030803810000a0751503007800300c4105800e01c240c1a54050541000f80903150005446102c14001802545420368903690145409604c0009460745003641c0001c0009616600400c4500840720002c5c0d4032350321f86400b02514000c1103071000341c00c01202c0e0008040d203500a000c5001c4c0c480c00101160200d60b5500d0500e004620115210300060060b080c1c85d41d20b0b51700028915280661080d0b8080c1014921420f1060051480405aa0040c0c80f140300c0c4d000741e1251020a03000b17 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 176400242 1250 176398992 176398997
    0x3150a06080f0106090606050304081204140f150a0b060d0c0512011202010305160816090b12041101020c06041809150b0301060509090a020108090a0b010f06090b120a0507021507 78
    0x80303845c000d00a005c684031a40304c5401d00104204200001d15500d0848028140500078016940c407541020719080703041903481c074814410a565080b21000010340030311030282201e1200020340c3c0c0c9014050983e1400307001c1d0758010205000c0110220aa80c104000c58001450054240741828481c40101607080e488000c03120000c00300c1c103081d941d05000782a030003800c1d110610101c805d0342e080100000c074010f01944541140d034801c1621148900ba10200500d1440d010545030241c01c03c03d400d449009460131180010b2603100b03200154004514134a02074802401182001c1c50401a4500b00c8100307410f0440080c0d0340c03c80c000001c1d444040c0080140e0300c2c004000703103000c9104245800c549107500401d00c2050720b21308110700508001442910a42d080c60f00d25110b40b42c1140a903d0301c807058000170100110400086411045c0742e54034003c40d8029640e410782903a407180c104003140304c0d6600b070002c54001e402c00685000103c1d0000c681100f03407441200d6840d103183e0b034030074000c0ca42520398000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 176401492 1250 176400242 176400251
    0x160f02032b170f01060e03150117070909170a020f030a05180102010b0a060f1206030f0215160b0603030702090103060204080f030c07140111070b030708070302030603150a06080f01 79
    0x41c41035001c00c4200d1041030076800c5030014180b20302000351410f014814002001000d10445520752001d204001003001110032891040d615030740c41d4500041c035000c0c400224030412400052212041c09054007454101140000c00201e00c03e44519641c088010081940320f01c0451841495081000f828101c0031555002d483e00c3c03403003c005000000160102d411a814034044c844180d903010b080760121750345400c0c070491410482c01d0640d00d0303407071786000c80301c05c5480c055000083c44080140000c2c1c4520895050048525000c21901140a4046909030342d02d801011180084c00444440da0413500007002c0300e044c50010350001b950410709800460b4116004038040125480803c41512a00c0c00c2001442c01d021024000301e90b200c3c020300c070715440d51054000c01d00c20f99025000c401440142001945c03100c03600c40da1071300358540c4190b07505070000d814a00061600e600c01e20035a80591002009450a040140c7d2030481030840544030b6a00305680c2c1c0d6000800340800c10003240080124000400d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 176402742 1250 176401492 176401573
    0x20a0201090503010b01120c0e090a0905061303050702060f070b040f140304080a0809060f13060206070504031203050901020f070605040c0510081308040b04030b1b160f0203 76
    0x40c140703200d50380000d010303a04002d059145aa04650138a40d00c0e0140d200000383c02c0190142220b0740742c03410081940006240c014403110b9506608202c41c040d00800c04c035071941e1900c500740494415003104c0940051014011807005141c004024030f0b07101c05c0c4410f40d0b800c010300c54507070205401d01a03e04580300c501031060380d801c2040600907002c18000a10146042900e000f015540ba13880d8004020002100080c403d49c566954200740c4160400c0081e480d62100c1d0281e0078000c2d0a1340728040c50015100300e00c0081d11032441801141c0a40e5404001014015081903064003e00405802294155000d00c0004d007444032540252019501603040450141003904140848014940055000c0c0740350841170b0010a40268846400858910307051116507286c3c01c0c06011801250001034064100150000074000c04941690141e42d04400c2e08041d180040207007503241c0704140b000b02443d0503042801021071641c15124071801d0028041d100022101c10500200c0c04000c40080c9402d014000d030315 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 176403992 1250 176402742 176402747
    0xc01050709050310020d06030f050303090708030f0d0c091e031a04121805060409021903090b0a0c0c0203120307081008152a0a0e03030f040b0903030415020a0201 71
    0x54000d8000d040040d0200d04220100ea01e602000700b082c0701003a00014016200741c81e82d480440110b40010b400c4408881e14a04661030360301c01c2d2007000591294550204000001100b2101d6144c00e18482034a800031851002c4007030b0580c100c44009021010000081e00545210000d11040d15118092040d505620344441250745510301b80f01842003450420001420034080300908075042e003805410407400c12050220b0100c941c01140d0002800700e00020761481e00c1e006032003540340d02d900d0041f003240744020413021140b1000001d04030700380e202e0106a41c08000e82c40388050001c140b903c18040f05403500072901d820700c0202000618540001003120899110040e41d40024111800070b1040745042821695070030344c8042050280e100030040303982c88070f0740d090311040700100041e2007503080540001d01105820006a00000c40e034181c8045040c0c1ca00807040700c10316924000b41908190030500c0d141d001e90002214103415120401c800700e40d240c0400c0c0441c41c040f143d68010440c4a1807071000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 176405242 1250 176403992 176404001
    0xc040c05040f0b0304020303160303020301150f0801090e01020702061c0510030807060216060c03060618060816090e04050105040c0b0309100b010e0a0602060604060b0a020d0f0306050402030a020c01 87
    0x60908000c000d1005001e4120348265000865400b42c821588a07161030000a01b580301d41d440314441c25a81103800d604064060300990b0480d554030042c00d140320f40d0140c0035210f411010b0243d0000070380d85001800b01e8840e9520070302d41e5920080c0010f060106aa001ca940d0750701c01c018041d8010750031201180e1980c22400382c0da5029000e00018034a062940c0d440603d0742c055004024501500420701641d01c40341d200d21a00002d800c0202403042d00c1d54080b000e401071240f800b52900045041043d081c201d01540649000c50b459951109101e607240031280000c900e03103807081b604001c0100c9000824195002905001340c0c002c40c0009020304141c681030400320078a601110030007006200b009000d00000c04c03c810703004c6c50a14003203029582c84004840032460300e08a103900c20003207140480c070751b41d000540d01c0c4101c0d4140e808002c0c0d5526040794824030b000300740c401c0006901140c550345e11a0b20441c00304070681040e08000c103500e504c900000d010b0340c000300c4000203003540c003180210800409024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 176406492 1250 176405242 176405261
    0x10b03190b06070605010918120503130803011202090f0610110a02030f1c02010b09010b0a2d110307050a02100201021315030b0f0907030b120a0305070309090b0108010e1f080c04 78
    0x1080243c1c00d0640d527101e18001584000360a002c0084000342d014000700c240400c0c0144d21038012548ca68442100b1baa8552014400381e000d48121000544118491040c081c042c0d8001400700e400c504448108a0385d12441440ca407100340500700d940d60050301c0403c4005050000100648080b2304020590300c0c190b00783c44203880440e8108012816151600ca00803415a2280940b8542d00c200d4880203a84022113500340700c80005091200441c1ca4001000820f09030802d0394800b21000d4003011402d684e405585405802d503045102188010f1410b42d07280100c030711a9000140c01d007040184e601e0020704e241e900c054020710001c002c03000010b0341442411070701c0400f02c521191051811010680c0703403c0040c80c903001d03d030b42c4075044080c42d070b00c5900c0c0c8d0b4401c1c02d08404403606070740c0c0d03454003c1c915084900210040b504a503004079045010340208401e464060b9615101a80303003582407002a540035103040b9919035030811030031007807400240c247e000c1c00400d002042e0700d00c1940240401c581c0c0c03221 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 176407742 1250 176406492 176406521
    0x5101407020303040c030308270c1503010e06061b25050105070b16020a0219030b0105030f0a06020714160f06110601090209040608150109060e010b03190b060706050109 74
    0x404c00c80011446680c00c0140c90705803031f1100d0340f5640e842c040c1079a0a848841140790084c010300200c5185030005e114480c0b010f0548400641002800c04a4502e0000b0f024401c03c250080000070442c0c1402c4018201841c07040068202c40c512048d0442e051030012012085000010304500c4007424802a01000401e402c1c03900c1c1d45015000c1c1c60b41c2da00580041d09464540c0700160194808510070010289030700d800030b14081c912040d03030000c010741031243d1004451903080d000c00020145004a844e8655000000280000c00da03c0eaa40400a509c2000100c8000310b01c40d003000c141100c10024200191041c43d902d944990800e400b0b04902141c2c1d40c07001d030801c40741d600d0000d46504042000c0b811152846809a00c03803c07048001800303008076402068030391188030101001e100d00005154100c5889040170003813180c0b0741211030f4880c1c0b42400350300074040c001c0001c1a02980c1070314041c46036540c1810006a0310a00200003565640108030607141c854032040107100021061140d0190030144070b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 176408992 1250 176407742 176407747
    0x50112030e041104081501090605034216020c0603010f12051014011802130e0604110331020a031203060e0a0905010506040b0a150c051014070203 64
    0xa0350024040360504000a000c0d54450180c004041c1c0c3d08816a03014100c18002e5032200c16000c580c894081400348500e840e42130070000001541c0c18041043c040d1580f85071080d05002e5007064060909030a035000850b1102e4104994108012036000d1303203401014030700503400000b90a0b03c40245403503000582588030340e20800c010010036130a1180a800c6610084000b0311802660a0690a05010002d0000d00714180103032001020b205000c04c40c162404c034041e928001003012504400c0b8000c07060408042070344024140700030b40304c0300d0810b58800002000416030074000c14010109800685614580304110403c0214460740c50080b41c003816001640111b007600c843c2c0010f0b00680440c40054445404122100040c510079000580613203240a030300348032400d01b005404000d10340604207980d15440c1001003000b40c9400d029000c3c40150003495104850305004a2110812900c5e040205202c0504c0c42c900000b0428040d0019100300790900150001280e600e0000141c001480780e821074004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 176410242 1250 176408992 176409029
    0x50604050c0a2307030809100e03040b030c071502040f0503060c0a0f0215040c050111010b09060f04060315061d04050307060203100b13060207140d080702010e0a09050603010501 78
    0x681c1c0a0740d090751074a151041001202c141116400e0050300070000c520040019400145a00078440500400004041300c0d0310207940802c100455010302c5003075500e50003c11007086840304400c05950014103030300342c503841d19500d40c1c1c070006500c00d45068545000d4000c03c0c100000c1c4480c1303104d1002448190054004e1385802520b44005128070340001d8140704651020341d408910030002c0c8004d00c0c3c0c40b004c002d0400c1c18642001c28413240310744942800100c4e5817110005403036060056021300c40d4050020700c1e20342ca40340e04200101a03482510354102e42e40b400c1c00000b040044c0842000c8001700c030000546241015001c041580307000300e4100e20a80408180000500300208031481550400760040e142e403521602c0c190703410185c1d0f00c04880081e0114403000c4842e006041c4100b120000e03000c5841c3c441d0784000c80d901007000d1110300b6030301100080c15040800d5488008100036881450300c1194240d0b10700001d40a900541c000f45a0266035204000c6107007403d04c601805441c2d60035040c40c035290ba = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 176411492 1250 176410242 176410261
    0x403060b0f3109080f070615031a100311010f030e030d0b040c020a080f18130c0e0423090313180c09030f140109060e03120f040309060518060f0d05060405 68
    0x180070315503450400001034600502410303a00402004800e01c3c042300419603282400c528402084c4c000405480030701000c946048ca000506008490307104143c0c949818915006481455a44016600381504e410300b00307140c2c010a0000b40600c90114400241c2003d0900911040342d01d4842e00d001036500004800d80481c5075402034403804c060700360b16140d681e100b81032400c0703140342401d81442c0c0050082d0000c0c03075203042c0d036000001c0c1041141d6408c0382c1c0845020421050310b0004082c0e460080b59040d41541c141d03580c2c840c01b64014a40d03c00c0f80e203450383c401911158039041e98040b4041040c1135003920030114807401101c80c001101c1c6010910325085846200000c1d01040d0020060320b4464900001d1540c00e4029183e07141d0461403c010702140c07203103110f4584e8031201162030000701c410f00242803100034481190081c0d405640c2c844001d0f0900d80c0998980d4410f045480c170000e10388031078450a40c2d0301c03002009240c03031881916481b003450042000540c1d02c00b03071201c0d11440c200010840c0c3c05a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 176412742 1250 176411492 176411497
    0x10c090e06060c12030c070c0303050409050907031e02010e0a03030809060903033d03060b1003060b071b1701022503020c04112106010206070c080403060b0f310908 72
    0x12038101030666988490f2031b440c8151017000c1c0000d048280c000740000a1541000c01f500440d0480c503c140103a6480c603200c80c2e1600392501008080e2994402c05800c036003c0c140318141810f00c1811701d06010640030740014009015540200c0000388000d0030000c1e000c0307003844480d0700000c25400550445c1030070070f100d082d004410341044240c86151800c0864001c1500c1c8200c1c846100124180c01094580c05d000d00070704541075400c1e0141c4e0b00340b42c201180c2c5105e4424a0111483d90312040c1c1800c0079959824680b01030080201003010f0342c0040455800c0007208070102070600302c800184e56403401c40c0380000412480450980118400000c030000c04e40115000d04d0000084400040d05401c1225004030350058924548504850303908034142c054280404a0082609808403402139a500c0401ca4001d0102d185c002d00c100d10034070040000400a03000721084060043c00c0344110418a800704607038800c01440d100004056090003004980c1c8201c25215a4414000501204015488400307091 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 176413992 1250 176412742 176412763
    0x30206011401171303030c02030702030703060f0b03100509010c030501080d0c031b050705090109051b0d020f03090610080c030a140a020a0b030f010b04050d030c060b03010c090e06060c 81
    0x161034494040c80280c2c41014020b40388409084a805141030102c0c03030007214207050350120042403401f200301d440c050001042c0d48407142d0080c000d0105900710b0b52004050154071900b0341c0e80984070100302074140d40a010a4100b01d4402100151030b1618081003401d554003d04c05c241494641740060000754404550303138500e5080c07403e080035509242d00e021102c00b140701c0498082070880f03881ca101000404a004002c030f400072150b40e0120398070b42403400c0454400b910840340340e0f41c10661040ca0f4102c444007804800d1406400142072030351300c490301c40300c030b0384200d501c000a0381003101088140101d250f5440003138202d9030000d10507040e00740c2c007080e0785e880300180290001034640c0510096407010400b48442d181d0240031140020342d83d960120f01c5420a40e50007041c0301c01072001080c809030300c105503012035000070040300c541e000e0754078252040007030220103562494a03041c241140d520240244544000e0fa40d0f1001c0804c0d00e017400d101c05040c030103400d2510a00c01004021004e03013001a025202 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 176415242 1250 176413992 176414009
    0xa0b011a030106080718080c091f031412030f0f1302030607110703150507020f0613020607020d0c0807060f030e0c091e040503030f250e12010f061403060403020601 72
    0x19110702c40f050351b82d00c201d503075034206030781c20302d1408110031001140c0400c45a6064601d005103407602c0e07111285103403020b0706040348d181700288100046940700c8403205a0311048402c0c0c90301074406038a00f500135401122150015040e54061080c104180030f00d00781d100c440c03110780d012a070001d42d00282d02c80300040e101204200030980400804181171100c04021230380300c0d8030b210304081d1401145001e410203c0d110700260240070303000c240481c1c001c600c1710f105481e88003000c00c0c60f040c2a800c1041c240c000003400d9030005558000300c80002c0da5074001c100500f2803400240441c3c0d00c4d04c40010030300664010b002040508080b003095910400081c002100b00c012a08982190750703000c1a0114121001d50080b510f214040605c81442400b00042d4050f0701c1c40311044840355a1b286040e0501004081c042038150594000c107010035120700640c1c044c003078000b015070440384030402e180c609407007074449140c203815581c0e03030301b00000708515072a00e403050002d502a00d480e240545010303466140500c5540c2c0f9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 176416492 1250 176415242 176415257
    0x70305250f031a040906091103060f0a050c19030618020405011b020312070b0402030c0d12080c090409031706040b060a0e0312120403270603020f12090a0b011a030106 73
    0x290401d440001d1422035800b44c81000704039072a040c2000038040c41441030342c01c50300000c1c43c400c040c180891002e00c1012070348118011501d9802c5c6503001003000070100c0385500310500c100c804005203c0e00c400340e580301e1a0f07408244141400721240810318640400500c0034070400c001c22144c1d82040e181c00d24010785600d0300d003200319a0b0011904044070f0b602c80582c10200064170004000403010340c54007941c000c0d0300b1680c200c0640c000b4040b00c1d0b2131501000c0c06442c800325002210314031408140c2d900c8000614600d00708829840800c00307640801d48110701240b84107201d5004514102d03a01580190304840c1401007101c41000b08040e4490445d00304100300086890740404d88080251146a09003030601c076070785043d01c50f1540a510420389044000492144580b4500c1c1c4d11860181e4180600700000000d69152982c258001c1d403000c0b2250010032418032a40c40c440b6905181e180c821908640940041141407415030740800703050300420720a18071f000001804003880d03000c0c3d81c10348503d42071240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 176417742 1250 176416492 176416511
    0x30a02040b0f150712050906180409021302040303030b100f11070b1206030f01090803060d03090314010c080106050a080a051f06030c030b010305040209041118070305250f03 76
    0x1800c040040032440d0f041000300a1240c0c40854040040032154002c2d08044a15940f1503c04c546902c24080459403221040c00b110b013008102c002500842080100001402a110f50110303050071814900401401c1e030102d010001d041d054041c1c4001c0780d030210b4202c41081a00301024000715446600c28007040160710341c4844a007400c01020001d0580404043c0c0c444140c41300c485401c580440f070550203070003502003a180e415014001c03008607a030300003400c505642e200710078030603003d101c081c094040040d807401c00408221004098031345d0400c0c100001c54404803180c00580020010b91107001008010040301c08469030000485801c50102213005c610354031101c10800041600c0e00320400402110744002031050340580c800c081d1808680ca0900c091000b08005408a4008a8000c0d41024000d8005400070b03014840001b68524003c0802c680681c0d6081d20044045086402c4000700743d80310b052200130304080c082000c0c0803002c1c413a204020300100d80300421910003200e00c207003810344404004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 176418992 1250 176417742 176417749
    0x1d0a120605091908300402060a0905060309010501030b070f080f0a11120a05071107030b1f060e15070312050c040801020c011d01110a050705010204050406260705030a02040b 76
    0x245080800b005907106074050302e04010300396a000c0c0d0050175203c056840803908442034100a04e86080076660724001c175036102e4092151f16480460820100804040b01040b290780302c001941c00381424200008141d811403a1011b030b6204054070500070710810550801d4a6640030034001e5114030513051035811515050740710300150800280c2e06508200c041404c801c240c25156a080c880e9185c0342080c403050b115078a06803501c041c0c1d400c09080300d4005d24001c1c808100e060302d5194100c2a5102014401e4428601c8803180b05030903044480000c200311455880791a11504440100500200c81c84c58000942c1d80501030703c10303040c8001141c0e612032001960007440c0380162802007074076200070356841d00d8100d4403900034403410f410303007207544036540001c140c0d688144108540950500b6615140451110080e10203420042044072550b400f013001060f00e480f2405444003c110360134032410780c550314142108800401ca82510026848007900b009035a03800205c07409280c1d0190f400041b40290240070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 176420242 1250 176418992 176419003
    0x30b01031107080304030207151407020f06040f03031e09090515031b1201140c030a0b040c0c11030a050c12030c07080c01110604050606090a02070c061d0a12060509 72
    0x350851034502064000c01e100729030f0021407240b482030782a00e02c084d0302c8800b079000760b00c84000c110300001d14209104c090082d081005000403400207000d4000c41001400240c860380c800e0300031041c0c24100c00c0082007090741108404007208813454150007003070480707440145480d01c1031040d0714046031280302050314052a0422003604e550083c09503016031007030460700c1104a40150700d079401030b42c1a4684544503a01071062100b8150030302c080b00003e07110514440306640024009004460340c420b08001203035100c0c45400590080ca4981c40390340e0300d050600c10316008040903000d00a4000d506220001040450480000001101c08950391804054102c1c030314090705842109910411350041040040041c0215030000240c2c2c81c0032044000800b0b20b80c4520080d10010160303801503010410502e00000d80d2139200f62050001404e110766921032001d03400540d80b141000c9410011620640388124600701503118050320b0000d895881c011241950b01313140000504a1a9030707074080760014809104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 176421492 1250 176420242 176420261
    0x30203011a07061d2a030303040803071b0b15010315051201020708040f0f05010507210509040c090501030f061a091f050405041a01050304172502040e0a05030a030b0103 74
    0x44442c2281c011440140e40d41715040d442106584092140301c1404600c0060a07081020180c040c6085403600d9403500d0440c1c00c007508040030b00c0400380c01098040e40d0780326103149945c020000060541450b51440c00e401c60003481c2e1504042c10310034a0010f40000f0441c03501224420b40e140400003440b100f85500901803000000c0181c03000250005820003400e80b41c2c01a1140c0800000b84596614019a014404c50318004c4c41c040e030f003e9000314080240d501d40c0c61103c0c0b8070300f08189801103c1002600b211000030059010490303201e010300c400c4d42e241c071802176032584242e003c204407803c000c01502484a10000c01c5c9240070001000b600986400d401d20201c032581000e1044842016030010300650458003803a80194a0080380c0b500100743c000800a0800068498520356182e945504600390344d512001031440e802042400030030a4125502c244102e007000c124070100303e0070310400c002c0e61281c01661501d82d0100c13150394085203001c400c4440c1211141030016415440e20016800b4208010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 176422742 1250 176421492 176421521
    0x16032a0e031006120212010b03060424230108160b0702280e0f070c0b06010201090b07030b0312183607020f0a0302060610030209060a051306030203011a0706 69
    0x101c0081c03e50741003e00c41010910032030750315101c0c04a40664500321041080c0b00327640340d071000020401040c101160410700903031072501000c0707580510051f541601d4038400d80c0ca4805102c0714504506184503020140540b15003400b074559508900101a4844018020a102410002454000c560307030643c104010302c0c04403402c4841d17060020b112072461001032280b01c200054540c00039101414031117680744298103988913900811200c0e111b501903d00c0c0104668199982d8801c0f000200305030034030300e0344111010340d0040307a00c0b003032441803500b00303210000321031208030090181142c1440081d90084001030165458900a1170045666843d1725640d10800701864014801400c130b00900e5a549200b10361076000c032580340c0e0b02c21525580e0340c8074520020340160402e00201d0000e2601c50292140e40c843d074035001d0705058a11000881640c4401d6960011410020300b40c0f6044e5000740f0614000c1440c4c2c02c04509641c542114400070030128041c8808000300080d0140405c41c456104500c1c03009a81e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 176423992 1250 176422742 176422751
    0xe1501090e2b0f03020c071503090606030605061519050a090b030702070608060d050619480f030b0627040605040612020402160b16032a0e0310 63
    0x100851420040e001e0804000343c10061125075040c080c0c02103807070310180d0b4002402000d01e03005610040c0e444c556000000c0540781e6a03844049041d500541c4040c40c00b0340c100103250304200013040b40ba125420003000f020101440301c0352454000030182c15030b05020b4103080e541c504c0301400440703110481d5042194064000301c1405031860340020004155038154840c1d445c2600e03142c040140c480c40b84500203007194400300010303e420140c3d940b600d44e61101020702040581e17224140c10700c0e50301e58861a0b0103070032000b0b1454a41c00c10028107020300d1060070461010301003968100030f00400d90303940c0c288241270300e50000f00982d440f014112410482c400f50b0340d00d4142ea81070400783c00e8203e459040da02c120300b011804101480c051140c1802c4030042890781901c1c84040e820700c00650080982240c1d800d10f0001d0120100d40f4114010380300d10031070f4004c0f0812520310f2001030100c1d59941c03031603848811031541c1e4402c101507110060900030802d00740500400d51103000070b803903d00c0c000c0d070548019081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 176425242 1250 176423992 176424043
    0x10801030209130f11010905060f091009080307050303160801030f170d050a020a0f11100e16080a05070e0103020a061809020a0504060207080105060a0b0703171602010e1501090e 78
    0x7001a2117862035401d03038820740070315942c4040000702d0240703a2100c0048141045920781c140b500314654110920141045600e6136034071001c6600f150083d15040d038440d0030000400a445820800110440d00e15007450304155046450700c0c03804000c10840184805150b1524204101ca4202600e210500001c2e05010321308c0d002d00440081e400441440021907407158090140c00c2c01855000d207842e0058004041d5514401d010102401c942022140c550081d07480c01c0a5500c610341c0d080015150060050031187d0851910602d000709a600020380c03005214014001603817036892001c112502c9107442d40380d8885104500444100725031020f19100e10020b1a14202034100014208403502c42d020760b00c40a03034800344507003030f030784d041b41c140da0b022024400074450f10065901500c00c69009203061009108000d018040865090b15030381561442091075246450b0309005820100340d003000602524420f03012142c520b04418007800a00503141c22200a00c2c510810030b100306500300303018104403040d0f03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 176426492 1250 176425242 176425253
    0x150803090108190507030b100329040b0d230d0903060518070f05120105060d03030207050307080a0c110d0308070e0409051005010801140c07021e06070b0702010501090b010801030209130f 82
    0xd01003801f038002c2010403010b248a030301034403841418584a4400c2c0104603150765058104c6002d590840e0f034016074881d1109030648401d5280c0c501c25119071109900e91155040d030404c19101d103002c418903503110314942d9503800d910580c1241181d40c425004102601d070b546003144610600714802140d4411148001400401c2a018500b1580e00f5a28894440c0c0c03401c200c1802d888040b03070740d260400c500007981030019200b07074020280d003401082981c2c00c2c03030345556421100790b201d0303280403001507001e0038408188203011170f10f0218000c04a030208900c0340c00b694064005100100440140050103840c040c494407103030801e4050503400016a104094060403000003031000f03010b161344c55864884501850041d010324203000c1c400c0b080416040232455401c0210842d126000e03202051000509040541c6036000035040c85403082100340b4292812090080c00c48805030721003c482400c3c940300c2c0c01c01c0d98001500d42d05580d01039881480c590380ea200f12a036804003901000b0042d0800c0e209204c144603 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 176427742 1250 176426492 176426501
    0x71e020a060e03040e010e07090806090a1101030522212705031e01020d020d0207020414100b1e030709030b06151801020a0602040801020c0115080309010819050703 72
    0x1449504104100702c4405241980c80c002c600482c110140c6210041c441032121520f001c0d4000c90600e0039400c0035488550480c00c00700b050b11420000e50000000784200911503e046e50b6010007032a041026213041c64200510b101e40390007529030b2148404400c0f043c005600a54040501585072300c8110000000340140002d021076116400b4000b501d142480700c4003440d580c60101c0708028024100d40c0303031003454240b20b188901e008011941d401c02c044035151a1b64009000480701501e001a1210140d005000030389003000c0b051041c14510302d0410014000e925055000d441800c1c0e00c01d030302d841d10584240300c03503450803503000102c0b4004001c00545951108407841902c2c40740802d50015100c5505208402c180c80303205032100e110501c0b00c0940c107003c010380c5081c144030520440e039801400d910303a48200e83c8650030209569400040b01e81d6289000d004e8600c011500c1c010350800c680ca050345840c0c5900501075268100301d55030000c90f01101270b11607075070919100803c0401090800405c040d000f007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 176428992 1250 176427742 176427763
    0x90d021201110d050f01030302071512050c0703020f010b010f180f0e01050a0b0403050604080d140420010c021c080409152c0403110f0a05070806010b0705070e071e02 73
    0xf1030400001815004003502894120b0707602d5001840700600341080000ba4000d041e0000d01048404416041444810b00139980075121901190f569400c450400038101000801640403581c1011070003a41c0340d900c641807000450722494085d19955040e8110810940d83e03a001091902c0d25650203d01c58200e0300b0507034100c4000325103012850b44d0301c0c441c2140b140210700c401b401c01e400040000c0c01040b41c3e00020002c00400d00340028601e007800c01419400c800a882c25541c514036100c40c41c22021010038041e4103500242014408406150f000880100b03544680741100c2c01480850300c104181141598054240c5940a100c40d2541c2e021091046542e440345c1c2070b020042c080c41c145110394a2900c242140003a410b116050740d9952815600310100c10144c0d4800c0c880c51201d840441c809028100060f4450009041c2842c5410b84151410606800c42a141c4404100030800100700180c0d440c21280c00c00d0380f56240f03a4030600f095a00d0f101400704050355507901211210095070104950111 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 176430242 1250 176428992 176429017
    0x120e06061002060103080405010509060c1c02010b1207230a0915050109060806100224010f060f021506040912022103090309060327070f0911090d02120111 68
    0x51110708100d070355110070302c0060622041007001307002c039510509c02050403d00c003800c1c140ca0000d030303485020b1404039950b400031300b0f0110804036030540c03550a0043d6a0300c0300040304c00c02c40c1d0007000005e00d619080e16211b0050004101c2801c4466100815517a4050040082401c225690781d48010406882d01d0420000410184cc0300407070a503011f02034100603194982e0740e00f4507540ea00300c284031418101d5004030013540f140c4004000002c218088031410307804042e900e601035500d04083d01c404094140c02000600c402400d001821325070010380b244840003428061170090705c40c540414000d100c0500040c054007a0000740b190404d070009040001103002c070001e0310341000018a402c0003808182c42000c0c903604100904071451528002031500401c07580c051640e100100940c4503041c8201074030400881d00840c00800144407140720507001400098014001280082c40700c036220300c60950510700c100740f00d086060940d26400d004454900c05500200004078101c04803560310f80001c185d2548 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 176431492 1250 176430242 176430259
    0x206010806010e130203010b0415030203070f060807080711150403170411010f092402060a090f0b0403110105010902030a0b010e0d0605042f0f061204080901120e0606 73
    0x5401000003140782c1290700c034640800070b50b1140c29101107003450090080e60715640f240d0400c040c65a6500c00c1030945c9001f450b034061280c0c6075105060070104254000801140342900400015410483d6542c2c064194070b010301c0c1d241c0d50804140e80031840110000c00d144034812159400e80c80600c501c0b802680030351141041c0b407000a0100880000c11540188a009004442ca8042d4080c0529143c03240302030030000315090b1914005c030b1240102ca01d407140b02203c0300d981030030850f0f010302c0300d0307504640703070980901c2408096150510401100080100095070060004044c50700c07600080040d0400800203010700e50750b908082001c0c0d0019500c1e040a11300c2c1101c0c1880c0340d0701403552031000d1500608881840107207500c840c0c00402c40140159524056052710801d0002d10900c0400c6010004051582c061400410300200d0510380402d0350080d603041250040180d0409040c1e075001d94441c000c160384001443c0100c4846180b000c1c0c600c2c071681058100f410700c40003c036065105101c1079400c603c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 176432742 1250 176431492 176431499
    0x709060b0307110f07030813080319080f1b09010e040507120b03160902030c070203030c06010e1b090f031002071a0702150703090302010207170d05090606011b050106170d020601 78
    0x2c0d01d03205800c0f0035131030561001d00d0801c00501381e0b1016040d010010b8200e40c0003541d8480c2400c1c11680001254269840407580d1980401d0b000600d1603045404440603405c54902418144030703030b6510140f4042da269000c6029407c82c1e00c25070300014260000f030030a0005d4242081f010300030607020080c5140300c40c20320000001034140001d0504207610500c082d03a00e4645010660002584041d281e14080c107030400c010000360310100010014050290003e003125854410f0340c0e109450060300302483d030380c0301c802c0d0340d00394818050075039650140441b00c2e041007070000d500180c94119050804c560041c000700b151010300c44480e420090040000071f00e08440c0e914508200d8440710103808504021400724081503909103e6480704255502c42d0000614100040d104c0c1000e00714a001401d10b501e00014403080040510302075260800d1510001307001c00d00384140007809007401d4280211000940d60cc400b01030103001d40140d0010986d40c01c48216811100d4155510348205084400143c85281c0000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 176433992 1250 176432742 176432777
    0x906020a0309112416020a0602070602061012080c3f0903280204020304110301150e1902040e0106260601090b031f1811070b04020609030709060b0307 66
    0x845400741003a512402080f20440c050035607082202218440d544164485c00161142d20980d809092107030010802c152400310001d2405030000c103030070f410140c0200f08000e00c82403c0000c540c1d459201c18026216005a0031062519802030709614100040e50000a81000202c00c51703428000d01d001c04030482050389190050f68030802c034285416070b001464155101d401807885c013400b01c03418095210341031090740014060307810503a01a1428800c504031031049140c240300d0020b810301c400d901d400020740352501107262408000c004143d20404a04410700106440d81100c000c2c3c03a4914070410f2a5840d848000c000b200110b083e54112881d51300742410b82c902c8000c0f0a0f02c224816598404140d00302041f02f051034201600c0c032820000811450080c4500310071a0402802140c0e1103c19240d00111242060750300c0e11801d820040700c00c103d03200215040c1c400c00c61340141c041d03410715610300b09800820300d082c0d602c0d4407030130095180c80ca000c03414062803002103000300102d9031524107080b00032440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 176435242 1250 176433992 176434009
    0x1b2003090a050418060c050405040b090405060a020a21020409060b030c2d03090a11101b050c151206040203011230090305120a021b03010906020a030911 67
    0x2480e80080d40407002c128910386038000e464001000c0d41491180c10640c0d91310015070300802241401f01d0004a4180b205007024443c41240050407a03660306e041c00e16461701c3d51502c030050150000c0d160006843c140040c01444030292040c0038981c161030a6800f144124004e4009000b0500d0050400400007444081203040d60700840f400e1503020319044582d0f8081c180e4420440c1c03002001401c40000e800410111404ac40c820007c45001d05201410b6190001601c8040c020706840307403060704184d4400f03135800f9044d007a090740c0d40020f6440c00c8041e410624504100d142402380d01480243c005c040340c0c0c69400162013291414800300781b254861400708026404240640f0b81180c0c15030000744003040308450303171b820340c844504401f80c455800c121658150115003c1032034082070004004204024040245014903612501000c2c201100c0400003500e50040312494111150741c00e0b2859101d54080d880b40004680c000700c110340d240d04108014010308000380d0300783c85100c0c03000302c190781c2030919000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 176436492 1250 176435242 176435257
    0x10501050f0a090b070602030906071b030804110a0b0c0105012c100807090603020f1215041401060e0603011a090628080303040c0801060602030306131b2003 69
    0x140d0604200d440071000030903811200800c01040400799000890004030303002803c89500800307000d652460328456440c40e01a001c1c0c00d0380f003042186c0b9023152010350420045036009905140a103582e4980b03080039400c0340d02500b001e60b030003580701d000001d0078101040105074018098000f40016030f42d0b111702c4d20b001c0c400c0a218014034030a481088800342070491145901c601c10001c0405040d4a9480c2c452034000c0a40000ca0070580d21a4140103602e08848100440302088412061140b82c00e90002c0d1135504503d0360600c6821180045810040070030440305400161100801085680d5621710b031050000780c801c540203503e0304c00300321020030703140d10f10411020b0050100c51051711041d040c021080203101402540d96400c6c00808003110304000d9560007000302500641d1641440d0401200344961540003c00c280e1421070300300031483c1c010040c3ca5000c0030444903100c0c003091a0345103c0c090580840503242e40010007615608940d0050000700903d50041031440c012a040301c2d0055032841000d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 176437742 1250 176436492 176436497
    0x61407050706030f09050f060901060e100603050402130212040c0605120f06060403050a082101030c0306020d0204051f080c0c1b010201021e0306190312030c020c030304060504030c050405010501 85
    0x25030600c40b980c06900080407142e102c440c00104a1711039299503003406c07a201c5c2401d000b60403140510403030303280c24014100604032281c0050300c10704200c4464840420688981414551070390006001e40d910000c01202c40d0f00325038010365072a82241e800185411040f07808940301e10511001080c0c86108100340e4602d80c0000c50031420070703140c4030074480498000800d9903611000400000c00010030038010300012900c50070320300f511100c0e0295845941076100c401007000e00b840100410101d203c03002113004980c0c0120005989104000103074001c2d208503001980c010050100304c420043d00900b00302004007040d60f90b540c00d070701d40d111418040d200d0411031036083c1c2d0001d112000070983d0700c04d0b00d0700380c003005000051401c9060352507100c4020510720407802150002c020800141881143ca605401c00010300006860031503513000c04414580340c080040650b6840d040708550b000304851703580303400b00408480d1202c0d035038140100300c0d90060000702c0e48440749842c00600c0741854003a0a0513100140c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 176438848 1106 176437742 176437753
    0x5010f050f03070306090c03021c021207080c1309061d1507050a05070614090a021c030203090105030a060b0304030c140714041109030d03020406140705 67
    0x990199010700318241101c1e0042e074001c500c403401d072540404005106001341c00c0c112404c08190304000e402000340a01c141200c0400050b9400c0148200c500400b442c40c6003200580320301d000c0c03140121680c0324070080016864111040c003010302554000043c0154141c0710b0a05450740d4040c559540e4205840c108640d1005020700c908404442017428014105078200801e141300300340c0b41c0c0c0e04111011501c03604100f03003900719104440110b1b00401503410480c2e4110346801d2074620482c41425211042d59450319040c809a40103501a005503092015160056500f548000d003500701c40740e5502d6021440f80d4100b4055801070b4080d5440c0501401e840c607060f0f58007072000314200f4555110301e004011041c0034040c0407064450980300030070107140f054081c800c0c40c0912000c250781070140820034640140d255003e0003c13294181d40b403000014007000c0c81c001920407100080c2c0141c000 = true := by decide +kernel

theorem cover : BRFrame.Cov 176258992 176438848 := by
  have h0 := BRFrame.cov_init 176258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 176258992 ≤ n) (h2 : n < 176438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
