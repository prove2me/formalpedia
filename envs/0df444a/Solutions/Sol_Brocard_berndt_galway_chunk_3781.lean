-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3781
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:39:03.481732+00:00
-- url     : https://prove2.me/submissions/8b164d23-694f-459c-b986-ed92a69ca046

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 679856115 ≤ n < 680035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 679857365 1250 679856115 679856131
    0x1020f0a09050a0b0406020a0605100503240c1c0b03010f0204060c1b06020c0405100e040b160f0c02120114010b12060402031005100903080301060e0102010c030c09050d06060e01030b 80
    0x3c9203070750f000c00c240380c0c2c002c1c0d1090350050f0300a00c00003000180350307901c000e6000b0380001c0808505526800428540350540c9244002c1c40c40e8480c00c01d1850600a8000d27920541c0f0004151514001927032150000d14a0710000c4002600c600c42e100159a0a4210100c40361911b0800c544646d500c80004064204a250968510700381c007201c404001924070203042a207800350014800c1080311414080100001030100100c4101400082150100704c82020302647c05030407900c0150403c3c03413074500d01c1c030002050441400094100c030310341e00790000001002c480d0111288841c040906488501400344401c440303444000040000c1451107882019100c070380725031000c4803229901e04050004910068030301220030142104100080d20300700a60200a8440c5d01d840c5401550360307518088260003e07080100401c00c00342d071401c0c0750350342403068800310302061a080c8008540c0c10409841c2195500619005465030484501440502d1700040300402081444440642e1740742071140c080038050314140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 679858615 1250 679857365 679857379
    0x18091e06020c10020703230906070c08060106180806061f181502010e12030f04031e0f033803031308070302030724080a180c0305191e030201020f0a0905 67
    0xc0407040d404030807c01d85181e4a040c0d2070310072080100144c40c1c21850007111792903540d44010425140601c0814000c20082e01c1f251030002d01050b01350161042500701d030394a90310800402a00f0b075a104480c11001840c60350085a04800c2130b0200c8448840c640c510703170103104406001407000c0b920020590000c00f540d00812582c00c0c280141074940b211806001d0003410240301144400c400349020702d400c14420b00f000c0009550810300c11b5200304100c4503840c041400762540c50421900350284510300d400038000c028840c42ca0ba500760311002150094054000a4400311421540b0308204659202c281a20b8956101d070355094a1542e400c0c580c08202c4c06400340b01000902d5211480810320300f8104400d50322031065600c0401c071440b080040c8403482071503c510303000665841c864003001d15035018400c0c0d441140d0860410754030789484002e031107140d1254007901201190000c1c040d4100c0307031524a0b020b25110218107080380680034103103c4055451002a05051550304524150210f0f50107903951 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 679859865 1250 679858615 679858637
    0x212011a03120a0c1b031707061109130b040e0316050d0212040b0d02040b040b0309010b01110d0c020f03071d06041404030c0318060918091e06020c10020703 69
    0x30802c0d0300508110401044408101d4000241e40415141841141034005420181c3d03c0c0c44002000844030300010301000002a600d0500c03a550003211100d000d107100d51440c00f10600b000c14070b4103000310341c803611169645a00013425070380c90f0000c0d2001820403007226224032117858070108104080d0821617882c0701d180f64151a460010820183c05404d042c8440e00309450030001f240c00e640702c018100c1c41c450b820000030581c1c15003030b40540302400421241503282c1c640910601d0854800c19155818407085904c804892080040d951032200c56602d48803803240d00e18804186034403030040b036075940345c002d020700814088085c400d4141c40702c000401200c401d880354800d00040b90540501041e41606107800030300840c0c0112105d1b21818800e1030680881d01050050701039541e516004400001d100040400a00f00401e0790407119005034503007000513038040c0d074820303008524007003000d403843c5a04400c075000d000103541950302e0b00c04000b040e1000c0100c1109004000c0d402040c0c201c0215402044e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 679861115 1250 679859865 679859893
    0x3200a02030d140f070f0905040f0f05060301110f0a020a1e170403171804090303050105100e030c09071202030a0c080a0c08071101060902040f03260f070212011a03 72
    0x541d0148804ca41d20745015258040d08460040c40508104180a6160000510b548692060f1180200003540006110320303005600d400343c85028102034400d070305003159020b0342c3c0100e2003111a500c00d104181a66200c1c04c583c142e00300340309a030b80602030309000401340841c1c02540d021284107502c40c2d0b0707090007000f92005401407240110700000d4040b50b25905e56086001d1000c0042000444804296509240c40c1c40010280c6d007691038110000f81e2144010071243c2032506402510340264200301040d604c8500100e55540794685a961049000202150055003c0c4a840c02460242e48013507640b4a0201c010602801d107054001c0300048544c0000703143c0700418450103002c20307030907035654910f61580c0303c00300ca03080b000c00c41c0f21081d55a9188002491030852004000810303542c039100c0c1c601807550609402c44401035840c6410100035240101411513040100c0740f041200e20035582d1619403030300101d01c4d040c001c01c10b030f2041d661074001d0012078462080044107581000b1411144c1450307113010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 679862365 1250 679861115 679861151
    0x2090a0b09040b360c1204031b0c090e07032a032001080606032a19210902010813081201090902040507050c07030201120219050406090807030f0303200a02030d 70
    0x28171039440f10418041c00c2c13020402c096200b0341080c001c2c41c110351042481c0d180140b079001242c4080b54142074682042000e40320340c5c0206480d400488000e450000d2030341d01d400c0329401c4070135200708044403041105580d0113541c60414000d150001d110300d4035406403038100c00315044559111380c04501654001b820314548802101e200d6240301d001000c641c070400e800b01c54030f4550f142c0c0303589040e0300c240070076000c2540070ba4400400320a0f580e030b60f1510058041500d051600340b00008801d4509045080c1c01507600501c03940d030481c1505510029295043c2880c40f0f0038020036140700100205440002541001608032141050003164100426281d02c034043c4c0c6c2c10320039041c1002d50b5410450301080990302984a400009a1624015103007007991201241300038800520a000b0a9020406001032a07000255401401c1508020507031541191100b84015000c070f9030007401c054850071a4010412810014a82d0101140d9510748030005a00301940702d400c00c0c0b801c070a14a150241040d44481d140e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 679863615 1250 679862365 679862371
    0x90509100b0618040504032d030509030c07170a0c0612050601031e0207140303040b07110a03120221010b0307120504150b011107080a1502090a0b09040b36 68
    0x90f20324440c07000b078041030001a20f401403007034092090f5107041c110b41011076030b0020703007000d4030188000d20720748221400341c1120005008210254810302c2940000c607400101e0906488004403040307910521520301c030b4504051400000d2001201d5000003810940144c00020b101c95030f104e050041d5900d4070011030498841d500c0320040811034031305418112003140d00400506000303800015080ca480b10b400780c51544180c4044801e01e0890080100c4140c4c4041c10b07c0076030075907802a010340e19030307a200205010008440754040c0ca500140e1500d0601030082c200c0805011003408009a682d24154016150411600000490741032508026480100d2280b9481a40e00004203454250a08100c60080142c91201810700c00398544040c00c00b0000c204200040014000030311f00d0076210f16200c441c01c0b04080000c100c2e00e0040c07140c4015940c81a244100340c4528443c800d440e11007840020f0081d2846182d0150040107001c04240f0809100c109407081c006c40f60340701030a1620130318111011100403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 679864865 1250 679863615 679863637
    0x150f210a0b0708070c1106090901030b01060305130b0402090c090409141c020a111809100c1d012d020304030c06020d02252411070501050a0c0606090509100b06 70
    0x7012104c0001b40300c200140181e0b100280801e03003403401341c07008030b19244820703001a070b1180700c20001040200c0d410f011f0342741d00105855910404840550300c000a6480140009110b80c4031040010104d000040039110300d001d000300103200c4cc0f038850030326403406041c11240070f0355030282c04100343c070328030b00294030046040240e07006140700101902d5014200b100300c58260b90105500480c1d660072003500c20b980340241070100c003030000c90100401c1072088a194103400028001a103410503049500601810b0351140213003440104400c4c0020800d85050005141104511702104540c81050f400805007054900c10401100c1090f1940000d070b9440707001924960040e0300c01004188e105c040072810301d03a040d000101440b8160780b241c100004800a205601d00d4008001200310b00c1c40354050324440210900401070000c02d070401c00001e02512903a82c22100340151208101b013041019800040101a0f85904001500700801881c2d141c1001008030310a8600b020341401075440e00070202c0719001c041c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 679866115 1250 679864865 679864877
    0x30406051006091404150b0a02060708040f2037360207030e0f0a0501050a0309030c02030f2125050a050d03021908150f210a0b070807 59
    0x20703200c0c200c02004013a540440d080390300c031401e400310300e981ca540680203810701d0386881c2e449141c885d0b802494102c00401038810030801c0e40504c00801c003041001c0c8815a0850240f840000342d0101e0620300315a2940015009081c480c040d0f43c002104041c0720046030322141e40094040c1d03079a0b00c509000b010501a00310701802d02c2c0d0480500071207911501101c0b9510320500c8800c0610104114200e1300f14200560100344a030042c0e42d039500d0f14403402d5001d25000c40d41c0300c20803810b05000810b40c0c05000003503018595603013a01e900789800b40c0c001c00a450b50007030031200c1610701c000c4069115144440505042002c80444c0f5004030b5403142951131240d2074101080b820812a01c1d1030b0500815001c00382d520b40202c1c04d001e4007142040c0b221504241c3c1d2a14003680d1003101010051500400d4003074041040342001c14000340300a45141e0283c44a030841d85460402c0101000815071118480400700f1200496040b094003e40803c0032510389000e4030701749440d540e6502094543d290100c51220010314 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 679867365 1250 679866115 679866119
    0x1b0a050c0d02030708030c0c0a050103140a0b040f0207060e0f030c0d1b0803160e0607020603130c0b1605071401080a051015050408061501121a06030a0203040605100609 74
    0x500c1c081504603180003d045504030359854071814111350100c001030700c1c03a0f0400c0e10360803181d00700080c054005007420710f0704000b511f4409c1605205440040e018603c115150341c1c0f10382860f501ca80103081c008546203011541c0d000385251180041c880445010658042c3c582690380c103000c04401d17188100c062074081e0182000c081c07011120038519110a81d0004012159040030490601c0510321400301c244010b1421f04d010400904410515241e03a481032204001200044c0c03511070a403a086807c080301751560520601d400090004d0039000789154007000705070300d8003801100c014640e46e14010421360385825103e0724244900b003c0300150702e000c1486a0040b42d5030042c954800759000940c10320f10010f680d101d100a1030b90885192012000030b101050901000105110064100f9801010382804060400000c1c03e40841124000001c0ba83d41d00040c40d8002d00540b01101d1080c01840305035240381007e01c0d18000e40040d1030545001c0e1401c4001000d90281d54171100aa4800741c8642e94624 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 679868615 1250 679867365 679867369
    0xc12120c031614120307021509190b010e0a0c0c08072d03091d1305070504060905090c040605060319060b0a051e09010e012a05031b0a050c 61
    0x2a011004250062004200245608540c00c03032141c042ca1283c281e14070380958420503107150250280045aa00100308144200d045d00040c020050340b44080045240d591040b100a0421070581202d03415003c81c030000508001020300014141ca100c0112101c4a031140014441182d12280305840400e00040b00080400d0f42c40b40600703076140c41000359840081c0d0a14020240e041d800802c2140d80160520200030980c00a0650f00641510000e4000c2c40f080c1e40c40c5031101110140071318500f000140d18020621000344102005403001074414003c2c9a903600b0361400a16044808440500401705511524a0140548802c803003008060354215200c804000800e15189140741618542d2484c0c00070308910000003910140c0d0039500d0305919045100c0601c09080c030b4240440803010703030800c00a0080d13030704405108404442840c00c0854031034441381e480a24842d206c1100c500b491909103007000c0140000c0200203804c110340103d810344404503400359460031700f00740003405030300040f2810100b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 679869865 1250 679868615 679868617
    0x316030b061c06060b0315090f06190308190306170703020108060f120c01091725180b0f0612011703070213090302010c080603100b1512090c1212 64
    0x644115100204160b28603a565011204541c5c0101c6040c0303404410170841c0401600c80c02c0f0345107420703a007036812454000d00200020600030002c503c00c03500580c2903000d2040b2100d00c2d501031540814907a03914004071035900f00c4035403503010000000b810b084005c509404c0e101030301e00e00c80c403d200041c52524151b500640e488030009103c0c0d034000714000c000d864280e0324982c0441030300c024007001e801081014400145072620681213000361140c4034034180f81a540000fa00086401c0d080303080c40703608862000e0071310003070015882143e10350410668003915035840d42c060700e64071108649030070a01c40c21070140a103500500703c0f150040d00003d0300400002d9810800300f204490000103032032401010764001121062444049056960f4070044c0c4001c1580902c50300ea03209400f4102140b0354509a0000b0742d440400e00c1020b80781c9602c4168100594a613514044280c0d050040c7d541d03100e06c803c5444c00740c0c41034210342070400c51043e114280c1d5541002d030104c29035408404091306e03440e21070311a81d900c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 679871115 1250 679869865 679869889
    0x61c0b060111030d060306150e100306022206110601090e0c01050904020d060e01090e0303040b24060c031e0a0203070f0c0302182509090903050d09030e0316030b06 72
    0x8580003c10440116604c11312948000d144a00b00000d007a0202000094030108035800c42080070025400b400760000b03880400340100c5e03a10030030147c0e8800101102020305102d1601c0c01c3e045110034900400c2c91500140b02108a002e1003040346c0a60380d892200c9801e45115460704207a9420a001d4002103500c90340040400090117040585801641555401100d12a6001c41d01034071800c00113008145082c019071144240000040d0704604050310380e21300081c3c014141204d4040707032080411003034a030700b440f65403010341c0201410307201d04a07100100d86a82c08440350b41d00801c07801141e850440074010540e00061550390055060814541d14106d1150400d40140e901d400301d2640040140e8820b40300c0d1600c84a88003000e096030078040d40d1000b0440d040031864103008001010590f42a90040d58001100c0006001154882c664101038400d03200d44e0450080503820054000d0034103410a402d030080d000103400f20b4402203009002c80c2d031240b038036000041c00000702d580800c49503c0c2c408140c400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 679872365 1250 679871115 679871147
    0xc060e04020403080d050402100905030309130b030a0b1006020f060610050c010606030209040e010c0c061e090c030b0601050c100b0a2106050711060c160812061c0b0601 74
    0x45096104d0311080b0081d0045402e0522254a5404200450414240e035142241460900d5003a090504001079168040c281c240b901659035440a40221075039070300101c000e9007029054030019507603820080b001c0c000842d003001000c05000800103000d440011145c0780e0312114000b501070741c1c9401c803c000d0341401d10000802007280520011060320800c0c855240100340d103840050b5611144024001943c514030300007941d0342d261a07504400190800d0391031a24a512450024070609000c5d5540e00c9411100c0400d2961890722243d1400c021000748150280c034054071900103280d413410011581d901c90115042c0060304241035038554200c01d43c1101210500084c556160152a071981d00c03071a100d144e0700008801d840001c00414403200c1d1280780c0d0001c145240200c004101604403070758944002d08000840c80f40000d000c86c001040b885c8240e600340e4410072b100c0d0b4829180d080302d0040c00c001c0e83c0480c496100710000d0714003904104210413a10f94001c034904d0a0341e465030019135000b102140340007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 679873615 1250 679872365 679872367
    0x3030a11040e0705120703020412020409060216151a06070807030201110c010c090503010e1b0f21010c020114060d0203210a140f0301030b040303060503160e070305040c060e0402 78
    0x440e1420014000c0e030b12900c82544d0303554440c44070640e00d9440642c054600c00c1030502c1007209128045800c48500c40150701a100882c0704426487d250000f403003208031440c80f000d00808c00b0400c011015203c00b00440300e500003404000c010001302c00b4a902e100c7d250725400700c000c0100c0c0e0001064000a05076850180c000010891081e00c850721030355116008803207041c0d646010140310b454001100901600c0c05030002c200b101c607502d4440b566009003e54086819185907801c03a019503406022280b0604060001c240e90001c404014a041409101c1d1920300c1d400e102110f01203910500c1007080070501000b080441e9205c140a1050717040407400160303018011250100190011600640e1504680000d2159100030440c00204a54200118a8014030040003d89090351900050300d0660360002c00c0c00f8401c0d251890154001d00c07141e031042e50540541459118170200e00b07040e5100300d42c4035025542c1d040da50000214100c0e60110b600410708481d101c0e05100991091005400040000d4401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 679874865 1250 679873615 679873619
    0x4050307120e280521030d14070804110405060f04050f0a0c110a110a03051f110702090f180a050d09050d08041a09040903030c14090303030a1104 64
    0x1440660109651540842c20780c040c0307400309007045044545451801e0000420480103402c1d0f403071440c1464400e182c49040003d00a80c0c500702119010707108500208102d90b41c0f249440b90410103420102204020040c0c2d40b0002001c55001d11041e5104503407000001d4120b00c465400c2100529010f0310164000c2480008035074180c40b1441404e0261848010748041d51902c141043c003900c005156041c10000c40c0c00550358080e400003a03491a4a5100c0c40000380742c1001310205440d29071075440500640309450011036071804460032007c030000071a2091000201d480c1c02100140700e400d0009402c250140005103402d0000d45084d07030010005d050104518102c09072441c68886984e0094502d1b03000a19a01600c54004444100901050b210007211626540320164640685d02c1480c2d0700890400300c80320708034094011216002801041040014104c2c240200142171000c810340c0440c2190021f0000c010001e401d85000752401002945140c0c3c56040440190449510b000c081603014480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 679876115 1250 679874865 679874873
    0x607091211220c020a05190203150c04080c0f030a1b0b0c01052509060c052b020f03040f14040e070312030b06040e0f0603100606090303030e060105030303010e04050307 74
    0xa020004030414803411450104030010208407802c403c2d440c4255400541e14500281000c1680c02c611044003800100c60180e03400440e08012580340a8805e038841c010802986400071000385c01034800c00700450301030b010f0f0300041c420380b066082c0104c0d51607480498000000340b0420115000515021030350b0300902d40c0c409104149810070348280300a40d449204004464280211a00181c0180300311520300c20480b01e0013030800c0000d40034810030400c400b0080d2003400400c2001454101008404443c104800d06180806141c80510100140958a00003c80010002c140ca0940b0001441620440d142c0300d40914065802c01950703410a4842c03c0038524000240907080083d40a50f10a002681201c40f0040c11070310614036042c4a420240030900030b01500389181d943c0f200c0b00d03048020b5203894a100081c50039820084d041006c0341003d0f8081a0107920541c4001203e100343c1b01413024031800611141c56000c05d005543c0c059106000420025240740030260700580035a00f40e1b40f8200054807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 679877365 1250 679876115 679876129
    0xf14030a050403060b06030424020c03031303110a02093d0e01060801030510110712031a0d08031f080f070e0603010207170f0d090c06110607091211 65
    0x82140086803012400f0401c1c040c50340109a4901401ca50491075031400c1c1d60351290f01c406041c07182a0010201450a0a82d40b0b80c2d812140d1250070901200d449242c04c011100343c41c1c502540450004a401175001c1c4092400501d8089107039008040d01100c1c0e44044942c01240c4521a68001c401d0900e12010005007102c41c8000410405400c01c1c003415003080021100c110041e03100314100081c0da40100080340b40802c2820350309802110120341e6618030140140701d40203002e00a0400019019580c2c802a010b03805280300a48151f5458510544502004407440e01e03c24080e2080004200051150890000300725009040c1003030310031400d03201c554480c64844040142d80460b8031054091083d10b04421500713a00205c00c400070351a241c010340e03072085240610364003008900804100c07000d900c0c886609a40800800c48010802094641814500d4840a100b0940070601e00743e4840c3c40f500c00424428403803509620b4200e0502d26055142402881d0b5400030396104448854540345130b0f030703011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 679878615 1250 679877365 679877377
    0xf090513030f020c0a030506180a1e020604050603090d081602032d03091506040b033a052502010c0807020d06060b03270703030c0f02030d0512060102060c04030f1403 73
    0xc0020641031402c000141009c0803500d42d080307041c1d4004c00c0f80c0d000055540c20b06005040c40800d003590310035068400f1840e54002ca0b0022032348004080200080004000350883d1168110f0b500c044168881305000704a58a500d840386006030002c2140c10001441840c80c2417116607800c08070300d41c2c001403103029216904265101111a088040d41c200d45190101c0c00c0b64010350211400c110305424603000035950fa07010003040c0d0303241c0911000e041c683e00f01d00084890f00000c83d01c038100019449100104180d04c10300c641d41071210081201c650700c401400a2240301ca0381a12650301030444e42c0c64540c1d40b9044880c0c201d034891a403140303007030003d04940a440010954030303001036101d081c21700a00c5412020201d480b002442211360381940003400280d1081100d03050300b040003400300c0500300b02e103120502c404065010703c1000050750800343c2c450300070800d546501074207450907283c4000481c0c07070328015500c83d44200014001400030401001444204070303c9001400f98802820140d182150006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 679879865 1250 679878615 679878623
    0x90203030d0213030c1a03070e03011d070627030b0a2a020d1d0d08040504020703081f05010909020d0f05040c0f080303190207050a0c0f0f090513030f020c0a03 70
    0xc0c4400c100700040c40345804040c14415840d40f1004903500c5001a00d03000007000d840400013a00609c41d1030752020350056110440040d4001c1c2d0724404c0d80300ca80d03541d620510a190001b04980030f10500407c0005200407011415070b0078201c160300e983c4901205010207098402841da540c0b0040420200f5440502d001c1d80d801005008a401c017624007038105040b000c17000f001c2c040c0d030f55002007041c00118800352280c1c6003103640d074459492608121a440c0110f40000b0b07003281c40001d12609258200d40b295200300707020498004030802851510300d0b09007c0303229040c0400d12680040c0000402030b0040d04010103600400107002011901d118141c4505440036201404c1880d4184480840c0030f41c1c0f4009451000021481c504040940810390030300400080c031440d601148407010482c003031085089094214245100950722204e42da540c9440381c3c402c4454468418200080001d4140038151042ca0b10400b0304e414050a500c05a4400d41c1e191a001c0171401201840801d0707503210304409001e1401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 679881115 1250 679879865 679879897
    0x4020d081e0316030608030702030709051b0c0106150207081002030a090605070c02040e0d0e090601110f0102090a0e06060a0e040e0d0804060f06080a030c08040504020708070b0601140904090203030d02 88
    0xd010f1014080b60030a8100c400309410801526015803400201841201e08801d0700080c00d0361118140611145051041c0003851000100400c161805400c2030040e0769106a01c0001c6980c0803400340d81d03c2d001482092383c01d0300926040c04055520b5400b07154440c80801000c46d00075120341d110300803036000721130020115003a10051003d50419200380101040c01100801c0c0c003001110028160702c08001000d40310b1800320300042c0c1075074818401c49021034144001c480040d03c4184405010b5085200006e02030b04400500140700c540f1041e0310b43c052a005000b203450104403d40072112115210234441d041912030207000110300c0100180382810703031107990b60451030030107141c03441c20f42d807200d10b10301441070800c0414040c040740890310b100403a0341410944e000450614084200740115480b4541c440c1c40802d000c0d0502c01c1c5500201241403080c044410369550b49070040d5101c0c03100c000800b400c208144a90501410b0a9114411351400101108d080040c1c0d0f80d0303e6026607100d8850603000540c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 679882365 1250 679881115 679881151
    0x20d0b0c190f14042907020901080706020d020a0305030c070c0e09011508120a050319050c213106063b04030e0d1a0117010504020d081e03 61
    0x161001c01c500e0307000036020400313191078a44810b0102684800e41a00e0410b1070400c41c0ba41a11203d2048900c4641d01901510141d079441c1001c94444030740d44070765005809002500c20b10070744040f90000c2039a50645070213080d078850007038400e20f41d0400e0310100d0f440c940ca550041103404803e43c0007482400e03c000081500540c890b50041030760020b9103c00031507130000113441c1c0c0c01c501d03100c2070340caa1026500e015610f0743d44849040302004203110703044c403d0615080034003403070081c031074010110301030b80030151400f03909007909150031001c04456142e074900d8916222104c8a00b0302c04c1c0303140e0f080050300e10000081d445880341401c80d1210340c085664240c0b101c250a680c25001c80380045a0344030080314140391112618807001550700204010200444803800c6805a030b071340211200142c0e00716405a49081d038920910705415000c0c060303998114503000fa60290048140a698841d039400707425100171304660307904d210b01d54112441c03030345003082c042c0050800c540b1840f02640c4035900c071a0040b48034079 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 679883615 1250 679882365 679882367
    0xd030305192f120f0709030c1206112701200c0103060e0906070305040204021c050f310812072c0913051914010605030307020d0b0c190f 60
    0x502601d4007010000b042c03048811689018a800c0c1d801003400300328001e241d450001c11540b081154000600010310300c0c1011034a18284000424954841c210401c91003042e0064030465000da1107003108031000c00340c1284180d07402040e500300f1301030060516903003140d00c01c114401070800c01d41a446e966800b0091600d000d6906005400081c0311034050680242040c1c80d403140c507040d004100078181038507880032804544840c1c1c101d07201596060711280001007455000c0e409844283c92440d25040c05001003400340400181c10400c09160007504001000d40c82c90715805d56a280c0e00540d00350302c1c18072131440078229000e070b200c2c8191101e54500c2d942031110b940b0491140c00c018070754100c580300c990042599031a003003009038018015000882a0136228038000d45405142484502c41c40d01100c00c12081000d00304a401c00200020002e2103251b480b08207040e540e0084510280d8007911040003280840c0714950280d401c043e6081d40c492034251a1114a40080ca541c00090001941d900300001c2e01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 679884865 1250 679883615 679883681
    0xf1003020c0d110601090c08071b14010506010801081204031b030501051305010606020105281113091103042301060f0f060806121e10051609080c0d03030519 69
    0x2d041c52507000c07c07081115903001005104018540b01c240008141c0c00e24103100810500c0c10b07456840711100000c1a911403050703018090607149a408102160000308000780f011070800ba8003900081e0490910b855038440121000c0c1100c90107220520210010004c11420b006061150b14001d241200b294081d241c03a6084800c980d00c40b0046900d032200f4020340c41c507100103408000d41d4031400c400e44403001800c0c00d001854500891402c0c11400545090307052150b901c460125001c00c90704004a03258651514143c1c0f00c1180c004092000c004258864880264521504402c01000001c0e03201d89405001044580c160459441100030300d804000c803d901010b01640150306541403040f207030814041c02da03201c1500811804000d0030251a41d41e5807420010248030410883c4140514104a56101581405850101c1c0003911841020075000e10000d10001c5c11035011348041c44010b160f49088009241c054540c240000c461401840c038407d150099451001034a1496109000d00030008241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 679886115 1250 679884865 679884869
    0x1e0705071e060c1d0a050d050f07061d010c0b0105060c0a0f0501020909130201080f150402180a050105042304110304031e2d020a020d080702040c030204050f1003020c0d110601 77
    0x81c103031040c600700d903e07417100a2403e04803070040d140030201501625001d0b0400c184c00418803003500c10007400003451903024460f03440304101864121000151342c801150180050440a052030010100401c0a420300c1c0000300f8502403000705940240c0b085544009260540d40401d881580d00410b21045615040d030100fa0008030280150410200070340c00600b003001e0040c85a14000d2203180012000b6400754110014000d008008540d0740b614071640c000700b080201c1859000d0b110340071022800f035028800f102c00f99000541d0710212000c05800c81003442a00140e840e40241d1030b600505602e0842501a42c001c61003900c504152018200804513800f961558001c03c00808204030342c0c1c81c00d04041010301e00a10080a074001d40304c0b05205a14000342d4200007500f0546821826051180510181080900c00c0303e080c8000e400c82d40c41242640070324051190b01c00741c54510028a480c005800008400e050300f000750034160184040d03828513580c070040c240464400300403641d19030418440240 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 679887365 1250 679886115 679886147
    0x60819020703020a14101119030209150a0203250b06100c03030e070302030303070c060e060c09010f020c0604090e07080f0309150c070b0d051e0705071e060c 69
    0x1041c965603440096540700310800c05004151440c4841a07894000e0140f280c00060204041c8002852a02004540d0b40042c4003021008110b4407080b42481c4030b802182d00764100104240c40b090b80415045034a036000601590641c03004000400307094103c243c002030162400c12f0b00200b02913617424141c140341e40007442d00f80720f410032007218031000e90007401660550744c062500062190004480758501451500080c0d450710021040001071035004640c6101c0c10b1052505103c0995003203c01c0c7da41c0d160948540042070401e0101c1d48140d48100070130100f100c124412100300402e6000030800356801754100c211501c0c0c4550070b09084074400c00c00d210041c0602c0005140396102c07007200035103034040c0f26989403141c10003144c601840305010050300c12020011040e201401d55a21070840d041e40034840c0a000c20b414400019281172250000c8090380d404104040711030750340c0391822940399005000407501d51091008001c0721a0500640d0203800744104c81c0000d02040090000c3c21580060b04001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 679888615 1250 679887365 679887367
    0x120c071e0816032004111803071a1b100e0d0f0507020a030f15020a05030a1a0a0b0a03290a05150d0f090501180209011d160504080706081902 62
    0x50015422800c4420b000105044003a221340008001d006829200b000840d4041210326841503c4000e0b0000c51000718100d5402c07030740c0d07040041014030100c00d18403e03890082c0300d50b40042100b28080180308894600741d82a601c800144c090445914081c60900c6601000c80010385c10380001103c09a640c650400c3d07030801c80d040d070018108039240e0100500380100061000200010559000c2c0031401103801951513114040c0000c000d504100e036085865070a12150f010841404a107007041c280000d44111122803c00210400952121103a44100759503130a4107848108030994178482508441c00091201007003004015040d80700742c000b203100d600c0c0722040669075171200080354080c1d0040341021404148149000d001000d81040140155003448403020b50320811001d46483c061003210120704076621201c003025000b410340c1c68100070151a0b000320700005102c0315220035038180c5140051403e0307102d01100f8206a06580071a022410788001e00c00c64050722559045a103800746411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 679889865 1250 679888615 679888619
    0x4020109211707050d0c0b0c0a050909150a0b04080607110d0f0c02090405030904110309030406034101050105130308091219020111010b03120c071e0816 67
    0x30344100d840c0c1d141c0050014505190759404821803074161080507801c00165010000b40751005003e01d0400300b0200d40c030064800004503441141c4003a00c04007041c50b6a0076040450314000c2c00602e45016084400703002c0c819120b2402507582c2c003200005032a413401f2850711903140a4400d49821000340c1034000b44051340c0f03000c00d200f000015510107800e040d450315481100f04900141d07403503641d00340081e4011101c1020402440b4000005040d540800d175001c002c0740900f02104659400180d517a108641c0003000304004152203030700202600503020300074070b0be00041d0307040ca1800606035282540b44c0d0000030011034100541caa083c180185002c0c04c1551030308103000d40c106503086240c0801000c09002081d040140d46a1074102c0013640c40304801c642d420040c683d44001c105055410482c0000d20445440c4910407040c000c886840b80301030300410342c4c2d01c0e800d400304409412086644070140704414000900000240450705501c044165021449042000d0f0074100200038006185a031801801 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 679891115 1250 679889865 679889909
    0x8100b09090606240d0207051006054603051504080a0f030f09060e07060e060409021e0706050105010f0c0c090203060a0902041508090703030e0d0c120b04020109 71
    0x6095800340045413901d6100100c4c50100000500340f034511554003602041c05a03da030165402040b0740750040048860030010140b4610a50381a40103d07500b00c3d5805445095441e5024000d80000002d0701c0c0c03e0701b08050000c611449020750101201600b10652010014000144110790040e000382806400d41e207459160034035071f8404c01242c074041101035011504628881c0d448001303080b241f00e4052200092070b01303040c0b0251560001000c003d000754100055000c1c0151450031044001410240c2081e00d010580d030002d401c6010300e9414104400b07030010039411160024200c4a10550340052954105000108000d20f004072034810f121504402d00042000000102e040387c80c416405640e0388e8420300460b10240703181d4840242e0720b00100d0049159070018408400b032894507a5080300c035540d5079050303e560786040c0c800a000f1500348952101d00b4244625a0310740e1a001d41407012850b40d8400c01e40c0300040d000360080e1243ca6401d0300b40421036a2142c048e10080c02c030403220305041e0320b640503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 679892365 1250 679891115 679891123
    0x1101110a020105130b0c0a150902030c04020708220806160507020d110301091113140f06041b050c011a0a0e1306060803130e072001090c08100b0909 65
    0x20001c1e043c0b1201159540400c045010010042c201c0601c00a407603110580199aa81514910841c0e50700e4080070541c43d0300c0110b00c50309081d0b60b0000c000b00482c40241003400000e5100d540305840d946403c0100d044103004850603078001f0303565a41070040345440c0c00c8034076051140142125000d2060a41601005a8000d00b0340c0c1e60a50100c40c0c6044120325440c0800012010f80300464143d400d04924200380884440c04c0001100e0a0f540380c8001307907010124104a070641c4000303d04082294010030ba945500007080365102101600000d04020b801c0c52900c400300c89a01064005a80020035402c164020701030b0140140c0030511078421200210005a2101c4c00340c003801d0300241001d00001c00d80201711079100b002c103802c540100043e03a100c107901612070344080d600701100880740c2c0d40042e20740c100041e1a44102c04666a0090748030f070615800c1c01ca000c6000e0136000940d00d41000c40003107070002c4507003002410110020056080e0000e03e41041c1ca0310000c81a110700c1080082045111001c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 679893615 1250 679892365 679892383
    0x902071412190c0f080912010e07060e0906010c1e05160918080904090f080a0c030206070206010e0a050405150702010b040b04061206020304021801082d070501050a031e09110111 78
    0x40c0b403c075100c6c04240c0c0070030a02c0302503c042003455030a2206107510310704007142e41403d444044d6500c1100d00b2184050100055054880a0005104074000c0c00131030004030300031040c0d1404040d0307683c5c3c890094031000e1034551151108860018bc0c1082004201c0551040092805808940704c039000c0140d206c5210070b001d44400c10b07025070303110340d0351508010020342d195420f03a81c00381d0556242c48026100a100540c2c17003500301c015114007000304601d5400000c40d54100c403610340c01c0c8003096030340e00403070806040e000d0012140d6200d201050001c008244000900c04c0d1199400010580810b2080100752040000c80c1030188d0300c0d003002440f0740c008042180c013155412030380c0076a03280c65510106510303009500d228101402910000308006002185018010407802c00c0017801c481703c08240441415001e0406141d81e000d80c5040200e54082c03800b80401c08464180000c41c4031404250700304030854180584074036a0b544504804121b14843d40c580e40c4103080c80e11000100b05040000d54400f40a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 679894865 1250 679893615 679893623
    0x30f121e140310090e0706030e060408030402010c15020a031a01110c102a030818150703020d0204120c0609290415110d180902071412190c0f 62
    0x1c00103c0701d11101180704018000f240341013009401c200502c2e80c84207020b008041c00281450b425840712074000480301d02440d005412540703035807515401034801802501c03040b03074942c0794680360050241c0315101030201c02c001c40d00c1c00300d040748603090318240383c0252014550500000120303c03982401c0029502d42d10000503142900000c9005a080da102c004100e20492009050004e584280304021507800c52a442502c50005c10b441c3c0c011300c18a408145081c0f10480d034444c40f40003142c840120502c0d43c200046080040c544441c10b440300c81030b60f02580150058026a4000c001009146003601c001010b01d40b070001e515508205503182125241400003031802d003801000002d0444004c01c0740c00030003c4141c4618006102e0380003400602030404424118001e0740c541c40079860081c003500300c0820708080c07000259820480900000d4000544c2a1190b08a80401d2440c0034420000c0c2110340101c011080d454806d6124108103409241300300c84100005808007a00040d810b20103444401d0340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 679896115 1250 679894865 679894867
    0x9121107090b15130602060708040803070c020409060501061805090c0301060503280506011e020c010c03020109050a030c12020c010206040f03030e12090a0501020f25030f121e14 78
    0x14002425140c034880c5203800c924070014500b40303014003139540071040721000e400f580c095680b9080b00380d0760301307604440241c56444100700003080746115a944600081c401400021010754548503101100e80903001400403d448001c80c031861404048980028201118a40310b20f2514074101c0c5580e01062050a0030700c0000300200d110090340485400a0030b000440c0169001e03546109000500400d4540300d002c9414031401040c901100682c40e402e0792500e40080c0400b9014000441f22010707039120136421075603101500c8001580600c07211503a14002e584405000c08541401031550f0043c180c40025913000000d5540c99907000300da40c42d4010303000b810343c040d036008604040d0080c0820b034200084030b02a031010152a146018090002e081054070195081e80e20760b8010b907a03c01c800c010541c56944409184000c211a50001c0c480484150504142c203969a503190450940142800c46445c0000c075a00e0148580c00040560010051400e01d84100301c1c0c0d0b00c018103051114428170903202c3c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 679897365 1250 679896115 679896131
    0xe0309031b120610090516020c0112060b0f03010503060c071214120f0103140c130f09080706050403020607030c05091e0d030507060e071a030a090204020a030912110709 74
    0x180b102030b042481c01c1d1101c03c1d16902c0c03800c928900407100250240a000a140c200070400394252900400080c0305a90001c00090b03031003034019610408003010811002c4e8032a000801c8918404e8060440f640200d07041036120350403c0201030404400400720003045a00344440000706022480b600001c011a06121004512403050194644a40841044051920014070003078042140c6100e0403a03019441007903407001755814242e1111140c456007a8010040d030040c0f20400950341c03104862000c3e19030000359011041e0707900341c01034104180940d02c181d0f0350001c2005040e01884a5907114610389020000e00c441e0038009800781c02444107040c000d080742c007101c1c01211a880f01d8040484030003071003092181c0040c500284203503c400320442c1d0503418084841010b100000f8a03c013607401031a101c0050407014120030b900c9800040c501c95040d07031900482c00250302c07144024403140d0903079030340424400d0681c10440d00c10404c0c00601c10402443c902d01a205d0301c2c01180c14400d40701d0110010411032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 679898615 1250 679897365 679897369
    0x30304110904050316080906041202010f02120a030b06040302091009060e061e010905030f1f0c050910020c0931020f1201140c0a090621050c130f090e0309031b 70
    0x1019887d030550b0442c00008000c1584581041c1400505201b6a2446900715510f90200d07220403005d4001251a1018020242914040d4004491100020f0481d070308090b03594000070745140d07099800c1084049074200c14046006c0c0c500a000240c00d44c948407000341d05060000c140448034401140c40381e400c0c24406860261f01c100049002004020300301c0da5403134024551661190750700150030300401c510061b2b80c514258540954840351140d5280d56080002900030b00c10b0701d040c02d02880b000c501943d00d100c5510ba0b5406030881c040c4651a2011201e0398a1000100b890510300d00058100701f261030700381d07005a50302e1541c540d00d454203844003400000d070641641d0140c1411003060541c00418802c000310514400040c3c040d60740d4550300c2140c0595038039016581e41596212221809805944000340000682c2026800081d2000300504d4048200580321805d6119005200810341d19401041400c185001c1c0170302e1040c400b40954a025a40700001e40e03200b480c085000d1903045680030200c074030703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 679899865 1250 679898615 679898617
    0xe10110d0e0109061421150109050d02090702070306020c0d26040201030e07090204031401050619050904081603020d1215030b0703110a03090201020d0c0807110f0301090503030411090405031608 85
    0x10a01d8840341b02011070140c0402c0100c1c0c10031680c0c0100205048052842581704600302c200301c800c042c055054600b0241c09101070100000e00c0d602c21f40c414404000001005840101040306500c2c0c00f51200f82c003c9000240030083c548403001c0c0f117908800c1c802200403082c141050300140d0900300000d1003600000d086050034444e9220000c01880810008188130210300000d2512200d08020001507403414100f05031412503110707003000001c3c580810300807400e00d10040340c1c0142c007462040303050030f5040d4001000c1452040080f40180c100703d0842c100981c01a00e08034600c1d44045061000f146295040d030040b00c1a48000b4026a0f4030402040f2024029840f03900701910988a19550348034109015000e009540400c034014441c2100380c0312094414040070408503031100391903140410603101d40d9580340205d10040c1d40045401145503440d03a00b48103103459070f440740c400b0b10f0b00c2c3d141900302441c0980c10700308032600a07041d900412000400210441310000b020014964012842d801c018203a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 679901115 1250 679899865 679899877
    0x11090c0a0810180f18080a0309060f0c0e040501060f020a0204090204020405040203070809190b0c033105010501050d020d201305010306050a110301150e10110d0e01090614 75
    0x800c0c5a0f034030300100094019000396410910144080c8128a4a4805038021382006480900459001c0c0141041c442c032a030441200180070300d90208502c0d01e6504050201d507a200b0203080441c074881e0074507000d41003d0140c180185503c1c2040d408803007607208041c2d00d0300e000d020028440e503560301d28082156540d41c1580c0150902034004c540b2031905200103068080e0503280b0f6103c62280507006e0400d6044000440b00c02036100000192a842d5400c2d040c4158102910651100500910111050b000c1041c4d0503040d401040c0000034a01d25420000d00315113044c3c03c402d0081c03005980150150b04c65141c2d10200c0c41c0e014004445041d580070b08560064408401039078032044040c0f0041c07290000d5003145044c0e07806140c0070040ca0b01c2d44000380040340c462200400c1101d00500040004052400302e40c107090038942012a602c1031880f001424150f0031844281c046024240800f60400c020040d14540311501c0c1488107450161500184c440c102d0341c803582d82080401007032070314442990025108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 679902365 1250 679901115 679901129
    0xe030c0f0f0a081e100203042414150103061a0915040e340c080a0201060e0a02190f02063103030606030b15040e0a0209030d0c11090c0a0810 62
    0x3048030312400440c84c200002d01001c035101d111301e1050209034456842120301896224042203058045025100fa0403454150800004c03030741d928808443c0c581c080c40e030501c02c3c994104462501461000003404884950304804051501d804840445200f800102c0d038103030f601214030540380300c0260f080d500e03107200d55000b03c9260760715030701030003000d1705c65410403c8005246004607540346c084041310035020402107036005c0026800112400441c0c007e50041000c014184004504035440300364000822400f903d10402299002a0a070040e140c82c040f5414007487d2440d2020030f0055400c0c0082d035804000c4c02c000c450b1172000c01c1114100780c7e0840f409103811000b62808040729102d04025005042a20440300070a041c21086202482c1500c202c201c8418048452418942801c010b024048030040c18101540c3d8204141c00e41a0750401c1880c054812554698020706103c0c98084c1d00d9401d042150ba021f000b0020130301c0481d2a070241560f40e140c0803441c0a2086944003440100020460f40c0100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 679903615 1250 679902365 679902373
    0x615031209030303050a111e0d0603081b030f0d020a0216030302150709120b04060f111c0203130b10180b0a080f0a02010513051e010e030c0f0f0a08 65
    0x2001a5070005004411a40640c0701004981d948001840039034a2401c9031500c40d26040081550f030304a00c003072002040d43c1060910b420145e940c1c200e001159201e4100f62807504000c0741041c200100c115451200740420b0f0007039803c1c0b0380134502c00541e6000f48001041c03200e4001c20001c0c266403080102c2c046010304065880f0410342c3c1d80c01c01a480b1030720042900078042c18200010034840c0115900d100321844c20b0000510808503441d10704d100d00c0b016000f12901625280030404030781e51800b640064280784012140e50b0050031003403200740041c405141a4060040c001c010094900d1030a1a03006600040a04582c0c1d8034007035520554100764004480d02d440b6440c501008150f194070200802d20142c480c001c800340c4030340e2050b944044641501c5007a900920751400154410005415900f40341000074403001c3e1928001000124001c0402e0740e00011420004c4066a100c0344403603220009801500080301c0603008100308160080741c1e5805900003103801c040740d4035969408402044854151 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 679904865 1250 679903615 679903643
    0x5090c07020406150806090126160801061d0c041a07151d0619020c0f07030b0a050f040f0303110d02070c0812040f050904061d060a0f020a020a061503 66
    0x560801207009136040000303100030b000241c080c140005601c0c143c03464031400340c45043c1c6c0121094818500c840307006510f4000e80a54140d0090390300d1401001e030841c60000301d190b0f0306204200e020900c841c1c009401102c4d41d002441a101d4290040302c05650b44580107440c3d0313141d00c10b203480c564030030420001e00c00c040d402c00548100d01f980e400380001c00464490f42980003068000c05683d0401039032464000e241c004c04a0400c103002c4d40c010b00c1a41090320a440303040b50144421810808240c0c0159001400c030410491b0030301461040c50340c0005001c0a882080c109902e50101100b105e02004083c10313505d03503002c01d06000800543d201d917901c043c8159036551046c0307004179405442c2d2041c54031600c6900107030b00d441c00318802580d0650304041c455001040c600b80400c0b141403005882650919035031954070f42030642100840d90468442c81c002c1c02e56051010344034040361501c0e2880000c0e5407044c800c0840300369003c220402c08640200b00810940c400d061280c40c518815400100b00740c0c44003880d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 679906115 1250 679904865 679904879
    0x7121b06090605060a0803030604050426180619030f0b0411070b090607050703031a0d060b01090b0901120914010c09060809010209010e010c0c0b1303050f010603080405090c07020406 80
    0x151461142d0018800c82d01c0320303000c0c813035000c0c0c0c03a0251a5064205100284180c1803560029034864006d050034803c050400b2052002c0783c02c0d288a400e6103840000b0070300c2e00102280140000da030015034901d8602246100c8000f501401034503c002055203c0074007101c10300040d00001c40111005108024058403440c04600782c0c0d10614084601103990310020300ca00380c0100d80d0500c035220036290710340b4000c5030395000c8000b00031b5940c00100c0180e420313858503080e482d02010080304c14424034000a40c00213010003d0700d40c81d22540810200002042000d0142e44e005140d440c440c5100c038004281e01c60b01b031400d41c540c0814207a00203200d628041400f1561a805030b600310803540983c4440342a51a96808103090344075001700c01d404142da00f1511403080d482085a0412103000e140440715803900c40381c07000c03100c3d4000c0ba18030035030440d040c2091060050622410f13440e259003400070030010746143d45030340d040c0c00f941c8215407284401e1000500010826004c0b42c6807580d00510802ca80ca03102c00c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 679907365 1250 679906115 679906121
    0x60f1514090105030106060504050d14010c0e0f030f0d110109080a08060a0b070203060106141b0f0c0a03110d05100c0801030c090504020a05060d091b062307121b06 72
    0x80401c0c8150000070001510741410301c40e00f4259452a650303d49424106020321203c000040b00444001565070b0400b200d41c0800c0c410303004d191501c0d543e0500c4500000d01085003210226440600c2070b0014103501d04841d40c0000c20186828007820020410380255072040c3c018818540c014105100003e0140c4002d80d114994500c5003000700e41e44401e044d140e441d0280c0501070040000e4240d8400e5005101304d501551105501d0b0001030803880c40c101030030071044007071042805004016448410840b007101c42c1440841e07203201c8140c0b141c1c1410b81c5142c680c0b1030010900824140100d1480003602c2c1405014040c841c0070071030f4164240a294606840281410000d01c001c0d00c4d05c1103200c0002c105241c41e80030302400780da002000c1c24403039070030701d41000842d9000441c070704003255480d94000300040c011010860540d5031882024030700391404d40003401301d0011003580c2111041e03d008200310760441c3c1d400e41c3d406a400617100e030f03038a0708488030543c0e003a2000315040302c05a0000204804001150b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 679908615 1250 679907365 679907399
    0x7050f010e0609030f0906071e060e0d09090c0e1e030105070c030509010e04180605040b0907030c0605090114190e06040807050d0611192703060f15 65
    0xc100c440c1c284103025440d15810f0380d040000381c00030401c85c0181501403000d007002c21801003900e4030344072040c0d41d05d40c4001d81841c4401031040504940c0e000303009030b034410300da24014050003820205001000c01800e01c6082d004480e0300e169550410000365101ea0903034003040d00f0240042900424420003e007041c81d0950b0741601c658240030020340e4062060400340070042c0c5c16100c0c0340c1001300d504015901d4820f040c007640d800c10b41d81e6a0306c0086101241d08030f400340c1d000b6440051281858144070a42c50402000d040055004420820000c0c254160300412241c051030055200c40034080100c440c0258404906c0c800d44000c6990a10444154800c250f024003584820715459000b42c103101c1c860066205562240d08204020040d80c1060000420064031408000030180e2400d103030310b403440e004020b0307074190f41861070810880c480d001050b4441c1c0800c8040e100500300f0141080d80319038a102e0000510031078550300c10005104207070b00410b01d80d485000042c0990cc0c1c807580682840e00b100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 679909865 1250 679908615 679908643
    0xe0604080d05011208030103080a140a170a050105030a02130f15050f01020a03021c050d060e01060809010902031c020a05120a230d0c090305121306030e0c0112110705 73
    0x21000001301d92107800c0100c02290791003001181160310316203030704200390232510a01c010300ca60801007807501001c8500412020040e80c4408400c5010354903403404000004002e1000540743c0350050025540025541e03072203540c110303024440d0710403c0c0d5410010b09211015030b5041410514044440d0111110340c0050350020380c0e828040b0904a03004980d900e07407620014003d43c1201801c64040400301041d40c002401504049182032480c400505c11141d850341b05080e071035525401440390681c800c3c000c03900b000e020740080c00f440f145600003070f48070070b240041c00c3c10050b001402061040c1c000c0c41344991040e0000160f0740742e07074907411081c1c10320752161407810002014142c0b250001242c00202440c032004c410925070800180150800c02440071051420510020b1031000001510030041419503c00d205030b22034858201200701501032529030401c2090501384025010100310000d048400c44000f441c00c0c8101d400c400d1052002800758001540c0b8200d4005203043c14428000303001e88282c111 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 679911115 1250 679909865 679909871
    0x906032817030a0f1b110a0f1a070c050d200d171006140705010623040b040e0607081902070803090714030a060903051c0b0a091e09060e0604080d 64
    0x4c4510b1002220f40f00c2c0189801c0d0b885040c3c12500b4988214142c01c4001e150b507040b200200c005072200840300e0031061045038900f4480c140c51100344403d03160140c0008040c180401d0280c202e5403001d48407a1082684810496031914400508141c1d00c1c0b10200c003c012020b403154500b0327852009001d030101000203498800d480c0041568042003c41303803c100c890039503680c00000c40204000003107174003d6038107840035900c54101003a864015a0400f0006003110b400212a1248006220640c1d400304801e80c40b86241c020210102640070070f01c2a071000461415004550752031661300c05280e0501601c08c0030070b2020a404c01000040d100550107011010202c842d80c9903903201380c1c81c2c24005034482d19015040389808c0000680c05030410820184a410603505043c658428000068528030765030060307640390f0044042506100300860007400780984107000c8500064004240c001e01041900121a5180e84500c14001a0740c06a0311900c1e040043d10540d0070603050204032500801022604149 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 679912365 1250 679911115 679911131
    0x5040302040204060206040c05060306060702040e0a08190210051608100b0307021b1f0c2906130b06180310020a0507050709021606051f03050610050906032817030a 72
    0x2b0f0524140d911410380240807500e001501e500b8880034040303240000501c1c0c0708424404002403400000303040c11210b06845003004c91b2420400a1604554068124030f580c0f4003000e02c00401031000780c640d01c01c406800c3c002101d4440401900d00c0c12030552240542e4500401804601940415000d002940300e900e050070a2512008109100c0c8401010455030344c02c0305080c4c440680212070a4480c2c0f809040004c0408100000d03000000108181d0102d8541400d41003260b640b8148a0f0040050340e89042001419004000301d0308511840e800c03036406880740041d0501c1540c1c204160400311640e610290345811000030301130155009280102c50310f016800000c03139100c2e8ac500c06d568108030200c425508c881d00d20f40b01c8000404001c4c001e8007089180001ca10080e40c0c01702907440040d48160001d12981c544564007981d6030b2510340001c0d03c12085402448040e41c0d0002d050011680c4145a80416aa00d055040b0340c00303080348c100800020303040e60500c0b64492900c001d140309152091003844008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 679913615 1250 679912365 679912369
    0x360c0f0609100c0f0b010603020d050c07440304030314070c1b0b030f06010219081b072402010c030605010c110402161b0602151605040302040204060206040c05 70
    0xc059482200d40103000070744400245481507003c00b44840c041d80e40c500501081c0d481c0da2400351803d812500c0869000030303100041e0702c3c50380b081e01d90001078031249030b003051656600c10054480c400c0000144600b80d030030081c02c448180d4244d40c003800041a010071030750401805070006820880b4140d01080c685a02080740b506a41d903c24413421280e43c0b24101f5250980c5c40e40641c42c0c15203854083c0d030000030004101c40304482c00441c0501c1c0049686285450003000080c07070b00d0b400310b1050110075840d03010340c00003a80f80e1301500e002024a110380c503842158170798054074150f2582d115815101c2e10320000c44140c0741d02d08229421004d191300174441071203102000c0d003d4908900c00d00340024010039540300880c440c41d0741d01c0c02501004102601d4960042e0381c0c9850380c02d00e08804c1c1c4409092842145108405019010007818076002804803008074918500c08070b2402400c41940740c607004500d10205118500301c2d0003565004004545803611204000d44e02d82c401c51301100c84508a4801142034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 679914865 1250 679913615 679913617
    0x6140702060115081b180f0406050a0303030b06130b0c0f010507050d0b0f04060902041d1303080a090c0902070506130804050f0102070e1e1e360c0f06 66
    0x380e07061040c03004030f185402804460705034000b0a4040c450480d82100700d442c001c0f00c0000d1100d656629041c0d580e07082141c04000f1040745220380140b00d1854083d0420441d2074480c540802c4a4242c10300245162103d408a801c40c450414039441134040c900f000304030b4451400150078001d44800407240303180003a0900c14200e4038240c40803400b16a082c060070388545800e0300036101d03802d000391030390340e2090501011606407131094011610041c1c021406014650703000860543c00c050200c0c00d4186810840c142099000300e01d48080c2c20400410f000862080f42a00000c442940c004d031f82d04401c82da00c282d01e0000790001e400407a428010a4086412200281c40200394a074008181900c1c00b031414080040303480740c00c4086410b601500c080010600400b1184503c00c48807880049010700342c0508200e000e82c00140b111400c201c40303444543c2404841100640e1069008441110380318100310404400c009000f42802d02c0c44c007040301e0307004100010075069150794082c2c2d10300c0f50746c0700408100002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 679916115 1250 679914865 679914869
    0x51b0105091824090112060f050108060a140c030103030e0a0e0a09110301050f010b030a06050411040623160c030b04050705010905010509012712080408070905060d021e030a061407020601 82
    0x1004240c44e0040c81003910704000b12600c980f0514002940074601d16800d82500c90980c81410660400002c000c854602d500454001d454003140d0302a6510340300c2d601c04010300040c0405410404084000c075025220b14000c48040c00ca030015080030f5240140845014003c4c000b021140784004c0103544683c0c0c1014055140601c06d07a041032300361030303080c0029166640c100404a60199454034400030769501c40c0d2160640b820b406880340c0ba074850a208000e0640da80c03003071118004410502802c40910140000c0c1c6030b05e442401c01450a0b050715080006640c550798201034070f0540b00c1c000740410810f0010703511089640c00e88031010625591030065420340180c5010754082400d403002440e114058010366001558540304042c285922a00d09201194208900710b9583c200020b0500c10400704006681c000c1c2085441400145417460104044422580700240a0721072a40c10305520340c0c06003901200c10380040e0441d01d0408150800f080540045860f0b054045119001b040d6290300c00304042e41 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 679917365 1250 679916115 679916119
    0xa230a1a1c02010c0809040e060a0c05040506041505120106050316140901200303090a0b010e0123041d010f0609020708091e0303120105040f09051b0105091824 70
    0x400c0201e50010355036003252200456020108014070a42039440b0b105010355580745034000d00c000d00c0c0c81107440301222000b8512105121050004010a07034034201180d003511465030440e0001d101140c000c0d00e041c01400c185095040c00200041465a8050041d5108212110b81072154150284050392080c0c0e80100c040340c461401c000d481c40320350041802e012100580c0400a400e810740840f0503045400944007811990480d00d101400c0c4081000032902500c11000104c0244d4903040810700c0d104038204050800c00010f0300321100960741c90713125400c0c49894001e800d90800041c50046d00808003651188100341c680b05010403591b8262085e00c160b1544000c60506d8a00b01070f00b0071001c0d882080c0e094170029401c03844841c05880900240560012503159200356504250401064079501e00310b00c5000752030680b1406c003051002031904104000001705000d222072010048420b4821980c140b900144000c132140803c10740c081100d841100065001a8072000c000640e103910808428520303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 679918615 1250 679917365 679917409
    0x608090c091b0c1005010303080609010815060d03112d01020906090609030f0a050a060506011e05160c030f060c1409060306060d0f09020307060201020408060a230a1a 73
    0x420415582d03001050003020443c226800313011900400d40a8074003d800440004110300144925418039401c21805401240007911010226484c4404000c80c000c0100344180c801d04610300a15024401040741d0305141f40654201440340c40c500351a40c1148642500034404655041c00500c4045c401e548400740c0040511345081000c0040090341e4101c0700d0000e07854029030f10844070180041080031411441540540a00c0ca09070808004a60004040e681401440207004602d800201c1c5074410101c00703030521546807510f16144400d40245030000801c40b8214000110034000e41e01d898003042c612607881881403400c0d204040710351516206001204c0f40082c0050700c40c0e07161200245d5030009014194604040c14090070005603034112001e00c00c2555260014019410700344443c00180c811800254545460300040680c0c079080148290707440e69481040f450403200c400f400d041503452a025111031410841c100034014041c038044400d400b0341c0d1107140c0c0d00504001900e0100c025080c0c10071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 679919865 1250 679918615 679918651
    0x3012408070b16020411070f020a0e0606030406092d0b1005010903030e04020d140603010e03030903071103030912030a030506030d080a0902010c02031e0c1801060f05070c0608090c09 80
    0x40c0c0f00045a030354201d038415140d02600040808000181400c2d5003d1074034914122086d00600826010640180f0146280f2504101080d121001101d400c958402c80006903800241841200c10b9281003850503424084c011400b0004000004281118010864407804c0c0d11800c44c01c2501840e54862940420204007081012a004a0f0044e40588001e0400742c0780c544145200b0080300c0b0742d030340800145483e982c180311072420244a03212450320808015131031420b003041c0a40d601e01034000000c2c28800a0041c01c80e4503242481581d0310094081e2080f0350b243d45452245440380c0200e01d01100080c0792400042e03a40c6800140c0540b031481d151254910340e100c14844c00042c1401510981c14000d1400485006890070850802418440c00c0c5145009900030303038103400e00021003c142d100304994128510f80d403844100e618110382d40c90070581c05081d01c1c07217015603c0d400f903941c1c0030340803a842d0b440014001d5000301c0030714416044030040d62030003c0328408204200c00f080d42ca01d41200900061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 679921115 1250 679919865 679919887
    0xa150f0f020102040f0b0c1006030209060409060608010c0504030506070e0603160c0c091506081005011b0b0103050105061008153109110306010321030b03012408070b 73
    0x40d141014003034800586402e0321002d6040c010081d65214800d1014001081030484034284500190380c05218801e001151542c1c00241c3c2c0c0c040c01521302da10a0380c0d035024030360400070b040e40600300030300d0f00a000f8030000c01c2e44000a4602d40152000365241e00450001a880d94400d825942c2c12200081040d404c6031195107910502074100100103041c00684d02c40540440c0c64040c003a002003107943c00c04205242c034664000b004030351a600074020b0040c2d880622500d003401c4003100068402c2807074034080020007100480c0184a0008020b4039404029001000780f01040d040240b04c2c40301074900641902c284441101d5a140032075100d0902241c1e403100c40740929020883e0440700408040d40c0b0401c403404c0f90070194040c10520150071840e9640d07540e50802c0f0764030b6010004481c00301d020307004030345c55619000050150a0707a020407194254a515050320b01a500c0329000e488054002c2200c02090021070040202401c04680030385600c41d0300041c104c4c80020990250b4010a140905200441607 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 679922365 1250 679921115 679921127
    0x503030c121602130501060f021609020c0106050a030b0a051302090a0b01110f06220b0703051b040e0612071208031003050d0504090c0c0b071b02100e0a150f 69
    0x140001a511184442da000d681c54201c4c8080e00402140009460352400a000c2c00e10880140b501c015900320300c407800003074040182e058040350b00701c07000965100103040c8070070b004103144d81200341c0c00b0300600c0c40401407000780041b0501c680c5006104020a07101d11205000c60940d0b05802076101d42500c0018600017180c1e008003078040e406041c240e842030a40041a802c01210b090010403d500100070041e0164441e44010b0010800c2101841600b1180d2100c2c0702d4010b004015805058803140420f400c1c113061000c0c0004211170003056500e480e00c035a0302c0402ca00303054036184e1040312a00c0401031a8040410001d0448502605000e42c1403543e0b070f54154903800040c00601650724810000000c141c060060809080786603660907640c03403d22007d82e00702c90304a4203c108120860042400003070301c00310640c0e04a1a107003841c2c486102c2c516a4862420b000740700094001d0f49188175451a6900600642d0400c10304564036030b40c00d510740e40e594039400d1b100b0034524001480004081d04d443c0c01a6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 679923615 1250 679922365 679922377
    0x1406060c120a050c01141b0a051e0a030b01030b060d110c030c071701090c0e040807022d04051b210403020c15091522030b0f010503030c12 61
    0x1500390744001d640819030510301d402c19001c52020800c0001d10040c2c44c607003803148202c0c1340c800e29109110713403c3c41c00b8020a0540c16101044100c00001815060755014105030f81611034003000b0f01294504c0b1800c884090303041424000301090412883d1192076000380100a00c605000c3c1c11141003542c00c1c007201c8040c03d221036044e5142c0b0b004224200754803005000900701407000170000c0000340c1c80c250005031101001d00da0b810599140074040780024960400c0d05007104c55100392003040b62940d0400ac0458414404020360004186845203d0900708070307181c444c01054810600c181d03044040a00090300d40444800c14003c200c5d54030343d864040060301401e4407254045000c400a00d0010202640d00820354081c0e015900144440c2c110b494540840300000a82401c5982000143c002107082030014580d05984104042940c805007084004201a01030341144044046a503d0414508000040e5540281140600000300c2d507400c00100700c43d090a16803000f054041d070840b0b01001950012 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 679924865 1250 679923615 679923637
    0x30611030405210d020309010605030f1506150d050a05010f0f0f210206030702010605100509011706150d0f1b020a11040b04020301060f0f021f110d0501060906020d03140606 76
    0x9200c4c0080c0507034079102551080e41c01c1000003807101e007410101880c002d0280850301c0c00341c0c802d4041c80707800354009801070742029081d2022280c00001c0003e403031480c0190120108070518000030000f880703a158020504840080107107540c400d4450060304224102c03402a05061030302c0c030504204440940c02520580c030000403946c801c1801641c00129194421b69074040141e450340000d00c810315101c0792083c2620300900300036281414441c0081c2440610304a50144a004a0300140072a2960340d0070307149203280c1413030603540ca010181387c0e0402010554000c4205600c1c114900740b80180f5500c0203022600b50350001c082c0704405641da40780d0350107032a00c00d542040d11103102d5107480c1c4035800a10f010304520b888440c480796401000400c2c2d5041c01a03190110b41c05444116000000d11649404a41c0300070070205007003244400c8000c640c41030040180c442490000000b6a82c0c3c0d00000d650141c91a035405d4902441005000f10103840c2c4080640400c0c041c03020118100345484030041c9070103010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 679926115 1250 679924865 679924867
    0xb10020607090e270a0312091109060f03100e0705240307020304420905041109030f0a0203070b1201090f0b040f061a03040503031807030b0a0603061103040521 70
    0x140c49069004c46a10034000d5600180410080580045440c5491081c508041080540b151207221020040b5950385008490060104207162107000310042c01c4803000d01160225100321030040b0041042e6044048580039210000c034030382c54015206051041c02007000d091001000c0816065644054199025444204000110500e08907000085042e141e000105841c81d100000c03954044204000240003001c083c19290868014403180140c3d9002e03900011503041c40d0a5040e014482c5603407440e4148034000340c0c41d002800015140302c03a03030310a0b41900c0c0c030075607588946441c44c020980100b06072081400140a910003907400205030035955a400b0502c1d2606602040c210b03008202081252070301c8070700034404030600360140d550621042e040940b4600d020b1312583c1d100d000203040c80c1d202c0244165030001c040000c1204001954018041c003501d1302f0814150b400900c082e100480e9543d0410305a5880c0300d8081040c1c80c42940c00a0203032024080c1a448200003801c401c010401643c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 679927365 1250 679926115 679926151
    0x604090b010c05012d2d200903120429040e0f04020103060f0303020712081b060f060d020616050f0d030902090906060a030609021c060b10020607090e 66
    0x9024064510a107117004c1d040d482d2003000392854140030440d18144440baa060008a5140d044101400c01e04400300d005404542d0354070020340000362502211004881514404030004003040900415040c00c08800300c2d071044804a0480e400d901071841914001074500c401142100143c0b0100c100c403500200c07516280544410100520716000d50b6a81a04c02141c01000110350701489207002401201f0449520030307203113540081d0b44001c41d001c2c00e106481c0100020f01040782c000c017a107048082e0ba20405c0c120f00b0710300d2b43c0b039a6078070011181c18030a1000500411704608150040c0c803803031130300a03104905d0310040c914500c0518000f040300b1665445411142c0304110701c10704c44000501b000daa404110103915004024180d4000b0304500029006442400350b03540c0d07090b2990045030350000b0007158881d003074000100a003848280c101c078581c0d070300e43c184400c000d6143d01c00e94902400700d45030007141200080c00c90740c881d4110340b0301d80810700a500500018684400d0584e010070f90340c929024404c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 679928615 1250 679927365 679927373
    0x9010c0606090b030609011b1407020405041b050d120f09090e0a0308150105030112080403150509060f0f0a0209040b0a03060236060903011404050606040c0e0604090b010c 75
    0x1a101d51042451698508003d21030345024400302d50841502d60084c869400313580c13404c0c42800c3e500050f2509002440c19050706640311035083e6410b00d40c0040080006103010700384044010290f01101041080300302004c601d41ca808518450019001189620312400580007902e06041030030325101401a40c0000040c143c445000380c0e080c10103058042c0c0300202e0b892030f016008000240005180d030380d8170941d00040366404015a8119014400400c0885280f4100b8402c41d2040303270000b9244008400881d40c0300303242a00f1050190aa04085450982d20b10800082da000c0964000c000c1080950108524210540203001d585000a00c00140c60242038000f9070404001e80c0201c440c0e94000c40d0101c00030180301d180408140f860149518084035081c0c0700101c50320706c004042e1003081c1c04606501a034509501449041d07a04515010b0f00303042a092150380d803002100c140e4441c07410845200040d074465940401460000740c8403600382030411303a040000c2c05c4c6400c842d90402a02d01c56401c045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 679929865 1250 679928615 679928621
    0x70515100f050d030507380609040b07050408030d2307020a02040b0411030117160f0e1504092f0f060304030c02180604050f040b190b040617190b0c09010c06 69
    0xc100311584407000c0b250b400984400302d0342400280e90700501e1f10108100f03a200c101d649170340542c0c401d41080e55540ea110044d500d6000e01d0704074841e24440030075410010102c1d42c1c014031a641c1c00038580740900e410303e00c1000034400100c42000060f0000d00560006041c42d030414419800c2c010000314031929400e000c1c0419410990000002141c00c0b5420000300505008504410300300040110044e800d2404c520300850461041c94610100c0c00009401908070300004680450b005009202050342401c141c044c1215084060000400820302002e030307101c408106c0e0005010107461120300e02b184108120107a0801081a014021440001001662403007050030039600c414419000605080c401d100441d280108a055048840c20034480425014485254050f0803401450a101881c454800140c000704224a4009003011000b2862014040500d20a415200c0841d4101040030803a4081010f008101802d0701c643d070720104407003600c000014105402c0604002101864a42d100021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 679931115 1250 679929865 679929893
    0x325020f0a06020306120105010305070b0702040207021f0906090825050405010e01090b030304050906060c121c1404030e0d170f070519082b02070515100f050d030507 73
    0xb00ca5000003000070902e07140182d542e88144d075800804c81e560440d5911035a90003103014040d4051300c045094011943c0710380454803d030340c1c09494241c00002e0f0441448007a0041840c2c900800c2c0c5607400030651500c0760f48500d0849840c1401007104c0281503904991205c504080d07580c04045968010800761203e009460003030041d03483d040a5589081c681c001120501414148660000c010801a035036983c4a1684c009100f120f00560302c09002e520b040c1740000385500030000e0203001c964020191080a4401704038680c2c804180115064030b0301c002c1c420481180c00030701103030714038581c00d8250030040101c9146502c60802215005104e0f010715010790450080c40c03140d0540003542c8800c1007400d025281c0d44003103071201400d00d218103a89070042d80c020f0040c8460110081e1031000000b052010020210a01102d4119641c045c0ba00b44262100008048060b0399005100461580030004040400700c80c41032140807811800d02040142100c1d40450540400a0510500c00454160301c6900310f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 679932365 1250 679931115 679931123
    0xa021c050301240c0305160501050108010c180b030406110d0203010b0a09080a1709010522050a05011803110f04021b100207020d290702060105150325020f0a 69
    0x41c403580b424201d0300340302182d501030494650409030200d200541280b918407403d0f42c5030425640b1150880f49160440300003417000750542d0b0038a400010072001c107511003038a242c0340e940c3d22003124240c142c801640503a940300d461400e800c104005030100d0803942c00308181c07007078004580385072101040010b001c0e600203030018103041100295403c029034000180070001c0041c6409080c20380311680740c085180c0c05403000100160030002d80d041c40c0b60302c01d1084030f040d00004582030001710544001e00546192602680c2e001e03141c0120302007425030045081c14090030248000315603480c155555a00030180c40c25800b81c20151010101a1550f20f03800580f9581c4480c0c00a8890000c4035220145402c1200c01c030a580d95104102c003801603101c202d0324503805600041c1c941461ba070b401100b0300e424890f0005600b0f03808560818841c2c15a030205109040790021228a060b03604001d0200200303200544030442103d10040c84c41140c01540038108030090200e0040c3ca102d041c00021041c00c050036110304507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 679933615 1250 679932365 679932367
    0x80a0c050a06080609061e030a1110050316030b041503290603030406050708130b04170316030c021f170108070518190609090201020105061f050a021c05 67
    0x1000a041040d05007000b82054907100640d410507078081466500054812030080038000d4240c0c4441ea01443c1f454a550409000c40d07025080b035081100c4102c00020301c0390f115840c4160804115817180007624000d04142c0403403425088800001e800501802e0b614540081c0c40c1e40341d030f10710880da000a0303000031401440718010406a0414421b012000181c0740d40d800b000c0041413004c1c54400009540c00c0e10390f91f0400315501c0440b824240c881d4050701d240706003010714041c0d0214603110800003800c02c0f0790f1020714501c08604c59400d02c0f03449000350030f0403807482c840800c1488040391040604045c02c0c1d0014011403450300d08000d6072020f00b4503414520000c51003d006d031901026250062600601c02080908541824400050011600c030081045074007031002c04640c200d0a0181d0084058007140020020203540b102d408014002c200c05c281c3c090351070100003a1140c184001c9030f0b40303c0c601080e01600d0031040300c081911710740c210110705811407140c491207199100c017554891505a405403a15 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 679934865 1250 679933615 679933619
    0x1814190e010e2a0306010818191a160809150c091206091b1801090c14181e03060c0f07060222120305040501120209040516030e2407020106080a0c 64
    0x7d488000c0241c05002064840344680061a030042583c050303d4544615503080b500550800320303050f025850280b141403a8410511a001d01911190351400e0000e40301d036090380d40c0f0311404a032070701c0c0d48111180268440c20005582200c0e00c00062800e204010001946402001089072404d013044402c28a03c0d442600201c90b88a50700c51011400c440c1120a8822105a004044038092061140048040d1603c20742c0d15860301070701030004202010b007425502d0f802813840c02a5849580e50310a80514801403400d0340121929400d000c0c4444040c0003030983d51200e1441005e56404150700c0d0002c070a0074030030140058440d000610341001008988000140c060880d09040b9aa6911030f220305102822142e00181d08070741510308850003400c0645d141c00e0b60385036001c00b9200c0e10945613806464181042030200300225401106c0c80555030401080042698041d59504009500c0c00786000e100d458000740d018038404a94042240c2c40040b450a0303035000710b40d10301850f0301e0048913411000c1d801 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 679936115 1250 679934865 679934867
    0xe060d050a0f0f0c050d0b010c12090905060603010305150613060e1905060d06090f02040c0210050703360803010806220309030807031814190e010e2a030601 69
    0x180344140c0b05851040140c0641020054600d106c0c0d1100c41d10b40d0380d100c0d003124503a070b0f00800c16400c106800012810f41900c10032802022049a405016040c41c580004903a00b8102001624180d0307074007400411141810a40307080e04900000c4c10191700584103400076510f03400301e00840006040c4800701c200d45080203a54403503040700ca00f200456a610301020005160b8540d000d0301c03074507a084440061850f1090038100380d495440c04020750400d04100c800b0303412540c001900120215050810400d540f94648103e0955041d0b602401140f00888403c200540d1896280181002990126105c1c28500da0303c00d181600240d00c41307034090300450208006aa02d1983d41d00c0101d00400310681080c50f80d607400f8105507101d000190040d040810300f8000c0500074a032025946072016010b100c4165208410115810442512030050180ca0072404c3c1400041119400342c60b52161800701aa0070318020f4013201c20024980800798400c1c00d0548003990140a00e050b00e0815071064076a2071802c000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 679937365 1250 679936115 679936121
    0x72402070e04020a030f0f061529030a020a09030c060e102307030c0b15131a0105030c07120302250302070302130609060e0f0903040609060e060d050a0f 67
    0x402000410340180c100070043e503c07044c50f00b003925031041c0c0d5a55003500318100207640c84c0d15513000804c401e1070903018119000c60030b20020200c4462141d2104c00c0d4052200c09102c1c1000c41d48109030440c01031020440c00940780d0081d1403075451900d4480066940c03915011154500350b407013440803030310010f030902c40360070501484000502c0e40e05001c25012244214036010304ca59505004200c0408034500301003622030400d2100d40340c1c00c503ea20b000b40c101030801c401c00c0c0e080f040c0d15510a10610044c50f09031183c500460308401000200c0c007500d405007600540f403560004025034035030303a0200000000a0b000007462181c162031076400507119202d803181c03020403003008201c070914034000001640000358006943c00a496040d00e00f0200c0085003c1c7c0300c0c0c040c041580069103640c1c1400700202e241340c23923070311541e1154000c4010030005854a81d0300f00c0c1c0320f00c503900039800050100101030040c14041c160b18a10300c040608881d10b030a0300302c883d48048500940700c100d0080d403108124188509580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 679938615 1250 679937365 679937369
    0x603130b060a0b070312020d241e05191503020c10090203101d102c1c4b0c02010804061d031c140406020c07240207 51
    0x602d805a21a080c02c03801070b458041c0e0702d0000c0401241d420783d003c08031099019540d00c120490400c3c041000c80880311080c800000c42e4681d0b00c801000000030358038a009800e00c1d000c1d0012103000604a00300030510030400400da401409904108500140440c001c0640c2c01c0041160b90380140c4969413a104035003050382c05850444420300f072100c5407003d65800b00702c16241c07811442001980314280f12045e0b04070052994401d5240c0100d4031032a400b010315400c90840007107030178083c07140043c1030400c1c0100305800600b856129400b0321480c0c40c0382e1403040d06c4102310b002c2604005281c00b50703039200042100600030080450100f14000a141c40112140c088402040002810141c990760b15005102d95495540a030410004501242c00c0c00101c0d840382d1006440541410300007a10400580c0c0d03a9401414080c4d503044810b0312981103080c40b4899443c03008888404070340305071034507110900030307401440d0562843c0c000c405000402c089190303d4400042900994071184994943c40a4244010de07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 679939865 1250 679938615 679938619
    0x12060906070c0221010b03030a0203090a0504020f03180c060d0c02060703060303080726010b030712050403091406090d05061008070e0406110706090c14040c120c0e0603130b06 77
    0x100000069a03168010300480c1301072145248100c0c0703880c256074003500604e12415050700000072004641640031004201e01802910075425180e685c0081c40124481d04100103d100414070200c0c4848103485800640311604400701c40d02214510b002a1607a804600c2401c521503442c0505088203405101f1240e10001d9414204002442e641300903140030340092200301081200e0403c1e170042907096030181101451140248032640e1221400100b0740d10503698a8007060034184406640c207141d0140601c5146c1c0766980c604c00900e0448045c1100105800c1c081e4842028440b01c001c1e516045100c0170428051801024281020007015106c0c1030b1a4100d0040d81e08130810502c00b1030041481e1a40090b41708000007202001d1030704000b10f50041940050200c0d00702030185003402a8004070400b40c4599000c03060549030301000300821522500340800205d04956244100c0110b20303401280c4040c00c9003490f240c0340602400242a950040360035013082d020f0500414207121450134007691141007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 679941115 1250 679939865 679939877
    0x412020a030e012709020d050105030a15050c04170a060b180c070302162403060e070c020301110406170109090807120306090f0e01050c040605091302091206090607 72
    0x91900d000b410681141d0300340741444a000180c050980d512061080c00300081851100d086498161580207540003013034a99440d030074400040760516020a02240050788440c180080c2c040e03008052024000040105018a5083c000040c800c40a0301c089141d240c8528042c040c141003d1402000701e48501040324041c034044000722128002540d2a42e4102d02d0091009846824502e400c81c9842803100a060110704142c40004d04103000c07001c00c54150045c0a0444003005044c40101c0c1100e44074030500c03251064001c08105000c0c0610720880009002030300220709581144a48080b96003d68000000105510075458a081c40c0c01c400c5c4c1d0240031458000e0024481d503859400550007940720190044010b4104861800c1c020b41c0500010b0843e035074280006400d84045400a106118041d001c40d400c0c040021005400c4034101e070240c54054031482d060241003400d000481181c1080c11301000e90130007490301180c0e80ca1110720b040c4604400245001d02d4601880e0741084c50142c6290b0a103ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 679942365 1250 679941115 679941133
    0x10801060e220908042705070909091106040b1b011a060c01090b0f06090708010501091a040503070b0403050d0e060a050c01141009060509010803090103050c0f12041202 74
    0x1e12511844810400d25010603034092244680310003c20142c00024440e02001400040383c0b51520135010a80c0030104003030141d415181c0d401006d0782e0040780d0400000d041c00c2c0003440036589c1d42d030146d80814025912030482e004040081102a805a00803a00d0000042450360101c00540041d03401c800100c03009002140c01c17119500b0038207074005081c500c1118045901000321100358451805280c1021101c0124103002c0f4580c000c0c101c00f920f146d4001e0148100180506000d001418100c0304180e66180c0207070718280c41046884503036030f551540464100000941e07554200202c102501e2101d0550f41d03164514030700a07207003010032407002c424480300700c0040d581c0d640c0b00c1c0301740c0300c1910847c00c00655641480d02e12070300411048075501c50b8120103005102d080300304d20304003206445c0c80103000c1101c60340f01e60030400041024801e000e01d41d8030411000e001940b1a80019400945443d0013600341424244002501e42102540c117043c900f0503070421081c4480300d2400a5460600d001902c4056 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 679943615 1250 679942365 679942369
    0x102040b040605070201110109031e080f270105160905030a080f03130503070317090a050a08181c03171e1009021305090c0c0714041503030e010801060e 67
    0x1005a2040605103d40402c0400030b59018004410408240400270815410710b4500030700450f001241c0d6011851007011a010388900642d00c05026016402d1340c405550368000c48078181e140a11403402c0504019010b4180050003401341c0c034007071410070a0b80621959800001000e030301c1c00380d1040344031303034082130b1041c0100300880c003190090b400e80c0d841c1a5682e620400301da1804142c1e0080200790b4130001070a4010300d1341c42185945a40d00480504c00a0f8441048070b40d60f400c000400644550070101070240014995070060854034082034107060044130320720002d01600603915030b00300f0f00b00001d0326420030076a000400e5200100303450b1081c0c0541c10070702480d408c102c003030004a18250710094040349118100e5540b000090444c0c46042d5626012210a04401e807843c2c4581c2d4041c5e2000d5010408500121081d03402207101c6100805c8403915000c980c5009080404a441c0c01a81e121403442c0400304440c5004e0146001e80c944e0b004582990000620800050740700c0d104000915403a50600c1e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 679944865 1250 679943615 679943617
    0x140f0703151d1e15040603140d0801050a080c010507020f040608070e0c030c07020d0212010510030203070e0103020f100e03062e0f0618170d0912120f0c020a030309080f0102040b 78
    0x41940e1a04c2d00a001e204010030018141c0d6000a008010200d80c500080f410014000c15443d445545000b06a42d13100c00340b0802c41200e0103080c0482c4c120003450f2005501c54405840c44500050002e0768401f4044041000c4035403940006000c0d801040083c0b15141004484541011f003190000d4a540762500742c021390b0b800382440c001d01c61000c0c0ba29020035940d031140030014850010001700168144002e1400c44e1114502c0120b019010b84000021032503007002901e81200c0d0081c0101c00c040e40795a0411000c2d18007111040c0a0008000c00005a0386081182d1445a4010f80305000904001d078000122140b0254400e00c10b915030038814030080c0f1480b030400040318041d007031501101090409030300c440605074210b80e0b080c1c0325040c500d8000d044000b0b00300299115944806490366112420044400b100758006441060400f0060300024400c940400700081c0518103448800000d07400608000c0e80c913401540003a402c50010b0000100078440813204441050003149000d29000402c0e0031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 679946115 1250 679944865 679944871
    0x42108070503190f0c0f030902090a020c0709060803090f0405062412270a080405061c020705010906062c070e062b140f0703151d1e 58
    0x4010002c80450004984910f4845044007103400c1440109401d140700401002c040146400141d850358250340454042d20504030362075005014a0003903500c050010002e0340c44040142c1d40303881440b800040009107031041501030413021014540c3c64845404020f1215106206a0b20aa250500f4041aa9202c05401c0408512450007148050010031400103e000e5819440d0542d0b483e4801c00c0340d0081a8440d062034926558a1001401184100691799000012004100350700411091259141000c041d04000c802c52200800d4183d001e5030881c1a170300115402c44c3c1b1a91681c050008001081c064400074028990038004486200000b041d400c00035295030300750110362207011544c810710409a400340e020b8082c008607a1055200c2550a00c1c2c0d40a8040c002002807508200700c580c14140540100c808810383c440445440b0030000e900502005090581032680e101c25003120520b441c51000000d099201048007500410714208600f1310b00249510341e01c804051141c1003500e004030820390 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 679947365 1250 679946115 679946117
    0x312010303032a08040206210612030405010207030609050304050409151a0102150402270405070b07150b030a0219031110022a0a0b03070e011403060d0c030206040e04210807 76
    0x4130710f490390b001040561040ea20b0040c643c0d010703085001c500c10700b4195114040c1d0710543e20304510310054440d107510381c0590302071240141c001d81010400701b0340c01d4000e0a0351500a00940e49443c1d6113400040480e0540e40c3c04859440202e12000404c1d80700c1d100c0c2003c05099044030024010081e80001e460702d601906001d0202d00110118055440700b685007440c026180800d80121106141c01c92000001150122140d04c2091004503aa5190005451741c4590003001082059443e21144001e400101d0340c590b01440781034240ca000da40ca08000c00c1c1410814800100054210f043c0b0311781d00c4201c10403040c0285041a07040c001a60b001540007800c000b501c8107505e0594225800700e04a0b510072030600da1100d200c040105070360480c100210b004440e19181d88160303481c03100042d5004480a138000c0c08446092000586c41e0030701c080801030380c0d440340111a0901352030f030707001031400e80050b000b0740c40002c400c0041000308860072003080840e030307200c0100d110b0a09900d18002c0c80d01e20002c1440d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 679948615 1250 679947365 679947377
    0x105091801060308030f2a07020105030702390f0a1a2206030507022406030a0f05010e010b06030f060d080705060a0b10111905070302030312010303032a 67
    0x2554040203510807805144c2c0002882e9583c01c00310752215901400365040c10110310b080d031100565110080d10b0481c0d075040d81868504080072900107440320f0300000c1086042d40614000019906007071000d112a801c119400488980018000c1c402e1a205c0c4c412068006e6050602c050340d00d0743d6010000c4111171440405185080c0800ba0000040c0102e5556904030b52001c501e1016000c0501d101d0000e80b11f1036541001243d6624030100d81d81c008003000410100040048061000c07003661001c1d621007406021921013640f1030b55048840c0c44000b0094800fa507580f080915000401c1c01b0f0400420401c03680d9500350301f03003001d200c0d030300350f2000d000c0500c03a52a0880e007408100107441a20000c1d6004000e5591a140c070740249001781c004041c2041c8131380f51119203c070b24107005110011000c850b503001003084070b010261005e80c1c8003503010b09a8191180720400001694201300401c4204200580040313203500d035140c0078003034070050040c24000c5001c0c00403402801c06940f04401042080f40b1300a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 679949865 1250 679948615 679948651
    0x30a09020607020a09050a0f0902060d0c180801140105040605010906030b041404051c0503070207090e0f01050405070e070c030e010c061b050702030c0301230c0408010501121406010509 81
    0x501d1032050301c200940041038900001014150382e070081d032168800c0785080c40846881c0308108200c440d5203000961043c004e10a41c2c1e03035041583d2024103202d00c030381070114003540601c40341c65404080364004102691503040b070a010310761284401c1c0c01400140c4080c0030090800707001901202c0e0a00540381096511040b05172240d90301d8228598403541c503408200340e403c0c18103107a42c484408180d1080750700081d030341a580c0c0034840c90440b03214a83c0c41d40a40903084c01c051250000c1c00700450444202e10036141c40d03001d002000c0c072501d4080c52080d0700622003030346050640304074004018030311030902c07d00c045607101003a0000390b5503941480074a0039512100791450140000c100442c0010607409150404c3c16510350804010402c03a4000c90495800c0080c00c0e0416098071019200000e071044001d10003074031009030385961394100010b1305c03050f42400d444003034440c215a0300340c0c81490403220b410f160100380440f18130200c8038694201d016191960511000ca0790320540a4001c9018070341011407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 679951115 1250 679949865 679949869
    0x709060f0e04061e230402010e0d0204110d06081605030715020f0f03030108120c0a0303110c060a05150613050609010c080c0307020a0806010609030807082a100e03030a0902 76
    0x6070030540e40004084c0160b155210b09070040000690001c900441700744001010a0920201c0e441943c0c140d4580b0a11008903040c070600300c1401000f02d0f0803d072106411940d280c0c1c00b0014100307004d95104000b8070b003440c240001d441d020a406c0402c51400b05d1080510903901d02140e50390540764031400441840c6000b44049160560103510f04a582c050101201e84107080440198102c81a890803259998031440032004944107400c2d00a016034050300c61600080d0003904446003200d8a403c1c40c40c2031900111405040c403a04490a4060a43c0c80c030130421815969000411050070603130f6614208006403800304c0d002407460050314450500030800c42c801d80e20070310b5081205035011056644401140d41c0c081d40d2a080350074220f01c48c00a205000c11100303c000b80c00707030488640b0390310030340300c40e1840e00c0710f004680c4615020340d4469801c004c1c0042900c191140f0b118a414000360500181a000700703640d00380300140007003445035410490324010100000054a41210002500140010340d600c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 679952365 1250 679951115 679951121
    0x901090308030403031e0b01050d05090a0c0e04030201180317060a0b0c16080a1e02040204260c0108010f03110a1d09160e040b1009060b0c0709060f0e0406 68
    0x310040820400100300700806a00d134002540d012069840348940840700c010b00e03000e07615148000c0d40062000d001501d0300f0000c1c0d421064000340c1407415034002c0a1300da12000c96a100f16081660743d03420020500041503424450720026400c20b91072410348203d95070380208036a03011002c541d152004400402c0d2203a40e9021400d0007860001c2110795031789600009103850b407560480d443e003044171444000038901008a100109075900051030b41121200b540d0640c080c45400606a030420707420322012803842044c81c810001c105868903682c080e0140720301081d00c0c0400c82903c1d5410480c072200108282040ca0f44404292540f00a8030b040a50f18100825041381c000d601080d6000a0f90040e04046140c0300ba2545c01209040709440c2c0d82410442c0c200d0b60711450388201040141c01a000501003020040b01da03402504803a05003414130f0f0349804880c1a6540394002401540300000c0c09401c2240c10001080104481101880442c3c980b8031609400082489060b0a032015400040c0421407558 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 679953615 1250 679952365 679952369
    0xc0b07020f19030e120d050f160f1b050f120a0501060f05091303020309041a09040305180405041106070516060e0103060603050906041101030f06120c0509010b0f090109 74
    0x41140c86481c844091101e581d03400240a50104454080750b040b14201010360803205d030309080041020f028002c1d070494150b4400b4200100501741403102c48209a564450076040b40e0244800c41101c0c800d9051030407500c4200c581c0d024a030000c0000400498441c0c0501c6105003c0c00c1b80c80c41000c407061030300c05061945058008020754a00703000815100c0103158a842912801d55406500340e03641d403e0410f1010381d00c00083e02507402806000840e242c0380e000106000314481000c400944070102140d228030049d83d045000c940d01056880034000400c110300100081102c00f80070318141511500f08004901c0403244c09008005001400c0c48000c003d41ea00703540d8482041e20b03101e0307910f1200801c0d0311905805a0b0000b42085400140580f003030003014003900c4904090800354070381d9550000b066141400250605032920a132007c0380c82e00f0711070b4400a1020940d145903200582c82c1c00200a125500100d01c242020b0005010402194080c0d135402c01802440d0f590303403c04880181e404030038035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 679954865 1250 679953615 679953643
    0x1101030c090506161115030f13020d200607020906060703091d270c0120031c06060504030b0408030a15080f06010503010b0f011d040e1b0d030c0b0702 66
    0x20700a5081e000500030380204c1c6000d4aa051046403100c0d00f04220780402e82003106100c0010b1021403491511041c02540200102c0050000c0c6495030b0b000c1060310020101c1604c810340510810708909200b800343d03c1400d0310841e00e151034400c00d9800114119405484035024110100d044030030140940c010784060080000b0055007850015105015180c00302d600c00e0408801c56107000d51944000c0e901060241414080d11400c03114100440d8004030145007503501302c85a000b1203412500503c014420010441d0132020b02580b00038070102a034805078403240c10400100010808201020030341c0d80c02a0384245807654036101c2546020207170081c011602c05d440c100780710000c0e11100000f4094404800c2c5400d6440503a40e5608044c222550315100d203401640e03544c90480355602c515080b00d40ac0c1442f00c030303518030400540c4c00300d005c58001c1031034040035074014848e00e40d90901114609691610485070880209884d1340d0080101d4502c0f01300604100070300c2d02040000c2d00a0101480041c0f407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 679956115 1250 679954865 679954867
    0x106090e0a1203021c0203070c0b072007080d110a0c060504180506130207140a0503071b0501050d0221071e03020f090909071d010608010801091101030c090506 70
    0x100210a501c070607529000300c421028520045882c0c50090082e1901802200400014401042d244a010b51310040900c2c04100758190844005224000000d000e80c549549000300b402e040220758501c2c890030b4140b01e125a00c034020421a10000141003040c1c1c1e040f5261080c01d0501c144800f80c41c080d100103001b01801e248000200e4142e52080140040fa007201019069491461000d001116403d4443d03030303002542e400400c040e41d0000e800500c540741c4182c40301c810b80c440e201d00050811070719003401c55280e000012060180211980800f00045041c80d48018240c64040060158403e00800c041056001326a5800b100c2a0891807680250b100b0b1140405281c981d40090410b007580c002c0c034402001c1216900d4010f071092095540700c040f002249072030104290100714410b84002d150b01e50038450308101140e03030440c00c41028860358070390900f00c606504040300134000a20580080d42c19a1515080001180080e03007140c001403000c0c05c0006020130700c410200c48020090b0050382e00210 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 679957365 1250 679956115 679956131
    0x307081605220905280308040210120608030406030e1504152c070b120c0c0a05030d1509090b040b0406240302040b04090f171b100501080606010207060809010609 71
    0x801182002e414a00d44640c4800e1241d046010145508009401b800040075240010014100707441c4c841c207241c2e81d42c01c1c00e0144100b10f0000006441498000d400d05820108040080c55018044d149540f5405030280c114440c102d071a13020400401080981841c0001c4210020b5094035400074900d0514040f039100c0d00001c4c07590700142e00020281000c0d00303101d220740000388560b491041c1c407400f51039010034017010303121f000780111039402c0460840e2660040c5001c6000083d01080103001400100c83c003c21121641030a8914400942c1d200c454000d05110403a000070303510310701031a4010b5100c0d18510041d00c541c10180c0c010100c0010200002c03821003ea08269075a040310ba47c11a4800c40d414000c5486010900c415107040305401820503010345964000120241500c0c030090013207540d20b80c01e040155804100c0c00c89801c050030f945400c4043e10300d200070801d008540c058811a0024403003801e1620000b035541c1414800c0320304000e20742e07010490070b070400e4204100900c0d5603101442030310 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 679958615 1250 679957365 679957373
    0x6030504152307110c040e0d12020909010326030c27030607020708120a0e01050f2203020f030106051c021c0303270f020906190305030903070816052209 67
    0x40000b0b42400c2d2610031700315150040d02e0a030180d21344140d10741d0080d0024080401043d01e05844081400c564241c0911050489842e02c4520b80d0003180245005201090310b0700e070762003040d1040d510010888008004001000881604540c580c040700b040b4084000c0d03800070840911001c003c03130203515009200c01c2c44056940094100d0549949a05880c40707401c100175801000d2240044600c00301d980048180d410390302a82c080c011090042d24118a040074100802401c10307081d4803210b001003e90b0905109508147c622a1096141907000b005500e00300400207005050a6007856036884904a01030b01b10744030b4941c498408400750351040c00940c82481e01a0251074004002c01d280b00441803281d007241c001c5140610b0154128040200400300c0e6000d001e06018010031300c90300054451400500702101c0103e40000354054000b41d80c80b111100c04041c18034807179a00410f4241e000c14010000408000b0301101101d81c100d88403003069490380c1c60f1502a03a0070412580b5942d18111250046c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 679959865 1250 679958615 679958627
    0x2c060d0f0506250804050a0206160605010e040309080d1d040603021806010f080103171e03041416030b0c0a020705130c0f1704030f030e100e0706030504152307 70
    0xe0043c0d12032003090410750310403120b2101c110340c05861980301043c40005420f00500030b091551081001c3e1003108003d8584105481003a400380c28004a020208000d055002040e00c010b402c1000c080e2a03280300540c0010205120641201d040e800100814405503840d80d00070390080da40034116403080000c05020b00b4407207070b040712068041420000c5068490f41704401c2d0300e050360391001484840c86050508400d29412007c1020040000c201400003080380e00000b80d881039100c4c0d00b034030003905200058207007010045010301c0c444941070a420f00000d94000305155200041204103a00d90203e4901241f51100c60780c40a80c0140d04140d4040003103d894000407032843d078039103410840d102c944000701c8041e031141d400b00e4842c101c45008200020311800f6000d207c05418680032901208200a1600f0040d411004000203507803440000003804090101000920403424200b190f03181c940c0300d02c1e550643c21586540565070b252903441d07100110030b550038a8411600082c008a28100d0005000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 679961115 1250 679959865 679959901
    0x3030306030b06041112070c020a15031d21121819030507030e0409080406030f060503030412080c0307150b120a03021c0c0503030901062c060d0f0506 66
    0x18040b070000042c0c83d403c06014424000d4254200e661601d00d544003519401003000d0070020800600c2401400587d80e910b41d102c018207011f001c40c420400c0000d2000c1e04039480d41090f000c4942182000c03120040000c00c00b00c501d40351031300b4403501200696003013155034800c5180e543d00c0d40005805001d0038403074080d032603099400c00200b2110b41200c000c228171402ca0440074002e0008804000980c0000d101d11040010800301030404507000c03400d9070b01c02030150080c2e00300100003503441e12000010a200d0161070000c5c007040e00554078003414904510180c0d1201e12014020b040c0000714030030480e00800c00c6031140c0e0381251000e0100301030341450310302030240301040318811400407003200007001020659a030b100c1d0f41a0001d1210070b82c00140c0302d103052042043c00c014403c4541e0748a01144050004500c104580c0000144403130500c2c240700300c2d481000d880c20201150f444000c0340c0e10915101115000007080711281c800c10a0342c0750105400e035620704018aa80100420311140440300c0800e42c2c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 679962365 1250 679961115 679961123
    0x11418010f0f08010905070612090609050309010f1803061d06040c06030e010b0a090c20010f1b09030b0604060902071b140604090504020301020c07030c0806240f03030d060303030603 80
    0x70340b069807100b4003820f0b10400c0d10301a015400181081117041c1c06410658840886500c0218010511340c0b2143c0464601c550f0603156500001079503040c1d903a000c00801503034081806c10741505950900181d0b8889a1400010071040da5100350b030200841041c4c554941c04504da048400524003071420303064030103041c490030020a040510f1303540360110602034a1020040502030602a910781b042c0c24001e40315084806042c4070b00c0c1c010002590f0500307000e101c8002c00c0c240000c65040384099080e403c50303002d441d10940d0030090740f016100c1240d00580c80d20440350002e482010b00d031078020029004041303ea00c99120b00344005180810050600b43c2188a4000c4905860f011507031420041881c030010b11001c2e81c4640200001d01488089500064205001800040c100480401c500340380180c0b9030000e64158080d07440400114808108080d07001030f2425200c03038984440480710090040304078201d8400c5460020043d0261010400d80726450f210550510105940b070802800400d103501083e6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 679963615 1250 679962365 679962389
    0x5010c0504060509011805030102070b011d040305030c0304020307120f03030606030204050d0b0406060909080408071d0a090f08040b0c07050d0b04171e1210050306011418010f 77
    0x280099000e24296411a089a00c4442c40c1c21083c03401150302d115a040028484480b4080104503130700d0900c00b426480340f10380c1c4202115410703c3c04075a00368180300791101d2425a41c10421000a0b40041601d40260101d080c0b00c2e01c0b0344651000a0070030041750840c5000d8907189004200344030003040890343c006e0280e1030811070f40342c46140480c146e200d6400780c1600314a10f51503c1c130000d0b4588100d242c0c030130f000d40d2002510a032107114a2065400340c102c152030003030000c5814044084140b03c0c1500034103448910104c41c2010b04690006568006c110f07802132540d8000400c140400b03840005a0258845642780d5183c1d1102c00005442d000308000d00f4092180010105d95802c0c444034407007109402115010640e40c0d196036041c1712098000d04a40440814000b8161038a0300f001e00400d1440342c1c80c141a1103002d44103501c211088000c010003050048503204100540340402e00c00e06407a040b8a0080000c05c0202c041070614411035802940850188000030741d601801c000307641620900e030950 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 679964865 1250 679963615 679963631
    0x1b0c060e100222080c24041235070f06151406030c120702070317070b060f0f010318020604030c06180605180112090f1e03120908090312070501 63
    0x100202800e5018112850713005000180d02c600d000031310355054840d100300841d00880e100c0404403044d00a071b8000b038014a01400751008110507415004801c0c84200100304041d141d2a49c013142490003c414042d59241c0080c8043c00e0003e400000300d402500320400f44003004060500542c050000e200d59400d460500c0916180c510346641168003d900c1840c0341d504001042904509810010349218207500c0380c40f09c0040021011101656400011001d01d07484801c503090a010500001b4600303842120020b00c07411590382c80d91400c0c482c1000030301c1c001600e2003100c40b85d000f14400001000e5403004010400104100b014410482515440d40e2080d240803041d240b4400c402e5414059800412014003641001012a01001a840d00d0503d00180004c003080e00d41011203220000031745842c0c550f02825003e00040c07850300503240840310410b68007011b084d1401800741101820b00c04603283c03262414001d001d4140c00351891184010151840c04c1814070220030b06a010010455481d420000c0c6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 679966115 1250 679964865 679964917
    0x17210402210c0f030a05071205120c1009080412110f0102010504021f09050a0801020a0e0609030d12150f081b010f0813060f06090f1b0c060e1002 64
    0x418089840c1c0034001d241514a6808006407501c80d207101940510038040d070760000c40c0040101d2001464800c47e00d2a040b01d00f4286a4140448440b009003420400c000340302001c5c0e00000c040d025410b400d00002450b11444c900900c45126a80c003141000f284020780b0380034001540130740d4081c0442200c60300300a80244005a090340c01c11a0080d50100d0007402641d0360b00550000e9a4280c4990b00d859105191036800080b00c08400383c00103600b9a5010032034408454202c00d1505e80a101103d480b42000780403000290b45034166002c080c200030080b0944001c1c98082d8115060030b92281c1a003c10158803a01400003d0f078481c440e002c0c031031160082c0d042d90700001c3d0f0141d00282034117235210095204440c100ba00d0724032001d400c94410940000451001ca1243d21511124000c44003002c151146008100360a440d40a1820b8410900e000c1404402c1440c20005465140071030500300040030300c42c200a8000d0803685480c0c02c941c02403851001c085001035000b030581080440500385003501c00c104d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 679967365 1250 679966115 679966159
    0x309070806070f021c05030115021207080309010c080603070b0d0603020a031a070809061501021501030b100503072319061206080a02030d031d070b0307020d080f0417210402 76
    0x17100004a030040006000c2141850288031452030b66004950707090f4001c48520881d0751224400b07075040f00d004014801524400c0c0950403c941c180c1c41c00c440380c0d003040c00000f038442009205451250500007402c84a080c0c81390000002142c00034425150941e8a04040298072020440175940e80303000c0000a820b00e0141200c0d601034503a0100402070b80e61000d00d081c1c011200752610030b041d4802d800244a17020341e1850042d010750b10510244080342031140d20818288459007110b0312941000400380301c510900d2007510756280000d2500c0541030f10f14000300300c3c101e0341044c442081c04a00640441c032503802035003a1000c80c1d4100c0c0200080c0d6a180751141d262010554000d41c103401c8910030345007052080c0c01071040390b04480300886035034080700410b130b10303101c1664440e00c2c0103000402000103003030701030086125540702c03820140707014588100d1101000200602c001c1c080340c41050005041c500820907200c00100150b0801e6220b00350184c3e010740540d040b14128880d041000524446811a203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 679968615 1250 679967365 679967413
    0xd060e090d12020f0309070f0503030a08040215090a080f071a09090703060503100504020906030102030907060513090501060816051908061309120f020118080309070806070f02 77
    0x1500d1a07280410048540c200a494a01c0b0308039000e200302e0b15041d4420b401103000310406402406400e00e000f011841c0441103900c91440380d0414410451602d0f001103034240e001c0c0d811240351041c41100e0f420381e100360103929480c980021000102065030440002c16404030629941140c0c243c0d0794415040c3d140c03401840400780110814415400729050900100e500101c0364100814407640f150f010a1410484485035800a40c5039000c3c0815401c116600301d4028605030025403952502c00140760b0394031042d01c1804200803001411602503640c1000d100701400b032034101800f43d942c2d1883d004001c00e009030b4083c041003284051904109015904480c10f064001c41c0e408070b80a084801542d030602d000f00340980200414140341d109007a140b007004281417181e214a030f0f0020f2249801001c50035810504003e6a25025400c00d602c04080003150307030701e58008602c070307502d86d1110340385c0b4102030352980304034628852b0030180503405401210940c14007400c0e60896454126209551442c403c042c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 679969865 1250 679968615 679968631
    0x30302060105061e0901021f0b041401270e010c200d1209050a0204020f040609080a02030c0f123f1617120103020f0405041a070908120d060e 62
    0x880d22880144130409070404c410140140c9100a0303804249800141c0b5040052800d5a0348103131102c06840c02d4402c812480e0141203003000782c0d60504140b10360310051804400703001c80300b40c22408410101c980140513154420002404010f000080c05004a0030343c040e029041e107045542102d8018000607604c500302e10f20761301d65821410181e0118010700701880252017502070036080c54056111070006000060781e03480034641d0395107000c0c0000e008200b1900140c4680d0443d01131000565000180c1c40c008407411070703050010031800f10000c1c000e00d10700c18021003107000d18400e5944405900311151141d0f410702400305903071180c1109290045d0716224406900031030501100903622082014a80d007103110752011412004000031100c4950400d007005071030f060380d4a00610441c200b801c0500920441035500744918100766580099812540310705111001da141d001426403889201c03140e00400d0610f054510742c0b81c0d02c840e110140d50100f503517440e4403810131100040c00000d03915000d02c907a1078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 679971115 1250 679969865 679969897
    0xb09030604240212010e06031f0b130c09050f01030603030912020a030512041805040201022505040e0318030f030f0304030e0a060c02010336060f110403030206010506 73
    0x41e56105105111030300e070030407224450310030018501100c40c8010040c144c4840314496140d854218502c00b600d20080000b03000c0c0d003100f282d446012159440e101424898810045090f040010105007800c0c100045905114140803c40080f25000f156a4050b00c0d0140c600f03209040d01600190b007501e8940c8130050024080700020801020500072000f44280b0081c420340035a5030f2510f41c60700e410b40c001046c0001e503800180c2001a105000f01260100841d23800070b00040c41c194001075110013100100d500b1121a800401c8282107181e00da000c00350000620810006803d44400c0b55250002e4246140401600070600c126290004081d10a00d40c81401180780000342d100d103500c0c580000e0021014020006c080340910713a90b0300a020050445642c610584403800e00006081c0c500c0d40d18010210f000030034102148145c1600003048454280004070451041c0749414801451802030508000b403410300c1074030601e12024000d000320390080c0e007181e0580c0d0701c0d1340421089100f1400c6071920701c49 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 679972365 1250 679971115 679971121
    0x1061103040b07080706241e06110f030a09032a030305070f0c0b03072c0f12030a030501180c050307111f3801080415020c06060a0b090306 61
    0x11182c0c005003503031440b0720075182c14014a075664006031403c010006003044103101000c2070000340985000700400c0044000084090303464407010441d4581d01411040145011803400760840030814907403280c290f003007180c0e59101a803070300416503030580c002114030015000d61040c503100c6864507489000c0421203041e1072a4a0b41d64207131030581c40580201c0d800344d01c07211900041544000028014644580f50aa07a031800200040c603401c2c2c000981400111b18172041d07807080340c030b01d0030344d440218080e41d4840c048103008000440200c020394418a282c44002011010241d158000c18100c6421905100010817400d04035016034100e0f58905000480900c0021b030a9482010180301480d10310f0180c0c0d5080042002403440d22056034060903e040c0c13205c01203000d4180740054604100b0094040303814101c12040e107180350203103041401d81000080c0d0007180621401c81c0001c6401a4405d1085650360013134244103407a4001241d80350310418005030000f8945040d0403c4030b0004500a0241a60b55 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 679973615 1250 679972365 679972379
    0x1f030b04060e06190b04080604030f02150f0613110a39170a2109050c091e070f120b090f041103010f0204081c200a0210080f0106110304 60
    0x80c074801a0131000300c0e013098001100c4407200004d1019055400140c03915190030b0902500500c4560301c030604550081e040710700c03400d1440900c203070040d0f14945007102a45403640019119084034225804c82c5141c0207250824000070001005409410b4460351121f00b030000a2008a01c40c901c0000c10b0984803045585d440c0e48210a0034078114030519811954841283c0d178080c10343c0111340f8460200350900d000b0400410000032840c0520a201070901c00c4044966034030b6240d1421907085400356030300b200030544040030150b1014200c0c3c1d1103448000b180c5801b200c010f1600078003140050102d405904a100e01140304d0041d50143ca6020381480c450b5161402000c0c24810010000e0b500c42000420394121558207000360424810345040240e140c0382482e10f01420309020201d040d450300c1c01030910f1900c1039040940d80844112001500b80812401100071781061441c0d90000e6000c28500c42e0403010603003244032503021b0400c64040d00c180780e0700d45038144c406510b80590141c0960090000b00802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 679974865 1250 679973615 679973629
    0x907020714060409020307050a082805090a050105093307050d0e0601090b090c0a020d050307030b13061805041e031206080c2706040908091f030b04060e06 68
    0x310042e200354540342e81c81080c0801c981040d940100081e070001141003505030300203403040c0c00100d40c1020354a0032808001000d02040c03401410083c668a42c40081e4185405100ca80c541d2a0042c0080c421890100c0042e51504544c50000600d0440564a441950045a20380d0b40b014800804a8081c1c6c68000c0d0645807034011140e4480e405440e80003550030401c0601116008125001c400704004c4500c404010341220000d000070364503a401d01c03404880e503500003001c040c0c0c401c1c5818031701e0b501c1d03c41c400c044010741a400081d42e00080c006070030540d0006a82d00044c11a10744d18141ea52000c0001341d088103a030300c20380e0040c240306220041d030b42c440c0c42c0c0c0c088400704452203030400c144010513141021040e20101d40c00459150002140e541c0d0504140d001074000d0107036030b6aa0780640d80b019148540b00507018203124040c0b0364444040c3e04200000d821942c480500908541d511085112480d068040c0e400042001134200203175030f200d40c10b05000300402c1c0e4040c081e4040769aa0f42c0d0f07050100d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 679976115 1250 679974865 679974899
    0x44b14090303271606030b120c101404092a08060a050918010e01061502030301060c060207060e0a0b1012031d010c0c03080c010501060504080307020907052205090609070207 76
    0x44e0240c0d1094018160102080c01c1c0100b400d5200881c105134140f041100d0703400004000900d58022081303880c60395a078008601e040e10b0190902484c2c412803c0c9544005019a030881d5440518200283c101c40390410000500c18a501011403403140300d0f10011111410241e90700e540045000d24240103d00d0401004c1c0d0307000c3c142e15940204a0307034006403a030a541036445464a80e96440505001d005c401c42c2c628018014140010340c51949061001082500f10510140c40075074013003102820490b143d0080c608141c290b20498445807410304081030308040540e030001c03064111045c0007911050903d90080050341548906081d03a05030380300344507103201310800f0504100448580c40300050907070700318401544c01660840d4a841d0403002090840b04180c100405000d002e1000b00829180001210450740e41035881c21116107507004280c403140035481c200b400c6545403130031242840721090b4038442100c6089134108211b850741c03824805044400c0d030340000142c1042c4d4081c0551301c0c801000e140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 679977365 1250 679976115 679976191
    0xb09090a02130b04050a330c0206041d0603011e0207050a0206161b03211718060f0f0601080907051504090b044b14090303 54
    0x115140141c02c0078540d241458005060340300c4007040602041c1848884400034120744840d0b0401426401c1c600c0c4907000c041c01c10000c00944210206011900c140d10506c41341c0d40c0070f00000d44847d00c8005240003600408041040850401d00090701d45c501402420100d2801c005501c90801c5000c4a44029500040c0151040d01c100111800180c842c1c2c0000c1045404e0448440c3d04c00380c8602e410304800180136181d140d2200260000d1011440d034440c82c41c07072008900140c40e50f42c11000000d07070746c00c00d0304218020818a45000c01014600580b05c10729622000c009845035030f964406071002c03011041d10500c400340d52401c001019540155000703900b01040e0070859001076512400913201103290111841c84d03504c00301d02080950f819000d0300d40b03030020440f01440a1300b486140990031100d005200c58001f10203d03e0095410305c014a00c4002c01089040300044810303c14401006e0081c00d0514810700c41b4800009000300c10100580c3e000c2c8203150149407032001440c113030814421524a4401d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 679978615 1250 679977365 679977367
    0xc0316060c022e080f040302031615090602040504060801140615040b031e070c050d1b0203070801020415090b090d02060910020c090109060b03011206090206030f061302040b09090a02 80
    0x18443d080b036104000000b110030400c01510428504004080c1c4c540a030021108150340d50900000075004000d850400d00b03003c5010060881d9400c10846141c014203000041520b0180305405200e49a0014025281d040c0c0d41030004956030f81c0c030030303089030403102c0c0055511449401248051416445040c1900000c02d840e07800c0644410269049500903902903042100c00080f50b09201c1140d03170242d500c1310305070801d40fa4481c0580c403510b40340c40c00300e406007040141c2c0a40440030344c00300036064807401c1e03000b600711000241c40c0d0384001d0003503000d4051a0b251031600096038034858441e60b00c1c1da05951030880b101c0d007006441d0041c1b18002c44440720403030b0300c00030505c40820540c44d00d0602c0144002d280d0b000f001c080c0705d11400d02045074410380080c01240c2c1420700900c4144040c40c203ca04440da6031003d803060401d5424031074024098110b0095014100005201e04d144404d800d40b40240c03000c40d03d25203040c0c0120005004c03445a4441e00001102c05e1280096a161800c112940402408809 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 679979865 1250 679978615 679978639
    0x31404150c0e0f0d080c16080d050f03130201031509050108010608010203070f0e04140c0706051b0a0c05120a080f09070e0411240c01240302090a0f06090c020c0316060c02 75
    0x28200185155081a0202c11910402030308408208074550540c01d03052807803404bc90200b41c05417510008003a4800c074a2107080071021a4400d034004013425095107520302c10700d5114414000601001c0c030918040f907081c0040400c180340180b08072030080d4855107501e21794034130450f000e40303101c0c0c0c0c3c5840e52a031182d46c65021120000e050101e81d441a9104a00b0690340c143e0746c600241101d0015109803045000e101480350b1144000c01201c1035501c0b6414140c5003040300d80707000e030301d03090682d070140304804404282004061b4210003160300400d22800401d0066544050ba15030300c003c4c512490b0041130406001c00c0125000c441c0c3c0000218010308184119000454020560645204000003547c00050003540c5904280701d1540c140081070f9079a121f02c47c8401e8a409640154007000c0c1c812403054000c01d0040e515503004a1880003034403824041c580da20301c0481c000f00000304803100940151140004249004110800000e0982c03407d941c02d14142803080710402d0a40700120781010850b800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 679981115 1250 679979865 679979887
    0x1501050403240203010321020105040c120c170601030c12050709051306060b0d0f0501030807080a120f1d0102030403021c03020c06010b0304060e030a120c031404150c0e0f0d08 77
    0x10b50107580030700b4414510b00c2291f20354030900c02522180e4001c591602051100145c40d0207c8103040361490300e8201c48081440c10504840c0d0300950040b92066810014414542400701c0d229040b0b0f8007400b045401569100f4480c1e01c0401e2990700141740342c00c1218184000422507020a0700210301e03013100c80e60300d6000d035141c8007242c001e604034030041c5001144122114005000d0402500040c800a1000c0d500d16a11310300c42d406001c0004000580c041204021680b08410341e03c90404180f0b0244892008200c400b002059480b0b4a4140000d081c0c03c1d880100005000b01da00903507043d4020f01c00da03030401e2980e45101070009007000805808124400c4800001c1090034040c04108011540d40e0400e172820000300e491034180300940c0c3e0000e03c00c1010554011100b000884c9202101041e10040700000b10020001401d15071601501c079001d1206000701c40c14060b03506070824004102e60156501d0a0303440407980a802c41e0300c5044403803040b546043c50600064010b1050b80e03454102080051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 679982365 1250 679981115 679981117
    0x3080703091106070b04060b0102010207030e280902031b0307170606040506121006020705010f0e04020409060e0402030f071202300604260405040b12010203091515010504032402 78
    0x1045c0d50048a840c1400141319030b901c0f850203011000d0000718603100c01994098085001404003038440c0784c4400c203419450020310382240344e1040070300c5041d0300f89895500610007504282c4842640b90780c501441450364050300c01702c0780610780035203d108008030b40101c80352038200c00500b0640c00c0390301804005500d8803072030082d01c003001c6801410078240c40d200c90717000360006d0640e10a070110360008508210598004c050703003250421071f00d0b0450b4408980e00111b40a8440c941c44215010318103c00050103040100415000728802c40940d052165000c00c1c055403118140101d6002d00c10301c0303020000500e08804485606103403402c1005881003c0d5444015115003083d00c0b03100c03138102404001c20001084141d070000c0d104121f081400c04022904610140030707500450b40143e40c0c41c2c0030b508296603940716205001140c00000d40d03403403910348e00c110780328280c04900031703e041c03510408a103001e400360801c0c010000d0706965444c1410310b1030b00c8804000f0b00a00d074100f00101c4a0307070101d0080308540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 679983615 1250 679982365 679982377
    0xa030f020a153203010b0c010608031306031d031b010e03191106040b01120609050a03090f0e150f28150206070206012303031b070b030403080703091106 67
    0x107203a12001c2c20303003d0f031446000d0340e01e10310b0380710078103100000407600140e0304054078191000c840360107440b104a111840c4c0100380c95000000184800316503071107010ba10341c20550940e860395400f8002d40c000309104800d00a0ba161981a1580040c400b4116120300503100d6965510740f80d0011840c00d9000d599282140d101e000900400b4181100410a66030040d0300080c0340e00440c4001c0c109031a250711036084020041c05800815070905003418107104050708044101a08403003a542104000c2c503001e80b0310352261050009114810500150894004042034450700c51001d0030140306030090304000b014102c40064940c0071003070281d9500c04e00c02d900f000f01080300401c440c00c419a401c052921910348040b19290f82103600200c1008040c0f940818014116490107071620401c0000700d4003441c0120004104070741610003c568015800590746000b80320006c0700c0305403002aa16000017056034441200c1c0070b0041030f140b4000ca00f00364481d9000b1a00301d070041e00c1a1040e0309590001600c50340c084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 679984865 1250 679983615 679983617
    0xd03020c07030803010b130806042f03031216020a030c110103180803010302030c100e10032003010915050102031b01090f0609030809010506030a03050c01060e16090506090a030f020a15 81
    0x41111407c1c5520160712601805003a8001d06032450b1035a200030070f070980d00440e1041c142095140c800324403218454003900d950020240c1c2d0f01ca40c0ca0311010940e41c01c0c210740195619410300c21040217103001040e0b51420a805984d00000103695440e0a0000b16001c000541010341e134125980615100d24040c080c03461142501555952550041502e00340c0208112813203840001c1a0340c007455041700070601c920805442c44021000f80c4841074000313084000000c1c0c0d11881d8020300700b443e1100e06009606981d42c4040401058601030000d545000c01402a40e002d80d2080101c10249515102e02d81c6052305210000300c1c010040d035554144850654604603102600c03000c000c0c1c2019000100c441e40810300b10f00800040ca400c80001c1c3c2c0e00e0440f28001340a00100080360500d4100a412650282420100c05445c0d4208040c4202101001c4040754000440c280d50200d85842c010003250303400000100126400e90951701c40c04d440f15888a4101d9000840100000d105195000105625521 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 679986115 1250 679984865 679984867
    0x2103051602041508070e01140d050f03130807080a0803010509090a0f0b0402040e06060a050d0503040e07050c06070e09220c03140f0105191d1911010c050d03020c07030803010b 77
    0x182c0b81c0082d185c030307850303401031040075911200502881910641c46988003508441c81140039085003429420301d441ca0342c448080d4000062207208a4074895400c9044035000341c119885155100305541d15040247c000804540003000100720310302c2c1c5840e00680009650381500e00c0042596910b1110074a1444200c404112105c10003080d80303003507c0f131600040780d0386018001d546002c0e0000341c801082d40c012584240c400c10010360610804000b03550181c190351201d040c0e141071003e800340c4540c1104103641c015120300760020384c0c0640300b000514108200685030041c00d031590803100003410303855441ca0b8200300642c9004030102e400340c203c060095001d0240515078540501041d41407481140b04160361381e040c00d00740045564442260090de40000c8000507400c1000f481e05402d261001424041d00d10506030203003000c00c06c000043c2e0500d0b102e0140c5558146403e4010b640550102e240682103030020380404007203030301079001000340c4408a0b0a4607000f076125524285540c1083e0090104030740 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 679987365 1250 679986115 679986119
    0x50c071203120c0314010b09030c092a0c06060109030b15010c061a030c010315210c180b0d021f020c0a14030105010803090d1104020f0a0e0a21030516020415 69
    0x344428115000d404002041f40c5026052004642d660f428006014040d030718032800249841c02e1089030060401d14615134000340886400c0102580d00800e20500c10f50040b08049000780d8018004c880450381d014100340002d030303910130803624a1f401101006060041c2c1c0f0384201c00081c5248104c1d541950403481b1f04401090290505142158100080f414149800300c411360820040700d0020480301503d41d462240300c2007144c030341040e06140c180100b030041200340103c3c0a0b19100e4080d28400c241e44010040190404c0800a10306200400650040d100c40b900103030b01e20421002c58001180c034012590350100c44401715032040a160300004442c0200355410100b450203000d664014111103000b035080450160014513110084180200070481d007141c1c2110075201d80d0142c07400c0303990181245858031101c04015000040701c4464920603035441c0c20200d40c410031404da4004480c80744d5640d031032b5001c0c196801c0c0e8070341d17201d405944914201e405c110001030341d850045010701d602d00b00090549034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 679988615 1250 679987365 679987391
    0x10608090c0405010b120c0f0a170903070809010c060603140f0708121c09080d0f18030e0103021b0604030f080906060105090609010c0c2301050c071203120c03 70
    0x41200345010340320b1420070700100500001081a201d04034101c0c08110a29100c003e119211846100c00d002d41101c0081590702040340c2003410020080c084651980c6a44d95840015841c0c0c442d101d0000c042000500030080907511034446035482510444000510b55100c1d01c0d000308981c20025009005d03400014594501241402894010417001e80203081040087c1340d07414140c017880010020700310800405816010f41604440300607a001a9041da44800c00021407005d4440c40c0e0b034041c2d044d0b0518a00c0711407401002444040f032074042e50381c3c2c1180c5a25400441c069800040881a0100c040314103011145007072040f580214829186c0124002c96441c001d40440c8009054000a4100c40704106260b45c0140468041d01022641036540c1c01c0d0100040e00c2a43c5104c10180c18452a50404601807640e20844860203100c20b001c240e18000501c0112000e11505a07610360a0b00040f808100040b0308400400c0c4103446410401e90741c048008468086440039004000080c3d200d08000c070703500e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 679989865 1250 679988615 679988623
    0x30405010e010c05120906190203091f0906030506060403060e010e070608040507031b0e090a200a0e09030712020a020901060e101206210c090605030a08090d0b01060809 74
    0x80c01c0000c00070f09142c03903003611500e6a280c2e40184420000305003d1964528048803401075031020780da8100c04003400000e6a0790000e842c01406001c101d10514100c0020404492000480c0d944110f09541006012809448045c1000b600700001f030001200142d9180118500c6207028400010813102407621185000302d03980c0b0560520045506000c081280864000c003501c3e0406031410001194010b03494041040c0c0e48204249082003040c401c000f280421039890281c01181702c48450a108600b840c0c00300740b0300e541264031840b09102002108544a0404d5011070309105603410510700c0d071036400c0200d040b074802c4030068120844010852401d078482c0381c0903001502c1e111559031660000310b403401010301c888405100c03504116031360200003500400046d01e4140001c036600309042002c1840041d0145088582e04000c10010412042501c100340803224020018031810740309855140792940720142032908000404100c001065058074164020a0a13540d4040e991400e40c00701418 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 679991115 1250 679989865 679989887
    0x9071706151303150f0905030708070f060615020114061e0303040e070503040b010b040b030a0b030f030408070f05031c0f050424080a0903050d0b011205010603020a11011116020103020903060903040501 88
    0x85d41d4603240031840071a600105444460354081c42c0941e64a803581080504a2040b417001450340e41001c17030104030380d002c0740070000440000350000e02c004921811850b0481d04102c40c002d8000804511000e45030310210046240084003074141e91409031200d682d6008408100c9141002c52000014001002007005c0c050b4014003031540303135a06180c04c00300d1440315031001520f0780500603142c3c11503a40d9a0350901101c05149001411280d5882d959a040d507100c045a2080500700e10340300100290740c3c100440d80091514021000d02e80952400b1b000b80e8203100c110444804002d400c0c840411a401c45145000310743d182441500040c400800004183d070380b006005800031418640c40400003070b048025540c6d131110300f60b004540303003848600480380ea40326407400b20a007505000000039400e803d54000c042e2008140d40d4207940b5904202d105090b5041030410204280f0208210010302207100c4807441c035a0720500d030251514618500184c42d00800355083c000303d4000040c01c22096030000c88940b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 679992365 1250 679991115 679991141
    0x130806010e01060e040b0405040b270a03030e07090c020730080912011806060b040b0301140112020d051009140c18030d0c020907170615130315 63
    0x2258144601e401c40c4070780621410342402041c15110005503942c1e001150000000f401c20400c40c681401c04602030300b01031b01e40861001a48100760104040c4520354085a00520b000b048e50040b251740403402800f01c010010fa06025820740425000b84500484550760304a41c02460071608090b003d00030250940c6401c107500749014000c036108030b1018804021280c02c80441d58450f110007001c10086101c044d800078039540b13081c950000900700400010010760080300b04000081d250501c440c01c40c41540184030b56640c09200401822500e002544003641e0180342a004515070760003003038143d0300000c4061851644aa04010181011450306401801010410300c095121041441c10440c0301414200c12103000190380c040143c4174804000700c0c00c10140440740781d2058808024801e503c456402ca00c54051b81c8040b0320254031807031800c0d082c1801080348900300c0d120f4004002d21b10110301c4000e058082c040c000382d24500ca505200304021801030710301d4242d224411410504680103504150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 679993615 1250 679992365 679992373
    0x60a0905031f271103010e10061703090102100905120c0a260a032004080d030b01020318010309030c0212071701060815150a3302280c0b1308 62
    0x702402c0b0041c0010f00c1581100e1495440c0c1e0078500464090b00d40c041e112207040c452400c52003141203565014004480f404175405c03070140740c000b0003540c40344100070380700e40142d0240c5401040105c1c2c55122040c424072440031147e8000c40c40c06429000c0c0c20582483d03001b81c000700c20401c107004010500e2500e21345600d094042c11103560b402c1d0300090190341d02050425035290925a6040c0795220308080d04011242d0031501c03603540c3c4850540e00e000409031540020300703110224560354000400d80350180303002003200010f1a00c5900440c01052030315029805c0240c0c4104540c0940c4503020300408000e844400b5010140c00c1841d0a00d080072035010002581c2c0c54050300300400d201c0030815080165400349407000c135481380e9450006ca41c400250490707000034a0400010b0300c0e400d61050380c2c41d08094101c2d61641c1c501000300e20002030715094111000d40c1041c51074442c2521740b407084c01c0c4600d01e2030101910400c0315480d210116100c640000c5000c1d0340002e141250000cc060582005002c070710010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 679994865 1250 679993615 679993661
    0xc0c030206070f020c06040f03020a080c011e051903020a020c060304080a140c010f0b0a0b09090604050a0f0608160e070909050711031903050112030905060a0905031f 73
    0x2966500c0051a2030100042410300541c03d91080c0801940c800700100351a8503075442c0c009101c1c4000f01840120311681400100141140022650b0501008161034040050b4400484c0c0b806140e207c0038520204001004440b5482e81410b104d1641080700c0d030360050f140d62101c1006031600c20310481844c0710314401e104100008460100300c48aa019518006100000542e84205540030303c80103942c455080c8502e0380718629042d8004081c41c80102c4100007420b03a00c441441d214425242610740005402c00000d03d9824103030000c607003001c00c428000030444485501071701294999008801c0c1ca420004490000c510200b485c0d1014055070714560b110740c01c29080240c0211041e100b02c1c0112030300d80b400070312002e004034106000043d00d101540d584a60304841081001100c0040402191038100049030b0b010820074104001a4144c503400f159a06007020021103800c03a251071810000e00b890042040d0702c00344240c04816040301c0300c440c4d100200c0340240e000d5880c40940901051000940 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 679996115 1250 679994865 679994867
    0x2106010c05030708220303020105071806020c01080c040f08010204030b0c030f1303050d0203070e01031a0a0b1305040c0f1b02090115031b120f1a060f09180a0c0c03 72
    0x45600c49a0300c40707181641c03400050389101800400c1c1c07180c045c003003041c1c4100005040d01074005901c603848a070380307000550440c2190045121810f010b07240060b404400042031550003480d40d150001c071841000c1d400c1981c3c84001e015842c915422040c216500810100204000c00071030940288c4d0184505040d8a00168904120300700208000d11800703030b1040b441c00b4540a04211141240d4201c0255500d203086440649054280312169000078940034030301e160490402510021400021302488034185440011f0480350000301200b464406d050000082d41d94641c8a03581d100f082e2602d51400440b11100702502e1804010394544c01040c0d400e400c0001661740d2078840303056031000c1401c00f0462901c40c00440050000191002d024010420304602c0650010009a6080403a103400d001c1710f0f101000c114151400d050708002070402c0a010703003800e0326100c800313130803134001251681d0b04110515002504d4888800e1815440c4400c081c05d00584840a000b0f5030321845d03540c01c1c00d00380d420181c1d43c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 679997365 1250 679996115 679996117
    0x21201020304031b06060b1b06060f0a0614090604080606090f04050c060304051504031d03120d0902011e030914011e0b0102070509100e0f0c04030206070204020f2106010c0503 77
    0x2c100040e0304100607001042060706d83c444406401c0503e055070700c403140384100b0404d0540d5101001c009205070f8000404902c0c3c00c8500d9244480050300b916a014a8154140d6440c3c0182ca2114024402803144402035111440644014122440101340c242407400c10b100148402800142010100b40200404120b000402100c4440d040d0741e025035039656810a503007841d64210f018011004c1c00c8042c0300c00d143d40084007000c0c4071580511140c0c070100c03d904260351500c10f007051101184087c041050b00056940c0000c118074010b040006c0c16010300501100140a182a403a0100e0341c2c8200480501251544011455100c0d40003048581d206040390300545000321002900c1d02c1e02c131031010509910901170700c2e00500b0050903165040c10602c24080c9010b019010b60701d6900280000255804850f509082c0a401411262889c0030308640a00a0583c000b000590f085602001030003030009131a4010111035416680389500c40c0d480c51010320716440044d2800d410410010003000125070048 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 679998615 1250 679997365 679997387
    0x11060406020a1e0212130314070609090207020d060b0612010b0a03051803031b0d0c02010e0d0203030105010f080424050406060f0b040e04020d120507110406150c03170a0902120102030403 82
    0x8a0681d403102c00903070361351042c0d06d5103400c020400c41200c1c9070100c0e24940094038805a4049407102c2d0b00c0700752100001c4013240540381c0082d602c540c6c1f106044021a002d940041600040070f8480d030300d4500031015901040c132084c2d01c8108408000102001c0c02581482102d401c12403082c0803100c6c9601240a8a82d680000b401d8991200381d118803c03c0440600411100355040c03510051100418950029000f80020001036601c0d01450760b010781658804012207050f104144c5030203c0f80c0034540070440708403800410480c0c03004540302c2d54000040303021440580c40c40400a02154a182c5032030400d05a409561203c95010716030305041c488144000169401c0d104006080c03240ca07511400000c61000d000e0344040c14a51044010403501c07648036009280c481d00403c02c1d1800020080c0500084801901c1110101308540c079450000324071074608411b40c03074020724105031f20903100501e0b51900075059038222085695502c81108600f803007a00e61610b110150300840c1549010b40b030280c4401c081d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 679999865 1250 679998615 679998643
    0xa05040b0309010603021c06051308030403050c0a0f0c080c0909060105010e0301090219031704150c050a14060105040614152203150f02090d020405060111060406020a1e02 75
    0x200000c1c052440941c46080203680086c10513004019a00461710001c21940d400c1d2380850400303000510141d499070320000b60540c07080d622803860f42c580c0c404690030340255030321400c10700506602c000484c0f40320101000700f0303010b40020400c051602ca81c00b46816108985140203005c000704000b8404000710342c2030304548080c20294411817090b4002401040d142d8002980120000c449420302008007c50038142c0384a1001208010300d004111600390069124840001c10031003c2000414410314210401600c20800c0799805207050396207449011081c8010003803a4800c01c010402071502d40105402001c3c050710851821040c000418420954520303811320107100000d0354402c07441d00099526a00c1301032544070000c10380342d1404140c104480050110b000e03060070b6406100620754070807991a100c00404100301901c580c0e09010207810300920742418405070081605192000b0300080b441188103080050f69007409643c0504201105004801c200318919507061a503a00020942a18880 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 680001115 1250 679999865 679999867
    0x80a0917072102060309010c093c12060e010c1b0f080f0c030405010e0a140d1e05240106090608040c0b0c030910080c12060f0409140c01050a05040b 65
    0x40c042d162a0700550b00800207410420000030021407040651218030541007564622004566420b10790720b0b59150007003a0b40c0740c209100039070030401c103807640e0000c1c001c131408000081c07047e03a85808010840031280240d5030240c603001001004502845a139041090740e041000e10001110300d05d1400c9114698014140002d61801d0014400d000084c1c94402c1582074a580da10154441c0b429202e8100344103140c007141031014130b61001d01d40b2064140640d02c6150904510640c00380410494002580d002d6902d020000c0c00300e403100010341c0c1802007060040004040c040d44900c00c200001c2048443d003140c80c0e01243c0103105c02030f4808110422101e040c500030445454509181e4541c501c1640130031080800007441c00440b410100103050700c8881100d109009204407a4196030f92030049501d110511000c1004036100e118401140742c02c1071010b40b60541c0400802c0c08a01214608941a43c0c0d208c6121041d081445040140d01c90080e001e02e845410000360007030140c03090280340250096544 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 680002365 1250 680001115 680001149
    0x60a050619050f060c0624180a18082208030a0503061201020d090c050111070602070b0a030e0105010b19031b200d050417010209130b03070e04080a091707 68
    0x40e400b401e0742c0920011400b1b8411074180364500c1d1000300c04207200c0701c818900301031012a1034680054911580c010450010340b442c0e94001d6080c0c000c00c0a407048503c10603820070460040b0f80c0000160045070f4a1414405a1000040800d06081c40310351101c0718581c410805042078551081c00da80d04564155450900707200c02c41842c1d4068060024607013a5586403440c44d00c01e0203161782a80f07007101c07400e8079803040084038a24038688680b040e000704005030744010001c0141348450340c010040c8070b1203485d0000d401118112004d003940d2080e1321046206402144510003860506050140451142000c20910b50180c0202c00a2403440759000140001da031051041414854070401c5806445400c1d90b4403610700d0030000e032036a0898042c1d000c1c0700811040c2203010782c0051007101c040c0d0381d0007803c4200441d54072030068064400e628038207402d4000c01100046029130320403000e015501c01d03d82c83d519101a808010701c40300c0e10f43d1004581145103002041d031540c0100300c81042d83d150243d0416600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 680003615 1250 680002365 680002369
    0x70b07081c09061b08190f11031b12150409060914063d080a0c0e070f0e0d05011803051e0c07170c040c02060a050619050f 54
    0x1000704030030400c090008140c807045011055000321122841450200005880c210165070018a030b9100c5401140e0703a480460000c0240c08403840c14158004804500740c00030310030b80c3c07042d01c031503110119094801005000305400b50340c04c2c1014030600001c203223040034090180c4040c8100c001e01100d104071110b8240d201030751525040a001c441c0c1103401400100424a80030350040c19400c40500c25000d0740f400308181c944c910b048205000c0301744005010b1000341e032000c0711024910905007a160b5400440000e07001c034050184070005405000d984a5940c070b41080c40e040c40170010516000c10118940b00c000e1a40c001c0c02d04082c440003942e160b2078020700d42c9001401421130403214040c0c9e02384034504004255000008000304030540d01d107404aa08010495580b60064451008054110000c2442054880448290505407150895200540c200d011404950010745000c0041e000305040001414041c0140c540208040e10790246413400c0104c0300105203a88d002d030620640c800c5128010503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 680004865 1250 680003615 680003617
    0x90d08100f140a0503010501050a03080d0209030f0703050609010b011e0c0c140406080607141e0f0301032307090b0d061802031216021c06060e010f05030f070b0708 72
    0x60541111910250364503641240100e902c4202e0345889000415030118a0303060600660341290320142c0080080c60131a61070a1180d040074806640f426401d00c00c0c24000d580c200040188019100042d05189003181011410060024129540c503130508000e4005641d00c1011172074a80750035400a0b8031207040c020f0441d80500030302809020074052040100f0300034440d144103030409100302c5042114070392f0b03258519251041220301c2808141c0d00ca4580c44000b0340c900c02403207111f810300b0302c03400c249101071102000c80d005034180100150000c8014410015443d00702c0050380031220940d20701d1816001e200d80e540f01d00d1f0044007125500c0d8106182e140d02d42424445da215400348082c4402c2c040802c500b1502e00000b4004d0b0320900c5080c01628034503a641084402d581c0010000c41060305258003400450204265034040c0924603d0241d0b0104072107208117806820714041d0f846841d4500140840403c0858008a1080d000b00c2043c440031200011038004a6548800d0b86894000e60300f00440b817 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 680006115 1250 680004865 680004869
    0xc0b04060e0d03020307020d0c151104080109060203060f0301140106050a021501080a020a0f0b090904030c060212100b0f0403110325060f090302030a060b0301020c0f070e0a05090d0810 81
    0x61241088242d00d103034254010714420507503a42196840342c0d1325441241d0440180401610a090801031480c2400e80c58020405021076580100d01e082e0b581c460580c21038103040307401d032115030b1b021003072044600d0034642d003122084040b00244401e203a41d080d19200c03944188034800500500040d40c1000c54024080c1c100b0000c0095010513103980c2d41e200722601c44100c040700300d10581c00c8502c04500c4003106850701c415548003100042c01c10380c4090912508540140040d42408850207041c030018403070b80010f005a501c0c01050519905085043ca50004165080b100040c4020f0040c642141c10000035074048a40081c0b00300044518135021908001c02c805240c40580b5600045005d08071255240c0402c443c610342e110a85407010305400c071607155107400000e5050b0062041003020455a40080b2044500100014075001019404600e404007072421022250406442080942d20501400e41d0148610348144494502004402e83b90100c3c07541c0c610a1018031804036402445030507541340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 680007365 1250 680006115 680006141
    0x2090f220e0c0301050a0509030301172806050a0507140306040b0607050601080c0a05100f2714030d27031b1404090b010504091a0a050f090303070c0b0406 68
    0x211010000c01c03030a481c0c68100b0a610701030341c2800c1c0030800301e050b40e105191299500350302840c00c690a02400e8203d8000c1030212039440c2c426040e403940c0e089c641c0982680c40752011421181c03281502c0c034022042c0c0b1002040c1e00e12240c6400c042201044d00005a5a00040d030b22010507074954905000900810342581c40700c2c0c00071404100701c0204500007400d00d06803010002100d02c01c880300c10402105440034000c5030b03009140c0108159206000d29000c0e1041c00a03824844100d6640c40b00740340384483d610f649107034000320900f030801120044d00810000d40801760050049d1041c030f410050503021b0030302c102252610194034034074222011100d2340300c051035100c5045141d00002184400e03ca5919015140000d0001c000740d50940c5010320411290690010035404c1680c68001008010f02ea000403c0c0d07204103100c04480300e1004950300451103010f150764000342500304010106005407000b4401c80c0b0320791042090000568100300301d0b081980d80240d09500c039541302d1a040c0d0103000720401c601c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 680008615 1250 680007365 680007371
    0x306150f1503130302190203100203191b0e040612110d12021506060703170c040506040f03031407050714010302090603070903030e10091202040219020a1502090f22 72
    0x103e14000020043c00d03004e54202c810f210405181c3c4a040500e03180300951580c40b4800500020805801440d4045032070f1070b01c40d20403500801e00b82e007604c800c0b00c3c8403807800340000310310441b580d00034071340c000610410345040258900740125614001c903030dc000603000c2d40000344821115940c100400d416568071220700030703840e0700051020756109404280c182100075903400080c40c504241e0f0640b0245c0380c25503200b12281c0c000d4040041181d0000e040960381680c108008151610b40c4c6c070041c00142914140c031340daa40e1850030024481844030b00c40b000e60700410005800845e00000b412010384404090604c8a50441401a0000d10511500681240c80402005045500991003a04490080e240d6181d4044480204074414100201280128951300000c1c400c0404e40c0801031030561010304010b00d40300e098040348860b0746881c1c1003040180e0099a0007003c200041100c228491f5440701c0035030030702c1066000600307201d2840c11810301600450540c0c8142c0c54a214803e0010280701c4010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 680009865 1250 680008615 680008621
    0xa020a0b09150c3a02031b010203071d061215120d0909091109010f090b01020706172a070209060906010c021003020c100606020c0306150f1503 63
    0x800c000e421003500d01d40700700d01030b10601e000e0410328001c4405084600d00584080098114024016030082c0024404101c80204980382952400300580b10400581c005607240c016040c0c1c1498032a603d901304405990050052048140e005644071900c0589a8840460310012002240a034011035100d050948062401d202141c0350881e581e641c0c0400c1500c084030114134410300e03103540f80d64060b07000c03000402400d820070084825a0080b0105449000c082a6502c045000200700c10f0b070070b80003495680020301c01040703489098800d102c0307402d4080c0050020140307000300241c840001c00341d505407014441c200080101214102d07200842150701e200f6442035a5900a0794201d0b003141070100c0c081ca10400101e03016260410301c01d4130401050355145a078040942c2441064a849a90071051603028000c600c0b0312a010f01081105c04450100014218500107009103040c4080450310302035040b80080c40308188100c0d8140310b50761803c0d5141100510321201149206d41c420000410b024808014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 680011115 1250 680009865 680009879
    0xc01060f06021506010912031b03030b0102240115050721020c09010b04140d20011b030f05130b03090102092407021c020306072102040b16050a020a 65
    0x24420903240e2aa007190180310445021a4009600350f130101e0109040140400603a0080070000c04103901c40d21707100c030741c01040c0a206591400b00710801c401080d11000c0d080c080d540d0401c04060440301d4600076030322988060004032042c500c1070042803185c240307003030074514802d00407422a0003141e0704c003002c400b46160007541441108504119100140101e9200840519010400e141a41c100d200c003540b801d0300d000c0426a89001503140e81d60020004035012000c02c0402180c1c1c60b403c0300002d046515080054001022103520340c00303040d078801d06d0000c0400032030f91001d403103001c5251703034101340d07503100489414800420141d5101455100c000010080c3c04181034024017280d07802614417089003102070f4800604c009000180441417102030290310003502c1c00d0380c140000b011a854021001450710740100382403160454000e07000c140301e000160b40c45d8040305048102c485401104508103410004074468a100c0c011100c654145ca80f00da0209105080c0030001219030300900c440c8900e0307940c140c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 680012365 1250 680011115 680011139
    0x901141c08191e0e1e15030402040624212306030f03120402270403080f16050c0102120106120f02031603230705280206070f02030c0106 60
    0x40120015408000300302c0800555080c02c0e2550701c0036120715254136030310018000784030101e0448544000e1012251001c944515840304c0c2c40c020060a001d40d21b10b0a8014442614281d82c00481103903980d0004040142101032090005080e519111401880380d0001c0c0c2e2422900e001d080d02903901d450310081d003243c2c10b45c03480708040801034520b0b40d869560404142e241c40c1002e642501580082246041c0c0c4070411364010b50240c030052003c210f0325030018054515001480c0d41e40702802c0c12400740400d0680000d01d403a44081c5100d4085030b0386c0340c100707420405416034200708014808007146e4413549030000e4040e01c0c450003010348800c0e819030b5594001040030300084101e841c014500480b00001c0c0c05d8134000c5911880c2e2114101c0d90001c1d640108500a0003405d0382c012888541d60300b451901c05030703085158041c40495036295180c2e20140384a20f480642c160000b2004ea1121001010094001c114141d0001d880c4c1400e201004135003c05a045100f144040c400075440c0000200d02e05415013 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 680013615 1250 680012365 680012407
    0x140a0b0c1f14010e040c0b0a0507060213081005041101050c010f02071a0c03010b09150c01060906061206080607030e0712080d060806060d110f03061003110901141c08 73
    0x1d50b08540ea03642d80690320541d400076140502452505441031000310300a0f4001c200040581c0340c100d140c01c0c0030f500c0301c004030381184441005130303c0d01c0d4504108600080010410310300180c80c04002b0790400340c0d944e6010000211380581404004034036400300c11800c1d80048110b147c001000d65403a00c0b6441c100d090786d2000561195070032081c0703010604d503000c00001e50741070b14080c04c5020b00e44001c41d020000102d00041150100c2c3c0010081c0b4403400d1420f0080b20010051154085182400e100c03003c0c03c0001c4208a001c991440c21404105c84840000d4617038000c0ea440c00c0009041203601c00107802c104058100c1ca1541510700620800c000c0b0b808024441c1c1760140c4c1040080585030402145c0354141038502c20f510100c0611702c84017003140300003469494000101001c0c504501500401d041076022588c1d2100032681280c2002800015403005040000031505502158102081102800708180805010301c00000d59944d01c04030303051640001c02e402007680d5441d4615007840ca84400c030300b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 680014865 1250 680013615 680013641
    0x21160c171c0b01080c12010501140d0c0e090903160f0c0b070305120604050103050606010e011e020c1203251502030906040201110c060a180e040f0309140a0b0c1f 71
    0x440c000508480e000710035208000000c81031021b690b462305004681c0344001c90548241c04004010550342485e5922812513202c1070340d200c1c6000e0340005020010880c000900c16200368208200e03040008402c054030802c40c50740011100c81d001094185410100000e421102588600240e50000c0c160814054000c0106050071000c03075540d40014003081d40d0017844001c0c006c0d441080800c40b150f0050f40c011940e100185801304c00040c04207400f05214508000700000741e00603035520809030502d03056407007030200d91000652404201d06500400b0131080c1e940c4c1c1d020041d0030700b000c2c010422000034910a40c04c600800355102d043c40b000543e192201994201d0209211420a0080d800081400c81211000500d01410000c2c0c0c00002d440341000c0840e480c81401e00c81c90082580f0020095580c0114003604040d245d0030320030702c0e0203004820640c0192550b1582941030001a0392040084d8003a03c03007800e1a2610f0741d0080a1a0380382c500540302840300852045440356040e80d0f035520014401d010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 680016115 1250 680014865 680014877
    0x6030f1203090f030e0d02271008030901080406020f0706050f0609040b180a061b0f0315140f030d11011a030a030c0c080321160c171c0b01 61
    0x116480940882d450030000600c81d15103401e1000200e4003034162946a035202034070703500e40510302d0303400035128a5208003007036a8081e031003407038400c0d960b1a44800d590000344803804c040c201e030406140700c3d624020600081d041142c440005003c101c9250141c80c4803001c4107000e540c560f46c541c901900035180031100303c8a81c001d586c0c0050700502d4440790850259801c004002080c1c1c6400c0c24000da84910150712901c2d92160002c130030001a424815141c0380d10440010003413420030040010321000c03013101003104260404215440444500304900c04071580c08260301a54129000461040c0300348440d00d60307241c0110145680310340c1d0840c00340100e1003001c0000b00709452100100919000207050704c190550311a010020000f801090000a420b004039a82282c80b0b41d00e00e00b0307510355030080904600030a02d01c90401c2e0004010320705160803c3c0c08132040741041c0b0303031010010961800a0343c050112800c91101500c89080001146c21307401410349591740c40002d11301501e020f0541400341c2400a00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 680017365 1250 680016115 680016143
    0x1b070c0915081b0f030a03120221010305010603050c010801060206060135061c030c1b080307050d02060a0501050603040f030e030f1e010501030222060b070b090d02030a3006030f 78
    0x81d01183c03104074182d0540f038000100000004540003500032020000203c02b140140394108900030102c107008510a02c008285581913151050415240114040c14000142c005001c3d85401062841d4440402c0c45c0501042d8860300510160203070311440d1080c0066540b0050b03001d42c42c000561481101e007959440041d162401d000704001807c00703009400140c1c00120304c030004001ea10148808007114110448240d1124a1241160301c880400c440c6503201c0140c030a8600e40620409030f12034500002004298074040108000d44070045c00140710704200d91b03a000400d03024800807008500041c00300c550644a001e681c594a070408001c0c14054801d043c5203540e070341014011036040c1c1354098468808031140c0c0c2101084185040f00f484550f5840c0c04000c6000000b600c003400d2007030b005442c1a06e00c1d080c00c1c1102420502c080b681281103400c100003803e035058010440201c42c100341564031400000030050540360a4001d0042a1118285080003061000140c1d000c1809805400c5c4c20501c11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 680018615 1250 680017365 680017369
    0x3090c080619051812070308010b070f030f032702090c0a2102040305120912010c14070c030212031207052703030d0e061b070c0915081b0f 61
    0x51007112111a4941044070890010b19070390085030b04080c26450b2182c614124165031801c0c045d810004c20590701d00840c90205140c0d000034018014003102da0100d2801c00240c0300d0b032070107000c41c4034060244440140c00c46521403180e4025010740850711100b002d0080424129030000d8034481040e44691100000b02c0c0c0708004000417500c00392800d40b18031410301d015a0082680401c11500005810350038800000410070502081d84000c0380c11142a60740e00d400802c00c00c41e4448070424801c980e1402e03480c0d54525400010035865401015001611015540743c03104c084141703600b0082d045482d07082c020407043e600101901144140404204180c2e40e2030b1000c641d1405a0502029a45e8014192410180f040107034464001d402400f501e1400808989080a0385c0f041200c4000550025042020240320940d030f2142d4668108582403a11004c1e0f11000090703000760042e045010b46e202c410140c1e03500c000c000724000345103280c10348042c402410005844c001043e00c100d8043d50b81204080c640d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 680019865 1250 680018615 680018623
    0x3030306030a030c0f0c18110a0903031107090608030a0f1106070c110306090f060a06030206180406031b0f05181b09030709050603010b040209030a0609031404030303090c08 76
    0x3650000d0014071150110342c40440e0784440f0758405841d8121419542d10100c0c03045284030001e408203141801207140a0740340102104d0311000030800c01c4000344030300c00c181c582c416064000c681d050710341402c2215a0755a614140501a030041003140d10780f03a8001200070000c030191000844903203a801181500748001d03a0b10400c0320104582c075400120001c0c03205401540f142c1c208071700495a041c280b0103a0400700c2c0c9002c50950380804145c1c00752500300c1c0c090400704843c4e54842500c1800b8003038a440c5501007030302c070300841010800d0329075003c021000d0f645070344c4d1000b40107581104005002109040c034904060049006044500300c1a450100301703820990b2100803020314250b06461a40e40c0c000e40f140b40340900c0c1c8490038455204014940c5a030b501080800003805c0401000101c4e400e01400301405c48041030021800f590050044218503540032503611500358102c00e020401c0d00d0300d4035048403c458031542c0ca095600000c100030080c0741d811750000f03c8842c031500002e4080d0b51107424180e41d07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 680021115 1250 680019865 680019871
    0xe040b031915110a0915170424060b2502180405010c21051305030c0f0105101d09010b09011410020f0303061c050303280b01140f092d030303 62
    0x101d00506402c2000100c146c1071100c0780381e07813443d180701c0806c0c1841e080c80c1b00070820342c0c041d90031041001c20b20440c0c0b41e40312402030115000c140d040080610341504003c07540510380410005955404000302840311391854030040942c020041d00741480394004030302c0c2c1c600d010344041d20150300e080102ca0b1114000d0050b002560010a80c8a14032801c50b09001c001d024010454ac000c0d040c602c01c80c13000548200098541220420050700b030b40d0300402c0c00700e42101c800808603440d800440c0c40c10401e0507001840c00310f2140882c110941c050b40c6409289000d0084440c0d4660461000d80000a0003940b607200240400c10840d001c00c00840114412659203203c209000141e801c2000421103928184c600400c03001a250103101032a0505e48540d030a54104032801413102d1346207011700e54094031048044a41e58410b00b41000540c000300002032a10200d0518002d103c10002103284000d81540140d40da1110000c0c000301078860790f0012280c25038101d0b60510103132422014000c3c0c0030314011082d41d00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 680022365 1250 680021115 680021117
    0x203090705040915050a0c0e0d110108041b03060b011403150909010b0301050f0a111309020a0c0f050a0605072d0c0b07020705010206060108070e040b031915110a 71
    0x14080d42403104110042c84080030499080200d6540c0d410005190f005151240240c401d0003d06000701d0400500300b1030304e4200c110f1040b800ca18542001584d81683d80b00181d0003844c00d0304c4c0310380c4c2e03074608000c42d500c074189450204451a4000820049540c0080124950a0740d41c882e003440b1208840140c0c1c0010780d0025200c0c0b0403a81c0040c000c0c1002c19070300358090204800465003010f0000804d0855600781c5251950b466580c00b040103000b6a4001e100103030b11005ca50910b401c100f071001188500c003600400715255000941101900e2041950030005a04020b4007040c20105141041d85c4880c2d01c3c0c000c60f0003509010005e01c00f01e006030f000c000030710b4541101d01c1100528070807441251441d40d200205000280ca03000c000304113001d10141c03080050f6001013003200c3c10079001914000d00100040e04000c0d5001c104240554003402c1c500c0180419907000c81d407420000001b90401d0f160310240d689400740c440148050059403503030f050741042420810445060008848100c901c9241c1e0a04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 680023615 1250 680022365 680022373
    0xc0e031e070f0e0613021312050c030d080a09022b0b100b1b07090e03032406040905060a0902190e06040e070f0903021009061d1c05070b2209020309 65
    0x313250381019404613001c2c5640140052422070403440075520706c3c0c0c0c6a0048078404503440400b01c20443c003081020010941140201801c91800400800040d0000c00c030003003480d1a15404021500c9410905481500308a08001c1c102e152400c010808031082109030350b82c0461902090380c3c4e030b2600d41c00c0000d8600380c040e00e034030700b1000032110451985c8019080011b4480d1081c00580c0c0040c5114404403122568040c6541b07081080c3d143c8240303414500c4e0100200c1d408113024415640b04002c0313600302c680c240b40118040d43c03404001821501c035507010100080c00014814010b403940c0341d02c200507014540b2410890303100380b0140000c030300550180c41d208981550124141500a0070080103c4c00c1034540918126101c0d408514580f41e042100070200e184600e09128144c0c006481240da1003456403030382c040c400c040b8000398120241f5600710720201c07250350710390302030050034802a00074003c02c04200d942c1c1c5c0030a010280200ca0a0004002c2c0505003c5003c01e0007000d5008607402411440028 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 680024865 1250 680023615 680023621
    0x60302100c17030a0e121206040b210c0a060e1011031603030f0b06120105060a0309050f070510020f030a0f0e121e0d05030a0c0e031e070f0e 62
    0x15168841480000c2c2c42c2c0c10a6102031200c0260711000542c410004607502044100b0050030391440d1030078901031052640c0d0144440c8080301d09056441c4d920400440b004141d402020011030402101d034580c2c00c03007060426542e5101080001401c1883e8401901c40029880d55000100c0d2071014103020654080384464042d190284201c0310f0010140d04401075a00c3d160402d42254407141c40c0400460100e512a1845000c0d40041d00c0703104c03010350f801da41143c81d0070080c196016100070705018184c40380c0000324083c14150303c2984900d034500d501c01c2c1100c06130300e01c032003c9650701d09041c860240b007248600ca111101c1403000c40c080302540501d000450030680010004d60324015600d907104104525a00e40711001e40da40007802080301c0f00c09015048442d07038103005207403031140f00b6694015035028145d01150941d104040f298403259401c4000340780b5140520454031143c50403d15903040c0b0071260404141480483c1d42195812400100d1340d807940c1d5828503c42c1d9800038070030786000305919000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 680026115 1250 680024865 680024867
    0x31926030a02070201090e011514030408090d290103050c040209010f27031a060f10030504170403080c061e06010e030a080a111e031b0c0904060207060f06030210 71
    0x191000502c141012240540c540d10000900e11f000d80c40401c8214900c10b18803000c2d40c10903d15000c550022124a2651510b07841e0103105100e03080740140038046c003441078004e002036002c5141c10f45210407640861b85610724240781003a032080c041510640510040c450361840c0502c01c1305c00389501a140c106001c15800000e580b005a58043d0110404052446010407181c09000d040510b00c115101014458000306004104500900a9004641100c40d04103142e0f60310101c40181207141c0741c00b084c280e440c8c0c0760030b901c6021819001907a04d440840c1c08005c00c04946c026003000d0b0162011118141c0e15000c00000b8104140e000501c60007120300403d40c554031440780400134000103421a12174041700d0384d801d0040d034054110708000419440b840c0c1440d50303042c011a002d00d1080c070442c600858140c14803a80300d114141c1c8000200051424955000b113003400034820200c8020b190001901c0c06060800c003950102e2400c40d05e0926200700c1080011842c460344065039005002000103d58078a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 680027365 1250 680026115 680026117
    0x1f020310030b07110a060903030b0108010b0d0c0c120507030f1d0616150c1701080c06070318180e0a1a090a0b100915140f040209031926030a02 63
    0xc4002d0030415244800c40c046401000851000341c41146e00080210850070000c2c102c403010b400d00c0d03041007490801080300f5020b01c001d03100406118400028903141410054405541484c0010701100105030200140ba81100181445034000c0e1180f040840003128100d440036413159455410000054070f96000341481d130098250001c0c0403003817000c212130503250213400301311000c030448009c0d45441c0b1351803a8980c803035058540f10941d12041031465040ca00000d07114032190407003e02a2401049035418144030346030003000800360046815003552100c5040078225882d4040070849420502170b03110214000808022f600e400c00f204881080944030b03030b02d401100c050301501703640c8200d41e40d40700850f41c64030f02c040c002c00c100c01d58889403078507055064003503907200c1d11100d0030700c601e4400070415001001613006454104847c40080410f2179000100280104004180c1622030070000c0e600e426082d0540d42c4600c0c1c02441c0c58040c006a0201c0b0340d00c0f032400d2314200e8148010174404110040c48a0f0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 680028615 1250 680027365 680027371
    0xf04050712081c0902030c010e06031302060f0715051e280c0507020f01030912110a08181503060102030f0d02070b0f1006020703020a0e07030e0f1f020310030b 70
    0x3034001d51826000d0240d80d140210090110310f00355130b603140701c0000c5182c200302e106040304c02800c00400388107004000800300d020050280e00d40355035040120045543d00c0701100d1241d802d02c1c00d000d4a4840508191942004403030041e0717000c92500c00415030310540f588a1443e0b0f00c0c0c0000307101c0c1c0740360744071060075044e0307843c10000345580c1c031244c03402803404501e50184441d0350259503915500e840050040020016860242074145490604502d002c200950b00c41d071408021824610035030b4074107030500351030420510b0000d01009000306607004100225480d0307012400c0d0842d941c2c030345d800d02c82132420804d101c195001070142c2c0c400c00108010860950182202d00d480c9480141480e180303440c1e034402180203e508041c2065024104140801007101d040050455807005001207421075000c0b96000f0313003500403418202c640b0000501030030301c030703400182d0924000b800751211410302c0c48840c0d40d00d0364000c0100442c540e900100281c07a40843c400c1d04c2c17052019010074200322349192600f8210320005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 680029865 1250 680028615 680028623
    0x30b090a0c0f2313020414040b0a260309100c03111204060c11040c05220602100b12011e0e03090306010515071b0e090606091602210a02060f04050712 66
    0x40c51400001300040e201610043c8008004244400e000c8020042141c000300c0c92940718441c9044184a05003840c50345003040291503d40d840441c5c0840b60342c40c41d40c050034030810381c403490780403416045036442078502e49103610a484910301e456007090303c0d03a140c01c0c1d442c040030300300350b070a12040003090301c0b0f107201440c054018125050502c1e245000b08080e02e2409000f41c0119600145041d6801c25902020080c901c0401d0595000c509110000352560b00c94002c7d1821035859055102c229a15070f941041a400050000c2204225003243da20940410b81840143c076847c046a219a030000403046450952000303014105c581c3c00c04040240d0b29581940d02d0b009800180521310019150303007000c6a030408201c0b8010a22483c0c0702c0e90704103140008000c40c0254003c0024051684c403000c00954110134a1050b0008008501d04101e1500c00e00300d507070b11038840200b000f0443c0703900c404006019040c00e607070903500e00e47d540c030001d05000502034030014056402003604104400d40412721554684c0702d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 680031115 1250 680029865 680029879
    0x926031e060a0f1514070807170c031801020c0d020a051504030512130603020405010c06051b180f0f130c051b1c0e060d090c030b090a0c0f23 62
    0x4590a8902d141c005400900c0c40c5100301304071103212508400e43c41340c50304020205614006c62a078944015005406000b00381d04054108808602c4182c016a000c50320030401300c0e5200d4400d010081c660b035510030b4505000d4002c04904148506041c0d44080b80d00d50080d0004101d54585400d214071700c1d03a00030b443c0c00c41100c00c0c4401b00014070140201c0524034001071480f0b464241c110816080c100c3c031540018141407040004021036600300610403403a50308000002600d964814000800c0c400040000d0440a000208950015000c62140904800680d4100e20000815003445180030401c0c20f180d0340b200c002c0c1440d02e0302c50102c1c0c1040b03940702410321388103080c00321100c07078103181a804102e0001642c2181350080360440700160b650940700170610300318001d4008000407585a101d92a41c002d0350a44070040074003848540300c1580e0041d07900a00d01c41d00c41c68407001c02621100d440400310344400c01b9070400143c0c0c4003450f02030403d035002203080c4518108142d1007000b200040b006c4154100007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 680032365 1250 680031115 680031119
    0x304050a020a030506040b0a0603170304020f090903180d02010e060f0405041503060f060e1f0305030f130e010503060f0601031b0305010f090e07050108190926031e060a 74
    0xe941c01600011442400145040d041907e040380d82002c00800c2c803511203142039010804902103103400402a005180032a40e2502c4034004100d020420350403030380d000403541d001d004104600000070301d2030582d540c00900d10280341000700426407030030844c040c2c0007500c060704110691401e03100520302c030391610150f14501a511000302c0d00f41c48a458860803515035958040042c401c00380540b40d0300260480041000034140241031020b101e0250403495002e49130f091654402ca02c421840d00030355040001c42c0d440b01c0d0700d10454101540aa05220b50100300d079040024582c890074000381c10707180c0040240c041517480b00c0882400e140c00402050400d5252924818440040c42d80d21180a15580c0c01150307940c100941102004100c3d802100400d10305071050012080210b11882620000d2a04a8094456003070717164101081c42d01b8203008a140004101c01c012800104a1100381c10b0041c0569001d003142207401d883c0001c130f59410081d0000841c245140caa102039140c0d00810003844400d401d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 680033615 1250 680032365 680032369
    0x20a05070504230f06180609010e090307210f0f020601140406180b041b0e09090c06030a0f0c09120f061e090203011503050709050601021227041a060304050a02 70
    0x10141c079a0745440034440c090007400e003003410000110101034a506d286ea410070802183e241c00051103801840c4601d24041084c0600600c11200700540091108130f5000414440e011003503002001780010580d00c4a48001c1107008119105140803030f034002c1c0219030310b04600d8111600107004000d6000350784280224901e06d4004104a003c0ea9102001442d8510102404100c0c2c40d44041825003401ea280d002c400c0c1c0358051203401a82400b074501d801c1c1ca07102d0078491440c1c583d6601c002640280c011013044025141e561100840c0440e408041c440660700d44019151320001d80242d841c1c1c10745c18410440820003610002501c0342c402e031000107900c0f0b180341249858442e0580d920540c5502c0d4105a0190316090140e0dd10717050b4005e11105096240d035958075500e030094070900d00300310740310800104103078004d009040d0380d540a00505955480141d01c1031402006208a6189004d1241c4452120742042e00c62002560088071010207150412420440590002001201c0070310a01c2e000300016 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 680034865 1250 680033615 680033681
    0xa02010209100f1106090c1314160201061a041e08010c03061a0903030913060f03030c05010c08061003021c060803070b0c070308070e0f09190606020a05070504 70
    0x2d640d060391103c184400540c0000c101c0f0100341c1c01025036a0140c0b00f4000d00441c0440c061010b6031044920581715030701040400040d00c0c0c0d4424100d9802c0d01c0070200b000d000c0c0c10300d14200c042440f81d40200304054503000e0035a004880745d05490b131081c030700b40000e00210700235040411190503014039003800d00e60343d10121400c2da20590804800281ca4aa04001c04007030480c0d04c540c1c090b00700f000242081c021001180c0c0d81d0140da14014880c205420340e00400000b02c4c3d11604c0900340d1624006121912810f010f4041803400303404403003070b40ca42000001d00c28480c0345011b0248100911070303084802408000c80c065000800000d85d018082e1502035401c03000e61064400908540c17010350344461103420f2001c0c0c0050010301c1d041d1084010040f0000107079020402e103500940a05203602c0003032074140443c20040c0c900c1c54540e007004002041c0300010b503285080131042c020b00d020070b201031030300d40404988455210700b00030401e50040d0070a01c01868540c1018111324050178400c04040f400700b03166118 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 680035971 1106 680034865 680034889
    0x120b0913020f19060305180a0f0204020c101803020c010507030e041a061c150f090f0e0a0605041203110304032001060e01050306060a0b030c0a02010209 67
    0x555121003c440e856000585044070554031958040c005003800d98010300400d800140900300035000254000081340d2240307280940c8000c41e428000603420607550414a401844802e810100f100e101c0c000c82c1b130820b08802e040c2c074896030501a003007a8044221504214040011102198110342e654449440c25a8002020600d1500001000c8103400c000d607848440003810b14107500d10301c050020032501000c4104040c0b0b0010143c01d004100034800d10b1906040207200700300a4005034407000200070002d0000c00c20300309501d100760500604100c105d03000d50742d480520060064503000200a1001801e040007103d52001030848039020041c001002c01605041300e5020022002c41d0f500d942c0a400000c2c0460742d108d17203128130341205c00d0180d0f900904c81d401c0040d10600e08003046d507007100c031021a0103207941c41e41101c440c032561100342400c05540d020042401705032076070404002 = true := by decide +kernel

theorem cover : BRFrame.Cov 679856115 680035971 := by
  have h0 := BRFrame.cov_init 679856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 679856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 679856115 ≤ n) (h2 : n < 680035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
