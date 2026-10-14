-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2113
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:40:44.935618+00:00
-- url     : https://prove2.me/submissions/2ce8ce6c-3877-45a5-8b6c-c4709a0415a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 379856115 ≤ n < 380035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 379857365 1250 379856115 379856119
    0x501060e010f0f021903053a02130f060518010302040b07060b0406030219030501200a08090a0c0b090f120304140103021b010b090702060105010e01050f0c07080f0c030a0c05 76
    0x1041030075840e012170920243c4a14017460340d05140201003003543c0b03c4d0003804107001a9090030303040300980c1c84400795007440300d4541c0303647c080c0c000001070301100d2039000384403014202103c08086030391441541d8200b142c6d80d00c8800401c60200c1c84000482880100005090003480c0c118074140c140001e03e00301e4003074a403028004a9a441202c041e98031540d0000700a5900180824420022440c000d100c05205020803a065420311007444810618061510101d8030110701d541c4c10010145401c48050400400841c85485082081004508049540000b8140031000c2990b20348070300d0103025003100892090382c00b440d0200340c100c5085c1c50100581e8180c0f02c1d030b04880b800b82034442004801074014a03600901c1c19410510803003207124154424140c40ca0700b0b03102206142e890a509a03101c070000d00c2414041038007103000c40301c9588104020003100c1d100a528a0a1400da501082e20302807240d041402540e0100d0403520180c502000a0341507460708a00030b009440456590f0aa106214840c0d1343c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 379858615 1250 379857365 379857377
    0xc03030201150e040f170d0905030903010c020a0209010b03100b0a020a0b01140d110103110f040302030c06070804051512090a031101230a0e030c06151c020f2b060501060e010f 77
    0xc02c032090f06d001c40b00031707035440c407810300c2014001d0508035107a034007042e4428460742c60400300c0410240041102e51565400504010743d9a2030902c10652940c0014103a00030440b403031001040b06002000503045001d1746034010040811289000c540520b01a001003009191a000d520280e80d02d0721400707280755a10038031010005e80d540340140c010f4281c40001118008000c00c201400049020142045a000310119400030103500c05001003446680b80c0540300d02c00410043c05982031034681038040910202c1c45914040100c142d100f0305501c250340200300d54005811f00410316510400c007020f0740e0305a50082045110345c0c10340c40b01c07460510900000060701240003809011050b07001d004040000819240e4905071068080d840f01011941490394800004844c6124100040007004510081c029085054055000c025a20460500455018803142507e42406505400d00300c80d03018802c2c84045498000e15008054400580001d01000312a00004010360782c1f15400741011480d40c2820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 379859865 1250 379858615 379858643
    0xf0c030f06280806190510211a0411040c020a02010311070b160305071706060d1d01020901200604081b03030f071b030203040605090a030c03030201150e040f 69
    0x104030202c482180c9018022800d000040e0082c0003003851841038024420b1004180784102d001c00480307000360744026842600e0002840003000030071002281c101c15006581c08114550380d00303141c1407090b42000f100840b0041c00d210030803810020b10782d01d00340b0403541031103d4000000025500c2c40692000b0b810103407070f4001201c0803000401180c0499401000c0c0c0c01d001d1400c0d0500d164048401015040041c0c034110014503500d10510890490300341142400344a07485210400c81c00d41c201c001184410360b03484018460816000100ba2048041c560001d41c44040400002d800c0c0c0b40381e42042c40304048005003003000d107600800c0d01a8025440111301b0b4940b03d0142c01c50b450103140b40c14034041480700000344010542e500c0c1d2614480d03290740d0384040800206600200d61000c0031200100943c1c0700340b205000041c081d00180c1203010002e000c4c040341507941d46031119244020390098000d80d41d6003001c20421080c42d9115000b9090813050740030a824580d81e414240d8220b8070000e06060505602 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 379861115 1250 379859865 379859899
    0x1b030603081909170106031e050a030e12010f15050f060904090318080742020c06072d0302030a1803020d12020105090c0a090f0b0a0308030f0c030f06 66
    0x484003812404c03856a941e00b40d000845402044640000c0c3d62000b0741d100c4820841c842d0340884a40540d0140140080d0000f56800340d03245411295010f600500c00c00111503070880920071a003031b60342d10940205040301c036440e0100300e4a032180c101c17a015080d0f010084540340c8940e02142c42c000c50070743d4006040e0b4503d060468210611100080008034419400a60090006000c000b40c8502180785205841d010b0340540d00e943c103e08a010480d04040401c1041d040021200100e00003240147c2d03081200607000502507070721030141180c6420410041807a40703d030381c00c0990840480402000f865000d01e40703019540c0e02411051508221400040003100038046401200840d800303000007803848103900d00080c3c07007070340c00050034015864100000c2c004400090f929101400c0a0454642701313042468103405001000d8040e0480c68841049a60315140c00903040c00840c00f550880c6d4030781c181880b010703030220009050500724203410320070301c280040300c07108068104204641c2c01e202d0b1034802032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 379862365 1250 379861115 379861127
    0x20a030b040602160501020d0c030905060a0b010504120503030906010803131503060f03050303090d09050f06070c030b01061806051312051509030c0f010c050a11120304061b0306030819 81
    0x180d820031300c0e0b840c00d00c2030200a015000740c10160041c00050203403c03242c80040b412940c07000302c081c1c51782e840040401c0c85425a81c0c414800c540040c0f50551506442d18041e00140d03058071022149603100104115030400144071a502608501000d90300d0f044800786880d8045005024440b00e80081081034000030b40240c0c4440c005280c403d81d04254560349051194407038204903a192828002c154815903038a21136015001a0b52000340340b100c2800c10b400910242d9000144e040314001d0b00300c0c0c404000708111219850003400c00da0380780e0a41080d801c14000c2007414a0b441f0005200d01808900d1000c3c0003008010140c8000c1c0c2542a1540354904016141c510300d00700164051b48440144140c0010110042002d442560216a080383c10f0030901401c0395610301420000075400e01c00880854861600101a00102c07011600744040d00d000801095100340d0b012281a50359862074440716800c4842035050a5103818204009403651700d444800344160844104541c403203540400703109004036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 379863615 1250 379862365 379862377
    0xc1506050d0807110d021003090201110a0c080f0313140409060c05180603100504020a021c17070513171006030c03020a2102011808030c061005010309020a030b040602 73
    0x1400320705550070034100030403150f00070401992030003d030200702019410203104e0640100e0340034103d09042e0400310320444c002d16040d40c04034104041100090704a400070071403602d200340101c8000c030500f890500c60701e2402d5001c2c40f0840c070540041c09050b40203080300b05900111010096402c0480c9511070004001f4201d40c840200303441c2c03070640200901a40200039008980c03036802c05038510801c420030440107000464190417107d68100c024000382c1400d0b005441d03003c6441c01100d0707200c0c0c00c40310980f0308810070003181c80002c0c0d404054a61402400042c10390008102d040480c900701045112601040c400e02441c500009403d0703003c421801c007040700c104620220f032410450f40c0d8591819500c105c00c9172006a01c503030791110002c5a5420940710a01e44010317168080c04590350740e54019541c03640c03c42591a9201600c2d24001034504040c0000d18041038881e000e0030452521604200700c250f0983c001c0350405103010301d0840145c490046400a89410101c2030407596651315186010344528 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 379864865 1250 379863615 379863619
    0xc0201050405120115060207050f1512090a05010b040203090d0e150a020c0f01020715110a0c06030f051b040605030411030a0c0608070c080409180206181f0c150605 72
    0x12001d404800b100651184c0c05ca66007500d590f1900c2543c40e00e04076030750b5215005880d400080c16900210f545000d1460b080301e030154a0204d81400c194030409040c1110482c1c1810060308030003101001c1100070321411500c1e9504039811411030500b810070030b41c1c075100004c500381070106c40c40307803068196600076200240d000e100d48125953301036904000d490f4101300c0115030040c142c01e54003480d80e600103c0c0040030740d92076601c50000180321050854586a00210700e00c2c4500406804102051000c0940000340800b510b0124007451074020701411107a008040c00140002c04006030401e681100c0dc13602202c006103032403512511a82084014100c0050060b40d052050007001000c12100ea00090100c0310140c903201010b41d0303040e0054a4808041c1070081c15280104014854004a90320501d4a40440521012002e80d60307400324001c0e44c03180ca500104001c1e10090b258042c5040c00c80e66421141241d030b03014100301e0000c80030340009030195004010300c4c862482028140001c0c0d00000081c000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 379866115 1250 379864865 379864879
    0x902070c0b1e0417160308090105071401181a1b090303130602070608010e0709030305162f0a0e220b190e0303060a0501180308130608060d050d0c0201050405 69
    0x514420381910704120000c00c0780305d000d51002005101850202101142c2d0800c648925164412004640315400040101da01c88207a03446000b00c04002d2003503040000d80c0c4a170101401341c450500d44c80181408500d54100400c032801c01002262075050740c029250b980d07950b02d44a94901d0000f80c218002c214606125050750b11000401e25400502030088031036607150100680d807070716188150708600701d4465001c9040450100b000034425401420340c00c100b10081c130031010003566049110f02010385a5041181c440f1a004844a1240c00c50b640302c5600b250400800d40c0782036011014950020801030381410140130110f4803a5003952580119507020480001d1454421b00001704035104104681c40306141c07440c1401c200f0400022203018200007420303070755550314007001140c02d03041855520550010342540080000c800d01c01410005024a1078219502c0c1040320081200e01c0c0240300c507101c0d400b65070301a004550007241d40304241c480c40c0b4040400903014001a121403103a5403000741c000791 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 379867365 1250 379866115 379866119
    0x60c090305012f03041e03210516020a030c1e0203100507020c0a180e03090a080a0611030c03130519030e010e030d050406052a0601030302070902070c0b1e04 69
    0x2401c1038030583c1480404110a18400003c10404070070f020842e802010b00d064100003009542806488000043c42403070031031450070300c40252061040c2100c039180c40c280d443d1400d2004001d40b000d003011900760684000c3c20719550b40c0d01d0040c0304044072034000d0640e5401c04503038072a82820701ea08040f0740b074002e0110340700560f21040103001030408a0703021006020b05280702c8100d10f01a4444421101041540075000c21340585000003400d421619141a03c410003600344c9603152580010000c104890240a14040600b850303800e0711103040703460030407240c104200008915010281c98125071250781074107000740c0d02d1900501d4204107945084212340c0f1000341c0c2c0105607005000c1d0300800c070700381d03105144c4244030000d00d030f07880320b540b8480e1001c500180018041c8501c6a0050840d0000f2040c44d02c009803100d100c0d014541000c3e6aa02c0a5508800014000d05404021440040616402c01c514240b01d075220750280c24154010100140e0002481040042c44408a000f0f100302680100c0d0b586c0d5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 379868615 1250 379867365 379867391
    0x21e0c010c05070e0108100b03010606200a020301051f090605060417100501171e1b010306031502032710050402040b1e0f09060603040b060a032f1c060c09030501 71
    0xe500b00a00300441c500b00b0103085041c9c14180502422142c60303444d00080856580030140307840310007105262081c41343c0030b901000b41c3c0d803d002d110701410010300c0030200082c5017500c200c0d03081503540103e080d850500030100040e40302d401c210b0741203c0302d01408000510405c2502410452400702c2c401140d803e0000224034442c1407083d00344884031680455000310f1151022034a18045011407600c140c000d5541410060700c03200e45184100d405140004d55107031641d5540b104000038003140310340c99038048104401015002100391411410344041c001d0b283c01028850794030685400400b040e035848001140854032241c11035100b1795001880641494126401e0b01c02d0b0461841c03400f8802e00001500800504155034603034080c40c4003405051440c1d44a0b1200141402c1c054026038010003540c500001040070301c2c01140c562119444912840c400880441c11002415a5228801e04001c01c21000310044017400c4005540d2082000c1042c408003001030700d07580e009a00c007601c2942451000303c81d01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 379869865 1250 379868615 379868623
    0x4210b1b07060c0f1b11041508010e0604030e030703050606060f0903030304061a04020901170c070b04120305070f1e02120c01050f0a05061302071b1401021e0c010c05070e0108 77
    0x1d01a9202403175406190301101907958a8040900640b01c00d81711440c41e400d00e5040b92400c0601c8052241240d80d50742c41c41400c484c800011340c07005400280901c400c03d6844003001c0f0000d20228010490b60b030942e102c4684480c1d001c0d0400c0d200f00d00000d0340800c3c3c01d02c05003d1350300d0104001d041d0f07a141d151504103180070b4018200c8000b180c03216040c84584901d001c0c4203036192200107a44490702403440c007040401c070104c0502808a812418402c000001d804401c0c0541305901c113144020060240403030181c203488000e44004103014244503407510345070b070110701030280340840e00ca1130010508090050b400c0810b4074462080c084000214100d641c1015041079008031220781c001c108503559440d60504450040d2030b4203611281d40710200c88800000d070044c01c0c645004158101100b242441c500496990640c40040c06080c2c981c5032440544c3c041c841c0c10100305564101c03040e035881e2180103e45620601c3e0809050080b40c41882061003010025800903050b51080c00e1102e503103481c80e00d507a03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 379871115 1250 379869865 379869887
    0x60b030f0621060f010905091009060f06230a05060d0518060c04060e1e10050f0409050403020118020619050d020a050309160e040b04110a030804210b1b07060c 70
    0x5004e41c22800000c0c403000c6480f4031031050390b60b0300c0582140b403c9944814060980000305a0f06c00e6109e004941c801c00d05032288000501140711801040304600e45019298840c0c1340340280311714205a400c002584a14049801c1495204000100d603590094901c1d850803203c18010034a00c140700030003500142500081080d50299101e00d8417900d404030800410307141401c4081c40445c00c80f050f4205909108000b8103c40500303041640c1421036404c119580c41e000343c0d1003c069940c4440030707c414160203100b0700e814219044095038002d0269004251a0f00c00c1c00c109900710440950000d201c98491810780c2c40d0300c0c401c0341003507664001d520f100801541040e22840e01030302070a410390000a0319543c1040481e00b43c1d10207016541c0e2140c0b03600500c0d03040208150b80d17040c08149440031399540d9a000034099441042030383c0c1c50764100000d801030f1100400c2c07001d48907074180c50468041503416540030f43c08940c802011980c0c1c0702050b010700301070141003401490642881c840c02d600d00c1e04201c8a0714 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 379872365 1250 379871115 379871131
    0x604170f1b2a03030d2a0c02040516080c0c030c15040b0705030103171c0c02010c02010c0e1305060103090203061003020f0409080913150324060b030f062106 69
    0x1014a050b401481200404419549079004000091a10760103400c48040c080c0e0705144c050300d000d41110003100154480103080000303140047c560f011450a4484c0c20b030001c50b0f0280304050220f90f10f0000d0103684001d004035514080c04942e00b92814003c0003200c0703403103407000c042d10140038400100f402d08030400d96044413520386020004d40c14611420540303040740c0e0041c10401c902c004c20000c500da1030f807102c0c40000e40707140d008a4030321803152180512800811254000079081520b440020708407450003c1d408100100d40986080356034030071505441020780c2e040001007a03140c2000590080816940094141c000c410400001501d00e52000c4100d034000d03241001d200315581c040004540082000602901c7d0920807420241012102c1c01101540d9800c0040c2021035042003010000c110f5000711491486004907800c41640c20501590144d043ea0060054038140310145906000081614454100c01800120b140d5a40c3e100b54000c01c0c0100d444c0101d1030340c2054410f4a621085036440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 379873615 1250 379872365 379872403
    0x319031b0206070f030b031507120f02090102100e03070b0c13061803060507090b0c011a0406030206040501050310031a0105012030040801020c0706020604170f1b 71
    0xc41203a00108219100300442c2d5074a903250840c109058000345400d03400c9a8240c0f060000643c1d040d240400118041c80c03442e00c4549087c0c03055450038054562448807859510b0041c0b00140c103c1e40c0016480c01d01c280b07014030220380c42440c40340441c918003c140d80175005040850502100f4202007000b0202d002a07085004601074032500c1c2030710095085001d00c00c110107141c00400101d001a0310860f085401d52030041c03840c1d946c0710806012900201d00700c0485954441c03034102c6514015201d400e07101b1095506102452a640014105006a00c505414003500100280c43c28482c882c460020b59030090812003101c21405880701c1020302402104e01040355003001204003000c80008003134040c0c20300c0040904c7e64140d8001d08503041c0c2e8007525070f0203001f02010a01c000306142d02401c007400c002800140c0754040701c51038a1510340198002d4041d508007506000201d41d07000d940303520341d50f09405810b03074410511604000b40c0c0b060b10040840070091808031b103d003080200e03411040d0300300c0c50300ca4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 379874865 1250 379873615 379873661
    0x40c180506060706092f040b121002090a08100219051c0b010e03060a0b0a1707090b131802040633021c020c011202040b030a0e031903 59
    0x201040354415106a90301ca00309011000014080f070304209000c5119100442054041004c090303004882c0540040142e00450343c03071186803c251281c4034070034000f29600c036885407440d2401600c0d8110580c5003050b160b00024600d43d5511805881c0b001005502c0c101d604051565000708003d410482d20b4080540b403205034815214854810f81e0043c09402141112013203490b001c4400038180c50325118140104981141d8040e542403161a10a044408003c0b0710307a00c03490100300e040c94054001004013621251051070821000a0601c141d9200c10300000300540c9107030024226003554602c4103115820301c0301200340759038600c414818462007a87c0c24420281c841f1058000e00d60744600302c500e00c0c144004c0c00074218241c50122182d03452a401641c080400c00e4000201c03a00c01c00482001507800708090302e081d540d11403064002031074444000c504060a002c61010300d80b2000d05603c1010707440b124a00c18061047c012034031426451a01450b00d5007079124081d0140000e10341c01108283c4424103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 379876115 1250 379874865 379874909
    0xa0201140604020c1f15030b1b0a05160302210a020705030f0a060911060f1908100506090a0b03090703060f02040807030f06020c0a060b040509013c05040c 68
    0x280e81104c100360002c0c0c030b6504000110035448003003800401100e580c403103040c444100e043d0000e410140d80a40994030191030131466030514122280c00204c082c000421401c42c0c6958000d0075543d407040c00c4c0141004031841c030305040b4501443c1c6038010002071000d040b00e0004030b0742000104140d40741d40d001d039803c141d40c072000c054a810400140352403940202c02c2c40300c00151664049003100348114100c001c441840f0b030201d0026004000c44400d20200081d002e00d6505414141c80001c00c01807601b0030b02850800c00616040d141445500c0c0500740c085000c01182d07880c20401ca0142c43d10b00301d04c0e912464010001d641d611010710003a102c1c1482c003810001c044085000315415202c2c904000d1100518640d1a060920525001a99502e6081c0901300d4440d50074020050580c3c042d100118080800108210449502921500d1141c1c90242e0030060168401003202030f81c4524001c1c0040d00e01840ca05e400c1c407502c050301c83c1c09201c1c501400c0204001ca2908a0402c0c0c4601541c03001c0f0420b42208 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 379877365 1250 379876115 379876117
    0x51905030d020a050304151107030b01030317060312031e07030b120102040305120f27010908150604050c04050901030b1b0310212003060903210711030a020114060402 73
    0x6005081ea800400c81801081e12244403c1f6002105180061720048041c2350300d814402203402c04c42d1011000340040091541c462600d00301014800d00c003400d2820040002030380ca220440c0040c0c8040404000183c2824108081c00282020710310344c2112454080300c0240284405080c2c107110f10000424035042c5101442641c00782d981c0800100000c90250f11459125005001c086841c41c608001c044d22804441c01900c2060560044048074540310f54005000e85610b43c03c0764410f40c1c0081804070b4034583e00981d071504040169400030309903c45c1520181144035582081d5040010301c0d000100b084030078a002e9201d40d03070585500e41408003104e081c80c0c9501c41607408030400c403c01101030111068046012140920300703291001e810b12240c0e50140c180d006a0103030b11002c0c129a80c607004d00e040510885500001c0140514940041044a1071540b0034100c031a00071520020700260300c40e401740480c00d610822078001c0320b1302c9550300e06009018021190300384c01c44e45040d05c00300e141c07030400380 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 379878615 1250 379877365 379877383
    0xa0e0a080301050f0a050607060f0507030212070807110f10050c090312090301060306050c070c240302071401060e040303060f1d0712020d02091e0109050d0c051905030d02 75
    0x214018a1a4680341c2004030142c10240d00e40d81c49105071700300151a90360840281890b611942011a90405030300c211001c8400c014242000d142c0100f050700c4a44100b228000e51240250510105648034240c0172100340309501e00310302c0d2600c1040804416488001410402e0b045442c0d002d100c581e5400c940b40600c0d0107170400150700740d800018504a071409030380c0605246d1002400002d0a65507a4661100b55641664400303203000340098035406010305102520041c10100c00c60f120006800c42c02c0d07030a85803485040504042e40031600404024100485020403880740c0000c1c40010340b100c402c2800d010041c4c4085011034a00340300011185e00c0380360200c080b40c42132220044022040340c80810410001400c01081005205040c00c100600b480a010200c0d20000300513203804c40d04d81403100000309045002c0da141c090006000d2140c0e03004c040b140030b030741040d1466080d100c003914017003040c07441a401c124ac0c00002210441c01042511401c1400c69070110112021401103040980c6c0300c0040e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 379879865 1250 379878615 379878623
    0x90f0f0f0f08030306010c030c06062402012d06050310150e01050102061303020a0b0414070602151302130603060b0f0105070b0a0b030a02060f070302010516020703200d0b0a0e0a 78
    0x510020303c83c1d6001f04152181d0034001c2c205801b6260380d60f81c940c07044a0366500b0051a614402d00b00f401d50300700380c0c100d0707011124090008100300c180c5194800030071250044000d002d001c503d140280c0541e40c0b500034100604000e0102d504841c5030b40628030140103d5249261201034010000071600700700c4081c00d040300e406030080c201c070b9152880c80c505921940b810540039489401503c200060500c4102c03441680075018480b514404c022056042c12044d501c0842103500c40c240c1491075401807003000c4d800c102d20000c0c41c8180003591004c250410f480103845c003200c0c0c1c035100000080c40444e400c4041000000c8507800c01001c51800190b0f85030240301c10241440480307c000511820559110390400400101154000399450b40090300e15804030766042501d44000c61000100368090080d00c0d080358010040c00c0b80d0018a1a00a598035220302c4003910703030101185492100f4407200d00720099140040c0618100200a04050800b0350003502d5503080b5a24010000443c40000300e8856161548 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 379881115 1250 379879865 379879867
    0x6040510180203040807051f0509070e060f030703050f0c01030f060605070b0a02040f080a05060703060602250e1e011e09021c02030f160f0915090f0f0f0f0803 70
    0x1055072840003d40000b001181d00310130412090010507810001c0f6045900b28540c2c0b2820342c116a80da241c01e440d405484001d6540c40a04148808000061565030007942038035115040102031000038500242584042c0582c0140b052031000c0324000b29140e081541c003a2024030441c2c01010b54081180d1117841250001802480300c0e000180700c4c401d4181e08811001c0c0007505040c1ca4003810341c491300307143d4800f0f03a02e58844900301003001414081c607035001d4158101041014a0500040c0d282d004048035905412920400450b211340000020741c0640f20070044c40030545094004e11803191040e134442e00c4820408400054017446001e0402607181e42903005680103840c2032031282c003a4124070004032108042052003a5601c6461025511540c440c2141c0c140e1400c1400c21245c00d511620001001c00850300310490b80550031443d81d40481d00840300701241e003101e0300e0f0101c485c0c06503034107c0f070140c030380c2d450b8001070020716080101c09540c0342a1500400c43d0351000340801941c40c6109030003903130704 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 379882365 1250 379881115 379881149
    0x20f070602030f04150c060f020405042405060703020102070f0f05011515030b040b1804020901060c0308060618030a0b1b2d0f0c0318011805100e04021206040510 71
    0x300c039240c0040f01c0d000d01c6c00c0080750341c80e40e542e41c102602d40c142451920164082001c12240c0390502491a80030441108800400046000007241e000607001c0e542c0181c0b000181c06003018800d40c112812650464218418408139103002c43c1c42c21000381080e110b6600f4640c0c0c00345d01c20744002800040b581c002c4034807200c2036500b40c8264040e00d00b4a10040d8890b42d00c50318894161140b02005031204070341d03403010b1400d03d40b5204104158106070012420821045039030340009400c40c1085070415011964541c6640c45030060714142c040d40c696503a01802000301e200100090b00e00d103a07001e500c1040907a944401244801c032070500584110042460070703254424041c046007200706104030350114846141420484510209034401c512400715941f0014580803c092044c00401000d5400d1034080e21a85244d0005c5071221f655000d4503120b402402145c0707507400d0080f17180c190800805403080d9152002242c0140f000720044034070a000d503050100003000c840488083c08240e448140030000c10704 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 379883615 1250 379882365 379882379
    0x61406100807021f0203011d040503030402061c021902071208030103060203040c081c17190e010e1b040606050901171f0806040213020c190501021306020f070602030f04 74
    0x780000d0b00384030650040a80c020b42e1540c121a0a0070b2644100b400075075070f54034011540c0030003208803403030310107424002c03040c00001400407040300d40098040b120a40c40301d0b4801c4035105241038429010303841c02d1001038058800803481d4400300100e10541c081c2c03051117035100f4070303280c4001a00a006000c60070401c0107000182640d400b540c3c01a02940a043c02291903403041031811100f00420203803d00603244410407507522640604130000d400c01e059030311b801c00c00101d10103541205100d43c50b0300d03129600c000c044402503100014a40703100c0111425214140c1c0d40809a000302c0ca50b00d03000d0b0782410004541503005008488038030006a4601010b110300c191459007110010b0309984580d2402c448011012080031048805080c0c41400b4100a0030103104110400c0016141c3c3d03400a801072051185001000c51482026020004140b800e50443d19143d0300920501800c003861558000300492200e0b80021038120161941003214410f548403101a60b5030701a8941400208a041006010007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 379884865 1250 379883615 379883627
    0xc06030405030c01050903031008011a04020702040b060d0f0518030f031e0a0e010b22020c16351c120606052709040f1505010305070306140610 63
    0x31034000c4040d00d00b0240103803990390079030700140d60403800c9504c04400e12400340244241003004144040080005014892074071007100d43d5407051500c123503408500fa00564a440d004402a80001081d8558510b0702450801c01000bc2c00c1e80d03c0c0040b0324140004808a141a92001c0c1c0c1d09200001141485440000318000b81d10013848032807986116140b586124001c030000501440307100b500403c4042003080d40b18211151241a00d201d80945d000880c0d58080c00302c1a15a000c001780c00141c1c0c2c0320301c040c040d01c0c5441d20034003480600e445800301c0001c1e001c8660480340354840700c800c0e040e11141401c01c2c40c56244c3c407030f144454402c0c1d007001c06808042c80042141000c02036031400c00744018802c551014007160728560060001c940700040e1003080a41612100b2002541000c0b50020810a40081500d04000520081550500d1031005090050700d2810084000c8075041c140040c1d030b180d01d0055140e107507034070040300c610b410041c1001c0343e040010a0b1520600018106030340b0240202c00482e46 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 379886115 1250 379884865 379884871
    0x90b0306010b0f040902030f0a0516090e070302040e0901090314040b0f090406050301020304031106060a0e2a0703020c030105010e06101d04091b090504030f0c1703041101090f080c0603 81
    0x70101c0c0130032001451041900245100e502943e00507221490300308682d5003903420003442000c46013074140959110a0b007003c4d4a0058500c00358403038515503242d00307040d4024030464000c40f0a5600d004108a514081500500c02061195031102131b41c4c0407403105980f06004d24040c08030030050a0000d114241050000780c00190b60040c000b244d40341e655404a0300720707441130740c0070b500060134a4000c10100c1010403010340c10040a462100d4001d151a1203400030300805040c8440d0610020441c090b420b60b041d4112842a64070b80503595101c03110b00e800382d600c4503d0041180294241400003418000b202c00700f900c20b45020b41040c418600b08041100e010fa40105030061141c00b160130141182c03201d105910300f003840351a0703020921a0a21503121011107075441690518109010040020780c828101c034880340c00d03401c01c5041c1d103100b490f00b13900300306d696802c03a404c2450200030841032001c2c88a98a440000a0300d800b0034482d1107004291612700706000c0c8407580c2e884918581c50600340b420040d68 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 379887365 1250 379886115 379886137
    0x5240106140d0203011403010b010f1407020a1517090a23071a090f040207020612040c080d030c030e0c0105030105130213030b071b0b0c0a0c1a010609090b0306010b 72
    0x1142c51564540c0400304c0e00f0a0700320ba01c58407140c8a5820840c1024456440035800900f014540000a010010424441daa5000d40101d0002c10f0351411901d41980601c05000b034690825516020464000c4c034405071a60011108002d48021603403080000c60269440d0b60040c0000f103000f0f2001c0042c1c544810f0b034141203002c0d03200340b000c0000c221540750402419424080005955010000f00b041900d0008006442c490f61040001d0300060f60b4030411640000d640da110030b4480c1e901c904013000c02d000c10340e101c0d100c03900070b800540701c10350750540c4540c0710660162420002c1601c00c0a0081c1d44504821881d408543c042005209918051041a131080f9031000007502d449150b20b4414080c020b958000c07035162040b6800d0201080d003001020300c0050042492f0a03001c0403944452024180c0070307044603590440040d0092040f0312070b075920114143c1014050807640c0c014420648c044d4024410100090441c0c0c20200394100b02e4010b02e08141c000400400c616403c1c84101003143c2d1000c0c260310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 379888615 1250 379887365 379887367
    0x6061e02150109020910020303010f0e0c070501090f020405011202130203131514060d050606040218040903020f06060a03110910030f0b0411060901120519180524010614 74
    0x9070014100c400c8540681281000580c03180141024440c44030016682d40003503400520050021260059130001219800c4014250079119214035101d9031003001c4e0041c1540d400c01450074148028a41c00803901c6200f80c40800040e80d80c0c150780340d0000c1c840314000350b00580002ba2001000303900d0700910741011400321107088a4084e982c0e060135045a44058101c0c0035111000c0e5910860805d108650180007a2213400490110f50f80c1d2035200e0754000c2a440c4160b50124a0b00101c4c50003503141104600d02401c00c000c44401d5080207942c980302c1d469807810134030400d8002901800c00e41d81003003c070380e8810400c40e1035560a03070400001075402003042001107228030001011501080461000364080e030390780300441c1003d0408602a10301004107600804041100e00700590f405140c070745984007445800282c4d6220040c080038420385500104d2801e07801e05001c0850360400700100c8144a1080c0300701c82043d40c01100215407241d020040c0c10303c0020f001c00402095000c0c41013010250000320501d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 379889865 1250 379888615 379888633
    0x20721030b030f150108072405041802030f0c0a0203180f060a0906090503010204030209040b0a09050d0314150a03080307030908030a05070219020616050705130509060a06061e02 78
    0x824030340742010f100ba0016a2043d205030800c0c0c554800020301400c4030401a10100d8248280102c42c824607045c4c20750341e00c9880a1a290f002d2041d4140c1d0301030000206407541c11807020044001941003511020700c0500c400000c10340e1444080d084500310030f0260081d42c2030400001c0404c1280c0341c000d8440d504450381207400442c07070b071b00c803002000c080307249884111499040c904000c002c9002c030341103140242e04c108400d01c0565500c8003115449075204040e01495600c0603180d074094807010b140242144507a00950303600781d0301078122107a88103501a00c148540d48186403803802c2c22601c52001d800c4014a20140045640f0340010340d48a081401c0101d500e00c169902c0182542c0102d8140e4011580c5d24103100c441503040c0301e8114504a10b094403030000100d90006181031080740020100c1c5020340b100401046000d2000e0001000e00070310100c000903000d00000007600381150019024003e810010392001690f03c200400d640c803a64074154034401c400d10141c50509100000341c00c2d48030740000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 379891115 1250 379889865 379889869
    0x2040b04053118140d020f06060108180309100306090f020301051507050a150519020a0e0609040b060403051513030203160206090301090f020a091e090311120913020721030b 76
    0x202d8071039004c03000c00401c1c508018203002810802180c1e00c1c410990030441c148041a03a00c100d140e50010101c111111103188021016841d43c8038000c1d04a402c8401412030ba041203070158081c800b1079207100010b1281041484010080784024000e1603030090002e25001c0c41040d1801c040d14481d48a08126154003038903445070860482e62170070710310103030741ca0300200b10301840c000012582500820748254245004100080c01c5402c203140e00300d0190601050b5201d25540795040ba40d02040040c003426a81ca49906003a61200c0039014000d280706052030104c0c3c00320607d50510744c0d0040d01540910708240f900d182c0700302c50404020007640e100782c051089018540d0b0a22072564494801c18a044a5000910600c00440d01c140d0001c0240380c508824094a040340703406102007240c9140b00000c05e441c8034030741034603040d4200f81d60141c0d500c0349066100c00b0b045c0e060014404e0b508100c40000300711101d4444002648a8401c000b0320000d82c445a40c0403200b2420081c0402c00c25034240030681c0294680 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 379892365 1250 379891115 379891133
    0x51906060f120302250902040321090302030607030b0144100b0906130605030403020f1f0902031c03020706050f060904020112060902040b04053118 65
    0x140984185030358038400c0000c0006a05000000d000c03914800d0304944207500d01a4445801d811040159883c661100c52039128220300807000e0300c0d048200719210f41c2c0300c2c00c5c05102c021050290030a0300315800c8003845d003180140340403821280e00400528059079204400c5024040304040181844040c0018441e40c0041003003400480340c100c07803485581d00d40c2d501c9518000c4c0c0c0800410010070b034004188200390107128107078400d507030010b50307030075a500e40d4480802e180d840740e600c4010440c60090300c007059499100000358041c034065400c039055049003074056919024580314007120078802c0310806100c5d10f80381d0480607001380020151400504611001400c1e100300c0350342e10f000030354001882800c010051050b030360004201031850200b840c014003c22820500540081d040c45410078085c0303d0044282c1003207018081d42c640070b54403560f64020b001c2e4250040e00500b807140ca040343d581c29101c0c02e4070825501e00354403401d1a45109200c00d402c0300040006000e00322540007600702c0c90020824000e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 379893615 1250 379892365 379892413
    0xa140f0426190506100b032202060c1e0304180905030d060e0a150302090f041e03080a0c0809101104050a14040501080f150703061e060806060c071205 66
    0x401c5144007015182041c2800c4c3d0091440824906803031013807002003481000e403540901d5410400812406200ea110400d01a111009500c00400142841d00b0400890308180300321215034101d0312115400a41612805075001d044000d50603e04203984c2203c150300005d25281c002c00a880c545481101d524040e940290000d00348000c10b03005002800185206198020f482e098404100900715800581e06030001ba10302080d9a02031400725084c0510100f10303640d0340039400d01e0914245c0d514030f40600750007401c41e0444180ca14001e4503034401401022224401d0f030400000d80310b1034102c40550801890a2000c15091100074400030841c1d40360510807001801d066140d800500070000100019103805070402c00d810f40200c02008071140002a2203000d80d5180b024a01a0707607607441e02200140615480400800345404918024451a0b5040310a44406940b504481e81ea44c0050000320702c6000180360ba1640031313000801581034078410503491988038200b0303161440607141500131140d0103c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 379894865 1250 379893615 379893643
    0x8060a03020d060510060e01080c0a1709150a062d1a0304110f030703030e2d0907090b04050118080a1416060503010b0304030e150a140f0426 62
    0x2e07901707008001c01d17109050710042460385040b18502107003c000810006001e0058030b401c01c0cac0441c00e44c800034000d4001c44100400c844001c0c87c14500070050300d548004510b500d0703401000307020114035850114054642902c80c0b4160302400e50030382160b5911010006040c4065012105201042c0e15842c3c01103200c01c0c04103000c0c400c3c2c5a0500d03080c121504030280314203074452280d450300c00b07074941c9003c00e02600b06d0390542440d08082d2011000304900800300650050880780320310300c0c108008a4841010072a80041d901098103a403458029107024510380641c0300001c3c0180006c200c60341c032520100f50f10a10001005211035520340041e80380a41c0303030104483d5105901210010480100408070109172002200c5e81024070f0007101404500c4180101984850000b0001d414140242d4044000c803402601107a00c160039a0400030950304040d840e90b000405044032059954905810340d01e900d1104200c103407400e460101c1008020310b810110b480310b410740e03d00038030f0384410900c44040201e81c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 379896115 1250 379894865 379894871
    0xf0b1b010912020d080a1b0c060b03010923060105010207090c02030c3003010e0c0a11160801150e180f070b0a1b030c080c031c0209010e011e08060a03020d06 69
    0x368440076001e41700091241c2526440d00700304480c1e03800035102100700d9400d00d08183e000c2c035900d410480040e2030407003102038141d0f081989000801040003820204104012680c0742c1940b11100d100d0744500081c41075a0040c0e10904091042e101d642d404501d0302901401243d00c4d04c201212118109845140741540c8810001c000030204002c04010010a1203100c80b4a881c541c103024887c1e42486c000b03014041400c4001c901c1c268886d01510209003200241c0c2d0845000ea0600039100035600701600910006508100b00d00b141202001e1005044e1694952003070352070f42c0c400002442c5900c590380410b240b8841d220181000050510103240540310300e9400568911740142c000d894290000704007000510540104404294025006011103520104c0d0f6542c0e181014081d501c0e50041c2c0f8010202c0c4543c0a03200042c01e1001d5004051046081e200c82510080c17920056613500b00120040c10485110182208000d109040c0d0710ba02c80d000410b8070810301e84a8010460010340070500b00c2c3d806075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 379897365 1250 379896115 379896133
    0x90114030d0503070f08040314030f0604110406051611061206040b010e030a061a0411040e070206071b0512030403021e16061803061806060f0b1b01091202 68
    0x10300344001d41d407800c414108a07140d401d00d01c000401129a8451850030011030a0104003094410f900e8402c00c50b5200500580b00d060000501c0815001591a00e00c25454080e0700f040c40c502d10416182251b50380c2d01d0361800c00b005404205a00c051808049824100c480020303e078039a204006040c0c2011401807202d05440c00005000c101c441d504280703418040c02c696118500d03600000e841c4840303580240042070a40c0c510303061103040e9070503001c960ba02c103003031a100908543d202800b07882210081000c00a068489000598585105940000015140580000028500d142400340203440340c0201c481030780201d00b481d4540d0708184c3e400c40041c0c01c00045040c80510740a00880c080c9506006040d248460141440d08010325107e500140b12003590240b2842108011090046400100c2030242c1070a0507140806040c000c0d038120b8015251003004904140d0088075a02034500340b802c16031500f003d0040c04030314000041d1140b0f82d50740d20794542200088441508558a00d025001003240790 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 379898615 1250 379897365 379897369
    0x5090a020319060f1103010b13051509010201050a020903060721090c031a090303062103070c0f090603020102030f030a0915050a0e12190c140313082a0d02090114 71
    0x1040e41049070303005420005c0c40361032040d80200726811101210703900317a6201801d42c0e001a4400d601d030301590b0302c5a691000e510144545a00a00d1100800d9000f0441c41c0d844e401c0910407806001e44250300346d40204000799400e07008036032050003504500f20900089021012110507180e003082c08407940303406d0600400800258400d60940c00040004400b254600104c0035a0380c1c2c00014103051145241c3c0d282c1d007021010484561410600850550781d4681680c2001801c080b054429527604250030900029414028032812081e00c2d0305030f0145142038007940403412507800103080c0400d956510314245d00050b400109942104060b030300007080304d1501001140c01c807071010401030095084107079081220b102440c111444c9482c543c80400d208140c1c0c1404494061041d50020310f101841d1545001d03400c0c0c000041d010440030508000707401521816215207600c410000e500400c03074903200c1e14408880c01302241000e080c001c1c00d044403204103030b00042c241c0042039101005035152410400c12034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 379899865 1250 379898615 379898621
    0x1c0c06050c041a03192409050601020d0807020a02130b090a06051302090f09250c1b180b01050c030f0405090c1201030b04020312040311030f160905090a02031906 71
    0xd80401c0c50060943c580000550090301509103000940c1c0d98a0850380e0484241054011b0395030803001c0040340950310703442400000c00d016504036015100e128a9181e4461007100e00500c12500e950140511008aa0900c2540c00102c44c0e800312154842022078440d486c2c0c03039101449806220300210300e103817900e020302c207200c52003030655081d1500410961456880340c01300142031200c140c6401d0720545c2c4090495074140c004520140d1701030201440228074640c044136005440c1d010f82021000040b84415031f5460131050303c140f80b03031100c42211070100e01481342e2100c000030b603041c10702d07500e4004142d55190079540071030400304008001003418002410f0034101d89a01c040c502462500d0501c1101c407140300c103101440003c0c4400303000750016046440c01d2100340e40301300c000d14402e03880fa6101c2c909810a442c0b01c2038014021710800040c4d901c803a5001070303124401c043e500d000004c5c540c101902d55014120061601d042446a50300c114010f0b1005c210506041c900344c1c480c0ca02c140c0c5540360240903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 379901115 1250 379899865 379899899
    0x19111b0708031c02040b0310030c050603060f01080a2c010b0d02030c06070615030c090b100f1d120105090d020102040f14040b130b01020c03030304051c0c06050c04 72
    0x290300c1400c05101e402400811a2442020f10450240781c6100700559006403045402c02d4941c020084107100c43c45942000000035288a00d00120343c07039445909109a9020880e109903100b00000d0301d00300154021080705070800b03442c032404142c81414010b2400c6802025095110310038036850ba9810005081c401c0d21443c010440789004d1528807500041d41e02c46c1107d524900c241c00005504082100c6903004015000305411000c04d070035628200b10360b01c0c2c1058401d07500d039a400c0810300c0a13207140c90002400b036542c06885011107001100d20458a020348001c01c9055081680e08182d50303550b40c4905041d2443c2d4500020807185000c02c990741c2405a011410f90039603005101c00d00503108811640390a94805402076441000c080d00054060480c1c40c6410f030f00f0540c0300000c0704054103503802c40b005404081e0201c031580d1540c9014103540703210484010301103400a48048914804100032a514001e262625800101032500e4010071a802552500008440001c0030403940703a81400c0600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 379902365 1250 379901115 379901167
    0x9060f0c0e030c0d0b01090507050c0f03040303030f020702011418040509010605120d020304060305130f0b0405160302090412030209030d08060906060403050d180b0c071809080703081911 82
    0x400440036514060406010b00541c8505921230001649441c89001500c2d0b24030516022641650409400700d9101d0f40180003d50020381094042400c081d691300882d4802e40c2e069441c0c84009590742c400b0002a001082c810580442000c901e42c0300da43c03a40039050054010500010742686080204905d612444000d09a02c0d042040b0b5151070380d401109590407140f4509000c615641e0741c0210400f000351184004041c1d83c0501e5284042c4800b00d01e503a481248110200c031301040d405290000039112070721000b0b41c840c0c407400004002950101e1114004080c0341005410840043c001030300b018458526080003600d090700304040d9240034002c02da04604261180c0e4a0076085881d05521610314852003424807101500110b00842d032011298020000351489a45640e6101c1d00d03140c86000e18801c2c107803400c2002c07004a22401c00d0344035603000e20b9846210744d8a04946c55405030b90f054801401c11070210300d00164003c204200d40508108240800c8449a94003440e140c5c5642100c00340788019 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 379903615 1250 379902365 379902379
    0x1302072405011203030b1f110601050405060a0306110f030405150109090305070209191104080106082b050d0f050703180c140d0501060e0403110a02090a09060f0c0e030c 74
    0x800741d00e07000b0149045641505d00840d000704104045400c000189200c40d02021a88145608941d405200e12038040415001e44a81c0d0340e80d00204001d0300ca0540f41c160713000450070f20810000745d0a078450307416402c070a0030450401810740d030924ad09400850f01610541c000a01c000c40003040d04408901601da00d0700704002050b5280c0b001812409003c20080c0103002460114901140c500310080c2c03104c1c11800c090052905425903514190464804c06042d50300b8200b020403072000105502410903020545205100c042c881c5100340200a5240a4240102000345450a0540b4002c9440c42c1d4a04400400d0350304002000030101c83c0006940516000d54080001c000b80300c124410b022521154200e01c40007808800045504084400c020701e44c3d80780c040300003446030241c00000e100d00d010303484000d4850380600106846121011000750700c0101c0400088035000160700c645501c0b03008440008840c6803d9981c0d00490309c00826100c042031300c014103081d1515081200c40120403054800b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 379904865 1250 379903615 379903619
    0xe0706080f0c0c010f1a040c020a15021312030206100902131511010203180607110c040c0309142b0e1c0b07051e040602100b130207240501 61
    0x16401c00800341050001600028590307078082d10941050518004910040155210400081c0c80721544080f8240c0683d040175511005d86001241148006070400c1d0788900d964054560348000713500030b0124488078240c0f114081402583d4080c11a05140304c0c3e0006c060a0505215100000d44070f58050942d0303600400c00c000f2a180082e0449c0121009140c9503a0f60341c0c05050180d1b41c103d44030716944020340c8040300b00840b0500414845016180c104280d54070b81c1c40d011000c488035605400340d40000c2d03010003107180c01741c00c1c40d500500d41e1080710701c0c0c0003e4400c8103035505080e03001c5443d236240407603015a4400c8603145102d901950101808112481110028034000d450035842044951046883c1448500803200c1030f0000e20340f00f58083c170f01c0c11a0740b81540d80a40b0b150030001c205403111044122a142078032105d02298103442c15030b00200780e28018100d145001c0c203070909074583c010380e0741203640c46010000d0001c0d140039440f0b0340411041d0100400e41c1c20011400b500d1248580b4145401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 379906115 1250 379904865 379904881
    0x80d020601090501120605090309041802040b1512040804030f0501050901110412060b0a03080301080604170a0905121204080a03180303090302011d0a18050a0c0e040e150a0e070608 79
    0x9940e1217541c001c002241d181e031034002041c190300805841075000340c00c1c4181d54034111800c0e014010f049100311810000a1003c80030712060000801003202c00d0030040021155900840b52041c3e03025116545e0305147c140c907580c6032501b07960307113500403900d0369180c0061200078903003800b5002e101d0080700581d40c1802d2070841840d0b016401e000010301b101e517032172081c0000d9840b02c01103030700a180c101c3d003055a20b50b5105481c0e50b80e880f00303c5080c0e031405011080c4204186403001159031584071640c8811040303042100704991003600b00e0f081d002d82e00c0f815010803d00481c034030107080103001d1a40644200144c506010b040c4c284090340300900c103034517010244006038015917074070b080d6902841c00341e01c00044000d1040e01005107070041c03a03100c480d540c1d0005134043c18891110899842c00414021600c0d4441c2650030b94400d0040e40c3e000c06c07000c0d81101c1c0d0a05043e0b112020312904001214040025101518000b800a6441c85449500c40103004401c400400c0031900400092074075409901d04105 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 379907365 1250 379906115 379906139
    0x305240307150306090c091d0603030301090e0a02100207051206010f1505072406080c09010605031515030a0e0d05070305070c080303190e19020405041704080d020601090501 76
    0x40c08074040c05419820301a034800d42c0120017500d8864070030000081d5010001e45000307203e01c00c500d8050401d203c81c007005900740d06070314003980d0007400031802c59080620080c040c11241341e0b1a12244180390400340546d44408569142c0c038516001391101c941464140400c40b41c0510090410764482c8004008100091128204480c0700090540c2c4001d0041c000b180c0e0b501c54640d010707200881b25030f41984203a16074460100104c070011400c2010340c0d550564141c589113564411640302c40c80c1801000000e000318011584032211a00031001c0f08a80381c0000d4510540c0a110090703a1004020003254001a118110b00101e08100400c007855606200410b0792140103c02006c000001c1103803010000caa242d80f802420b00c510507240c8920b0004614409407042c00e000308000c0f810001d202c0d02660380030a881c100c041c0603a0654a15440c035409100182c1400b51044a01d440e900f07420b05c14230540340000d08040c0c030140d03001d00124014440001c0c9424010380000711202c0ca804010020004401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 379908615 1250 379907365 379907369
    0xf050f16020a020d0816030e0a090c0c0b07230c100504050a110d080a020c03011a0102280b1303020c0f0108040201030906113010120c0302030d0305240307 68
    0x183c1d484280c050a00d409031050061412583c5007084504441b800c040c1c0022041c00780807000e8541281443c0d5070300210003520100d400c03200102e07104030740342004201e044542c207078051000c1c1098910780c0841402d0350040b45c0c00c40d08194124030049250301c0c00020070f1050481d5080c5200f02805581071984a0136100c01111500070300e492001039507000f6603115150034425444c1c020301c11a850b440310000194661403a0440a4400d510388058014000b0340c10728040c031203181c10790090525008002c029103100c5c0301807205540f040741c00c2000100240407a041c2c0d601c0b944450190112540341031401a01d44070107020ba076403140050019400c4140d038000e2943d0781c419024a004560051181401d00080c07455891807005e8000002308400301e8a40011800348650213400b40214072a1844841000d000301900c4244181e200d8410400c24070034100d00d0504002d0203040c082d6134103942d0340e000a113400c4d58819010003007600c1d8000c1009401c0096040704a11030b038034145001c5214180e00180d10350314a8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 379909865 1250 379908615 379908619
    0x1706010b1809070e040c0c0201111b01030905030903030a03060e09011b140d1505010f1106010911160606050f01020d120222030605040b010503070f0b0307120f050f16020a02 76
    0x74000040343c80f4401c044040c514040035004000481c20800c0003888080c888030300b80d01240907080310300204400090090b505c001c0b002c0d1403080c0c0c0c10810703004401810169105442c41e1201b44000c0b0800c1d6814002003008284c035442c001400e03850016020a0307030100520501983c1d24112141281d40b07100b81010712010014601a0705117003030500740d50258060780d42540d510500d001d001d511000310054541054a80036220700c0d8038410141d00844408084100110b540d82001d401004442c4468001e00300c0b144a800007182030100303034840061840100c640941e0440c0d21510b0801003030820f1005001c00c0e51003803000d480b4900c00801d01910b21208030080301c014070741c0020f1250654628441c0d488044ca2160700b043c1245640342030a901500041d1030036a01d8030700340d000004203490300046680403524000c0580000510b00814821290001800c0f5003c0c07103082410180c0160f07043c41a010408401d4400180900f40201c100643c80c0c00141081c400102000d2550b01d8540c0001d02007501c01e0b41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 379911115 1250 379909865 379909879
    0x2104031e06090812240102150402011106100501030b010509300304060309051c020a120e06070311060106050906040509131707060c0207050a090c030608071706010b18 73
    0x1003440e19000810b14020007625a007404200c0112030b01d40c0074040740c0107000c0350026510505070b45542c03407416140c0341426400744c2d011203101500c001200c404260b1050050500c2241a42c4507161241032120440c3c40d81c443d540e598105020640e00361280d0521520286803407070609000501140761601a1092090061804486062181c0b007000c010440080400103817030312036039500313405400b030550240200d0b054040d1080340919403841d88090185c020041c0d00170505103040d034484a40118040c003d200c1001903c041d150302036103400c0010700d1010310136503448540305000304034035046c0f00043c0c2020040140c00c001141e12951490292001e546045807602400e81b610020051404034015004101041e140619200103030300ca00a807011a000750018001c0400c5d02508a1702e5404034000c5a80c0a90f00d500300703002200c07442d07104507003414450500007106034640902c54644030655001098040f10b170400c141052500303008071030050031040080380c1048501c1c80c0c0007000b00d10703400b02e8602441d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 379912365 1250 379911115 379911173
    0x207061d0d050c0a0f0905010e060109060807050702030a0b0106170c2b05010b0c070605090607080d0902030f0f1b060f0703090b0f0901081311012f210403 68
    0x100600c4400d21252008013007401c02c9a948000e05048030031413044003080c03450000005148207071603030b20610030081691018402411300f881654699000340004007042424002400107032010400ca9050901034030501402d03600d03000008018904000d44061a00400000c1c00000094402581c103c00404010100c0410b04012000340418403131403020081d0b42171800005141600000401c44c124005040d205103d031180d070709886034400d25034500d400442c2049440b012441e680d0191600c0c0b12004004140c0c641039800107417625850020401e00c40c0c10044441400740340401001e81c405048040441d10300c1150000a01c10307000760340c030030404540c0c0001c1c0181010f01c90b0000f100600b1403a070f6075a8607400100301400c1c0c55046010340502090440740070628007441d001d07000348080d9101e981500d1040103800115800d184141401c40750201030409542c0312540c040e800e647d1071001c10020000e040c0342142d140c0090803900ea0700d02c0300d902e00300010720100c2c5964140b810301d45640402c07101401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 379913615 1250 379912365 379912373
    0x14060d12050f1314010e01050705060c0f07080307180807140909010b130c0801060846020702030d0503131b031a060f0a0b0a14070602190207061d0d 65
    0x4401d6200b41510020702c1a07010500c4c116510840100380b07802c1e0703a40755085624000560782e0348680100940654030540025007043e04800050042408081c1c0e52410258a9907880d20580c000351020310101d000d401300c0a40401c08071444100514500000f480c029141408000103042000b00e01400340002c5c0c00001c00301d21094100f41500c00c0042c00c8843c441103215459401484c0303900c940800640408000a40f0034030070b11110b030240e800c03200319071507031074141c2c22101d400004002260302050503800034104905108400d00c2a9000004000d40d1741c40603032041608107085188000140301051046c8603812102c80460704500c3e40c40350104082003035401586c5041045680010660903150362032200d040c17065240c450148406803071103240c883c000e07420030071011b201f40105090300c1d01c184100c0c48002d108840b031409800d0701c841003920300f4004c0e0310303041c0a9030721010340c04182e4400000031440850741004180700600d0340e4944000c92040130b0342d070112401c0c000c0259600c1250207104003420700c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 379914865 1250 379913615 379913617
    0x20309010b090c0a0f080105010813020a08030f0421050c010f020c06210702010b100e010315080d020f0d17062e1d03030306040207030903060f14060d12050f 69
    0x101c20040c00412980381c0240b00b00ba0360380c0041c042400141007000342200407030158680a040e500161a003072100e60300c240e5140d4560a90001c2a070340401440c00019041000b400100a9038611007042c541d0340e8201490003201c1000c41d07902599048030664107101048022038a085071700c2091a00c000e001c0e48041049281002c0c940400382e05c2180000c0302d903094500440c054490070703100d80c030801e8035075240a0280c1c06c0301d00c1003075800e0308040d20981050180b0320400440c05406014180001c011162550700d0500e04c409422126080e8440c83c5d412501c55010840002400002e400a200300d1300d03e400000c0c80c82201105403031100d840b120105a403580c86491807c10313101d814007544881d05c1c10100f600150602c403040000403900c0c9070040d0080d481f0000070385030b503244054011495500c0302d50500c80294001c3e102038080040300c01e40803002601d1400780401c401c4039802c0c00b099070701490b0003216294601615181c4214014040c2100141e02d0700b0310718215081e0750a0050305d0f5651032200c0081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 379916115 1250 379914865 379914881
    0xc111608070306021e0c01050f0601020604120807091a130b0a05040306090609050303090c0a0b0f040b0a0c020d060507080c16020906041803090812040f121e050c12030a0e010302030901 81
    0x300b620701040c411441c501c158008e0f880f60554801d803d8040d1a541c006980b9203030144c50140188444920050320035000d03e06580d044113480c6017024040740c1e22004003000822101c1d04072201c03e1300149280100005070f00c040080c0c10140d5042e4a130544a200140c0b4610036480000c040d6030f102c4a592007800226840070241a8005d002e40c1c3e642e00e0580d04043c0c903600c0107000e803032203076214020100358040e110701500c811501d4190900d02c0d044c00c141034100d00d5041100e0500c10420722000ea400180c6031030001000d440d11501d408640d60500c0e100c09000e0000080100e402444240a540119284407910b01980340d0103540c40040c545130280410058000c0701d52501c190305606400c001015408107a03002207856500c180c0380340d4058480c0710a40e070720692040c410003011008052086001d407104103d8618800c40342005140c1c281c0785a81e5440c4581071782a01d0036013110f00300000c1800c00f58411480c00c6030f80c0010318a40010100c02405c40380c1c0d01c661060406a0100014004940950001403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 379917365 1250 379916115 379916167
    0xd141005090d180e070c0209090c030309010c020411040b07061a010f03020d1d0a110d12180807090209040b010906080a150e1008100203090a0b04150c11160807030602 73
    0xc41c40c03600c2d0b04007070590760151b40201d000d0b02c50f41001134134094020175410400d12004000c1c5141020070340c0112848050340c0c8049e644581d544c0f0112110400c40c030000c000816101c403246458010600304075045610900254010240890203100641c2c0e22000c00081c40100d0b003001038503141072142c00d00040c01600220601c40d2581c4042c0121418002601d030f00107403082424120785a1000c0c10300c00b400c038825000808a014085907a003619010340ca41040c00346150b0514404180d490320520314003000c0707501c4400203039030010380141242058040c0c01a03269003801c01d12101403410700c1c02401020024060340b0326503034800786c480c200d6602c0006500102130000040c985406c01d42c001c411403018034403a06005104500302e21b01100e241d4000d403449506418042e1100c10566203039403c40e400010030480b803843c0f14098400d01a0b0f05441080c10060440d81e4030b100e00c40b2403c4900e032422007a1b868041a000600c54100030410380001e801090f264003c401507140e4100c4100200401c0f08110104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 379918615 1250 379917365 379917389
    0x7090c17090309190b09150d050a0203010f0605070c03030f0c020301060e101220060d090501150503070b0f0901020c0306090a030806040501060c0b150d141005090d18 73
    0x200d40000202400b00c442085030f0180c075074100800c4c4121400b003039210720703420440d007405035400624080006c0d2488820540c0103928100002035a40210340080710380d4009680d0110050000c03807452004100645400c0c10001c0c078140098032445180c0815200041c104002c1c0311132149080d104004807031407594007074000e012151300c450030003800c0d600441f00c040c1c601805000000360014600d01d4480306a4010380c1c80080c2c00105010100074140c0881c0c0030b03130000002c02a5246000d2075100e0309480501510002881d5a12740c07580c251054200c2e48482d1195110b01c4092000030307a14011140030241c001201c42d85c0301d0302c21005030b0070001c2442c8e680354980148010800e0903107000ca890851588a542c03040309550301d14040200300c030b90a00907140000c6522001c0400141c0c0d000c03055030409941c41d0b06440141340700c0300080c184c41d01c01c1d504503034903140c000c40140340e03038020482400c0c14a4142800c0c0000c0c6020f2800903035134050850840204413040004140d030011106c1b21310080c2404004e44 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 379919865 1250 379918615 379918621
    0xc1203020615151207030204030b01140f0f06043c091503080304031b200316030f08070606033008040209060d1401020d0b190807090c17 60
    0x294903500210351040c1da10036280011600c2d89481e20802c1869000c08141c182840300c10036124207003a00040c0408141a420840480421813203e001c0c2d008104800e443c1c001a0002000d00c040000598003150142044542c3c0e032419a403a00241c800b40c2e40c0c0072500c50741c02600c11521030300f400106040d08111101c1540400b6000113058581000d81d500f09a0034401418818158102c080240c440070f8103000003030000c02c00080c400c00c00703615600c1c1d44140c0340c1c100744855121b222100c010051519044010811031201c01d0406001f1808200244c0804884032455a19802590241820000e02c00040003600d00c2c108903503544143c001c4c40d042240c42042e62a507043c6105003040e58913100305040c1c0b018918144251088040d41e00c150b0307014011000340e031030320014030004180303440040b50368030b0700c1ea005102080d03400d04c0074003c0c076003810030085a0b0106820500c2400c503132420100302c9078808400203012400c0e00180c1e64040754461800001d8042c244107048622101c07412030b40b5403041c0520300f8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 379921115 1250 379919865 379919867
    0x11403121201030b0c070c15020c0316140118090c17150f030a0302100c1403090304090605030a171605250f0602280213090605060405010303050706090c1203 69
    0x1e2410703248603a001d4181d1340c4404902464074080d07444001c0c060840e2100030301050358042c0038041d000700c1304e00464030444440d40001e81417003128400e031b210341307000460300300041a10a2000c1d16225020300f802c810b96000740000042c0c0c0d0184d8003400300030780d44600d50b6960a5101d05206c0c4a82c460355180490242024882e05400c18440101d00b40308203a581c070340b0541e510b008500a0a060ba0640041100c0f02040c417804001e000400d40721003d101c02941b0649880c440700f0300640c41902c03400040c50350749042282c540c003124040e41101d4000c1d40310213401c0d40090507002100d00414070380c0b08429143c1201299120b00700c4a800c000600502600c40d1220b200c004808507008041c0d070001107000c01c141ca8150050007201c6504c501401a0700c0040c02d0710a200d203005000c100742200010688040c0c9040c4c000c120100c180e0004180800d40e54441c0e40c00740401c622a03203800c0001160207000d1540355842c020102c1c0180342001c0c0c056652a18402c0402400c5112007009000900400f182c00c001820 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 379922365 1250 379921115 379921147
    0x2130b07050304060201141519050a0618150212030402130204030f020f121f02130806090c01090509071206051e0111060603060c0c030408010216052401140312 70
    0x1068801540c07d04103540000707468816002d00c2070207400302d11441d000f0701000b0445640c0c03803803175406141460307498003140e5078a541081401602c06a101c0301441c40b41d900c1c40b2401441c1c00c0e4811241d8012020501c5242c0d075002c0344040340c694401d00440e4680d2224000290294400c407107222103680f000800000300a802c0015991490084035250280841c0300305004400b0700e040b071050400e4000902244142d01c2d41454498004103000303005080c4001716411035000308036074112224540c8841d04004c0a03c43c1044024500b001c01e20740880703054580404900301c820050807203030520a05811200251000d81d00260081030b0003014030490700462504a80803c0105038a54000b90750307521407420b5a500000c089008000c0980101020360742c2562100681d008000400c5883c00b007000000350041003400642400c0e800306101e0303036520035203140c0301b80742078040540703001c40a100b580e0b9415600955503403141103034540c07254400c4640b020000a030524204083c1a0491000400c100c91b600e58408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 379923615 1250 379922365 379922369
    0x61103090d120314091f0930030204060e060c0a0605040308150a0f0e04020118030c051f020a060b06040902040e06030d022b1e080a050a020c070902130b07050304 71
    0xb0f10200803806440034415140c12049800861940c4120580d030051680001c5044862850300000140084581d581e0a1800105060782403034010062039501c0c280161003072680081c10904086180600d4010080c10155190642d68415a40403030184c12804e02408009422507025108005070714283c03030302500450094440c6464444ca0f101c40d5201c5003045c48800082d900d5603012180894a04031010302034205c014412410404104031032141110b00490505c09103100d01440b0b920142031006001e01c4c8140c4050180c01040c602c20000581a00441c182d1035180e040500410f50151101c0070a0440c4075661100310417510004e0b0005400c10303040c50580c021441241580d4022045c1700080b40e85224108903500380ca0030080f92403403a80d9569600c5c07070010009042030181122603030351000c42d4001b03100d044004100e901c0c1c204801d81d40b1038400c1560004200304118201010501d40c956628054040c2c030a02a500092840007030010040410003400901c442c01d40d1b44a052510359200c1d0094 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 379924865 1250 379923615 379923617
    0x302010807050417070f05060c071806030b07080405011a0904030e031c0305040c050405070927020409090507050927100c020d18141903050f030a08180304061103090d12 74
    0x2458041910315050040351000c1c50003d0040441c141000100c0c00c0d0307282c44c144c4600e502c642ccc4543c0040010300c0310701c10510948a984500e40c0e0351a19041590039a0201000c40f910000e50b045248250f0340c500f010a50495014a40680a00c8000b0701091401c0d0f030501d80182295901e0780040b40340ca51582023244607a11849601606564801c10300c41543c3c02541d201001c03440c2d0b058140001c40c0b00a030946800c422a00148070b40408518401c1c1c03c07644560420420750761033b048200c00313005013000340320f00a22068400d44080d14099209240f400c000f158044c940104d007a040c8003201c0f10420900300c524820710f030100000100c1c480c000e580d480c444071488000c9003200001c040e0400c4908140800c69012a4001c10010401e20800c2485060050b82e10f4440441210100c049841002401203070001c1d08019580d61002e600041c116030b90040c0140ea404078140c200e45881c22010058400703d8605003401c841044040d1091030450103041c00c0c094010b000711083d00148061003801e89010042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 379926115 1250 379924865 379924889
    0xd060f0b0a170613030504030204050103060605040e0c06042d15121e020c010905010908031e0112060b030a12120506010305250c020612010302091807030201080705041707 75
    0x345614102c600001954641c1e65900444002640054840700e01c009080c82442d09510309038582d800941103ea080e041a2002d40d80d4060900440c1031a10403005101e188000400c0c01100c10b07000502c50748031f2070040c8402c0031280c440c0710081c0d800c404035940074608521841604140c40e4904d162a21104c00c0550001840b0389040150b240100d00c104150a80c8a14007100440c140d42c80d003038040d521410303a4550315940d81c6e4000c00483c000388038001115101d01c3c4c074144d0303a0034000e28484201e810b01040714180a04000100442404200d44c05000c0b80e00400c0800c541c812000007034240280144060074890001c200206102c2d40940c1d00c0ca040d5400190400c0755890302d000460071184100c440c801c000d03800703110b0b01c060040440100300b0290313101d00e4100401d902d1b0ba4041003407600a1300320000c1c510303d810018400c611b002c03c1d6141d407001c40010703190a030240c031901c1c1599840707180c170001e814001c4aa0226103c0f500c0351007210302800101041512100c0e0003950107668088912684201c000c1e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 379927365 1250 379926115 379926119
    0x10f140c010506031603110105030711150105030c0f0a0905040f14012702030c090901020408030d06050a1505040312020312070203030619050a03060b030c030f1606080408030112020d060f0b0a 84
    0x3001707128064a03000420b010705540e1540056400703070b0010b0100810b114814011801c3c134241040002d44045004c2801801c2d549410281031801e2003c0300305603c590076440304030b0b0071525091045022101c0f494004a46600c80e41000c0b1030841b544071f800741c010109200140980c00c0150481c0f4090b9402045041446109220414808604850096141d003102100000c503241450783d46800520510005107003d9407444c60354070310341c04000f4403800d080d22804100003d10700718003550300a1010840141585400c81c5004159110b10301004101007031241100340f502e8420025110411035070205244a4208000080d40d0b98000f22a22841503040901c0c0c0580050f17120700700000c44a0180224100d036081d580d513003020b40148240180c16100b220307401c2c40d090340d007044004210480480034044860008401c5450b00b5126000801840003a1003400002200c1000301c81c11213400a0004002d5443d81c400100c0c0d00840c110050620790070001c2c078001003480c90744241e81c0300000f03c0d40c09003815 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 379928615 1250 379927365 379927393
    0x20d05070c1b1d0a1d0f010f02040803030103080c0a020316080d0c211b0308160305040c0e0a1401150219020904170c03070605010f2102010f140c01050603 68
    0x11850007081068514005419843c0405102c10764010b03403614004a40d158000e641c603564a005101e40b0a40e0b640100e02c007005105003031080d805202040081540f8250901d902c0c15540e00c010301c0014125100002c0d04a00b41d070f02408650490340e8020b00b81c401c03004060003d01e0198185020f41340090081c101454a590700480e02c0e00790655000b01040104080c03281522881039182000c4400d10510080d003100110121002c100c031540700e07403111400790030090100480c0f01e42640c0402c040c14900814407020911012600048542c110901603c9598030f00c4020b000d46001801e00410702481c0001082c0b42c0c1100c00741c0464404d0903801c6814020340003540082c42030500c07a010750007210040c04540030503030310341200d18074584000e511440c01c95445405891a4002542918491343d10001881000140001000140000001400d41e88001d148014074400c846034004c0c14083e2044116007040d01503507201b111519404012600c94241d000f28502906040760068821f01415007844190 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 379929865 1250 379928615 379928663
    0x905060424140301090c030b1e150d0606050909390409060207020909070e01060c03020d0806040b0316090b01030509030d022a0a03080c0427020d05070c 67
    0x10041608110819620307000d03900100e6a60b440c503054240d52100c020201080d01c1c004600e005501c265004070051411710038100d00c010042189119016483d818014011800c3c1200c8040c20800c8641500030b00c0c0c2450800c2c010b100c81d0303102541025048040208000000c54008001400031424010ba03c3d006074904024116266490141c520014828841750130998030060409204030401854550075400080900c3c10484461010b64005e100c00e01c102c0f05161a5640100000d081030800300040d95800382d101c0384007020341410000080006503141d5a40d070814404800c001d0280c03401c0f40b64888143c1401e9003a4020002d01c2c81c00c010700c24080394440c0c4151407007207034001c0255043c1078011801c0e1010754045400b440120350095403c0780c8072541421260314446040d4001e10307440c070b00d81c03501400f4558014403581c41528240001c20150035403200c9403e054180894a000366108200301d00024042e000d16444118941410400100d4004174928a0b550140320000e41104180b040c800c04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 379931115 1250 379929865 379929911
    0xb030a050109060f26031b0f06070c02010507381308040314070b0f0909060d110f0117070e030f0a030c020609010302071502042c01060e06040e0109050604 68
    0x70f500ca034035104202036056501c10401d0b0070720744105d030300c402180d4040c428510703040303507074841030038600e14002ea041e51108220174101d07944142c014206a10f0010005404642180f00c082e040c81f000203158800c0221441c0761784042c6000c400c1441e01c400c81c081080b540d501c44025070f10780d03030829580812650054003a42102c12a03001901300c1c607007411135454246028175851480024811324601050504080c400740c012902c24042c0e070383d152040b003000c000c41b04a01a01c15406004140d0600380801c0e800c103051150300c03034141c0b0b51b07076001c410240c012030f203003890382c0b00840b000c1c030400042c004980d40c042c0c0c861500110031000c9403101c08603180c51380e81fa81c0172040014040f07034848801400509141020b8603400005040c010f09007042510b410401402420003031320a01c2c0c0c00070307060003003114003000f51010500489903503110130060160a03041100600511b01403140d4000c0400040d43d410003100c01510380202c2e900700361b580d1006070760081c100650b007551055013000711081c009284100040c1d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 379932365 1250 379931115 379931129
    0x6050a0216030c0314150705091c11060a050d1a010e030712030e040b0d030f1d1309050109050a030801081c1b060b0d03020a2003060c0c10060b030a05010906 69
    0x421a80f5550740c5041c0e5905400341c0080f140211075500801d40c046c3c020f864425203494452030340c1c60742d0701d5042003414600240f1f0320121144000030000800d04030444000020720070355072299210301c140001e40f0280102d00307103d0300140c109070007409105401a10310500d00d1080c1c9890020b00200f00801d40c903401c05004003014080e41000752000b181c40785055099100b009400040c59804600c0820070130580b0700c0341580825150054901000c1e40900c0e4101500d81c0c60044080c130440c5c2c07000007040740b00322050910000f901d66002d1000e20000f0352210650310341c000202c411031130780307440c010700154024401c400040c01818640e0702a110000042c840319541c65490b403c0706400041d40030120710805c00159011661904030a017161184000380180500a400400d03040d107483c034080d044079502d54048118025a8051503090362800120355400c0a450340e80c07207450351a0740100c1b501d008500540b6141507814610000380e117080711001180100e0071194144002da803942e00c0c1d0810340d4000c1c071a5078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 379933615 1250 379932365 379932383
    0x17030415050411090115080702160302010c0203010b33070b0a0507210f0b03030c03092b1416080d050a02030c10150608010308030705070203010f050106050a021603 72
    0x54032116660000c0d0b446881890980200c241610210b0314401c0c01741c01080c0180c07603003014211015040200d607a40a45c0b2840201003003011488011203240b001e01c4000d041c81503c2d040d10b0115582034100080d070741d0b00908440024205003c801031188204d145c2c0d0140c8030003980d0034184e8802440c0031a00c0701c54120807580d0454031490011b00080000504e054204910700c290891030808800c00f0340075410309080041440307007692001c041202c4424a007503110380c0c000c0154102444012064521403003048400a442c041200d6890030302156405840b150440c0080020007000725005100c480c80c0854001c480207580c1400c502c9042c01064000d2060651210303003c8040070703201c0c0d8018905d0039118410b072824541d0703404070627181a48013203203076082d90b441e40d03488021408000440401441f4a18105a85501d9901d4100d110700c0003404102c02c0020020312036066440940015441100d0290100115071350303050700800f141c014000981c0180240c04a00091200c280034070019a50421000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 379934865 1250 379933615 379933643
    0x307030804080a050903010c0e03151e090f0f030d050c0c060a022b0504020906090f0a0f0605310e0c1c05060103050a0201020601150509040c020f1009170304 69
    0x110005800c0f40c4404410480108032440480d00c080c010306800d403c203611a0709403169003d00305803c000d1220b961f90344654642082102080b0480307a00e0b40c00d0800150342e00030b9a00c445804034244100c400650b4442d10a8181030607036110008000c00903488404000c104d251648415848a8070413060301d48110380c40b007404501040101d9000701440d0700d4804034411010041044000506c203028655a10f107640e8004220541c1007405070b083d400402191b5012072850400c40c81e205001d4045d1000510070b81d6248880c640780c8039a4004e03006807600511540440f410703142c1c8603d2406105100c00d05500b0900d400c0c1580344910700480b460100c80d24094407000107280c00784030f66600464080e45d50013803035402902c0442c80501c0700e280030714001d20103010344803d035000282c070b2306c101a4004078559002c0e030520b0340390552210540314170100c202c4000c54400204002203240c0040d01d011844180a45070303903105a409154042c400c0310388210001004542310b0000c5000d01d010484000e407441c030300381e465 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 379936115 1250 379934865 379934873
    0x1a0316031b1404210605060d0c0e04050c04020c0102030709141c0f0c0b0415020d0906121103090a150b0102030327060115121e0213080f070e090307030804 68
    0x2514510842802c60400d540e50342013130802003052018000034080c51610740248109400b880341d000c1003d803401345208005a071032230441c01103403003403400b20810742003c1406c2200c14801c42c44a0f002c010025502c9a050344400c80c001e510a0f0303201c601080c1c071144001100320f2011041c003034181e030040540c25901c44c50b42081c40064812602111002880c001c0980080c0c18100081c0192150701c0d6851b89680c10645401700114803442044203650058611a0180340c1c0109040c00360340c1146030150000c3c1151707103410050000d40701c40c81d0a044001c1b0400c5004a0300040300d03203100340280ea4040242c41906041003c5500e40e01c0c60b140160800c000046588181c808401f44a200c0d440b4030040b204418001c01d820039000380c000540e0062010b5807001020b41c0300f401c1980242908004001086039091411020690000040c0603541c01043c106640541c061200d001015200b003640c05952400c91a59101c12640c0501b807044104640803900e807400000c140c0c0d5030254180c507070403080e45032611 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 379937365 1250 379936115 379936127
    0x9010b18030709060f0e0c07050307030c0f0501060602010b0a12170c161509050f0904060c05131212171f09021305040b030a0b040206030702071a0316031b 68
    0x10300d5816100d040800503010340036125000042c403000d41021011414810b084e00c0c0040c0192420120040901400001c544c01004035503505505040454480302c99250250104c66164001741441d46030500004005806400c40c0403600ca040301c10303003a0030b51101740356031008440340005070028019505c040c451620650080c05601c88410858020300030030342a4003041a5190012200c0c4290001c004800382d401a42c000090030f41184d4402c2c40858580200d0114080204041c110a444c0d038017232140303039000d20200c40d200000f2100c2c410b20305032950300d5001c0c00c2030201400c949806295450046603441a035054034000c3d20600e490a03241c48182c0c080e14007401c418010f0501600803a400111540f1510040c03507a603152a0000b65901d28020400088510180b9076a0198001510300d90005108480d8560b0042d070440d403c40d01c80e00c0382c200407498400c0c40e4008540b6001076401c02807603081e080300514807500e01195551a1400021811401d4451114003002050032008a0307562044c0215 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 379938615 1250 379937365 379937407
    0x611071203020c0d08130b070b04110f120604050609210d0623130608030409050c21090f07030308010608190c110106080d0504030213020c0a140c09010b 67
    0x220443c1d8000c0540000503a500016200c200c40d080000608480242d10a291030001010031110041c1007002030349800005080c018002030034594840c02602803991040d040e004c00c081c0241c0354000d41d402c8013580565582e0306840591f450311640c000650a10710001c0d100c02d0b1049440704903003401340c10512841d0719401036003070410002d49481c400305020803400c50104410f4009134040c14a00000803d0081c80c644014000c034a20382003020034000208000304a030110356140200294582c1c45030141c0025010b03081c000d690001e079018001103103084401078103009101c660207550100c44000b1102e59030b284148401008550038000400200b800b807108a40d0012229001e122010040340200702242d8280201e031000c90a054460040900c003403069038003800c0001300410100e52404d401503c07a005030b2000a1007030100c4440004040781e181c05035030b50320312102d0441d08009e50a15140d0507000c0c0c2001001039a03c124000917003140382240b1001e040781d08000b02c039890010766000d44040c0c00d03080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 379939865 1250 379938615 379938617
    0x904080913020d02031312080106080601050a0203090909032808060409020d0215130603050903090f031c0507020f011715011808010e06090a0c05040c0903020603130308010611071203 80
    0x9120782c040c4021a1300045120f00c003090941d1803441030910b01140020320302810300080007048030060203526001607030103401c60800d090460721a540e2040c1245988545c608841d003068528060105580002001d40140c040f044000202405040903c1c03070ba5422088070b0300001140c460103c0e066080942c40103c456001070b08500d0802115008030b101003501c0441d0717281501001071400d00b091000e41c040c901034581c524082c415030402503041907980c0a01d0413090b21070704c008001a4210f039404c0017a02601c1c06110001e41c41042e0440b40903245400c40d0400f030780560a00388246410317601c200c81244004142201400090321600c1c400c08004103440141c60500800c3c030000c9800e40c64440d840350040038010008502c5c14044a10305081030789c00f8000030038952100c481c940000d0007000d59002500c01c103440014510301d10041c1200e02050581c40030b5040341c2c0c0001030050381040901005003090081c1c803a5250350340e03501c2c0c04641301ca0710403a0082e5a038005c00d00610424000da4030620f002402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 379941115 1250 379939865 379939867
    0x150c0506060f12030c070e090a020a0312020106080f03030a0c05030105061b070b0408011e05040f0b0703060e0a0921050702150f0c0303100b040f1809060606020a11090408091302 78
    0x10911904e165500007001c01d6034607405000c0800c03601c00e00d20400c0f5800804503000c2c00c10b00300540d02064043c0d41c64080241004108006072003150f100350300020042881d201141c0c149000c00f4252916035000340c030044440c609007068412600d00400890341260000344c0014604000b042c890010104401d18580003400740500000320301d00c40f41e0140018018001c00002c144014015107250314906241074054141003500b08800304200c071300202d0540c1d07000000403c1c15950780800318014606900203d4492000c4810301c07804401c190700000c08107204215056088113030742c440e144100040411a40000d8040058100600b000e0010104c0c5130003104d185414402c40100c2000300ba0000e4018130060ba0000c010441440c0030046500001c0c110a2401c5141c64108242104400101c0c0514030364894a03034038a03051000c240d8019140070303811400400c040350b1503200080d100c0020040c19110a8190721040c96149004030b4144d018951000e445458940a00140320070345075aa001640c40d154 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 379942365 1250 379941115 379941139
    0x1406040905071512060e13150e060c030a1d0c01051605010f090b15010519020a021201020a1106100501081e01030b040209070201140a05090a060f06150c0506060f 71
    0xf554400d8081c002105803203036403902c058141254110f41c8607601c05541ca0200078184440090001c070000703c179070341081c200f01c02014035080d01009040071240500c41da01c558402c20620095101c065401102e5810043c0700d41406059036440300201480341458a4001c08079410a07580507800401b00d042640f0030103030b80300d203042d00c56a086491400003d03040c2500c0d40e040008004004000c540c0c410101007a1080c044402e0700001c00a010315081c3d0396511030140096481a4000c00040350910390007404135445c0c201100c140d501030341114a0840c0401d0300c0c0462640c0300b030408500c81e481080b120710081e2090340b038000111620038000c1c0405d840f0401c48814643c15200810601d400303940134486a89035801e01b48140550700074010503560869141840d0080a042640c805c5038204450540118107500c5c2e02602d68104595414000c01540c13a0503214040d01c0c41030b4100e04111034203071011503a0302c690403009441d10446188000c001d030f0400740c0018814605103071040e07017400026088022401e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 379943615 1250 379942365 379942379
    0x4390e0a111801091a0a0c0c0506070f0b011409192a1205040305030a0f060b0d0e010e0c03060415020412030c1211030706050606090d030c030e0301140604090507 71
    0xb80c022030501403540c4000c20b03900410b50700310403482c00a0201c4005800ca03000d2800b0040264081e8509007020085900c5507413040c00001d08145028110043c049555542c451605440f403d219140490340005c00314000204801058014011864041e040d40c620340c0e50030600740c8000c2c81d05405240410b940e091b5004030505501094800d00103a000820380740040c0b010050801b03031040008442c43c90074082000f00281c0d011096030703040282400003003001f110340383d0303201c1c06400310307421200e880c41007c5a503070b440d20501e801610242507400d00070024060010041a140d82a1503004c54155201b0408640010500c014a480402c1c21034001400c254417884440034030714402c8030560000305040001c0b001d0008a0844490764202400e05040b50001c40036095200d0060b07000240c0150307540c1c800610503840e03030760032261540e00043c95030720501141d18028007590b042c401c0560016403203200d0480241414481c002c0c59050b40760803006569168800c21004d00202c880480c1d1a008401c4002010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 379944865 1250 379943615 379943617
    0x180f02121317091003020a0c050316020f030a0b181c080415090507050f0a0e04050105180105060a14031c0e0102010c032007020a0e04390e0a11 63
    0x1441a442040715000000d06112550b81400301c0010502d182c1009884410303596150310340c0c2c0d591440c0c00c0c0941c95a00c80380b03080c0c80d20b02da001e50150260000082e4140050100c43c40a081c051007100d54071505800102495603d410804005107500390800c0816406800310341c00045408c0444100c0310f4140c501070550720006088460ba5020841c280184000c000d1001c0f15151b12107990350b42002105034a4581c7c50703442005114071f90046c06404a140025107461040300301802d04500440c0c5517040c2480c0140c0203107030441c0c940340d03600741c01c51105000b44018005c03e40240c034000c1070400c0c940e06090000c8181c1808074081c40c6d2601c1600f00b50740e2218003050900141d042151a901c0040c031031200003900352010100c94000f0103240903036115080314241e41036818109061406600d40c409817010404020701c0d81c1000396004481c10030002002108002c040c00e1841e10b00a80006071082c0000110081c0f542d00b00442c1d21012020034026106030407640340d44031b1401d42001c120640300008000301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 379946115 1250 379944865 379944871
    0x6010e0334080321250206060a081501051003020409021605010507091a0318100903080c0403020904060203071103070c08280b1b0c0703020a05090c032805010b03150a180f0212 77
    0x5600301c0e4023007100318a80300b101c0f40f0042c076201d0041e04407000044a0000010014042c59101701101c40c488141240b080d070584010f48843e88045559550702864490248440390088500750300384400582114480d04880044403842c00010100c6501d0707140050450b00014001150510750b9140701001c0041001152800007245c0d81c000780d01341c0035080091103050010042c2d107906008010030001a03d075821031941c0140c02000050701c0e500c616108540340807000c0c41404080c4004140360301400b988120700411107503140c0851750036003069106140d82042c0002d05800d8070a60301c1c880404509a501000e9001000880303400008641820700203241c0c05c041800c1c43c00d540b000b0820710850929016000182c541229000114a004404980785200040a03e006001080d440b4005101b41c00c0941940ca95803079401c1c003403980c40e0951030740f6542040b50b10307248442104581c3e00311400c1c808020026565594003500e400b000c0141d102002d00072401000308041d508000d1004140d4a140740240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 379947365 1250 379946115 379946117
    0x15030b090406050415021813060e011502151e131725020a060c08070b0a020a0305060103151a0d0203070c1b080606010e033408032125 59
    0xa00750405051040c8035076084405d40f05050710401a0318018580c0d8804204100c0301191040d070140e0881741d0b00300c0902143c0c0d00140304501d241002055040040303803000481d11156084580484032450300d841929420345000301c9460144004e2941c00030b41601855124110500161104c4c00c00d9a5103920421132034920700c0c040b070001c0340d401c0005d120202d0134200b103503600c105040440900d40020b46820280d00c66442408101c0c4208010098000296078803590424603c1d62203190401c02500a5072142c020000005c0c1f40c540044ca1942c060300c01c203e21002c035401524031803428020402c6a440c03000c000304080c000c0621451004056a0000314410655551007401d00078043c03400e03503040394800b80c842080e28510355003800031641c00900c2940c400700c02d1070114801140807000c68180898884040e010705d141c5214103803c03004042030240040c0403403005402d00b81e40c2d2010740b40c59000320300c16184120909859800f802c49070700c03202030b0407408259000c4004414903180e0750a401868450b24 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 379948615 1250 379947365 379947371
    0x1302060a0e03060a230606030c03130b0406020307030516140901050d022113050307061a030307050c03100608030405060d020405060403031205180a0b0405070f080610090209090115030b090406 84
    0x30401811402c882145403510140d170440d040000000d07149000060951400d060044002140c044c04080e45000d40e5070400d428101c0e50605041c585d010794030859109010a0410011a40710040703d00c20488050703140d034034803000014200b0b16602c141d210003c02070421900340900807807940107100404040c680408184c460307080714000c900903c0001030500303042010b071780600c40115602201f1541d11650004000451194915541404034121015160580f00200360ba004004001030014140c6c03208400f12941221581c00c06015134070300e405810384541041c04100701d18113000c0050644110b03012405410b00e510780d80402d4840c1c11542c420750005105001c41300c0405518032501d03402c802c8001c0000e180211034000c09580d8004644002c0c082c0c04043c00260a001091103418050540d13002d90038000e6958040c00d80e130700d0206940203a46191451400150101d141c400c0341c000e40d00240442c2d01580c640703c601c0c100350038409070b0141412340340c0d11030a100c5d68543d5501c4c1c1c841c6114480c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 379949865 1250 379948615 379948631
    0x70b13140a0501020d030b040603140d02010b03011523060304030503010e0702070b09010810080607030605090f160807050c0303190e15061504050a03030818061302060a0e03060a 78
    0x2004414001034086000d040304850501a42c1d034003140103003280d0001c1c280031440b12464804200203003825880500703074110300f400700c0c001040e02284034030614030140c0c000e11106510008041c203c4858032070000241111000070080d800b83c41c00d80710100c80010545028652411003c180254002c44040300007450000040c4481d100300540981c02c411a48000c0241504022204505200b03050029051101010006110300e0501201c1d07005051000f042c1c4003d030826400c050040d010360300405100f09848000280c00c0e407190352805100b04483c20000e0450050408140c0300310102401007010840102324a4600002c00c10095000e9258125011041d0001c446100100c500203403210f4015001421030285040038603000e0390f003020b011507865284c0c0100d03070b4194440e84944e030710140c2c104100d80b2000061580280070144038030b501c80e4880c40092240100661190012105141030300200c0c0741e17010250411401070705400284d4141990f082a407040040d24041c0101d501959041e165103c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 379951115 1250 379949865 379949879
    0x1062715020a1a19020f070213050106020c0d020901090905151608090105040302060a0b030a05191b06020703030f090e1602011b020a1104110714070b0702091305070b13 74
    0x419505014600c0b90300d055410803420305000e5034031140310b4903100d94006c20102c0809511504485806600a00c02c01c40c04c4005514140038040034851a805400741141051060130b003558900581d43c0e005100e10703503903070905011074010107080405490030b214000c2110040340c20b000340361f8001e000b0040683c41d0035034005002003001c00001c00503009070b4144020700c0000383d00058111f1304000c4480000c94900746a4011900d00a1030a801806c03d07c200443c0050703900c1c01c640003003021401045201804842c03c020310741c04a4031480340c400182d100c0c0d0310410120b44650122b22601c0d186207813032111607548030b9031084002e07400da512006c551100001c215020b0340910800215101031655107024880c0803a0194850382d01e030b2005840394486a8021545980f90b0380311800c41c183c1c00030b150b07845401d00d0400035401e401d40f1740011600d00c9082c101040c0c99035644d05030b4604541c010300448096aa00b2004454905040e608403480e00c1100400701e08540200d02900c501d4412080000700c0c107140180e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 379952365 1250 379951115 379951133
    0xd111b19030e100e04060b091504060f030b0a050603090d120b0a030b10090e06100501080c16110307061d040c1725121401062715020a 59
    0xe00a208849040c5605000a801c0140b00c180d44504541040003041c030014160703030f200c00c0307a00f402d9841442e0903400b02d18108484003402411364151203e0300d82180ca507442c003650b48100e02a000c0811101c65610941c144242c02c4030004940c06007458841c10b076240040341050300151480c01c1507400c4440c02e600780552182400b2510844440248050309080b4046402c42499000c0a05020445400603603400b11161060f03004010314039023080503615150343c9940361101900c0341243c94442d000005090361103040480e020700c0440a5051074050b1100c5069405140d0b0881120342c1d08049040b030690380d40c184102030040110380ca6004030049031410541440d015060ba86204520385004651641c1d03005c41c50710a030b40400030100800b6100c000301d46003446440c0300b420f14003505601700003c096030b02a8818695038a191410300c01e1020b02141500b01e55405d004601c00515040021200d0f52304240d070550000341e122080c444126143c1c0c0490945010000c001c2025178840c000b0300003003000d107003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 379953615 1250 379952365 379952383
    0x5031225030e012d090201020f0703030c020307080f070b0c0a0c06030609180b070c050f06011212110a020114120f01080706050403152a020a15060302150d111b 70
    0x40616403800391111150529841c00566829a13107035aa6080000c5900811444280709003810803105110395914005206003029401203001e80149100018250300018030030402c2c40c8280d001d0f000d428100206050b00381c200d14164012845007068400114182c40c0803c400307051580d070081001820410010142e840c1c0741001c6810f10782d4040c245000c14010b40100b9040f414a20b8a1101c007421810b00510b05400d0380700c0400c050182200000d0600d84540d4900c3c0140d10600c80c0701000364000d83d0a840c180320844201003181c00a1038501c005611a2014440d0311000503045c50808894619400380c00908403210341d1400702140041c006000100550b0004040900c1c0513031038142950390340103c845080f02d0350480d40f9124004000398034482140d43d5102d0190252090141c907686d48029950343d15440180e4502407030704401040224180102d40640340c0142c01407408080301d86641d14036038403002440d220507540c5d102108001601c1e01c010001e90078462102561000180421810300c1080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 379954865 1250 379953615 379953641
    0x10507020c010c021c080f0d140105010c12210501081c02030a030906110a02060402100f050a12060504060f06080a09020109181d03180d05031225030e01 67
    0xd003041654036a880221650701d5941a41d5421005c074600003007410700c40048000a01001010500c82902c1700924090090000c44680c00d102c24002c150041030107010a0052600041031801100003047c0d00095080400c16946008000201ca2400441c100d00c50351601d411255158401003110000400003070b40d01c1c00000c6081491100342201c0a0b60364400e1a115009242d110316222007402201e512030f401c144c0d0014012a81c4841841000792590021503049100f1082c00b620b10322200d21480b0440310001c050784942d85011800d80007503501c24039202001c60003903104c400100b01502c0303e0181d03000400d002c05100701d409041080c0901a12401401c0402e01d070b103803500c8080940c1e4004d00c40d4046914500d0030419035007003860036001500c0324040d5540c504003001c441420003600080200301c2c0c510150324481c41c210544003002036403c020031014046500a01443c0042c5140740c81207a08501035050030b014a1b640740000b150b4621150300d01c0004030707654241101b2801001c0c00b44851074101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 379956115 1250 379954865 379954873
    0x20c0a0806070e191508010302011803120c08070507060c170901050301050609060d050408180303160219080604080a0912050a120320070c17060402040507090b12010801050702 77
    0x400e10041460702c1d2400e841d40b040c050000810b984c00c074800040c5014020818020351441c2c070300900582004800c4c80120300140c0c03a00d81251646d0881386912080c1c9501961110441d80040f07401c951520310400c0c2980d414100708480000140c0030414807000b000d081c1c880031289105410445e0048400d010b41032070700401004840c04907070340b040803030741519011600700380c0b00e01030b42007c159680901803014120034541030521080c4140031020b0401c0180d0881280c186041d42028591a4005e41c80b01c09007050381c2c421800c00510341550301d200c04c8020440442403480d6510041450060240c030705407020000000c13001c42c082e620a0001e005002451400001d13145660782d00c40d80d0b0591940d02510400100300c111700903c0c0309400c24000150712400b22044110504c41c0d00680d54401d02c000c807580c0d6070b40c031000501d04c01d0152502c03108148040142a040d990368003400090400100176074100400d21801080f2020076070090140300f0b50300c003000f00360b075810719515a0840d10b001e00902c0035940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 379957365 1250 379956115 379956121
    0x60108010e070c0c0e090708070807030b060409050309100c03030f0513061d070609140301110d020c010f050a020a03061428050402160303060e0f0f07110706020c0a0806 74
    0x1100841c0d0300e400078594a0f08641c1c24a450414002d01072054000103e01c41400c018030520160004a8406a1f0799507000d442410f42d41f6500c0c01e981d0351051200a10003804040002c3c881d03d00743e406010640d0054003a28604000c0d04000341030001400c01c5680801d001e006254107069051207540c2564071228020041c908084001c03600800b00c04a00400c103503224820289201421860b4848140c401c20031512056140e60000d170020245000e21404942c843e200b00c05186414020680000040000285085000503119000e98042d0600a180350340754a0900701e041e4403031141034800c0542010041c0c030380441480c000c05594103503203c004003080380d00e02c6400e01d80c2e9519001040544084041821700f448000d102e62000c41d40e07100640c81403000c00d4450351f02625456090840340300788e80030807900b80c49603034004030305905450360b07500030f540b510000d0080500180340319000700c002d0501400740c1003110b003c603283c0741c2d80350090001a0008a004480c0342007030350100000c4c18200f405000945 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 379958615 1250 379957365 379957379
    0x60c0903060b0f090f1024030f0204121b0503060408030609070e011b02040b151b12090105070317090f01110910140705010608010b15090109140a0512060f06010801 72
    0x42800741000c0c401174035031000b24042c100c4604818000300130701440355200694130a034060083e001c0c0c400402c046420000041c0750340d50f41c1d10071942a60205800c40084a06c1603c9100d2469209001d0350020214884045456581005817508c10303449003204a0b076902c1c013a030500c540114003504000521694103222101a0f03007200c400001e444146942c00c164900728000103002d07042d0151241c1d004040c40c0c0058014002c0d0790010090381941c07054030828803200c034801540d20706401d4403003c0c1e1110144048803440d8441c00c01010802e003e03103800c0458601c0c2c2302800b1082101960120380360360040c1d21250b0020000c2c0108244404440c0740036040c4000c03200403d4402e01240f00c0c0e0400c01005404840051101c47d090704c81c10368014000704521903d40705218000e02c1d07a882140c1c4140f1442111030400d07403803c1c048424200c4103a40d03400509250035420b00050300c40300d80c85603000044800210780f58580000c003501d400c0d054001003001d4184822810060340c8041e080504100f0010014040c00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 379959865 1250 379958615 379958629
    0x1b01090e0a0b01110321060f0402030a0c0207051e100504050301020d0e010608030f0304020f010c0f030c03020c09160e0301021b0703020915030304140312040806071709101503060c0903060b0f 84
    0x60b0001d907461b14183d03950b02d00000c403120103d00520390b02c51700c00302c1800218209680401d043d4401a0211401d0361380303817804c002c525100c0b403190781080c102e4121030031a1800e003011004202042410100d04040e01c64002034266000401c4507000151b441080384807a0300300b4019a40188942d034040c52400e64100d080311344910000f4800b03801980303c1c0d0a41e04890344100003111030320307400078042101c144d414900100b400a02400540041c0304000401000b440c0c5042030500507102170000521001c5114000c0d1480d0f456042010380c155420701c545a00070911940f0307a010850b602016243c024103520400414a4015190441800040c024000162000030031076003911110250b03000c0d50180c4d01c0c0000c1c03414501d0500d21958090101d000982803a00091040c052034494507203c481c030845089190310704c4801c54040c103042c4c0c0708030301c889401c203c0c0d944908070180410070b80b855401d40325254642070713441c2030032001c00184141100700280300d124420600111130860740180203012800c009948 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 379961115 1250 379959865 379959907
    0x50702010c0206090402121006080106080609040c0819050f0304120b1f090204081b01120e0703020909070611030a021b0d05060403030e0f0f1b01090e0a0b011103 71
    0x1880903401c0408199a80c41c41a0b81a02400074800c0d56a09008581507036091020f881d44a41c0c40000003002c94010b0182c0e02c0d25060391056600c1c1100c0307a075070008212030000068410395242c00c0880011482e80000c3c230181e040d4100e03640c9002282515880c15601d07210392103e40c00f01682060000380950701c821b62000d6591604a0000c010035241d00381c0741c5c0c0c0f4414420314004081d401e030f8500010b80b040190050003c0f60b4091096075500300c40c0010300d0314034925150504cc00209800700004001c442588045400000707a021601459281c4c3d01140c54803006840d40081a0b01080d02005069400440c00c4851400c14020f5410101c2e19078010795107018440e0341c0b0b00c03500240c01070f000c4e29444402c160f4034500e400404644080c1007a00740503009001c00501c0008900840c507003482c1041002801070903c40c04140140140d1000e03d00000145c10754005242c104903d1010000703011680d0628140607248181000800e55844000540300407404100034a25400038008010000410440350380 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 379962365 1250 379961115 379961117
    0xb09010312271a12010302150c03070c090e0706082205031b010501050118121a01060e010f0305010e16021014061503010515070606030c030f02090a020a05070201 71
    0x201040c026000d9581c0000182c0c1882e812400e82e000a29803080c1408502c2156001c10041d0a0403807444081d2015208003c25031014141c200010401030034008101e2012840d14200c1c00d013000a00c8180504581c82410241c1e01a106000b051184904034840c00f0486100b8000505819141890240c40e658005060668020b0581026070110100b80000002d469000c0166540d840e2400691840c96015014800a640c6040e00106495000350350300710001fa01c2035210282c0c230b45007001010030004982e40032111041c1004125040c2034051160a001c0d040d551a062046140103000601d802070440510040508280c0100008510900b03a50303000920080e103800000c1c884107040c1d1030114070b03842040070286040c1f04010308090b1540b00501900302100c0c3e00102c81c029a4001900740000e0049582c0308054075010940d50500000400506100c0d10010904039a04c0e03e40010200c1c841d44140c5004c50940259021442c06041140d84100900780850400e451010010601c1c0101c0030b0080c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 379963615 1250 379962365 379962383
    0x506010c050a030f020c0909060a0c02031303020603040213020c1f02070c030332041a04060801270911010e030a050606011214010b0403050f030f0304060b18070e01120b090103 77
    0x10440c00c5c82484144a00d000c050111400307420001c0c01d6551703a4078200c50540d40c0500d08040440014404412124070034583d102902910f0705507020040d40303078030145c4200d034414100080034a5029142c0050004542094040e008120043c280354030048100312041c12100d00c1000084005034804108d44196901464941c6002040348148200e84010f202241c4c91a15034402c005911805000100151108680c5013121842c0300f0348480400d0060380503000210388000018003418000d0101d03015100c040510302e000314101c60100038100c600340c01007a80c1e030481c0941400d020f9604441c1000b600381d01640100b000f4095911070a842e42c2000d03108a0410545040d03484400d142504010790750b20b00b002c81d48065581d030700c0304c40441d9030042c4803c40e400d0054100320080c041021050303450342d400d0740c1d20480ca03555641d5941d0005019441d001c1c0d81c480700300204804c104051407079543c400c0a0b144c64100d01e4144680000d0454003c0c0201c450502d800c1c44a5404551261140e9504481d444030f542 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 379964865 1250 379963615 379963637
    0xd051e0c0424020a051204090c08040503070305090a0f0b0a090501170612010b09131115030106050a05070f050c040e0c010203270925051204150612030306090506010c050a03 76
    0x104d05115203074002030030900c81c0050003001590f40720700034400c8454a036001c1008500004081c0c62100c0201d41c0500316400921011000c00c1c0280003c15000100400c0650070a4403290000807122180d000104908008113444210702d4110780d0180240409003804040084101d2035400e54100041c085070280c2c01d070340f5458180f10004d400c0320703c01c01d0b401060380486103015072000c0001407414106580c0c1c0d61201d142d40741d027814840021a000141c4a90191131a824003101391000e910424003c001c000c4200700d00004142180284481c80e4440c101501c6003203202c078100015150307295216042074202c05521a150303a000811201d100e00d4825026103040490f4202488103461014a035801515100c200b200602c07804000c1e03008140000c841d2404a840b112003240c85028101d5600b44225184001c14045440544151600388840710045902ca840c0c0b11100201c04101804401090700d80f8000d0010315114001c041c0c0c013030420f181c940310621146d100c80c1d40e03c03100c1c00005024030103075a01d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 379966115 1250 379964865 379964867
    0x6020319110c10090b1216080c0a0309020a0f0b1201060504050307120204060312051b062e170a030e0301020313023d020c010801030b1b0d051e0c0424 66
    0xa183c000b00000e000e055204da046d10312402e400348084030814003e10742c0500303000495000d00003031030080f4000f2010b6824105811419070081c00c100320140d91003512030400068400d009404040a40481c1291980300c00b0070306815440e100040e0009800d026042c04140142c0d200041c1c100122440c0d820304030440c0340303903002180040003680c0010f0141c0c0180b120300f0007980d4100004040c00204003000d40c100c214501d20890300c0d10415507200580c07160104045e100301409101505280f071250780031414165666030318011b82c42600c132501941d070304840d04600506d60000b0049400682c00e80003907146180c5005400001119054000d10851000302040d141d903450034043c0c0601440c13120980320100c55140180e0f08440d00c0388403840144103a040541095115003502c03812a03a0115403d581910341880d9000180e1500b80701d041074000a02100020200b0303409054040d009031080d50113990700b4040e803a40201c0303001300340070305203401044100803034620071900855000034070a51003640524050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 379967365 1250 379966115 379966127
    0x71e0918050402090a0605060904050601020f0114060102070806151513030b0109180312050636090d080112030e03061801051006270b0406020319110c10 67
    0x21030403031080e50a581403421241540020b000328004c44941c0038503a5413007101e0040d20900d028054000340d0a00040c0c2ca1410315403c141d4014405006a41e6084500c000e01030131644041c0c540446880f08906020752560188500000360030b03c000940001d24000b40340408040a90400314000c0170f510301a800252140c8040d2281100f031030300c09000c86a41d074100003550034000e01a0358000c5240c8540f200c0807000d410010191240d164840c1c1c5046807400c11004002c10000f8172468104074088207000083c43c0d00c1880040010a802c40e01c0142e080a000110030040f00078003404c515400300c101d0001d03585d0011102411200b500302d42c401c0b03580320f602d400c032905c0025610302703034142c450760042c40302080844030f082c56104280c0b8000c020503034541140c8825840227118a0700400c003800403417108480c0681100020603e41c03044d4100070307507680486042e9607009901c86401a0404600111000b9407031030360b400504200e2500032800012004a6074543e103800030034500c10b108102100302c1c100d0041e9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 379968615 1250 379967365 379967369
    0x180c04050307080c040f06080a0318050d05100509070f150507170d0f02031612020c030a110d0201060b040b0304051203090109030311040f030f0f08030a09060c0206071e09 75
    0xa03058481043e52408110740e60b03518003006622446c10065a801d40308050301c5040c0844072500020803080e0f0150710140c49545078481d00708592051100b020456884085a8441162181c0020451250005072a20445030301424820b8590084901002050002d0150b10b060392100da48d0030380c081c01c105009584c0c078420584001c010301140800c00260301c0f02c8002401c1d000703904c1c080a20541c1c4003c56140d08034402142c1c41140710410028041e800c0b449802c003002c0801070f00b2001850b284107200400e25581190301040009281c2010003440b00388144102c0a40050070f0000b4080315007490f1403091346004600030110081008400038050210420005003604a0100125500d00b00855120f011b0000d07010241c0110741071005101440042d0001c42d0111101148d0059886003180d94002003903003915401d41c0c03224541807918011071410703001075024010035100050051542d19000081c0e0ba141050b400564100710200440650006141122480a451107020709038003040281d841801076 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 379969865 1250 379968615 379968619
    0x30503190f0b030f070602070b0921010203071812080903010b090c040510050c10090206040b03070e13020909180f070305030703090e0106020c04090f0f0506011401020c180c0405 78
    0x110079155007114180d4400c0c805a2802e5041d80d9840321904880b40c0d461281c0e11502c0016480224204000840c060207080461802094103c400480e80e05541c40b00b004000b18070126540041800445c1c0d8003e00c110f44c8224803001d140c400e00d4906848e0248020f003180300941120700001e0000e0b080d030b40070b5100044070b01000b001039440c0e00b094150a0403d070098000c0724044c1d40c809035401012070240069480a10502d0010055079200e1284d20001d80350020040307801c024144000300740b1220f00d20103180f0a02c41e1355140040c0c502c0031400c103c40c400b410440451103e104011034030755501e828000540c8451000001b2501e0041000c07402c1c6025074803585000c1038002c62901100300600130009081041c082da58004005440d00d20024110b01c0a21840000d0b078071444010506060a4101559260040d810118001602d40341d0725042411490300701d649402c80340062051004020101c01701d000288002c04401c0000b10202d02e08004450180340c01900d0080003a80800e0307003404880c058440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 379971115 1250 379969865 379969871
    0x110607081605010c0c0b0c220b0a0906051602091503030a0309050105090c180403200c01230715060803070c0e280b012a020301200703050319 62
    0x307640038040100105242141c035542025941056284205c100b100015013100701c07403030301da22042008480750f48407a41026112842c0b40320405140045060b600050164052182e40c44d5841c0030001c1410b00542c110710140300042c018402c001c8080c0c0228006107a0546a61003a0707266880705107001c04240010b558107100015140b0304103075043d04403181c501c0c89600240015101d8560306511051071500c1141c2110242540c5101841c1c1d06084541107406420718044488003280781d003000d4002c0301c401100c075074080c50024445503444030000342c801c14103044000c4001c6140e16502c1d018410408041e00240c0004129402175140c0d62201c0300a150007022280d03140c141303240031003400f520307803040f0301c0003044800008604441500e191100114004908510054902441d000a21005281c24100642600c12240c0c01c075a4500c1006200b5440d0952884211a071040501b903030000c0216444240c41207100b00c01c20402c0c4000d4500345545070401c40c1e100d82d1810102c2c00c0c016418030f0045a0103003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 379972365 1250 379971115 379971127
    0x4030e13020901090e01031106130e01410609031002041d100303050f160507060302031005150414010c0609081c41040c06180b040311060708 62
    0x203000d5000b002030200030b0300c40c80b0076155211491036070b8800900c0064003c403e401040c66a91070b00c0d400414080ca09480c2503031003151201d2866081070b00903002281820320310a0f50070410001035101d01ca4003207455421802811281c424225241c10314000180a00c8000c2040c10071550107002c0040340d10040c0e50708644481d50b0f2404600c40800e0f020b110035140341420b0200b84a400d440c0c00c3c03031003075a0701a2203480c5003212031502d40c0c1da0355200c0d0540d0a40b07040d00f41d2501000170000c1c002440209281d50740540c403802c2000c03141050490a41c40700b031040881c2140340705001d15031404c1d07a049600d07080903c40300303840240050f28080c00e4408000e19881c502005481003000120180001a1000e9400002e0350080599034040fa804004018040302100c441c03043c040005038580100c90b4107443d06007003c0c1c442d070b1112a000d080d0556080b02c104a450000380209035000140300c0c1206017141c809102c0d54a0a00100c2c118480e0b4040039100c8060003d03000003a031500c50464010a9001c00c031159244 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 379973615 1250 379972365 379972399
    0x11404170c040b091005060f0f030a0b10030b0306010306021b0304060203070b010e040b06120c031b0f0a0302010c080d06030f060509011103100611010b03060f071101050415020304030e 81
    0x4540781006031003945410301c034440604240c00c10340d20a2180d0000540201e09003810000103400c2000f0f02042c02804004050711400104040c5004128032100402c4101a0104200c85000354070908001c26180c095007030501d41e0000307240360441381c0250b80180e40c2c03805540b0f4090100c070354140741121440001400110f4540c004001c204007400750b8240c000c6a6260a842c40d000501901c01615021040021407058603007010b0304e50369003410008a031680d0750f001001c2800e01e1072409604c0d07800800c85149000301e041c4500c0007a030b220022030b29201c00504543c0082c0914045901c0034011001c00314240104c0d00701a4802c1c0003842d00400c5d2510803100c0340c5840805080220340040c1c1135400c200051019464003800e07203005891003901c00110504003801203450103001c08009500390340f94468803810340c41c01e025003801001c40714082070323142c40c10301c5004e094045110101c091680c035000c00c01020540082000c080130345941000350350b0380c40d2803d00f2110194210b40d02a4018110700c0c0c40b500d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 379974865 1250 379973615 379973623
    0x9050307170d05152b1209030506010b0a1713020a0b0417010b031f0605040905010510080607020a0f1b0e0727060e06070c0e0402010e041a01140417 65
    0x941d14400103101c160b07100c0303805000021305184215006074800e00b08250491280c3d0142034090805240200b0301c8020740c5450b403d40c0024030440380825101070050080c0704041c004180034200d1089158940160118001d01d4103100304801d100d040c01500204909602c001c1d0748400720b68000b40109030483d01c3e842583d40551052060194000c280e40201201c0d1006005040700000001c011b4012240381d090720050b04108158000c100e1541c2e1032022506540da03214150445005800004051401506006c0802d02c1c607004101c0590103c010040d60680c001000c001060344214013884415261400070081724082da41003d503140c0c48400443c1c0e03010070a140600c103100540e580c040c542243c061412a14507509480e00b042038280704c2c1842014003e60708220310280c050800303454001d09072100320121009401c90040b0000440c20700c010b560740142041e220fa50b0440e0208900001501c440c1002d4887d680050b0600030802c06142c610014082903030014202038212242000884120a483e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 379976115 1250 379974865 379974877
    0xf0801050f06011d190503030408071406030f0a0906060504092010020a1103031b0703020a090203091b0301240807090903050a2a030f031a130905030717 67
    0x11810010005402d9031240481402d08030444454111041d0035009028a404020301d03841c5802e9100310001519440401c010300013002d112016000c00ca0a04504000d108150321180b88503035405d200340045941d50102042c0c0280354a03900240480c140d1030510007404691303118640c8645480c0340c0c0401d20442d11600c841c802d050700d04454a410100d003c001c500302d4822400300041c3d10030801200010901c0c00400f0151000038102c038180101300c061200b41894a040c0358016400c07102e02081181401800240036080d400c505505518040d1141c550301e0741c45001c140f042c0202608201c0880e242036000307003044226080c0b005e031188000c0819640350616445034483c01d1041140000f82c801c882c2c030641907055803580d46c0519000010340219200b0030780030100c038504607008807003610788804106240309680c440e803030b44e00e10449a22406403ca0b044044519003200004518100554a85140c001801e2010000007000195400d065145015000008250361100f4803425000c90002c009000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 379977365 1250 379976115 379976131
    0x3060908030f0601030501060507020d020d1b030b0603010209010509090a0f02160308130f12090b0a030e0c03070308040501030c0306090e07030203060a0c0c031101150f06020f01020301080d0e03070f080105 90
    0x182038544a0046041b02c10912071440091000c2c4141001072610b4000d02d0302c141d0000740007020080c01501c81c5000b81004401c8070b80040a2403008004110842040b580c2c000030480c021810b1214140028280d441130b107400c24070078290100029541e8a0b01c0d4400c0c2103603040d85800b1500c4a284038204180c0840407442a03000c038507030000280e0048410030031804c500d507000c180500c0c50103460351043c5c21f9048018541051003e0b4190100300303000c0c850094480040240e602003680441441000d0415031914140f0340660040310003400807800c0d80b0219821140c080c80c0004000403000c03421401000c0a411288a05081c4092610740700f4002515074142d034001c13800d0b03803504e49a4004c204125400c2600c5180880c004201c0040402d0017041e0500d40b2906031400418201c182c4024149562050b4001c4080700302c48080600c03042e50304004400e003035028007008503d5941800c01e419998800c5541d01010010410a550840d80f0248002c60007811090741c605800da4540c1c0510740130f003404940e595 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 379978615 1250 379977365 379977391
    0x60903170a020a020115031502030402130e1e06070c1202070b04090c14070b040602070204020c160e010602070b09060a11030c06220b271914030a0f0f03060306090803 73
    0x519034205409511080380d0303200e801440600232039491940a90802401a68440c06103c10720703090111034040c0900d050000006841031111400804170310070312845401500c0e03400b10080106494000030007568160304181e1030004030300083e908a00d070454a82120403281c001140000f9040903035004a038004040340c8545601c0740c5125504040c0d402845805030020551101180c0814040d5009084550014202501c0d000c10aa2414548000c0440d51501081d100070100200c41c0c1c9040418013601840c07000e409803d1401842240c00c1c01080c0010b8401c0200040e0003442a02505c0746d209030014000a40b616010304440c665114002242d1701c0d103490049032112007070031048407401d00e05283e0029280c0140e0711050003501e0400c1050034a403504a1614550140000003004070b5040d0503141c2d150444158130518121000b00c40c0720020311081e030b005100350149150000d4200f488000a8a00512112200e01c0c084028010a500180c9168034040801c4140420b0310003c40c45010700c04a96 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 379979865 1250 379978615 379978631
    0x809033f0a0c050306030a030c05240a0b01020606030c091003020301050906190c0f050319020f180a030b1602070b040e160914120307050d0f090602060f04060903170a020a0201 77
    0x15640f0780700890f111581074202c91802c00010307005002c21050795010703a003110400ca85041c03141800b41403481400648a0345242008800780ca43e0064035040d18080c400360005080c4440803c0d03071000c0a5250602c50380300c1d0b200040c0c20840054802d0001c40c0c009000b444141418483d071915403d05440c400e6401c009004c54100102c100e000307050840d19160b40300d180707400c000381c000c407020f0300042c0c03000010355801004039603440702d03500140107102d401d5120560340d682c441c100c0c0d007240701445840c2c900407101c001c070803c0490720050040e503000c554842000c0d03d10901190490602c0100c2d00080e952030808030b80410514203003030707a461107061403504003e00440c0581c0c0c00d4481180318881e80c0b480d203040c0c820005060605032800031a4000c0403040328100189a69001c0c20210344264100001c1c03a00750b900112950300c801000000c194a0000d40303014144162180c000c0301c00140090800d0703496240b41d60805101c2e035181c035101401100c20851070304045000c070000e944008a01d40040d800e01580c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 379981115 1250 379979865 379979867
    0x503030c0714070501051209010905010e0106090606030e07091812020c01110102070c14060904020c1b1503060118123207030f020303121509070809033f0a0c 69
    0x442134600c161125802d211180d280e007004014010000e00312035407a0703c4900d0008100340100741c1c2019114002040181c20420010304990740c90b4401c004140c10800c0e20300c03100601240d0901920700203080441c44031003c0303100c9000d046280354001c007038140c14814204c00590110310410010000d90b0b8441e60040d800c0c00300b40c00d03400340c104050000189180d04208210841c1b00101c2000c0015000364100000c00c0001012a0007404a100310384d045140c5000c0f510700c8150710148454001c640d100d80f1000b03098840c020900000301004d05000030f0091a10304082c40e1031000c40201080608680d025140e45441540210764880001f614111502d0706c041c148162802e419141540a004140c0fa034515103604050b009060f0f81a601404108881c000314058070100741d2054420700c80c00e0361082d00c503006100310460018030b580200401903044c4001c02c48080100e800710216002503448410390490140040c0040d1032030164082c080c1507080d0300069059582a01c10000014200700300200010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 379982365 1250 379981115 379981123
    0x1090905100911010e220f050901021908070309020a06050a120b030a230618190c090f0b03010c0e030f0105070f140c100902030c0109030314160503030c0714 69
    0x300c0140440070f482c42c002c169511941040702190710091030203120510070385042011211040c910810340351200e40450280c1c0c42405007542242e00a0021454202c070b03999030f680094040e07501c6808120281000c113028500c40e400418100f0380042900074650350720303540074000398000440100440c82c180c45001003043c031032049200d41400513000d000f542c0c8072030382d03840d2540010884440500c00c03441e40d0800c17030300c00c1008000e1048204400072a82400000c030303080d00c0c0241c0020341c41c807101a0722404030300161180100d8030031152100350205107100e0b190840b1002d03000c5510850b0705076280c41003100c0e40e5076000b0510182040150141c0d070000704c4c1c0809803400d075001140c2300d402094031054030311000ca1040c01780341c000615802c450307418844618600c5091049001d200040e103a21001030400b5840c0500c4040d110355400d080002509203180d601a09a08080b10007010b040f40205103c001000c4002401c540e4a43c08816250f8919290504e031002e90032840040d50032404422081c044500c00003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 379983615 1250 379982365 379982381
    0x1201030605061e060a0512010807061205091506030c030604080a180828050d020303040606060e090c1c2f120402090414060a0504031d1c0206120109090510 68
    0x1c00b5001000350005021042d882540175404010041001c0c0720841c1c844139815020f8824036001c2e106982c5071242c010071001d10300e03600c034501e6490f2009211031110300144074094181d0441c0424441d90f0b514000a00302100180f80d40d1701402903a080100708152100101281101c3d5242c2d00005650344007030386495a61401480b400354044000c0003046d20700d129000c0c0716141c24002c0081c000d030299803272a081150002e803400c0503920100c2031008000c0d8a001e040040c201e18a0070120214803000051400040903210310341ca840000b41c05a00990b0018400b00c245988103414441124908241804040f4081001102c00350340004201d0300c0600c0c07002c60301c04012496124086880316009c21069010240003200c259000700101ca0f0381e490180141c1d40304001c01032000440386801e08000d00841064252401d807440b40010b8100310783d580090100e220b401c2c040000800008500c0420098445e215801040543c0c180002400c03241b00c5d040400214032900c2500c0900192020381825200e450b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 379984865 1250 379983615 379983649
    0x50610060e0d0602030411061201030302060a0b0d0b1b04080f0c040908030c181002030d050703200d020d0501080703060608010c052d0d0603021f0f050c0c0402120103060506 76
    0x8400b150000c24940d4002c0e42e0040d004041c10391028048030001402648403424050210318800010414580c0500c90f1540c02424900148141066070000546003610001c00a040c4c050361008a40d480346000000c0c05500d20500c0203079a52034441c01042d82c1c490803949001150f1040c01a40310160405000390720403683d0180302c55080d41c44040900c4403e401003000740f0b00c1002a020a803000b50359030011128400b001383c020350b50711003030031108400392840204154107060500c402101d803c03017140b040d04022900d44c902e02d511007094920800182c0f040842800515040200104080001080c083c089071302c5a503080003071507070700c03403031103007030305c00c0204103d0120342c003400414400c00d20b03925000c2d4807841c1c441f003103800f0500d0308001401c550800128520708543e100810320031402c0c0300001c2000d00c0164001e103c0440f0340d00e14004c1c480380c0501030b8107007002000306d00040013040802060029090040055440f1500600d040e902c280091100752422410400840c000e0f0511201d0f6000d01a00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 379986115 1250 379984865 379984879
    0x1060e06061206131104060c1b030b0612030702091602060709050303091c02030a14070b04050d03050a11060103061b0c020f04021305150a0e01050310031716050610060e 74
    0x2d1001003000c2082c180001e40f03080c5172103807107030341604004078001c04c05805a52070741c054601d01c600f040c8101040d1001120b4034540000018000700b441d025103a1b50010040701c2031451b0019a1008070308502070180b00940003a01c02c4107000804002c049500c0b0b0100381a421140039940c0c03400203c92980f041c2c854182c01d80c00c100325100031401c2808481255030816110030034035040e5640441d2400324007035401d89614619240b00f40441c501406080010b1030320950840c1070508090026402d0051001d0050500600058904000b8064140428584990b134203445096a4030f04010001d00520310000c5070b041c1101206a2055018010424106401402075100c8080742d50a03c4000e42c400c0c00c60803440240300703100282c00d42d0b4502c543d0b1150030003d4510385d03c4046404002c1c3c00340b243e04881030f0511000707108110603062071142000490750000340035120001015500d929521503550100e441e4070030300e028034052050025600340540484014005000c2d03850300101c5104c4d00320282c8941c0b04103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 379987365 1250 379986115 379986121
    0xd060503240121080a0c0c090e06010e04050a0c031202150103080316030b03010c051b0102040513050a02070204090b070e122a1f0e09010323010b03070801060e060612 73
    0xc622a09007824008804000360518510340b6021044e070003d090103170000b08400d0070355081118003080500104a030700000e001101501200d9606c640c8140540e0401041d4140010f0901001300041562160010000110b00c0d4503401d01908482c01d85090708003601c144900404141c1d0900426412681c001c2000c60030341e201d848501041a0041c0b690b42c00b010344030300c01203465039400e2080b160b2010a03070721001d039102c0001d03d203011103e00000c00340005910600c000c000c41d407a88044660041c10304031001815588078090307800203002d026800785d00f1038a42710f049030400000b240424090b4580740c40343c04850008004104990a5a404a44283d045041410480d0070401008000350850740c01c0810403403011404a4513960207404c40128a50200018100440d004a200c4d90221825208610380358155200c024140903081d140c80d09400d060020030812031000c1d03001500c424802410341c0c0500759110207c42c040d012902959500751454004642c023860041c046409100c00d40c0c0310742000d50703 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 379988615 1250 379987365 379987379
    0x1406100e0601171806090d020606011101150605040509091c0e040b1005120a0e0a111815041d0d0806210105010e070507170f07080d0605032401 63
    0x2200140c401c9041c070400d448203051415619155038400d8100003103c1c0308054040d02d41928003c03020300b810025070402e0383c8200d0300c0c030f50100703c9039401202030802c01c3e007003a000003c550040409500302848141e2800c80406c006038030000410444004a52403466134132040c80b819220110041c40c1101d0002c51000303100d04a001e841c071310f02c510400401c009440d8048201145007660103408810000d07400041c1000f01017620b140c60b50300040c81c404c0820001c0740d190f15590340c0d8580c03ba40a1f149004078100381c00070b6562410700745030350707000c6008071455801d0002e100d000c0780f151404031768440c50412642012600e0858000c800000980e0001c0254024400e070035100e103500a0101500007900082c100c8001f45d8901c103081031040790380000079566143c0b141d0044a200090a001c007000010400c51000c10401120302130740105d40d130036640d600c4200e080000c2c403e02c00c55600400200c1c011801c081c800015910442c00c5800c103800341d40c8003003480111403100c0790034540107540c540c942c900184120 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 379989865 1250 379988615 379988639
    0x10807030f0e0604060903080106090602060a0f0f0e0a05010506010c02010503180f030a050a0906080405100506190902070b15031e1207060b0a05120d080406060e0112140610 76
    0x8510240c00024410940a400320f0078408111002e4032020748030a0000c0800d607000f03403820b005001520f1326184043c02e000f802925000701400c05020f40d902c3d50070101e0300e00380d035521074102c5080d00c0c0e03000c00c1145075409155441d0000c2c40c406451651800c40000e42035401130800c18003c1d07905940d03241ca540e490715548030b100e0081519584691007000070111310b1040800c001c01e082181a143e96482c2d0344000c0c0b00504070201500203100b0030a0950500001400004107810115461580810300b81d55640120f11b0020760400d1450303049550f4900001d030200c4603402819110700802004c84a66140c580160705198144071450301684500d83c0c5910b0107548416245260074800d00349c500302400c2c100050210f400c03084040d0f40c5160340e03600c825102e10342a203050000700002c0c6d4099806100420301d10f41c46a405005035004e00c140400014200111a4031031009054556201501c95071241c0074083c0050f0140e908171100440080104144480051403600c078180c0358a400070441d04004e103032074038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 379991115 1250 379989865 379989881
    0xf0216061d010501030308010e07031802040c020a020a0b12060904031e020a0204060b0d0c03050708180708030a021e0106050f0d061e0506040f0b0f2e23030601080703 73
    0x207034061030305052612840a0103201d000798001e55814805506085882d501d02c000a40300030141071400340809000c0f07038001441411103404035030000340c04003412001e81c1400807504000354042114032000c1403217803140000d007843e0941010340c184075540d0ba100b4030028180c160380240102e1040c1c030380d000c044200010903d020300303c00d1064038030b500007560200301510042d030030465500700f001c900701a880b0118414101e4150755440c041c80b05040c00480600700d82c40c054150540d1815500050a04120400860004150700030807245c2c1c6045015000351520464009824081c1d8500c05090080c101402241c040c0c99004089440c001568420006030f01040b10007120b072182c4603908000300c4203c00200d000080343d08000816140b030140c080000321940a04404000f5150020840703d98840c205071101d00c00d011b85072142007501140032014280101c000081130180b0031500005842d51021100380301d2941c041c4010243d0703503590340e014243d010440f130a0b4000741d12100003407421882600080e207 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 379992365 1250 379991115 379991141
    0xe0f12071502070303060302010e031614240408150412031815061a13050f030a0f061a010c1a040201180e150306090a0f050715080405010f021606 64
    0x6107140a00c025016038000e03a0b425404203070354040400039540c001c1d4120f0b0319080210090f00059110041007004c002d0350340181e81554007002000d81c0a51100c4125880c881821030380403880e50b00c0b41100300b030560b115000b080c6180c011400d40900f90f0602c0e072117250050b68000011403501103c903d04400500c14400b5880c08500b402d240780010400840b001140c401039498003007240b03402c080c80d00304442e1423540e00c00d0aa0790704001d660090b6135050a100140d5500321403180003c0107000002c3d00c0d15098080281030307040072115100412686520240c020700208103444ea0303440d403060054421004914000e455560303c402000800710007585603980c8144141001a1424401a043e4801c450740360481c00000d1201c03000e0200f600c2c43c0b070b4110b9010100450041c105031500c0c9a0304c0d51180031340940204034117031030240c0342e041201c01c0c01010050000400350315a0000100c0000345400c4043c0d9050b240b075460402c80868a0a07207008031402118120305040003245150380340802031158465203c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 379993615 1250 379992365 379992383
    0x905101505091f05060315010509030c060408030712030203043801060201020406090f080705012102070818190b07080f0c01020a17060a030f110909060a0e0f1207 71
    0x1042940d180704070180283c0c0074502c01c1500c030329084002040d085064000c82d100702018010045580d10310310300556120001e103070168480b00da0314040303031130515100342866010202080104900ca400005414454092108550400d0748034405404a101c00c0d6009018041041800f5101c2c00e6200c603141c5226148c1042c0700d480805140c04440440420f80021300180d400150421040e41d1016280001e0014800c07481c41742c1d0316000302c482d80d0700400d214443c180302d1841100140b0344020106001e080d10740020965662119207000d00640e480803880540c5550004900912030030844d001c040d4000981d400035000f1410a00324440941086104443c40a01000304080c003d4080002e4058018404c00150b102d210090000d4980b030345845800c88900c04440c20008250340b49444141101d03000301c0002c903440f0450030400e1514111100a80d04050500300b405056440001c94511500d080041040000806a00d40d80c940c40101c1581b0340a80c0581145120521802e0017400342c07905c111030300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 379994865 1250 379993615 379993619
    0x1b0108041403070f0605062803030e0a03050316030f03090b0403080c160c030b0c0c100b060c0307050d0908030c12210106020c03060f07021b010306120c05120109051015 74
    0x6060f2150307031040b08844080d00c5805004448c00d00103070040403812000c23172040184020328168100c0503010302c0007408104503202418259103c9454010165401805032603881d4107200000910114911046002131501600782150034482d214804925510000d55941031710780b91022150b5800151038900280c0e0104a00070b2500c0c44074000460702c51042000200892035170604c0005c0c1c90000784502c403404801c010306240ba81000c5240e000c845c2a184000503860b902601051041c001c00d400b0401d284000100c11041c480d0016030450064801e6881d06256030f01d1380f03c2c03913440e8002d5442071285030388000d14210000f20010702810505200c801d80b4407132510380c40049061030b003082c7d0100c405030700003074100207040c2801c4c004d441e4010703080e8203a18210304010f01700030b54802c00072046c0001c5840820100c6060380c821b4001400404000d4021418000c0c18248545410080c0c13250070711580100038840d114030703010702502000d141c000c1e0203003401a24264001c0d0141c810b1400c0a20007103202400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 379996115 1250 379994865 379994873
    0x602190804121103190201020709111c0e0d02011a060319060312080705070c180e03030a06170d0e130b060d020703170912070804090501171b010804140307 68
    0x95041181c0960451000712080b0b0b03044c1400c3c205880702030840100628101e0001d81d80000e030840490380e42c040d0025048a9007150044207016164a4050603211950040c4001030300d9001900c01038030900c20345005100c82c0d41c0583c00c80c0c988010714040348080e519941420f1030020061648601d0204501c101c00d40402e03006411102a600219005020000c91100c9550701044250344030140d400c29910785411611030340a0240c440c0704804c842a03400104a40c1d0044607000b8100c013948250417641c43c1d04111641c040607141c240944010340d01501c116071808900001e2070010740f256078684106018000d002d01000703c9140f00c4041240341c40b040305042548442d07004140c0a052410016200c400070315008081d880c00c610b004072136505200600041c0c640100f1603007001402d0000c115075402d440e00d005e001a00547d4080049070b07203424000905011400310030034606110700152490320808141000c5503003000b003880d600061781f20700058000340421200d502c4080b002c0742128100201555 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 379997365 1250 379996115 379996139
    0xa03050709151403060f0405030d0504030e01020c0a140d03050c0303090105150f0a061d09100306061e03030e0604030b07180801060812070218041a010608010602190804 74
    0x100c41d1010903a5420700d4a44402e0445010000d02407080d81003202c415032100090340c902c80607154036a904016408101040010000c8980c6001d810300188140e18180c10050444104082070901600030440c0c191010b14228541806455041105c134203211100001e10858071640760044060010030401c0e0984c0c488200041d500c1000e60000124091400080800c400001e0402090150300e800700070120550704c1c42c00c808150340f204c0c54003008800120801f80220085048078940182d40a0700303202812000803202c1f025203004482c1840181c1e9a02c024214450078240410b880014070342091000034481d440c1006200310003804d00341082e8480d2208031440200740ea045e004902d01007000c3d0b0090b41108061001006110000c0081d00c0c84c0288183e01da0141f80c0f1484010200040c2036801c40d83c0c1c409032b00e40e9581b0360428074065854246017200e4000701c080100114442e00c2e4000144080c4600039040c181d50055001d131031480c02c4102140720840c9c2107441210000d0382480041811343c610702d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 379998615 1250 379997365 379997369
    0x20309090f07030c11030703030b0a0f030b060f03070608041b3605060d030c0f0803090f060a0504020a0905090c130b12070506030f0a0e1903020f0c010801140a030507 73
    0x111a00c001d0500d0b00d4041c0840d07651400c01010301807504801c0c01706880200980b02c4158050401007042604400054604189500250400c40340d004020080c4005094214414541954800c5154810604143e07540c041441241d0010380d035000001c001961200812002c2c055445045440d01d450f801300d0b54629665100b15200c0031103103003020310541c04586900c0c1070403007100e10070040d034140180402d41104003c2c1c070160910000a02da00204041040c6060742140c00c0344025460b414483e409a455606560050035a44501c00c0822489003052040c180a6680207240103546031424503da00580300043c011807981c000d0280d0300015803100614800c0074822400d00141c070000d42c80402080d000c00d81440002c541c0980705c280415223420049a422078070750900a1400d41d40e2a001740050004608002240d0145000c0f000000c0007140924a03224801d400392964880321040055843c050041b40c24001240c0c4070041000f91000c00d01442481000307003d00c034255032261600b6280122079 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 379999865 1250 379998615 379998631
    0xc100c02060d14061f031505091f0e060102030a0305130507031511190509030721020a140102060a0c111606090b040b0f0906070f0b010603060b0a020601120302030909 73
    0x54030400c00d80400e02c4241540c0200c2c129521020100014014403403811683c54501c141547d034499100c41c2c00c1003e880350010b0034010007442c141d1820694172800c81c00380b03003030164921107041400300710700405101061042d1010780c029404c003a2500d0b0201c014140241021030590140048400400c4081c80200003a44c042c59850140c800d45846c01c07000c6501614103030030ac07403205200c4441e0060304c004914209114510b400d50700d80303000390002030074003400e5400703100a02c4c0c0d0b149030721042789d0021413007145072802111501000e82c0c1d81e11601442c1c403500c040706801030304144006011101580d00110100c10b0038a402c00b01210b140703444616000305145c81010110241200b0403009a202c00030001030020001030030b040c24588007001405000d81b00e10044549008500040b440e21944180c4914030b0b0000c41c0d100b00c2d040301341840341242c00280110f800003401e14801150410300c800c215019100c17240e000f803c050307280094100d8000004807003201180020071504070700d030b03507409030440c060204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 380001115 1250 379999865 379999871
    0x10c0c03050f2a0901151110051006080c0d0f0b0a0305030910090302310614090a05130204020904060911030a0c08011d07031b0e0312030105030c100c02060d 69
    0x808440c0926403424075122025a0b044105810f42503120b00c0c40d01411130328417601212403085420000d5409440d80d60107410705100e900008601c21015400c002e004000e0f40e00f0300c2d40d42d030741c852808540c481d030304464858001c1d2080100f040a18480d41c40003e42c0400c044000604400c03000005800094550054407281c1c00818252000d02d4084034034001d005840c00c295160619650200e000a540d00c204000d0f14440c40c0c190ba030881c0345061684042c50301522080100a4440b100508085928405c0a00070042c140010341d0400d0b9501c11580680654500001111100d500304806940500300d5103400c02d4950400040e10b554a000700c101c00006030a8068803403404607241022108640c50010801c440b910040243c090622412a840c45c007840d58401103a442c400250080e01c086c00445d030103c054151010f0445900c40356240c0c41b0318044056402404640d01103c0799804203000e01c96060b08906100010b6151800a002040707681c0e050810207015250009005a00018000000291 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 380002365 1250 380001115 380001133
    0x4050705120a020f03030a0f14210a0507030e1b060909010e2202090703020a170907081905030a27030602030a0501060503160e0d060905030c1c0e010c0c03050f 70
    0x1518501415013000241c008506294116100800004401505000348038144c4908104010302c803080b0b071356100c896101081c3c1c0e540e00d00c4105801000484503030440c140340001080d005031290284864261181000344241a21a101c085010b101c2d01c0303c0b00c0d8020010842140c968540c2c2d41050300810649240c249103180009101812244114860b050048401c00c0d003001030f0381e0311aa071034000416160068980320758110036a100030040b03a44a00e42e1010500700542e13000d000a0708015035070620161001c01111003400c503400003242600a000307800500082c821f20b44500c1100001c265280c40305800700325000034403040040c80307420075200942c002080224040160080600500fa00d2400501d507240c075003c00c040c503409000000e0100003000702e250520f640c0e010800b0f6a91030300210100b0002845180039680c1c1d5019407081441c5004c1c038541580402904a0045010324003a03d41007003030481403004458100503810100c508410000001c00403c0d810008d5a604884000042c40100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 380003615 1250 380002365 380002369
    0x10804021323010f17060403030515030a0f06060602010608150a1b02010608060c0906070b0403050d1109030c030705180603120a050c0717070b070515131b15050304050705120a02 78
    0x240780ca8120258007045205e0010311408001240d03035009805180c005030580765a01507c550049076003145c1d038544270b0700180780c0134490b40300902c1c0011071040500300310b40c903a9068103034280d55141c41011201d4200d49140702400300c07004d440981c80310443c1790001e4101450004500042151403031000180e645500601c00410b04000c0140c00a00054446c1e040c00803600000d601c138407520400030803d070917030000306003003501440c107070ba000c005051401c1c4212020300e04c2c18901c80d00000b080d90b00c40d206031110b01003542004070b0030606aa10140c0b02c580081100900b6015039403016080381d41620582d48a00c50240e072100242c2401c3d2416954203556003100c0c2d840030b1074201c007034100312186140020407c04100d80024220300311014a0004d9403140e44505020741451036030800341c50030444038001c10042c1c1c6070061000104a12030750cc4080d001c4800810f0004840e000d0189180c0811824194840300c0d00500c041c40d40035109400701c03424252924080344800d403419840704010741c018901d8070700718 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 380004865 1250 380003615 380003639
    0x80a110d2108011e0501050a2c033310030c09091101020105011413090b0f01080706170403080405190b1b07120e12010501080615010e01080402132301 66
    0x50810032569030300b405008820134040384481c840c0e503041c07100c001032246850b4040e80e00c04035080030290040036045580500961280704031700310f407486030180410140c02030f04400d45118240203403401d540d1107003450035a01190940054001307080714004000010005600b0800803024000c00c040108001e006072804101c211042e0043d076040d07904040050010303600051400010040469844040c89203038501e4900500030400094120a0402d0400c011b0b11100c01c0458100c0d070040b403c5544040c0e6520b4200d45131890742e40540d039243c03052400700300400c0c403503a0115001400349080e5002020500b131844040710b5005001c5419045444c01c10000c021100501d08048041102c6640782007895502d450082d200b2540384418008001c00d4140785441d1101e683c1a0307500014000c01195031150407490f0780e03040840300c2c54100504132481d4080340d440b0b40000b100c04001030311285d2050f00c841d420400601d804050a40d409542d43c02281c00000c404280c9203620840c03140d4801031541426041004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 380006115 1250 380004865 380004869
    0x12060103151b08310c080f03040303050405060a170a060614041818120302070c0b0f0d0c02010e070e0612071503051504061e050a080a110d210801 64
    0x1826000c842c0540ea1541c001c444258028141841e41484c00f207054151089800664074070f0342110030309083c2e0b40800510f06155000d481d02c20b0101d8200d000d11101d866502e00c0b483c0401400034038240001c220701d0800d88040c04028000c3cac188003000d540b254030b545c5c90898044030800c410076110101000b41581201ea90380343c800450764540e20b4103003009201c4c0502d1820041105032140c3d40c070007240b031141c4211210f40c0082d034450580a000c541c0d80c140100070750469202651151413803240000c2d401c20b510b007140c070100e103030362a01400c000522105c1c0005042c0060403206554a6100d0b55803098014041c0c000034003c0e640c240340d035a040c0b0000380700407400e000d044da00450707000704001d0221003c00201c400d1511018500411207a42c2c070800f00c0c2d01c601c0c00e402d840ea0454141000416000c0d60786115100307440307240c40314840645c0e4500400c04080d1203481902c1366500f240e514100881c10b8010318204000000c1e056102c501055595a000711149103400c01800103030712418200d8590004003240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 380007365 1250 380006115 380006141
    0x310140a0e07060219060e0a1a070315150201060e092b08041407180605100f0806060901030605030d09180204050a0608091e03031e01030b01050402091206010315 71
    0x82414548043c3d540c050200c0703045c034000642049442082040d8001c100c80680e40015900b003100507103000709104003030303990b01c2101150325400201280d100740303e850016a0904106540c841c6010f10860303c960103812118119521504086911450295680d006080b000000e10b0000340304103080000c03c4441144419400b0141c13062003011368004405500550040d040190340d001642d2454505400c40d03221694220304880d6225810225030300040407241c09480b80c2c40350003c1c4200c1265441828140d0a000c1001d82c0c000c01c04a051442c050103207008107040004800b42c03210006490f00c0256004e160016112010070310418070391040380052030b0745599095040074203000000f18030902130b0280000b080554800511050820005001d01a01c081c4c002c2d0702401d80c20301d0951300c07030340304403842c21800501e1054008402c3c042d0408904894000e0601c1a082e424101040f019500410007254804454003103501c040a051060600a510030300d491400419501e00c0103040d42c03044044c05c2c6d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 380008615 1250 380007365 380007373
    0x6030203010b090f0a15020102030f07080601020607080a1d1b010c0803010506090d02060307020a050c0d15020a0507051b1504030201020a020f04020409060e040b010807080703110310140a0e 83
    0xb000240540030384518400403501c1d07510710780a040214040c00402c1c1d0020302d15042c2c1040305203145070107500946c0102c4104821271610b503200d0384203a949400548025005034400e80000f082703944201009508032801c04004165059002c074408407080f074200301a006500000c41c10542c4c0340c48818030004100086c04c2104245049440710707000c90005204960042c58002040519580ca04030038001d200e9004100b00e85904091100a47c0e942c0780c0d01080381d080c0725800480361a85000c404640b401640007901c4080008991458000394102101100a11a0034000180003420621400c07403000a591250281c28020320100070344a01c0c0071080d105400070800050025076804116404003540666082160442100114000b4425540075401c15482d004001c85c9041452645070b020340d01a180400d4942d0700c07040d02903202c0000c2d10518901d5071120302d0410014040100320b54130980010140c600c1e90040312625000d4848070f858441d10304041e0030400c520304042d0b11070401410050f070024 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 380009865 1250 380008615 380008619
    0x211006090b0a0311040305060702060c131403030918090d0309080702040504020d0506010b0a020c09010503060103020d0507090203192a030f0e03070f02120109030203041802160510060603020301 85
    0x1a000c40c0c064003070300890700340c00101d01800342d01035081000c1e48941611565038aa640c0c0c00d0a0345c455a098603100f005003d80713008030b213141031081c1c10369010804010400700820b01e4501c2d0004000d080300300d2a40c060000748001c0c0315941d00c0c1041d03000c0c00e030b184035008952450084d4100707050003946102e000034140b83c0b0749088003003030200003038a0980780e040d540007810340c441e0300024890764200341000300703a40310b07440000c10003c4402d8090100309090303400710703501013008400300104081c0074000c41e5050b520100041000d4642004420100c5009d8015a000c1507200c000c65410390303200302c5a1100181358410004203200791440b5510040c0c4241034299183e003402d91884071812200c0c80114101925500400114484c6901032070b1a06d00c203404803070b41c42203d407500c500101d541e2141648a00c0c1d200b448030031400c03018014265a15030607400755207001d050010401c41d481c541c070038960300b5035401c1c0001c00a0b0601255400c00580c06940141203030301d038241c000001e5604580003072080500600c01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 380011115 1250 380009865 380009867
    0x1206041a18060a020f0c0f100b011d040506150d0501180504051b0402040e041104140f220f0b0907090e0309040c1e03050405070504020f1c06050303211006 68
    0x50a40c110b0090030001d80d0390100130b012a0060f004801d030000c001d009400c070110204800207a0f48c42c0a071501074050084030008030040d2180100344424424511142480d100c543c501540540d911080051540310703d81011003064070f10740c00c00101c001e18550b81c1c00c010b001e003580c003030340c07441c8000e400700c00522083ca0980d59507601c444a4000f9a220032000300b08009481c0c0c0d40c1e0301500c01600e04618030610030301c0c0030b05009200440b1060450f010340e10703102c03031250b40341c160380b28441c821160044111260784485807014284005c142252250442c14a801c000159500810302d4549025142102007414804812420710395550300c00101c02e440c01090300c0742c210010040c0c500c07900302201c0010703403401264415180f50384484514562201703040800407030700d6015841540150b02036070490b030301e40e40c0b40c2040c48200d10a803c40040392400030b100f82010010b80c1c032008240310100400c049a1140d641c004a4510b401c0003024195081c2070380e035010002e07980c0c103148562041a40c03040344d82841c54058 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 380012365 1250 380011115 380011123
    0x527030c0906030c0f011b08030f01050d0b01030803190606020c0301110c0a030513091b0f03020a0531121a04020a0510020309030601061d03060f13021206041a18 71
    0x4c0110300484590068413180e07801190345800c2e407031700d080400c1001c021902e4405882c0d4000c5803981e403d0b021403400415182400604422400c0d03000d02d204e0b620307900756201d890181c0c10080003180e8035040c40650246d050814011403009109940041c410300002d07204142c2990501444e5000c1e201003400307031410301c1e1000070b043da1a042e05810101d66501e418914809141c1194211440c0c150034011203420900c51f044481000300407681c0c0b15001510030b030f42c0c11800e03071040e02445000100e09000d400000301c8a441c5d40703035000c01166180d0034220151070b282441d80316550f010410302c1c05031444000c140208800040c60840008190385641d29060f8001a050780e280c0c0100c82c0542280c1c038000c2700d000e0003002190300034807008048034a00e69440e0001030041200e55200c00007085400809212401c001821602504005440000301d6440c0750140001402084041c1c1c0c0c0819000a041c41a40c020300200740618040e90281d54075407400391070b0b814070318005400e103071b82d4030064003480c500c4000c045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 380013615 1250 380012365 380012383
    0x902060901110c0901170706050301062a0b011512060b180303040f03210503240310140402040c02030a0e0d06140f090709060807150527030c090603 65
    0x1003003030755001e00c00c4030b5050703d0850b40c001d02d2a008800311001241c000390f090030350680210f03044d00f01d0709459203402d001c039a0ba020a21580b004200d107000e40e611040d402c2e80d054000a4138803888024507148984030644607040c203910210903010081055800300740c1c8046000755010314840203003c168600140c54230a842131000080c03603603c42c004012800d0360248211001000c2428005400340d0700c03818800801c040e69541b590760480780d1071046d0303001400743d0306032846901c00c070808130b05502e03040d40342d41d1b404201c003507400c3d44c03501420074125100000c1e8800d042ca04003110024040b5403404d481403000b11400c003032a640c195402800080c080580c00031000d0200c00054441041c600b00300c2c42e001d0054549260f004201c601071004100c0307400040b075004d52040c90136800312000966110b036410125501d41c0203c035900c1e000180c0034880c040e00d81c814644026240d203001c51400733107003960441d400da4911031600c00345450302c0706172180c615003005015010202150301d131805060a40009950b04160 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 380014865 1250 380013615 380013617
    0x20a02040207060608070f090b040506091503010f060611070503060c041e120b0901060e0c040504110903070303020706020105010617150414100603050c070201022107151a040902060901 81
    0x700e2400700300103031300701030020b24040342224030642e103810005480720018041c020241d45050009102403815000305c80c000c00c40038003d041251181b10345030040500c21050a0742641d240c1040d140d00c180c1612407200144500c1e5964103100881520a9003030840c2584204c1c0f04e80d001005001924110758100d800312480503045d11a10300300014500820f5980d40d1208800b1120841c0c00d80920450403d880e1007204958020070189890702c07495000307030400380e41206506009000622086c10254441c103400c00d845e0240a05003003803600041d1400c0031b1500101d00680000f40f0070005903809024003070240c0f84a042ca06600f620400d100562944020300350075101c204680c14a80079100c130750000c00c841c103203800403440d680f4013000d10180345811072107013100003460007001070751404d4144266100142d0590241000c2441d0300220350b810190480c48803410001002580d0002c0c02800035252052266500480da0315a9541d02e15a034000821140b4006c030705041e049d5005a84030411100d411f402 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 380016115 1250 380014865 380014867
    0x307080714040b120a06030507050f040b09040c030b0f190207080910080117030301081c1b050a210210020d06050910080d0f090e222d0201020a020402 66
    0x29400044402141ea07014442032044006804207102e907642c002044101e1140c00710102c9a2100071031017040350050320000e002c2d1380000506100700d1500d1036902d0074505004001003804102900090469207040c4c50480300058021000c004010822621541c842034031408500c00785040742d140910301a40b00d000340d103201e600207182400c124201d01500c8821a0141104a543e540d00d0000b610f401801c0c0925010120b03030350101d0307681c0711001049905880841004e420400c100d00407045260521707403440400c0c01700e8504010b002c124026003080f0900e010304000c103041d408a040184114064528107441e0016030b040c10118240c00241d00740300c50380f02040050341d442c1441e0000c4020401500055408512141409511205d044514056070b040307405981442001c1007050b20303604108841d403800b0544520701040100c040c000242d42c40003000040800710118003944a080584480c42210384541010f00700b24410a2000c0c3c2c4e00c59041007001c02d200701d000b01d400217591030490441c020300c5160 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 380017365 1250 380016115 380016121
    0x70b0402061c0c0e0a0b070201051803070b07150507080f0f04170a0207050a0e2a1b0610060503091203250804031d060307120902060414030f010e03030708 68
    0x1030980486a110910750720100280e4440311401460b6881c1c0d12916445403aa8060101d4643d00c0241292511f130743c140c68503890503102a4400c0c18500c03440f8462036160064600025440022600030030140e0720405000040702001e40022003100d6010f8100d004001c43d40d410041862120242140c00000b43c600080f0a030750360341342144a001c010182d071000300f28089501d000d80c9400058507420b403a8102d4141021644a4a0001103144120741c03008880e600002030300d03408210038445a00302c10800c0f1500e8580b40751041088105d40b00610042001d50020003005900400c0c50100c0024203003030300d4094034608160355141da55130302300044040c0300440000401c044621542c0d4411500350704100381001e0902e54800a45116000c50307094020448841182e031414040c1070740464080350003040141152500b00086032444d01002d81d2a080a907034688036009070b640c04010300014000080c40c0c0300300d940760106250074600351f0303080d03402240c1c10540b219003101c0c000b2084e26031042903490410250f90b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 380018615 1250 380017365 380017387
    0xa0906090905011404150f06170901020903030f130503030f0405271609080d02030301030b010603090c06032d06090c05130303030e100e010b0103060602030a080c0a0905031f0c0203070b040206 84
    0x440c10b0344103101d4100903040019000c1d402c20049d500c82d000041040480d0340d070301c1c0b4042c0d0070307446120380341e5074550000c1115125a600c1540030b048140c84174110010525111000b0030b256038001c00e075948203001e000c034080159141c10400340c0d1110702c1c1d40c1500340e03c15504100d040803556002d060160201c4a4418158245c0d229800040080020340d04460344140c090303030065165031013030105a8002904030004030b91180203014868052368001c40300d0746c0030352920030308600a04040860820070f4000d01c140101c0040580108021102c030101d00051281c0b800b00a08126906e032108842444802d001981c91001c021240c142202d405040200b0f5242c6143d00c2a410100180e50b400582c89c5041d084880d100360541c00244c0918080e2420403405446810603030360f82c0102da032a04001aa0803000030180440a0040d20b5019014142810707156120300009080559102e41000102c00d40d048078900710480703004003040f090f5680050340c81e081160f103c000c1c40810080000c2d0041d5800aa01c445231 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 380019865 1250 380018615 380018651
    0x50702010903141005040f1b0f05010513090e1b03070b070b09030717030a0b09010503030703030e0f032206050f07080a0215012702131e08030a0906090905011404 71
    0xc14491802008a4589803501038047c07034030302400b43ca840b1051011740042c404845070034010b07514403c0703558229a151000466140d40000320075a044048194001034102c01c030301405d50b0b1288100090140e041c440003030700d82d03030b80c0002e003006200354041d0808200400c400d00c00c40d0401074200d29040007031350316040c135649107120b00c050042010100740c2e0781c40965008440954041c4590307000070b0249040003420040d92620a01a007a403503001001450006801b035030003154024001426504041142024181903820100c1e922914449074540c07486006401041074014200c0c904245041c4450070b00e030b980351400703450001418007800141550740039008001c24440c602d00780d8070030303c410740e120007113000e81e080b10b444c1c054040b441b403242d2004d03624894000c0d56006508400502211072a00314414020002400c254085401800011500e50001d01c0140324032a456182c40402d0b5182c00d4000300300106d103500805d0518544030050084502249903c401030100302d80c0410300d40440c0484403a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 380021115 1250 380019865 380019883
    0xf06080610030b060d03080a090204240311101b06110f0901020609060f15060d0e031c1802040b0616030e0102010b0303030108060103080a0513080a1205070201090314 73
    0x95110303100801c04034074103980034101540c1c4560301c040425150780d818402446081e52009003c01c08910000e0419249503000380720307607070006101243c00c0441c444460300503d0100c070080c0300541825000d1040c400005070200c40a0400c1d40d0301c20314403810f040010820403914801c400b0110001d103250301400100c5e040100416296034800b07550b00c00300c12402c2d0569009039103c501500854001440000c000f1492a20428400c00d4000340d558901c0901300c2c000c1071781084540c2c001021700502d64401100e20a8520f03105146009656415a07805040e450858940049a2850506440000019104000f0b04000741c4c144e4000c9069007401c40058128000c2c110138000440b14040c0d9103051640c004640c06102100b03130001c2040a920106140d242d203c240103410031644a00c0c0104001018000100604500c40c1b42c11824100c1403041269004041e50140c038cc141d1101c003000741030005d40103040c100c0c01c1c8141495803401604e580042d00c2400d0610016040403030034264000d0030319041c040c2c0c0d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 380022365 1250 380021115 380021129
    0x7080714030408010204050a090911040c0207090509060901050903070302030d0c03020d020d140a110915120f09060709290c0a031d04110f0a0509090412021005070f030f06 75
    0x42c4072529858018001e401c00d04c6860712486d600f6000181403400ca128000300746810046901c40104c13480203100280060b010300801f1445075990008a080d100d10880d801029900050005410110302090a44c4c0d0302074441b0000350010080d460000c4e40000440703c402201d160040381204a02c0342c00d078001c1c025010703080e400c23900000c0c5291707104030700d82d01190520284800051094941c1031b0721404030f41c4209261000c0042c100804201454076a108035440007000d101e89142030351108203081c4010060b84e00310240141c6605100f8021420b0009a40c401058508410500d181c000304210710103824004c060707250000c0d40d110f20500d14403022180301c200104202c805030000c0740b9000702002039490031441440c1207200d182d80c441c1703020f004100c001c0412031211400d0020703c10b0004003d82c80b1344003036003c8c00010004174880b0b0f00c0c0e09000500c00d0f80525140c5c003002c408540041c1c01c00111b10f0030341d03202510706003c09c11003a0300070002d520020724510340000e050501b440550001d20749504848 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 380023615 1250 380022365 380022367
    0x210d05160f0320030309060c09010c02010c0f020d0506040c05030c0607030813061127010e060a031b1d01030510120201020115090501060216050306010501120f0606081f03080708071403 81
    0x1550083c3c0000114002e01501c001c441c284d545103001aa1240109005540064504602c85001d076100e8210030340030394001c5010420082d41075001466590751010304840d50340042d82080244a0b0400b6040001c10b010340190602030001750000f2030505c5a00c0b001030501c02c400740481d255000c80c02c204c4000035031040c4100440a15218480140e403c4103491051074041c2103c094000001094005150303501a10303000401d090480030031400303800001440013010355511b1142410a10700043c603a0141c1070352203920b568811004050311142200a6036418181440b00380700070343e40f4558402003103503201c80e54941c80c82c0481c40100d000d041d082030405c00a942c0c001c0d02040010ba5580158101d481b01d408580e281040000b84248110040c03044d10307890b0300a4001001194020070751846100c206900c000744518400301c5110484145400041c00100340908101100d00100c4c0411840346010040c050403618640d11400c8910a40e14014808480490140f041041c210650529101848242c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 380024865 1250 380023615 380023667
    0x171902010204090606050405031c05161b05010302070b010312020c090109050601080105031b040c0504090c09030b061903081602090711070e01060e120c210d05160f03 73
    0xa000c1d4020f4011a02d980b803808200041c1c99005030200d404803034002d40940f8960301454426100c4140c0f2201000c1880b8003001644017810a00010160081c422490504001c00d00103c12a1111064110605140c4100b10040115860000c4141101d500034a42c99156050a20880c00d0202c0c040e01a9001640d05001041280850300f1180c82072400783c0e1908590384c0c0e5031040658502100e004d50951801241d9489254101500000044885424060325140d0341d03000400c1103032a41e1804000080c1c4020003802040040c45080d07402010071201400c4405d0810800d211318142817100403c860340c00954040941b10381085010380c10780080c07084038203250980d0701800c4104075950711555030150301070100711072a220007000d0580303441c2c0d6a5615500c44040510140803441d1200107200d2081c10002000b550300e80d10390200380d41060400c0303002036286904044c504a184031313107001848000c1c0400b206851414101038405604081074804211036800d090303030f0030740c1000c400d85c9464103403502c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 380026115 1250 380024865 380024867
    0x80c12071d09010b0904022d0a030308160306060215100f03080a030c031406090a0608060c07020f09130215091003020a020c1f030e010605030604060b0102070902070803041719 77
    0xc802c1c85440d142009102d08040482008030501c01114029800000e1b010076601040e048180741c152803000c000410101c180701c0e00021500100c1e580124002000101002682d03044107458000001060600740070045c200303e0080d40300d0701d00c45101d0215005001c00a80d003001000c5044008064020462085039103a00304680154424218280800c1c208426030408508c0b0f845150710b00d2403c00800302907138480b00d081000e072140240c00800d440d07071982e80100e5014018040e9502840c1825a01903071078040d44180030803944075140e0a03101d80c00060030801c071003d281c140e40566a504980b040015111401e01004c907016888100c1d4000840d40d980c0f0648580540c010b003040c60058089900840300142001209080c007070a40c9030b00d1229078901e00c042402900300802c1c2544510001c07610740d40781c00202e49403110440341500c51039160a0f507240c072560140034030405400000030a501d031003c2500d0302c40b0148000f400044c14004401606058669034106840004039507555210700d0602c600c0d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 380027365 1250 380026115 380026169
    0x3050f0606060d02250f02031204150507231c09030b012d0e0a0f09030c060e01020c0a05160806010f05100507050a03080a050a020c0a060b0a080a06020409060f080c1207 74
    0xc234003901c1200400d0341d15030a20070a442c01c5440000101003400703a07090b0100c500303400002045681030f01d550301c0135117200d242c4510b90341c800340d81100900c000e030a032940c04925000205562018425180c009101040581c018203065602800f061580c030b542d0340700d0741001c040a2050300c050955201501080504415030000d014061248041c04100f40600d448400c4441c0d01c2c5004001c6640310f01884002100c81e0010303503c001d9010300050400e000e4029890034805e42c0281290141c03c200a4290f000301c000d48017a025128410041115605050b081181c1034070074003940384200300c130788005141c0d14410000c4071070095008050f15048102841c015100903025070340184050308120010f00b014503940700340c030502c0031100003c1011003481c1c2c40c0c1200800270943c0b0103410401055020802d040c0412108103180d12504006a6071442c2c11b46420440e0350301e8100039200e2118440030880d0140000340003081100496001040e4819a00c4aa2802080d580060702000f4000b8504c80c244500c0e507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 380028615 1250 380027365 380027393
    0x140a02120c030105060a181e020c0304030210030c0206130c0b16030f0311070305070606080303010b0d0606030902060a08090f011e050609071407050109150603050f0606060d0225 78
    0x1d00240304d662030b40c00c2007007003880e05030180100e01c05001c1022600e0b065142c020030048424172860203140c20061346e05500341d13400000e412980750f01c001801c00850501454403498580c540c50104221809400001d4036900083c080b0a0300c03414540c5001f040c01400540b52005128880f030aa6580740e8400440c081084101010340105101d03090141d4a1402801035820207400c0000789440c0801e20f03541510940c00c440d006a420359a0340c00081120344040004601812040c0000c0b5200d0010b1000081640c8940d002070003014201000280182c480400b56442050a401c284e4059501c0b03c81c2c0350719000031100800302540c01d0101d504a0410091f4107200c07194a40d04040c08541e075034109010701d495050f00e44000164101040c60903008045014042041c4110004500340d82e040c0c8940482141403060305c41240d40c2d8031320410030803c0c00c20250394205400350242071213281010011301140901c003800c1601d103400044d03104400d1110300c244d00c24021000034000402d00f040c100800f090543e4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 380029865 1250 380028615 380028619
    0x50f0406030b01170c0a051b01050a0506120c03120a050c0105040b071106010e28060605040e090604030c0303021608030405011b02372906060a0903140a02120c 70
    0x91040d4900c1d00001c2044c2e4820084e01c100107242c03012070030040b9101e900c240c0303010005a20015106d10480da0a0081a00032049250041a103062039030030030031344610344000300c01d040c0c2c082c24004903207850100b000b40134180c1000d090350721200030b0b001c00e0328584a42d01a0300065442d0804100c1004203047d109802a0003655507810300b00080707100e5981d030351002c0c0510000301041c1400100c0034a2021a1101036100c030103003011880e40590921015641182c2044001c20808a418800d01500104080d4015038082c01000a8202903c01030804c41d08003d02408141c3c00107514041c420751135049a011a6000307090994900d0541080c9008040301a10b90062034420100700c8481751000a038100c644010981000317245030701d4030130000c0e0018412840e403d50090104403001050300600e820b070404403130b0900da20039115103049103203800800400340b40c411242845181e900c150300101c64400c0d40e0740410b0105072140c9400340365141800c87d1800070b501c210000d02c01540142d0105a4541642013 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 380031115 1250 380029865 380029877
    0x6060210090c030b040201180e0a0b060304030806090606090a0617070e031e010f090609050c03030f12130803070c140a030f05090415080a0c05040b0a0510050f0406030b01 75
    0x16100008141c0e2084200a00002003211060000c02c51007210f0035040780c4141402070350107000b03988100c04e900c1154404010034040a08000c04000c050080c0704894500300c50b030500d989480ea801524016000c0c081c1ca010b0003403a00018695200c0e00e0407940302d200700400782d02040766180e0300100701c1076145980c1c2c0ea8480c0740c1c6000c904034a020b00081c210105004015040a41c0022140c0d082110007000c82c205540d25602e07068025150b40c4207450b990b6019600200d14400c41d1704205107401720320a201d9000c3e9000300804464070403030f10252000175001000444c030b940c0792010100f14107001c1081c044c0c500d080000c1880b50907038202c00007000c00c89c031803603240c10307140650480651110041c44c0040c010904a4030700c002c81a100e20001c05d03030130000500000d030400c1107181e40060713030340d04d80c22162250303004d04504402d020031211040020a01114140844100c040110340003a02d90300c11503006003099001030040e5409441512090f918100303000c0d466950301d10005015115025030f0a002c114 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 380032365 1250 380031115 380031133
    0xb16050111180409120c0503090d0b1f081e010207060203010b12010602030316050306030a120801090f020c0c040e030403080f040608060102030c070509060312030115141c0218040e01060602 83
    0x1400c0c01042c0506170000341400c01c6140c0c2c2041654121102c400c00c480b14041006400010341d10804c00030406802000a1101c0d49458030070040b015924010310403e9551810040080d6540020300f50100224071140e01100e00d00301072694064019904020300d03441c008400840c1d0320300b445001d40300314801a2501965030f66120016a201e1101b519040c4498691013403402c00c1030b0044000b1600802c5c064220b50700821541c03561203842040e01007240000d2004001000211168010303002c0c2c0e601c0d0400114601440d40580c1e1366280030581c600f9004a86800d81040021001c0c0261401142c20425543c1e503568400d0250003668400d00862020a4120002c0f80d0194030000a496a04480c00020844203080908015032030718010801607140c8074803101d070425108010041e500800204410158050b000b0b00c02a05113040080c00010441042c0140d140414011400340311980030036500507030b00c0000a42081c154460279414681060900040180c0f51b141584402c00f10391080c0e00707a60081ca = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 380033615 1250 380032365 380032369
    0x3010c050a1d0a030b0f090d0e0604030f050115090209100f0512061c050106050a0605070b1810060e040c2304020d020c160e010504050f010b1605011118 67
    0x1000324064000080d481c1c001e00c2140ca0b10300403242e004003400a146444542ea02d607100301c014a4205c8070500100940344c10711544420030400107200e40000d0600c0c642c40d21020000c40c1d2903004522021300000380c1122641c0611a0270340c050305100f10b90a00500c0103689901100d000380d44511082030041c0180f40f220100c9911840d25180c40c207000b0390b0b64900d061643d425105202c0c101422942c0d11013103821504a10400301c1002c1d206d154840d60000c41c01916000400c1b000c02d2180d4801818002c3c108403207000180c5a070010381e03010214060304840f040e9007010251519101608a01800380b500202103494080d1910181c41a0301c2400c2254035241c503003154180000080341441104030035420b14907c280740a40140000c100c00501c01400c048062101c1e1f85400c3c80d0400c048a008003101d030522100080d07414043c050107041e00d003031007107040c45d48002507a4070051051002c0c03040c02140041410380111145500c02d60004020701c9110320004004900740d000d203400468a01d01601280414 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 380034865 1250 380033615 380033617
    0x180108070303081021060f1a0405010e0f180f0a061b0903080d02070302030913091403090d020127091b140306010302031b0a08040b0702061312050706021803010c05 72
    0x10700c04110011010703406005c0c50121403030174680110b600703a4072401004050509480ba110410340b582080d55030800500c0c00340811078074103070811010191140b041182e8942110702041c1c100704041100081c00804070708843c1841c2d42062443c0c1076028269045041c4100c0f0b41010325525112802d070003040305070070740564140c0114400242040350030311030140c05081c203501a01c0081d0003030050702d10704a204800034040000c02190800c1782503884040c0400d009880c0324241403007500303400843c585505200003d94003202440001d041001d401c01c0940e5800000e5070104055000390b403071f158500c0e2640071440143c07030640c1130100002130b07402e00c208071141303c0d038085220151521034030362850715420011006907000400d0a0700c40030994031005902c00003034005052061a40c0d5403a15141000c0c0b50002e080c0401510560441d030080c002d0041014200568802c4150310003035007012168a01e00c26186030080708000341c0040d101040c94034034641103a61500540204400803c40c14030700b040c064620f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 380035971 1106 380034865 380034869
    0x130f0506180426220905060a1d0a06030203060702060702010e03040e010b0901090f0b12010f08030313060e0f06060f03010203071b0f0f06020d0b1c111801080703030810 74
    0x1140551b1040c10b4008000f2201d0041c0549000305940700c42042c0401d055159003020003040200f41d483d032046000319405803d840d030b940741805000c2c0d21081c1c2210004059403c2010010410002100300c0e4260303412102c0340360080c0d0800c1c900c5643c41c1c002c50f0040d814850741d583d000c19640c14000e54a0005c0600c0850240c2d5405407998050038404103a000550249182c0310900206d038012064960244070141c0380540480c0e1030403d1300103030081e105021018041c01c102080d80540114490380f144005039000580c1d400c100b4181802c0744400c071201000140300204442d80c00c0c00c0905600700319405008420300b0141c80c0d85401103050b05003131007125241d03400900c140311a0070901949018000850b103c203102c10407810311030619200d0140c01444004a40c209540507a290152001120f0070b610b41c003503843da15500360301e54504081c0410303804100310306c00280c075504820400e901 = true := by decide +kernel

theorem cover : BRFrame.Cov 379856115 380035971 := by
  have h0 := BRFrame.cov_init 379856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 379856115 ≤ n) (h2 : n < 380035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
