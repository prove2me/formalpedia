-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4812
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:48:31.828385+00:00
-- url     : https://prove2.me/submissions/582ed175-43e8-4f00-8cbe-5c76b24e6be8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 865287769 ≤ n < 865467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 865289019 1250 865287769 865287791
    0x2c010312020f01141b0912070906090902180c0c01022106010201090b04120504030c080a020111060408030a1109030d020a1509030c1506051c02030c090136021c 70
    0x241d4100102c4501d4203e48080003402c0081650085c0f82110120441c241c607204000c0049508401c28007030b90b101039441001c04000f40441c6200c1c0d01d0003441007040410000005a0006113019004003c0c0030310740302140041881041c5402c120380441054034021542c0f0960b040001c04404001031501503100595800581b07a540103004110601d13500c040c0c8042c1070780c0c80780c0e030b03112881c1c0200844604010041c88040009001003440d50050b25015000341003084007440010021161040a41040c0d00008180400141403105498104070316500c085800816500306041c1405010b019981c0761250301c1351074000710380104070110180e0003211506214080c20749800283d1300da20000800207070042e414280031800b524464405d400c07443c0000f0840b20b030744200081a04001d00ca685040c01980e0300c4281c2141340810924039146800d503a40d88231b0358541803000c5500344141014164140440b10b405500c000001d00400c2d008c1c146030381c11501c0d510180f103040007a10108070540900c0c1c0c907100399840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 865290269 1250 865289019 865289021
    0x305060a08060a092406030b0c0c030a11011806020912010b010c0602090d1b080f1606050702030111030c04030c17120a020a0512032e2c010312020f01 66
    0x3003950540030042c009030302c072140d08400038260a1000e460000d02015880c0f43c44007043d105444413a003084020810ba411070800307680c0d10b070000d03000c410000003c01407100304881c04010303100350003490304100301500e480b0b011541c054020302e070981501e00e441c0c6102004029917a4040c000114054581d0304240916801071801c1710a0144503a0200d10b214143d4000a04190000d15450001510003030780c0390344581d92054105400b01042c1048416400180a201810040d2641d4110707100003c5c40420103106012010303041f54004c0c6410800001442015900e00750001c21350201e122350203d5491030305014540040e080b80c0821500c00344404000218908403142010904200b100a82049050341e6031403c080c0d4806030b014001e41c000c0701524808100c0900c8100038440018010300d0b41c85c0f40c1808241c00c29040c0c4000000b030a00c0c0c0c0c00244842d06800c010b22406d84042100414010424003040342a00c440720140340c04c109440d20002c0100440f1a141d4054104941c00f103401c18140209118 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 865291519 1250 865290269 865290289
    0x100c0807182907050a03031d03030105010f080603160905010914060303030a020319111809360303100501020c061602040c0c08180a1e030809030f070603090201030506 73
    0x4410b4036800b542d5102c0c1c003000a400c2080066005528603080e0540c0c2c40074200503984906801081e500c0c0e04c11110b0000010002e140c0c6204413019614660504e40040c00b0601d0100c1c8090810080e500001c805890410080c05607042c01030200104540d1024860050b1401b402a085000d080000c1c1041c281180345406000c0c00c002130281d403c40d95060181c000940004107400b01c410b82c0c074840d2010503402c510410008002080c070385942d903107000c1580704c078a440f990f40700345c0602c05407020000041101840b24109826562858022200d80e043e002d0314558881019240c3d80000018010651031504c6100121003080c2c09803502c0e00740707032410030448d4004e4018401400c98400151801490035502c2101d14a8072410604441456a1284070080e0030580c032030100c1071400c02c29002d051415514400081005860b064a541b110f410f42c0b802c1d406052000500c03000010418251507030f404d20902041c48000821500a1655014014091700500c04240d01091030300010404a05000d0850 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 865292769 1250 865291519 865291529
    0xf150b04061b05011b0f08280c0e1c0c06020708070b070c032009101505070f02060712030b06030c04031b0308030c0d0e012c100c080718 60
    0x1149002d9004614103901e59050b40b000c842030356903001986103860f15102105800c83d203566a40000c1c16104202510920b13015113914142a0701e80320b2144101c0072011082180c0031070080100c2c0900040f52305503409480102000d9200452124405103480c410f9542e41c4650300401071312400c11360f90041070780c844074103014103042500311440a04c02444404000c04666210380d054000301c0f6902e46030172400090394055582840070782c0c0b40c2650107250402200e030f00800e062006150113482c064251020b03503180ea8043c03080c081d02003418010f0003460903500700c02c82e80180800d6921a22440d141c0854882c00d031009010134a88150401141450000d80307101e1411000301500e41410f6440703220400c80d01803500c00b105c140402e0088002061900507500036111600142d40350100b15907800107071124412130524503031400c1c11014200d58000004441080c51011055480c0b5180e11400c0c20000c04490000c00d140c00c04081c6403d06600481e51403040324155100e450100e00850150614600c602c20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 865294019 1250 865292769 865292777
    0x20c0f0c0406060e0d140312070f021c0315080d020a02030d080103030c02060c101d0712110f01050c1912020a0201210209030106080303100509040b010b07150f150b0406 74
    0x100081c030341440158518100c0c052030208001503402c108491543c8c0c07100c4828440044003800303002e150354020420744494a01c03400a0a0860340707207115107003515400e0b802001016141e40b0085014030108505401078000c01064400d045490385c03001e5540d0742c8183c4200c0c02032003a8190100c001d4840d0320500d040c0c1ea411340e200020350490340c080202c503800c020880d542c14010b00f042103400315000d12401c1002091303040d03c8507040d02003008039800c013030070340e8401070040d5803001006000a15111034198034010482d0012094182840102c96a0182e28000c00c6944140315000e1039080e0001c0c85c072003c01c0c3c451390301ea0f6010144148120b866445012000f40841d5054004215045402551b2058101c000c840181444c801ca000642518040da01002c403540001040c48143c0d40d03189c0480f000783c00d0981c0c0c003400c0d508241c1e03580381c0b60440501c506403c0100120741c1508000c02480c64801c04103e89006001c0285004146001022204100c2558003000c503400590411100251412071344d251321 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 865295269 1250 865294019 865294037
    0x40b011a0a030f0e061303021b06030c0a021f0e01050c0f031303030e031303120c150504060f0f0b04050f09100504020f0303042301170112030c0501020c0f0c040606 72
    0x1810340181c200010320343c03615a255461041503140c00c02c40340c0d109551214054070f0307100d07003414040e0800aa1580081100c0e441e0b044010503511500103c81c1c01c821034181840d0359180000c0c08074241403001110803c0009800010b00d400d442a070402451407000e04020007032a115920321507020320501c0101e191803582800080e05800001c062812414024140421800d40414519007154001200d450545a03082801c4c4140490311034140c2500800c0d081810100e031a50301e1b2801040f150320003e400d019100c02c0014200b05441c0c116002a800c612818043d4250036541c02000d0000c030782d26180034030301c0c1030005143e10f13411000140c02000360002400e00410342959007030140c80010000c0e030700300040c0303501c500f6103480400003407004041400c0141200340305c003800600003542101d2601c0c10841256441d50510000c1144a81190791040d00500190154036090301c010b4070900028019500c00706007108065030225002f1694503107041a500011185010031040b22140d004040029031054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 865296519 1250 865295269 865295287
    0x1015030522050a020303030108161e0308071103100b040b01031406040f02040518040515040b0c0a021c1107060c1734030e01110607260c03040b011a 65
    0x40000381c00a002d8016211402c40b1500428a10761080c0d01c0301d040d03540001d40300d12043e0311160210010f8030b91300000c18000340c5903c1102c98210105c0c0000b4106881c0020482c2c100b00800c0c0740c2074105000070301a2070700950301000c0c0708000c246150b0006c0c0a2418410b0780313000c96219116500b403440428040c00384513142c680c00d0100901c03409000e0100c1075420071000c903203035a0b40c83c4c0c8411182c0490344021b150b80340504e44103040c000d440d5507060130003036008280000035032140c0b00554070540a801a41c2c8945681c101240b41c101c00c020544042010300c1822918282e0000509075204640e45c01c890314580d94030012548460020300c041c1c540780400ca0001a4584010001c02c9035400d0010505c02101c04420b60b044100c8001103d034042c441c0c50800801019040a030007c1d131418242804040140a000050303190b850042030300040020119203480742c01c40c015004e02811382c07200c2c081e000914010080c444181e0054038260b684142d034000016150b4103024410f160040d0082e00e19080403004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 865297769 1250 865296519 865296571
    0x90a060e0907030f0e01090f140d05070b060109031e0302120403050c0402031e01090e1c0804061104090e01060e09010b01050d1119021b03010510050d050f010510150305 74
    0x66a0f000c00c40b55120294030140d45c00c03d010700d1070b40500410603d00359000d0342c5040780c01d5400b03258680c0c0094010740500c0100c00d410800f5601c0071070300710101400f95600d1a0048402807000d0700020011050324503c40b15055a10b09014100f61080d0200c4074040050034000180b8003032480010984c1d40304050079444d60070aa005140c2181d020000c880e0562192031100340e070540240c01415520741da8540d0702c83d56200411821502106140c00e10110240b4a04001e000d030000400141503180c842e914000c0d205900000c4a00415110004014040140c00c0d598041c100921520310b640b80110046106c04006118500026005840307061030813019850303850242c56170010120303206005000b5806030310b4120002e686044400d90103441c1c10f0b20313081c2c03182c0441c42a20103240d010b60325002c208504000e0321403100f8151078089500b241c040304c0b175240c03041c5000d0000300089029404d1000f84139841619407101e806960f014010364900040a20302102210750840b9080c0b0120701d01c038801d00454501c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 865299019 1250 865297769 865297781
    0x21e0a180b1002030c12070201091203140f0909010b04050306011806230118050a2108071a0a1401060e0102150423030c030a11100501030503090a060e090703 69
    0x141803404204520800000752040c0144010301000d40c000103405442c080d42801960842e802c2000e419090450a400082040f041405034907144845d803502c1106040c0118000424005104105c0345d6901d405403043e40e16810030031400d40605c03520030010900084404c265001c6d641c0c058000c20090b0b00e404210031424031032105040f00d041d030741d01000c1684643d01d2000c4116400301c070040712415290100040172031040321202e030110341c80c00409000c50390b034409194003101e00c0182d00140504200d0b401380401200c2d2200104081d10020b460703020428058000098003107c40110140341d510b10324134074240d9605181284e600c181d804010302880380610f0004a400d501031044076502c1050310302e01d0034075080c1034406a84008050074aa034200c0030300b1040d403086810b4880a5410310446640390360307580c02859942824004d191450701840401009a03000c000004907041c0899652030810a40701d40c080c07010f031400782c8007208004c0b40250040035004900b40340030f0012070456441e09000c81c01001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 865300269 1250 865299019 865299059
    0xb070804030918052403100f0609050f0702060c0a050304030c030c06050414010606050c030f0f0906041502010b0405160f030f0618060f0302090c030408040e01090504021e0a 76
    0x200c0344408140000041c41540290140b80f900080608080030048807020041c00c2000761201c0c0400150107940b408580f0542545010300f02083c2c020798048000b000d48030035000545030925110800c050a8081d484450048107641c0a884464448410200c0203104c0d20091002040040010500191103a41d55101e054028070b00043c075160316940d800b09507402078409071500c04803549180c1c450f05003846080b00801c4a030a08a18007a05003403683d480f4000c02854422000307020918052980380e01c0c00301c0e620840001c0080e960760703854980052180e009040c07840e0040d86494400552070400c2c0c40754501805146100150980c9081421161041130340200e004254403518440048681801140b003e8104142e50110b6001444000411114076500030300114000840c2003015807942100e030754010850120940c0c1d40d40d202e040007a000d22407640080108084107000203401c031340c4d03035010718080c5100300c0d02484207603085213850014110030b9040550000c44500c08100c413242680e0030f800801 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 865301519 1250 865300269 865300277
    0x12070b010f0b22050402030a021902070501140c0f0a0b070311030408120a09080a021b1005031b04120c140a03030815190b03100906080a0210180b1b01090b07080403 72
    0x51340311004a8243c0e001500c180032480c1e00030410701e0f40140403200128103003010707100803d03281d407514000170291140310b1041c078072504000406250310300050151040644202e0101c0e889140706161900302c94400319070140c0002c1c908148425070700c120500f100d001d6a08508405d04120154103030a1030107101501181113241e9135002d040004810b04083d110b2008540c000d402800c20189500b00000c4440c402584248800b4180304180364001060f640c01c0141c8900010f180500c1100c0c9513450702c5190004401c0313072601c4c000f440030415441c000b00305a0f202004a581e00d00041818442007454074040140415920000950511089001411a050014903504228803181404841403c4030741201c0c0305c500b40041002200300c01403450000404d0008030800c650340c174141d04140c95092842c00207100d164041801003c851060740c400341d40714036800e001e0303a6a0744e581189500c59808440c441c2950000744c0380460300c045d418825010b1541d00030800c11030b2a40c491100705c41c0030100601c114184 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 865302769 1250 865301519 865301587
    0x8160815040809060c031608090f1203070609051e0709060506090a0501260a050405010507080f160504090c0e0f03030c1e030f0c0a060b100219080c12070b010f0b 71
    0xa003007c0d61018004034003c1038103070f942300214010302882c0030325104428041c02444581050846000044603c3e054002c0f030001815030442c0b42440c02c0031100031010b100041c00b003602c3c0c01c180e01e022a80300300300c2c0c15403013003044003980d0303030301400614046d01444030345c41000c0c0c02c020444c2c7d5005244210410110424100d1030382661011160140700580b0b1455280740d8600030441040424800c05070060228200f404e1039141c034041139451524020640d08505110002c66514a8015826240640160a0144054812844010000c1620002c80c900c212071a1000c5103150901100f103600c92451607029207034141c000e980d90260090783c01c22040c3d9074481045100c000c615a035002d030500c29039800150081c50301908108017510810f00d11640714000310b0003051a0759400050440d500382c110b42c07607103192005509040351207000711004008140119118840055800c0009104040c802d60070168142d899400d4441c40c917446020b01d00035040104050000403020039a02c50084504070480020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 865304019 1250 865302769 865302787
    0xa0e03040b0a2f0a12020a080c010506090c0f0a030b0a0b030f010e16050304030c0201090f1502010510142103070b0a0b2b050708160815040809060c03 66
    0x705078030800c4204005500116081c2c180c0602000070646024040820643d40c19003100443e111008031000510040d810b079120413035035000303000800178180c008890540740c1d000344120314080c1404540c0c00780703d07000480018500000303120036581c19000440300c00e81012401c04040e0001d041140c85542c2c041441000003d143c4940e0004601ca00070045101105500d040e175800002c1401510481550440d0b0030290200c90748041581d9106400d480c00e0b840c2d1000390700060750309030072603000b01614900d00600414640519200036081c40d4084d8000c1003950381e107180e064030324040380c06400c80c100c24100ca8040c0710720700b14881ca0605142d0308000c06240c50086e50140c6144d0016000710f4114000381e0070405860302d644280408440300b5203203505c0b2014902c090f00346450211038109400542a01e840c020302904010010151101c0030841d076105141503061315001c0c24a04c5654210b10503000c0d20304200951120350ba0040e54800003090a14044400300101034003d42000400ea100501803455 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 865305269 1250 865304019 865304039
    0x27030f250315020a091a070308070302090d080318070f060e1302030108010b0a05040b0d0201080910090b15010c1106071a180609160b0f2208010b0d02090a0e0304 71
    0x801c0c218034080c01a5199a03070301340500010030941c01903400d2240043d1000c01050030703d08942186915183c183c2440d80d03141c0c000d0340203029500502c0d030091010ac2d0300500300b014020003940104a00700f1411400d01c00220b15075922000390040c9400e010100030708002d843e0180d080c40034071180080448400c80c6428001c00201d0f0000d82c08190700740e4441c89030241508042c2c0d889009888103a400344038034040320f4080307050301c107928100904200a4800080d9002d205100240c1100c0c03090b14180981015418022110312060b2031745240f1034900a03c45030b8940c0036900e41c11815500442010007083d10744200310040c1c02c01c8500707a07411001e42400c00f03204001c080102c1d22510f604103040005a8640c40b080c0c0c90000b009240205940c400b102c1f00c5241c1500a241801320b4103104400740e96441c0c41201c1001d107000d80d107101e412006c03000030101c8082009800c20001c1d5044c0d20020000c94488000f00406c0440c0d84101a4000c200600860300094094000004400300182140d203425528040c2c0c0d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 865306519 1250 865305269 865305293
    0x3020c27060a0312080601020304081009020a090902010f0e0d0204060806040b0f06030c0f131d0105060303070f020906040e070f06091418071427030f2503 68
    0x3040c004030391110401440c00021003690003500684000c816241103a9640c0d09800380d01c0d0101003803040300740c00550103030b108100700c4010b07154a2064400c1260001c3c6200081c5c2903a04080340b01c0c00c0c0300200032035000d0580c85490b42141c0c05954207601218130a07010b41d110000303a41c5040d00403034001250300158445019180c003c001300401003c0c7d03464241842c00d00c03000060503070480e008058040c0002580c0c000383e4220120021034a15050400c940c0c000b0300d906080f0303118a01d1142c2005040c0a626071020146c04034202503100a11196540d00304040c3c60303103c4d690340100301d05072103a030f04005400c0c0481e010754001800740000600c9840150384520300b130f4695000701a0074250110501c0000d5224103181c0003407202c1c5046000c168040400168030780505583c00d503846040c4c1c8002001188548656902080c4035103540303580e500c010402c211000c81940705162503020b0140200c07524140003d81e0301001c1c0c686400381456410380c145980c601100303044c0c0c60308030410707140000c404510108001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 865307769 1250 865306519 865306549
    0x20c060304110631080d1110050a050414071805150301090501020316090b0306010c1502040906090c080601080f07121d07152106120506040303241203020c 68
    0x620021402c4661000701c0300c00c4c0d030207410718110200c0c040003614000140e681c2d010340d550814101e540c8141080c1c07850170420302003040107141401c040c8000030140d03a0000c0e0180d40580d0f000074810510540c069981c080300e11034100403c0e1181016240442030b58842a0031100000c4005180e541940c0040d00b514140b0b80f003550281d500005000203107105041ca06000c4c10a41018501c052801c6010f84241c000104014180603000b43c1107020095566000340f41c440d46040115180ea8880841e03000415640c025002058a8000c0400500380a000390030306c200f074144d580403e9640c0f40d91070442c03c00c1000e0180c1c428072104004a41c034101603402040340c40380040d140841d150750a0280e00e4a0a24507034848051011800f84440742c10b036200d840041c146001c4010805006001c4076204000c21040d8021480f200700d44007070100b040707008950940254000d68090000c600020f40168110008280000f0709000d810401c001541c040e501c41400c1e50301900541d452442000007094a00701c4010b98 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 865309019 1250 865307769 865307797
    0x3020907020705090604230604270c090605100c1b03030e1009030317130206030103080315041506030b190b030103030809061302120c1302090909010903020c0603041106 74
    0xb0a00072800c3c070380c00f0140d000f4422502480a05580203550114585080a24850a84000000c3c4154646400c101004441c008035118200035a101d4050302c0124038004452010342407000295002281c001c0e802610801024084888403c11040c1d944940c60801200c5c8181c0701d15480392258220030054004502944844440c48001001c0110f0928102d050000b17000f9803036010710110350300210032800d520402c0075210103a00d5a42e0200301c0c60150f8840254000ca0001c00030040240700c4001d140590340c035028080341403d0000030003003900c06840c0c240c149000700e81403c010f45403180d009080760748809404c0341c841202c44c3c0c0a000f0b207003c0c560000401c10000100420815a111003050750140300840500081c0c01c0c5421128181001c2c040301130300c40c1a600c1c0da441c000e404d041c0000c03446420001c2092a998031f0042e03a030000b03500600350301441044040002002030406005d5a650954554040c1080c01004c0003000403541010b40152a0600d038444440e032141c0324980180a02812201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 865310269 1250 865309019 865309033
    0xc030c020f03040b1b0312070c0320030a050d02040b190908012708190206071d090127020721110601140102100f0e0f121801090302090702 61
    0x1019280ca44841c5110910394401c00082200b403280b8020303240d07100074451114240e41c1c1e0841c002c80c914010030004245240710302c0188603009400c8000750714014402d84507103078031000c1000514064003103c0400c0072550810040c035040c080c41030006101c8100d04010040c103194440d26106125004004845598100c0a6144400c030b90024500c60040400b00028014000c0841c400c40c0c440c08504218040f10428002e450104009042690040300581505008221108000035174415041c2d82200125044a5120503000c002c809001038030b401c040d001740daa59181440903d5600c00600ca2141c100c21191a441c00341911030000b00000c2c2c0c0264602c142c1c104100c07006c0ca45401412019000b07020000090040ca648041903460468004071521248032003a000142d041900c1d440980c69110b242c0240701c6440400b81c2d01c0000c01400c69400c480e6602c070400704842c1e80d1103450101481604040c054008048510300d002200c00006242110580390380340e010803000b1b0800c2e030b91040136030032441e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 865311519 1250 865310269 865310291
    0x120e070501030e1f1107020d030801030b06030a02010c02061b070312092403090201030b040f0203090c06030c03040b040c0308033d030b060a12050d0e01090609050609040f0c03 77
    0x101503004034080e050060500303104d0368a10721206629003080d00398010b0b02d0f500c00004103240d032402e0313903803240e0050000881c0d1501e618000f05020424041122110880c0000c2101c03400c1c0081c039110003e41c1030315940c43c141071030b1302080000c1d0401807000c9441140e03080701060b5030b0f07018811140254402c8184488003400030340040c01c0e200c0a900000c04a110210821080031144c418070303040c0c40114240020340e01000d0004030003804210080030b40041c102001c05150350484d03030085100700440f034240c80c1800b60038010802240720940340034460306028000b040100300b102640315003103403141c0300002d45035641c0d50702c880740d6030001c8030340511800042c41c20600c101201185504c800d0014107003503a00c9000301d00701e000240501d01000e01800142d00006000c0c2d1900141c150217400c102e07007074034114180c92400c143d80700100d031000c00004a07681c00c901402d50240c2e0030003042d03983c5c0c0d4503009406070070a800d2044d1500040c030110303072254542c5c1082580940f280300301c0c0c100e24515a4080f0f4151001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 865312769 1250 865311519 865311521
    0x905030a03200409241d010b09090412260603010e071503240e090d091d06132c031908060307080f0c040b191401120e07050103 56
    0x6445409a40984a840640c0769080d80c212019180c8009002900b1452116105c041c40e080305044070842c8035000c1c0c082140d2045040e05405203001e8030b01200e1903a00c81c102103005000b0a244540c001c0d0b900c20115001800b194031011020300c4030310b48480c8500d24103a19408080d85800e4a808180d10a4148202404c0c28080c02a50004030300040000600d401b00c50480a011202c110040640d41e80e80d10101a4035400084515410031002c03a10140e12000b403984641c0303050f07070000303443e10032103000c011428029003a903000c5403804101520050707400083c014001200038102984076649200042c0c15030207a1007849241e646001d4400039449010641b60030082e005080c00d5255032090154505404c0141c09041300202c09140504540d150013011902e000e905801009280c020540140b080c0c2c280040c0910300c002c0b0898081c401c008504092060604041d6480d80c0404042d200500000030328410031904460189028150181030710f1a40d421102c17901c3c1030003280c1d00b0030b2004000d25a85 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 865314019 1250 865312769 865312781
    0x703090b060f1302130b19230a12091406070f03180204180b01080105070e0d080a0e011e03050910020a08010e070306170303040c0f0f05010503040f060905030a03 71
    0x1a0742040607034108000090100d0f0035802d110030f100740c001400f1a90706225010403402010054805500d4000762070b207000030fa1406503500000500d43c00401600e20440a2200000c0032408980c82c0c038000d40c0203002c03241c960000b407108070100d8407020941c0024800c0e04001da070504090014180c3d81c10100b4001b07064012450444081604000e0110a11039004034220380090b4101c500103119228100e200004540096010b032018000000000305d00e034048d0040303441002103030784110300c0200020821440b14a11940904003000034011555224051003a0b5103005a050412046007100e2910f0a084407541c0ca420800098449041c01180c0000304400c171311740c50402c1015070400d07901c410014002d0318144540c447c0e0880480200d034040d40694098800341010404100065180c14000c580e69401650103d500c0040c5200000303c014074005840d0a44011100a00d89946020011a043d07003005d4804d6600d100d20b00302c4000003540c0b81c42099140340c4681d014584403500100090205c0700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 865315269 1250 865314019 865314031
    0x1e052a011b09050d11091015050f040618181e06080a030807110303100302090703060b0f1810170a020a0e060313020409080d0e010e060408090d0b0703090b 68
    0x854114800c2419420003405400d03500140e5840750784c62214203202415008207a00550480c800038140103540f14210001c405881ea4901c05010000c2c1c0224201d50512a5800b4008869006e000c01d001540c8541540c03a120601c0c03401e0548119290070200c188110094018044243d50b101c2036a080380c500b608484c80b82c000c1030750420840d4901a4101d8030340c0d402500c000c040080d07000000f0321680c0180c0300d901d00d0310800341c2229141e01d8541001e1024242034001030348141c03015000112030620074041c00742a00c003115a594100b01c1c05001038503441c0c00490070f4014044042c0d886910a0701d41040241e2524003940e60031000b10904001c0030a0408040c000d0000c0c140104420404103030403041c013803800c04054844a6990380d40703036604a50b80d07415002c000d43c4581444803403024800a43c0c0608403654102404000d22081d0354051400c0310f60100185090f6041140014042011000580450b03c1e0142444a10352801e030f403010b10301d072400c50350000803c1d500d140710b034184402e115003654460 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 865316519 1250 865315269 865315301
    0x1509070f050d1a04080f0310032d03110f0318010e0d030c03080c0f27010f090e04020102011509090c06050a020c041e020a0c140705011e052a01 63
    0x9001612440c503d41040d402035151109000d000c282005080e10840e0841c0012420150b2241480000c0001c1c4080c1848113031601627069840115007214180c0d03801305e200d400701c1c1c00c0e20507540e00d030f500f581c100ca02c40c42c41d400d4074000c20f03d43c1813044409100402010300b05402d0741c80071204d107400161102c190074001d54000d0544904070360000350000d40c414203180d014140300f0903d0b540c0100d0030302584201c100038802d80001107412005052050395084290003124504486016808011501c1040081401c000107815103001c001c41020854070315001070041c0300100341024102e00003001d0710a0765000c02c2e501d80c0e1b50b51302d000034800c0a003407400180119280c2149850303070b81c0000070b40c2c611850b1140351042c0d654044a80140030000e6649041b013031610425900c070440b6400c00341004007040c8085d80c40f00181d8908071960740010991b4800e032481616a1142e001130700001180e0032000a10000a1100400c80c5408800803425010380d605104040c8403c040d0b00318a01500303440203900054100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 865317769 1250 865316519 865316539
    0x40e0604051506040b13020a0909020306030a06180204050103140d30090b07120b060702091b0409060f05011808060c09031c1e0504030201020a0f03021509070f05 71
    0x41010031211100d65210006015a0300c0f25030000d0000d080e131814440d072100041c442d80180c0c6144d50003800a640c107a4950190305542c1c0c0110300c081e84400c40e00d0741d501d900007000000c0080c4a551000310040300d0208025014091540494100d076400e03001640c0b801c0400880340e2078060100000d48041209150450605510341c80c00b01c80e00d4000902220140042c0800088000c46644a80c1ca12a00002201e0442c1011032000d4046004108116141400d01c1001038080c20054220b80401c0d5029000130191b81d1a45680080c01c1c3c842081360400c41c50030800003882d0103a502404000c5e201c8114100c141610700320024201d403501060000c145034003c1c500304166500810551360090000802c241d880303995174002070502e90350102581521a403c22070701070140e4004810401418403c1000c285c220076110103403000e000e20310000340140d1001c400c81001039044150301403141e00c680101e501d02050070729407101c0603004480008440e401301c107082201e0300841031020010700c425101c000300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 865319019 1250 865317769 865317773
    0x41103040c081506010c0f0f12020115030b13140604080306040b0306040f0b06131406042f0d090b07080f0615030112080903030f0405041401060813020102030f1206040e0604 76
    0x32540f001044c06041c88201c3c860307a0107100150380350135041640000c4d840c00703481c62880c0800b41018203e0b0040010361812400044155017039203c10140c90304042200402c0d50303030032046941c0082d1440200c52481884641c480314040400600e4010b500c1114829181e140c0b5105100850700301072101c62196100c0401e01010990500390140881c0d0080352021465403060b0104400e140c403102c230080090724101c804460041003400440c051407044074140b2520712b02e5003005406282c100240078040304c0a401281c041e5080e074006040041041d500840d0000554440b420100400c80e0200c0204004c0010440b900000000311540501d04441d10714071121200c50541e01e074003050003020100d401526884060100d07600c199048100010304172a035580345403900035800c0e00309200c0c81780a0390070450707100d0800d00c2c406811810b07101955110022551686101d103002c038001002039056004c1001044915040e80005100350302620a210340e050902ca0b00f440112265180180e415030400707014880 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 865320269 1250 865319019 865319053
    0x2303030a05032a07061a030d0e030609060f0a0203090c0402070f0201030501170312060303130305151614181905030c040204060c150b031e010b010c120309050c041103040c08 76
    0x4040c1c11a1000403004041c000c020100c06c00d01804035810f10520701040481c0741d21800910b02c1c0241541907034065180c218032a5a41d031010740d046078a80a10000203010100164090356101d003128048805030209240494100e0344800c9040d42c0d02c503c1c07096490150358042c004d59004251518800e07004606640070107489004118904565000240c0821a02e42d030820a030703800c500250103025401da0b0399240003596070302401441455003205400245003803812241e6120a400c0648440c415880b4402c00841c1d254040320b8400c00c000c10b500c0c5031202d107440f07815518820044c95400c041486041c4800c0500e00b400c0295010310681c010402806883e9000403142c0c1c1c502c1d1300007040c5a101d00c085004002900f604e5002c03a8041c0300b0950403520f96019603802c015202170b41002000f94181450046840f2009104054002e0203070155241e060f5100713500010555028005640c42c202d072590008056402d81d41914040780008418841884080c4101c50700038120307003000381034594074500300708 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 865321519 1250 865320269 865320277
    0x41d031606020418050610180501050304050a141e010612081b030c010b0a0e06030c13020c0601030507030204060f12060f140a0c0305150105042303030a05032a 70
    0x10825042080d000c10600e81c040d54040c00510380d0b102104070b6042510707001040121b900e00d10422100c41c2056182e07000364a2201e240c00d260910200450915005450b982c2c4054000c8400384521411000850705002c1180100314012000c2c2c000c030403d00500400303041400140a000e6450300b582001142c0380b45140724031103580f0980441c0c680e8a090000c1d200e00010060000c00ca01000404880e10071042d0710140000030110340c40710300c031500c0b07004044081a0445405805074409003d407002c82c5800c00009042c5800a44054505240003000c02c0c2440020fa0040b5032a5118605c00d1045182901a240c00f401c003041c3e10b6a0f02c1403800024515401c1300400250901d0382e00c030103011000c40c2641004110f80d04984d22140c243c00d100315180001c0c40d60344071800010340b078100410318a000031a140c03191440141e55142c2490b007004c644008404046440c458400e011181192141d02c083c0040c0010700c295032509134481c9013112000400e92003000180003051152a01ca405814a030030a807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 865322769 1250 865321519 865321537
    0x9060905120a0b04110a120206030612070f030c0f0e09101e050403120507031b030522030c0b060f0a090e070b03010b07021c0201080f130c14041d03 65
    0x51003901249814246070002c40b010301000090000c0200b8003041d000d0b10305042406a0b0114072080d540c0248a14402c102c102c001c2d4858010004210742d494004001482c01c60040c040e22511380d99000144450f245503070048074100301d40d40c01084400ca40102d2180107010704018038405281c900013194031000400d507200382107550303050340024001f8907640ba098000080c210400280c01d060030060f20401c0398002c000b59142c00d050008007541c0c030a010f50420031104120300203a141000b04240c001c0c090040c034101400c5070282e44c0b440c1e02c031003400020444600a8544e201015018200a00402d4001b0310b96405041c510120010a880b100d010408645281c035001900350440440542411010380c05500c11a40110010610740f68078401482c2d964400c60700b680c0d81100b9150784440c5a01f00c0381c000390104040c0f00007d4000940e0310405035106003180c0340c411b94a016541c441290f00c03d103421800e590f100000101030541014030940011050000c4001d10007400440c080b035030392051042b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 865324019 1250 865322769 865322779
    0x204080705041d251509090f0e1e010e01050a02090a140303040302060a03140108010605100237050d02060a0b0f0d1e060f1a09130609030e09131209060905 68
    0x1d01d80302240c0041c8882c06042c40180c00325401d15a40401402c0209900506008034644003070741740e00743c145101c0d0110600080d8041c00000d070072b00f000c06007400981200c0c6c08555481d81c0c0c0c00e00d8045820b1007024410f0f00071101c01a190200c1d02c0c00e000c0d55003000c0e0041c22550055800d50340359a40d001080d101101c0e4100c500c2c40e6140d04419003200640324000300c03806000700480012072134541c1074001c0c0d800e403441541c60f0340c44440111400c0782d031400c500f0310700c0607101c0f81201c20408003000410000458054406012030f100841d54810b4a800041170b01607006821500c03d0110b00031182c081c0020f039900440325145564601c200041c03012502c0c4200a007001a49011071820100c40f04c1c0820000e40c0010080222008040000e406070100ca09040000c9281d10000c91040c030384441c8079401034007200c00060309403041d5640c0a002780001c01c02a0144054040c9a006d140d031400d849511602041d1030454a602251520510024141c4000703800e010f01050f050001d80d0384003015030211031045071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 865325269 1250 865324019 865324063
    0x5030a0503090d08190804050d0e090a0b01020106122108040302030327101409070b190507080c1b04050c0d1a0607120905011b0b15040204080705041d 66
    0x74106013280b01d00300c1c0280403202d14507000e0794200d400182e040c0c8268014401c0d20301da22610002100c20006034401190310454010104104c4401a88a500e0007170040c000010a580c860420300c840c003440e040212a00c00d5181e0200813a020b842e480e1358808140750034406194141546c0103900c03400002c200f50300300f0184245501c1754007840d504003610110410241e5000000310102d810190011341c8141c030110900f0004940710200000382c200c05c9490700340d00241044800b0088043e0078480061000420406001c04030203d02034034014010210303a000240400021020070201980711000351500c40c40c41e080800181c4041c81d0100c0e900300414080004890b00c01078010004001c03403011040d049180440c1c041c00300302d02c40c1442d9144013001e840d07045050b9642d60045460442407043c1c03800c1107a145028070b0002d2070403450035402110b03a140b0280707007a0070000483d00720782080e0b0100c5119440b0b800f04201c1e038202032050800e4590032505682100100b9038009a664034000d1262441c591550 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 865326519 1250 865325269 865325273
    0xf07031509060b040f0f180c17030f040b09030c04090b0a020a0c2913050d030b010203160503180609061206194104021c11070c05030a0503090d 63
    0x3c0d00101c0042c0000300104211410304070440000c0030692420303801c4600d41000d04d06403d494000c0201c0d110b03408001800d885042184040324100c0170395400c0142d210034080c104001d403611000d4009890301909468503128440b04142c030b04043c0c00d6612780540d140c109078001041c00000466841403041c0c00140c0d580c8849a012950040c1885002e41008aa41840d0654090113448440380c00c4140c0454603903038843c40c03010304500d081c0b07043c028102d52000c06210304850103508114002e810500580e0706002403a100600c02070102c02c822292504001500100316800c1100310b01c60b400107448060400d40844041006c030710410103500c14464a3340000741c100c0c1d0f600300a0a54148a00358940380441c5d5583c21058525a08448503d204c00c086000702a038092030f81d4032000e151840e442c0c1c88104130050b01400300a5100350440c401400c26860000340005080c0280c070741c02600100011303a039001e9800d000785082d82c80d8210707502c41e0300980d086401140d00041a1903c2900840d003c50741d448640c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 865327769 1250 865326519 865326521
    0x60b190e0f0607060f140124090b0309062403150901021b100b0909150402010504090c0908010b01090b04090510032405060f220207230f0703150906 65
    0xc8904036a20400c001450720400400740c0200d189042d41c0b16050140d21481d40b610750b080780007405140123118040004040c0da15601c03444000b8440c040c1070030b0a0f82d94450f007824555500441c0d440c0c5407a481401407000f000344c041d80c2c000070340a1000000c41601902000aa101c5503000c072005d4881e01c0e000d01140800b4420341c1120317008010200001c03030b050300d540400c0c1d4513200c8031841d1144540c0ba00010012034204582c0081c4034441100160245005180a1b8801e40d94050002c0c1d041003418880400c0078002c40c841c1c0c03100440281c89404100d442d21503990309483c104000caa0421142a0040080d42203000c140d809842c54205c000c02c8641c0c43c5030504406018540c4050541c055840340f0ba88050520b802c210590b5015403c244a940e881c0820b1088084200c00156084038020000540000c02d10703a40c03c45030f60f402140503140401640315104802070310025040350b402255481e0b100711400300940e081074540710006d403860500e980c0701e42c80340d01e4480d202c403554103864a040340200205 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 865329019 1250 865327769 865327789
    0x3050603280b1902222907050703051b0301060506070302030301031202010f0c0503011509080304051c0f03021509060c0f0a03020702040c021015030203030307030903021009030e04060b190e 83
    0x3c1160215200d05000c2e036100b0224040c1402c0102e2400e661385e02042ca82c64400042060510a0704907150102c00540040e0342c42d84107142c10703030326409416408000104144083c05514101381001064541da1000b050700b150519842301e40301c0c1400b000074000190300401030321304494000042003640364241c407080e405408000c60b0410282e14000445805a4020740654141c42108082ca07400042d00784e000e460601084c02175480e00d620a0004010a03c1c000100c00d14a1140c1c1703030340100c3d41c072103a03440c640c1050003144200c026810040708841110202503843c1d80c8110150010030450514401801081c4100300754035a00840c001400811240070b501150600d940c00b420400000804ea28025100d000d9956512280360401007081c0e200e400c0c201400080c1da0b002800707107245440d44e90041c0c0003094001c104405600645440007060781c2503120340011a80241c80b00c180d00700c6004104021103005810049422800b4042203c0300740307000965403590251410b1a88100031244000307109d01d64 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 865330269 1250 865329019 865329061
    0x3150d0c0308070b100b0309210904110901020f030310062d0f020f0313050d060b0d03050307080c070521040801060833150a1503050603280b 62
    0x70b00003203003401c2002140391548281d94007404140e044c0d4581151084520090300c4e1000c0c26440303600c8070400d081d81c0d0042c2a40c0000f5500d4050b180860540202c0e064034050074040c00c816402260810180d6010710a070942a541a0702031071031345c034102072141c280825500481041001188044419281403000c601003220703540f0510004a10b102d10041080e00c00c00c50310401801040c60ba81010500081030322041c03200c0700340210005e4100003e0100204c4500401c0c1c1d001c940b510f01d82e8481d61103810304012554065501c0c80c0d62450407503400b5043c0e500150800703541900030882900820310120300501d1005843d02c0038082c447c402c02080b1024015908845415480c103080000c507008c00050122030110100780309113100034a46c1820496040b40001e800031002c4080c0092040c81d0a0380c00d8a0104100602604200c3d40b034420b482e030703024030000b280400b1030ba480043c0440b1346020065840c20001112202c41c02c03000043c60782c3e0500c504100c00500490502022680032030034582c114030104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 865331519 1250 865330269 865330283
    0x111012020a05040e24011407030e0f120a030f081b1b0303161e0e0d0323071a0411190306090c03030f0503010509040809031609050105040c0503150d0c03 67
    0x800c02c801c42c42c5d428904486140c0b038800c1c60780c0e035818855000c1e2000c21603180304190414100076030360b181a5103031414901340c02d92000520505000703079a1101c0405007241801c40c01000b040c0350310315014001c40c0550086100344400003080003400000c42e981b80c0000b0902d45c81181c0c88481060810034090100b8041d0f6140d408003200300100c0700e80606545002e100981d880c110204150711260304c00f080a00034060004041146007151810000003240368140310745401c10b0745200e42041e00000d07070300328180745e0400c1000080c5602484010f404041503144540440d20490a00d95506040c040c03480903180d0150701501c04551051205030b06540c02560007100912100459207010400c070940381c0070440c0440d005a000d03080451040301036030306a80c0050401280c685580c0c80b20061178103e0b00d200b41e80762181480c400308140d0000240e0008000040c000b04195061200300026501c0400903041001410b100f0024150601c00d19011311701d00030740d035150140360305081c8203d82e610070350801f9240d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 865332769 1250 865331519 865331521
    0x309020f12191110030e070509061908061005040b0a031515090207021810052101021315031107111801120c050a08030915090a03030c111012020a05040e 67
    0x2003c0c000039903090300201140c0c11840782861503416400c032000403448035090740c400001846203080c01488650072100c01415a00d2185980004420309100758003c00e80c65082001406034690b400a0b1020161104442c02e2209801c0940850412291440094125003608500c0b02003003140d64850b81144e00c0e07040c00307280d0320307130f181c140d0440079621030801203004600c00b00082e443d40c1902600d80d0700034420002511150782c070700400c00c2603124410722920034400c4c06544007034070400244020580601701e50081c002291424880c2e03081061014448820f150401e8101c010101c5640c0c22034080c29400041c0004886040e40880d0030301c0c252108084404144030300114601d1640c411003941c691041156040d03040e200c0f02880590500c500c40c00246a00034000c2c20407070316120a1148a13a01401c0f070b581d05000340d0030000f9688178065441640400c2c0c41001010130b100442103000041041a10900301030500b02000500012142e00c3d4032401582c041014206c0c10f1091040743d0040030040c00c6040c039 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 865334019 1250 865332769 865332773
    0x7030b21071a03060603011a1306080708010503030a02120d020c030426031206011b0c14240f07050f01090303140708010b09040905190804150309020f1219 68
    0x1e21515806041081070780b074003408019003403035011a0b00c01c20b80034203600e045918003803c502c2c5207040c86100b13401003d01403106041c11165a01f4102c010081e42c2e403441c1300c50500d42c0000d44145410381119000f0b4104002c003e0107542c00148811800120801e55940e030800110740200a006003100760506000014001a1607010b244020401c1c42c1030401c0050380483c0030082907583d100340011001d42c041c2d0480090b0b015070140e581c542c10b800400040050090041d940d10803d1810b54204040b07682031801941d2041c00e080f050092120b1414040f0343c080141441d80ba640750043c810316040342d1000007840e108000b070a03c8868a141401d10080c0102c030349c6d0703203000b034064900e03222820407071000c0c1030010700514450500d06041f500030754007442c6466484030920020380410301d010307901e038852185c01c00d5002aa41c103080780780c24006c0c030030103803103605148015641d0281c0e48960380030981400d40355000742e038844800317810316001222000d0032540380e10b41d02401c00c2022926550b05110054100302 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 865335269 1250 865334019 865334023
    0x1270510030e0d110601210209090601060f02010605210f1b041415062a160501180e0403030e030a0e0a0501051e0d1404150c050406050307030b21 64
    0x14548600015209a1180700b0383c01c85021071145000d80d503d80c8210010880ca080c0200c281c443c100c02c1c5103000c001002243c011918040046c1d80c90850750384040300400c10070342c1c00007104d018900329100a10130306144c04000303071328610f2514a040158441d800d400368000c07020442d0307a52110500081d00c80074614010003040190b00001c6a600583c28200e05100c5416a0200d030b40c031802c3c4580204500728502c0c0e09110342500300240001503500320541704000310722815540d054804560009012405003442100064151540200d050210306c0700c400c01d81c6100350452400780e0300116412106692141400c9004d481844003511f0603020000b91044082d82c000d400c1d0358100c0090f0b5800f40082e075100b00443d81071241801c0e0986151a8078000d00303032400c0101c0201f024000744280030612420402d21011824000e070780c200c800a1901c6401c110034200e6000300c0c80401c040c1e040c2182801c0c50148081e0207848010952400c052350740440481741e07562011510006540d50881e800503410a80400d6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 865336519 1250 865335269 865335281
    0x7020d0e060a02191704090204030212010207050715022103060a24141905070b24010513080d03060e0c0f04180f0f090201030b09060127051003 63
    0x11094010003030a07050200880e6492003440c0e00812010403840c02240300c4000c0484119146180002c2d8070104038032000280024040c13000c401642c0390f24503c100418a4480320035035103241d0042c4003080c086000030231600221142c054143d0484151084200c0c181840c22504008040304000d44174804e248003400340d48901016200d46212503218030380500c500d0403a601400c0034007080100600403600c141140c1b071500444038049424001107001001e4001c1d280032036030000810100304401481140c4c000340342c200b1600c000540148402040c3c0e0591000d07030340005414850001074202d80e01d4140c0d004000182808802d55258100000000300940840e1041150a00c00c01d001b06a0300c0308058212411001c00881e80c0d0303d071a140a4405e801120248800d01490399603003101c007209140c82c01080e004541d91000040c203000d0360710015080300c0c580d131002401102d00a04104580e40c018004200400b0b490786511328403442c100511103e20200d800c5035400004101100480d180c03d07800c52 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 865337769 1250 865336519 865336543
    0x19240501030c11061501050c03040e190209010801090b030a02130209030705150d090309241d090406021804020d020309060127021b010e07050f0d0b160e090702 70
    0x1802528024001210802030490440e1410f130000400324500e24034200440200c8103040c140b082c28910003004003030450b0405da020501c4002d486040090000c0b48455800310b40d00700c00d1045080040d4040004d0048605004440403c1d035104140251a40e040190550087c0e00030710300c840606407400408080c0d00030455a81c000c1c400d12a01142d14075100540d000135a007411540e40c2040c400d0040c840c0070b0000c25100340c050004d4510007050100c07a07403121040f00c02d4190280c00c0321030f010110050117008004845105e2241445180c04035a95441806400c543c0042d0050f80b51211081c991501c0780d01c0c0c80c0354a9003d8400260035680c00b0b030703540107140316025070011340d00c05a07aa00c00907005c0304c103038001103e040c00307140102100800c0c0036405071010081a0940320481c505101440c1d085034000e0040262641c09043d00300003501d0854408601a001681d203920560340d940d40c1e048860304068000750300155400f0304c415a80d44141041d0410010080200301381d4140307084080e440e21091016 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 865339019 1250 865337769 865337771
    0x315040f0e06040809040b1005040302030d050c100c02190b040b010503030f0d020d1523030705010f0302160209010b040f0b0708040608070903120f02241924050103 72
    0x845150a00d052080804004004000e40000d544565406000340c0c0003a5000394000d54841d50031800703840d0f8040102202056807502c0f42d1351821401054a09600c0c1c1d000c0c0400c01004000c0300c000048081004406401203410203d4006d29400c2c013a803e045c0f00c02c40d240710300803050f50303007505003c0c540c10854000c3d4018031711981c50380d0301c030014107072288140392422403641e07000c001041c074046007a0300400c1034501e546400541403007440404dc60044040c0d1240c02620080081d04880014a03184000d0625084000740501c510704800a0700d071001000c1260f09142d03000c200d071510400003289090305643e0040161943d580c460010680301c1d0050700450500541500e00880c940360000121042d56800150650070146040340c101c5d414240104a101004414440000014800b050302d0a04c8052a01c80300501c600f00f03040245000c01081c0d48802c1903040000309240c05074000c500c207800003031011400c2284104105044040c050b540707900c42c019607510001d1184040b0b03403c400d40544400341d034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 865340269 1250 865339019 865339031
    0x80907060e091819140703051e070306050a090210091a0c0c0402040b0a0807090e040212010f050a02210c0703080903040b040807090b0405091b15040305010501060f091505030a11031504 81
    0xd0a5981c0c401f400000d1150340180348144000b1a080c0e0080685100e5004070f5030180d480740c0d034a50554109917515404591a40e82d64001c5143c50710106e000d002c1c4902c1c10b0b8200c03a24084006035032a080b582d41280c0180b00003180001404144030400d000d030b8000e1710566440350303142000c0b400e540c0070002c03030000a02c410020981041c86580000110360590304142e803961610b4007007082c0ca86c0f201c22121040c0d9600d0301c0c082070103000350040718402e448078000140c0700d10b51442040c100b40d121201c12015110440104031032000d4003c141d4034910b42600e8621119a16000380510390710890304905001600800e00140541d00011108207858a01000740000040d0304140300070744405458040c1203800040482c031100480d0300c0885003c0a000340050041e010150200c480d0394803d402c20f4942c0d035101c0d03006200c079907000b00f4140f910a000b403401c88021403600404811240199141004111000000c143d05505a401c810400100f00290643c4d0741040c1d5892100c110084562a009a00b081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 865341519 1250 865340269 865340303
    0x90204151d010e04060b0d0609062f0d050709051c1109070c021201060f121205090d11150309030c0615220f060602030703080907060e091819 62
    0xe484035048a8922010700c120f034640e9a45da00290041c000f803a5040682502400c01150303050240700c807804d01071203002810403410603014040c3c10003848115100e40d0703208819240d020b8248111105014503110009151301d07010703021a0900401d5200f02c0d17011103d0390384400c0303200c4000c951505182c410103016080341d0341403051226811044800d0008a01244101c2015061510b1004100d0a0304800004d0140d1a01201003444803250045280034230007030103500c100301d98140e160a1422130b50911504041d142e0001402141d02c001c0c000309419004c8040f0100c940300e4803040c03020100140d007113076207900d00044440d94a030441c103013202d81c1d03104500105030741d02d51441c080014000701070a9032030350850101c0107850130404108011403180d610500350050356118403800000d0501a409582c8d9a22203050043c42114003038102019070f085107008010407500140040e00c50001911080150765900c0d20b401a10400210722401d01d004000e09051b1481900600034107c52040c04c43c5686a0641 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 865342769 1250 865341519 865341569
    0x60801030305030103021017070c0629060a0509041406030c0a0623070c06051c0615210f06050a0b1c022802070e090606010206070f0309020415 63
    0x20300c0040d002c20000c10051002d07080400d008100da03402030071701c0200c50440c080360708c240e900101d40001c002110842c44504210060140842004000c0c2214045d90b5126214a0006105408941c0300304400107120410b01d01031000c2d2402c90f00020001c1021481c109800c400e10f160440b44540b00740113040c3c40c40c44a1808400180c2601d00c6540c8065407002500c40c4106040210800d40114400030300030a80002d8844000c400034004507039600e521000e511318501004900e080c000d02c46c035070820340300307104150403107503810b50301d001610304001000c840c88000f0494900403640a0030550801200d0024045c0c0d03608420220b942c266186401641c2e103042c44107890180089800c94007001000f584004001600549260f03c2c5030b807503026540021718822030076210180500e60160700003900801c03900303511003462503210803204050b0025290000000307440312030040212080c0943c0203010f0300105d109034040100154003400800c40d200d983c5040b10340c0c5010324816513a0700c10328188004800124 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 865344019 1250 865342769 865342771
    0xb0a0f0e011404060c200d080603060103050307020118030204050a05180c06090f0a12051b0402090d0213020f1b0f0706170606130b031005060306030d030902030f030a180608 76
    0x4101d00440b160340310b5940d440701819000c11508100090300c0002d82da862039040442c8401c1400d0f100a0078951420440075010001c000c085512a0b0494001007000c507030044220b034250b41e0309190990074070440000c100094000340e000a07400c41d1a00c010001010780c580d200b00d018911035407035014036903441c041d040c1c0e90790380c1b403500a900224284a20b06690801490103a101c000080c00e902c02c564883c07202000c44880117000362841e9010034075140c1ea030042d551002c0d041c07510580e419890040c3c610081031646841000080c000d076000065072a1a02065040c0c80381b03000c10444840d52441d50809a0300a803040501141490003104617480d10f0880014000d011140251102030740b8100151810400310f0b0010081030f0048010031a001005c4807104007803026146040038503480741041e10640ca124169904602d01544080023400159940020340d0b01c4451194640400c026185101207402c040011410700103500c00416034803080c68020090035600a10200d000c8079081d034622007281d060320 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 865345269 1250 865344019 865344041
    0x9060b070c0f061d0a030b0403050d0605010206011203180302031009020f060910110a02030a030c050d08040c05040e0c06040b031b09010f0809010b100206060a141302160b0a0f0e01 79
    0x1034080c1041c3c054040350b041084035403c010500c5c101c180c0d070b940310000e0340034048400b14000782000600030707582035a6200c0e84001d01802e100a2140b9810700f0700d817000105c0038580140038000174a20086901c1c190130025400782d540039003a110384614006082c0090709900c82e080b03109018103401c0c00c5850520100762548644014008494107a10010548010380d008009000e0b9004462a69004d601c08101c1f0b00002807082c1d461040b181c4071030138074a01748100b8400c5001081111814440400e8088422078213895084400060401e495009245403166410215070000800310300043c4800038200650311a0b40204411684004480b841c041c09111307001d502c501182100003816220741c4035040c0160301c800c0318400022525562400100e50340b01113101200180d000d5010010b5a00300a9543c030010b0884600c5861821480320000720351805030a81840c140c1da0100798443d0360028103084d600b4141e041032200c2280d04100c3c40d510080c0c4401603000000300e0804840c0b0b0417810051017490b0050b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 865346519 1250 865345269 865345277
    0x809011a060d0902060d020c0303070f02011401031e0c030809120d02030d0207030c0f060c030e0a020312131d0103030906081303081005040f1b1b1202030409060b070c0f06 75
    0x501c145803810042c0004102a070700035909101c0b06401b000c03584000d09a03540024000c41d1030707250540d4001c1468061060750021641045c00913000c0c840c0300703001507054035441014040f1a80079030b50f140d80454803a09000e041282950000024004220010f004d001400d80b1070039450020f4080144e515003900c800300c001030388100303e1400300f88000e40c003400c40b451103440c20942609403511046001d0740d2180c02556100c0c0e44001c1c941c2c1c440d0301881040f6500001801800040c540d6400007034541e08003103c8c150300710b100001c4e03031000c120b04411120003401074680c16214004946800c2002050240001c4000c83c0084401185080c001c20f48144100102c030180744094000e680c00b1200d0003006011001801c20346907000c42c03036988038020901192920600028008080c881c1d14483c4050321340014140a001c80410208884041f0ba001481d0b406c81070050702140008002c038035500c40d6500c10380202e03161650100e0b16551280091100502800700601030703940302c40510200c10503502c1340c1c03804a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 865347769 1250 865346519 865346527
    0x10305070b09061303050f01270b0a0f0204030b0906130c090e0c030d03091a070f2109031e020706081515030c090a06110c010c050f0d0809011a06 64
    0x100c11500082c1545400903002c0c50624044900d46440b41480c0c0c1c0080b162a0040c0c03e1451150a0904c0758150f215002c2003101202001b0b8183c10240d851400006000c0c0041000081c0e001c4a07039800c1000c00000c02001155900d940307081284105200303550b082c20f280111004900c50403c50213610b04200e410000d81d000c900c0c980304e985070050030615101d0410740030b0518000000c1d5014801441640303007070f45002c1b42082051408000004041d42c90b51600d290000501150540c0035000e000081080d050242011078036418026108134009280f5104e2400c0018680070075501034500000c0342444040182d40d0341c1401700c1a038840c0464001d00340001d0b51100060b040f80d403001c03041b10860801a01031600004441200c001662049079076200110000603a030010341420460341006011034903020525502c030401690301c1d40e00c1141241d04100003120702400340b0070140143e030a2095054125440c5042c51540a40486000c40e4030030010b501c0c0c083d4042c14041c50000080317607040001c00051074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 865349019 1250 865347769 865347779
    0x3030709080a211116150c1e0f0b0406021207050c0a03080a090c420507080c030c0c0907020c130e03090a060504030203060109060b1804020d090303060312050301030507 74
    0x544115910300701c0400c5144c40c50302007101c0007840b4005441c80a000301c03650240c101400003001e805480b640d10b0400c4480b08140004ca07a480009003e0030014895440141916041c1040070100005025020035112800e100410980b035000f04408c54945456240c40d6072400c0b0141d4950080c012481c00d01c0c0c10184080001078824004241e002c0500180020485207580313420038001542e800151190380d08035045041445030ac02c800000049240c120b81c56640c201846000e8800d08a002c2024054003040020421480c0b130280e400b40341c101c41c2241e80303940d9500c80c01036603011000d49040c043c44907000403421040c408980300c0d0b0302c0e41c405010309001c4140000940d00900502006a403640030a0082070346c203a0b00d10320807800801341640d034261100e003113004140c10705c0e5069000c2c101941c64044200704510500044d1405401c030401031414800c0c17481c002c00c029104203034211180d0740c079210580c2c081640591110050381e000703900311800d1080050042d16584028080500746621800e42001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 865350269 1250 865349019 865349063
    0x100605030d0c0312020a09030c121a10090207052401080309011d0a08060415290406091d0f0a08030c0c0a0f080a0f020106030201050d0905150903030709080a 69
    0x11510340f003071a000150035030200c0700200301d070020100040045c034000d20800034480300140200c041c102049842440740c189543d551055070041d0080c0c140c00c0380c640b000888041e62215103a00a046d484410355540074039152040d22903141043c0c3c203080d185030809900c0c40d034138403507036080c1038a41e03281c015850140180019500d0100d0301da49031b6001000c4100e40d41d1551100d5403a000100b18560040c440707420700d80340c14116803e0001120305035500d002c031034140301d40030001015040001c031000740c5035071140100810041c00068210650080c1031101186082056a2408403483e11306801d80741c44010a54000b07803a2000d440010b0032200c001e001050b110790304c2d4001410f03069803100444200350f1a95030760201402e540c98003924089400b0034030b440703481e805c28650359884540e84001c00c28035083d540064180d01582c066540c01c503075542c00728010884104068a04480640c01c1d112440c60011811a81e076071080f940c020000e5503480000454000c00200604801da11181005d0200d1100c060700c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 865351519 1250 865350269 865350287
    0x2303030405041a0406030b010608221e050d050307090b0f03010501031e1109011e021e0705042a0804030914270609150a031b03140304050102100605030d 67
    0xe88003a400f06110300c6180d44034420803009500c0b4a55001c43c941c5000c00150103030304024121443d9900c44c01d11307800e224840e4580150100e52011203000c20030f401405240706114054401080c0c0d04c20114686074458000d03010f14498202981c0d0044017544a03036218106024074048601580c50a00c014401c5600030740204481e1000440c0050030700c29196044030542d10301700b00711186800c0015407031481c1c0d640007a0801420101182200c1c04401c0c88400941d60740d150807441a2031039004400315114281031020400038207000300103000c0503614003c40c0b100c028130040d082e180502011b0341c0d01c08032401205500e101d141c1507110382c1d4902e89031a040c100983c402e844c04a9108400c12013449013880140a03011040155072605001c43c9024014031201c66005406480391848611a08141e40d076104545416030b64480790283c40c45080c001c1d0103c240455070401441d054107440560782152000028104a8000342e003102d80d06032000e6486001c590f054080c46030142c0201e42e0b860050385c0104410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 865352769 1250 865351519 865351541
    0x18060c0a11010c08030609131b05010801271109151309110a0f050f030a0f0605010503130201031a030d0507050c0f130504031404080c030f03030903090108070c0c0f230303040504 78
    0x1400044103280d66001d0901c400242714880a80000c009006c25640816a580034100341d049071540500315104098458296510100c82070341c82d2900d1071062240b01050310b10450010b410041c0c42d090204041c0d440340c00c600640d190250441e00b00040000e224014450312400300c101d028681004482d08482e00140312081d9414030008020540704050301c07100031441489901000205507413840146c0003030300c59691201e410004140b0511002480c81c089106402c1d509090020751070300513440741d01ea2002c0351941c040d490300444440e0799819070000000d2035400d1140096650360404034007080750000c00034010795044070902c807042c0e00f82415580240d0b041802810a81528401c0810414007640940c000020a030407070b80041845089c2003214610311a01c401c043c0d4110319040c0f044a0350307406079100e928100a001d80214a0b994018041b0851660300404045c0c216a2650398015000d80349228820807508204c074039a5800c400402d010210540040203146803920300010000541000914 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 865354019 1250 865352769 865352791
    0x806180412022b0e150a05180301090501020c1917210103050102040807120f1b030b0405010c200616111b0a0b07080301060518060c0a11010c08030609 66
    0x800700c0340c3c99040340b07022100c026001c140c149251400301c005000302e5820219038024031001c81900701a80e507850545a04400c18036040381c46d0b454038070a0082d6038041c0b050480c1c05518003110441404010f400400b06100c0e804100d505150101d2401c06880803203034800ba11030340c149100c9940c07032080c25008010b5100c0e000c1e0030682c01c400205e64122803a0007a88221241c0e0350000d010001180240301d00300040003008100307020841140c0399025412001038000b4840c82c070803690903480c03210402001c0d000d103400c001102428545854010700070030b068014040411104150007804d404a20194000c074000e11010700380e43c0d1616040040382c00514a61281401541001407000c41c404000c0c00d0b180c0c0080200500d6444444001e0040d101c03032603000380c003001c441049454085039006040b00d0444403d49001d583d1440000c40e80484107000442d0b1a80c400d1000500844040001820100050181050104a407103081c0151283c24500c900100100c8041c40010300924000240951010104c2c907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 865355269 1250 865354019 865354033
    0x140703020714062b1b0504050607030504082a06030601020a030305090c03030a0504030b15011407020102070b04030b1005040507170903071a0a0f0c080103020d021519080618041202 79
    0x1c41614009aa001c0c0ba18922004040c2d0340b2141c060040311704401d10302940c0c45221000c108028111311860140600480001454804040c4948110380080107400b00350750821045096280011000c00d45182484800c111034000c1e501c3c5c030104807030145005070020440c4c1400340e64288e01903c40180020b00c2805080005100341c0ca0034801889280308585d01e03d0395a50841c60040610b043c09489440141d54460f03020103c1c0c1d8101c1c3c41002d0740482d10044a4030b6440600c0101e00d80100741e085440000c40200c1c0c00020004e02c104924007420001100a00b00c81e03c0d07100f400102d80d0121509800503814405444010000540745a0040b014600b41c81c9000e1b4281c540124150400416540408102040050502051240031060000a00c0c107019107400888020000315040c0400b07407080305603100a000319682c450784640160f50086c41341e42c841da5001ca506041c1150818071402151201c800a80c0b60302d40198600d4910100404209441c0c4407612148602c181d6100840c1c00c2d441004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 865356519 1250 865355269 865355287
    0x1050a08220209011d100806061203220e060d1104022a030a0807020703080a080601020a0f0302100606030615200604110a0905240303040e010305010c14070302071406 73
    0x28032004d004e4219442425005c0c0000c1c40300a05555004000001201e540e40c030501920001080c007a401c0101200d14203649902d50f01c255003540f14004603540d03645c00d40c0000c09954032941c03998104580404060405540d51501030000140c590103000705068100740240e0024030b450340c003804a0084441e590700d501124074012a070b180040741c07109421580041410704070264400d50300c0354410401c0c4094208145180d07941c40980c0110950035040c0210480004d00c141d10800070107100503080000307840c2c1c031025402c0180d00c4071030380d09140004600344400850000d02038003c06080f01c1e00204286142c00c01c51108840036401040903810802c1e081c51540c4407400d08000d801d02460050940c1a00d0b8042071040256080e40e9a105440490a01e030402010000d0700c02c0f18521000c081c0311910326884240006419485141c20813110310301d48000210030b1110542c0584108081c0c0d4440029011134840c4100b80c078081c404001703005038011b41050002c2041004804520305000d030055042400c44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 865357769 1250 865356519 865356529
    0xd09061d090c070501050c0f0702010806010309080d050916060e0f0303040e0f01240f03050907090603051c0e1e011704050102030402100f0e0d020a0f0b1801050a082202 74
    0xb074408280c0c102020402c00c003400750a204080d0440742c12400e41d80303000304400d0a50020b0041007001f070f0500c94620001803059010307822145685512103050383c2d80d0341107424036100910094803110034520400420100040c00e20100e41c050f12841d0701d075a86094640ca0401111006600989426010074000081c00c0b10f07003c01c80600800c0449100c10301c542c1002a0064001030003007241040284080c003640e0200d40003100d0b40406210b514000c101942c1c2c6480191400040b9440011000d1500400006126010900b81c6159010003820300340d0200d00e0804499480c040745290742e101c0441508103d42040c1e8038030760220001d041c18600406242000c0d68100d12004842c00d84a59400004102c110f00e8a80702c507205c0000c190400e00c1301c65842e10700c024850302d010a021801a46d151381d10a05541c1e45d460014000c20085140f80103550f2503050005594020441a1440c500c026250346c00c40d60081e4151140c0100955400240344e0310f050709024034400d822483d00803100700d004818056155 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 865359019 1250 865357769 865357771
    0xd0b0907051908010e0313030807030314150405010b0408150a06120f03030c11060c0703030b040c110f0312060f0f1504061416140f0105010e04140d09061d09 69
    0x550880c402e5407410344528290744004420345000d400810a0082c4210880705c0807054a4000608949884151038240c008000f8a02001041c1850b9010080003604d590b81c2c0443ca55420749091006176603230381481c40d2a000b58020f0b140d442d08070503440090f030044011080da00c88a6103a0103d5200d503215075500440600d21816035108081c50303a134006154040c000c03190030310320300d20340a5036890144d0106a202c50340074181c50300ca60f0000481c02e00303152298020802c8850010005c0054a8070040054400340d6406251501401592920701c0c02c1c65001c425940004400c00b0b20700c03003981e22441002600c12502002c0303503000400300c83c01071460325007901082e10950500680ba68a90400700f01604000d1740059104803c0810403450360215100c40d148030703040e135119041a5480e80c2e14604641406c4080110740303030329803a10000040200c00c468170540285d00070a407240f009208070640c2d030b4681c09091828030100c0c1c0402d000f04515449224440800d4002d20910714600718074000041e48444 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 865360269 1250 865359019 865359049
    0x23010807060905091009020d0204031b0303091508040f0f0b0f070e060a0504150314070206250c0b0601020129040c0c0c0303110304030c03060c03050106020601050d0b090705 76
    0x10019906100c035a4000b401c1c0c202410302107400c1c000314548900054a60b2509025040480f900869a840c3c0212680c05a034041c66000040000d000c0c2c00071224045621240300035400269540ca00042c007051515000031598020380c0e40b0f2040b90303a00d03192005506007001c0219513503d010840000418400d03050b80b806041210a4070700d0301d0030204030082c94107840d84c040c00d1203004102b0541d00480c0e0003604403011103110052071031040000d21810307001030040c28013249460044008110302030f6404a035440c483c06c0702900c10081034482150501400c41c1c02e00308400450081105100440c18000c0700ca0740c0440305100210310022800b00b600141508410459010001d030b403034041c401c0c5443c1c00760f01101070491070300b41406216900c030f800d5685000d10020301440a5030100549805081c41190059500595800c000c25981d1030000001e080d014890702c0040c0c508800842c1251002c920030f812103d006010444400487c1c031098543d18003d03180203054864a5000039803030b107844540b241c0c030b00c0f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 865361519 1250 865360269 865360273
    0x403090e2703210601020a0311031e13060e090601080a1b020d0e150405011125050f09070207050103020f1b03040513060e040f1505010920030613230108 67
    0x25581030341c1803420f0806500b58034402641d0740c100112664002014a00e0540503e008036011a400700d019082d8031518500400360362a0300c04030b110010b00e4200512014403201002c041080c1e036541c085489506407504e0642c0700c090240416910340c42001d4481e000301001c42e0000341407101d0032200a051683f919080e000d60002d01c1545a0180c102568100014050b264105c03c0e50501d0ba00c40d520b40b1407400703085d051280c00360442200d09410400d03103000c1d400c008925815954010180c030800c1c8011310410348101c00604a65005050002c540ca0007451682c0042207034506100055000e900604040600c01c0818003d4008100c46045660600c03e1048061a034a904050038400442084202c20024505000c0f003004442482c00c1c802d0360080c0c01c08840c0407104040d241c46803401342030000400b492800d204c004121000941d1100034510310180b21000751003411041c59119000403142c4550004000d603480044080c19040958048034102c2104828580240781d95003031402038003d03801030303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 865362769 1250 865361519 865361527
    0xa020607021c051605060c07090527070e010605071505061207090c080f011401051b100c0e010e010c08180604031202060a05040f03120608070605120a050403090e2703 73
    0xd5144ca0381200140800395840392500d0f4495003115035031916482a022155a10b900142e500c580d41000d0300503400d09208203080c0d00550f050740700d40d00c0180340110b01c4513480305400064814001c070212600c050780841102c41140580c9035142c000c0c0780050060f5000400b0082c460840ba01c18002031000e840a410700150305041e041d401041c1c904002c0c0038802d50404000103101c41028105d007400784032001d01c0d115941d41b1511583ca140c10075258131007500d52141c5c1e22408220b8a4542110141e21065617504240021030001103a10400b4100ca02d80811001d20740440428041001050301c0800b41d0802c1e28098142d202280c0d40703a0007540203542035103019050450141d8117102d007503003183d0000742c01d115030b044c580c0ba081220040c0351401010b000351440d25606c001a940c10a10082404005561142c1c1c1d17142c00180036a840980004004408480010703c0d501003481094041c5030982c0ea01d141300c2d402c0890361000e6001c058a010400700305100380010400880708280e12454404d0003868403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 865364019 1250 865362769 865362793
    0xa2a17100506060d0f0912020f0d020105010f0b03091c0503150406031a151c0204051e13210309060b010e0915040902030303070917030c0a020607021c05 67
    0x3003203040055580032a0070a020300c000c6a41d09400e4400780c8042c584002103ca002a03203c00c002d22032514005d20348030040e0005080e054001c2030b20701c40d981102d0151150384400410490807640c1c240103041d54081800c5090004c40c3c6200040c41d40b114101003251320021036030803803281540e141040c0343d0002c0c0b80041008a00403248031001602001958103003d03d40c11643d6038511181e00b42050320b01c3c03240f52000200010b00c2c901001d000f49401800a00640800d500b410f07900080a44c41680078a041401044006110104c404e402840710701030800300781c84401d1041d010090292056404054010b440324a0200d4041c503031041003100d460001d4404841c1c940300c01a243c0440d4801d05120f0a411444c0c40380d03d81c80c4c0001c0d44244030040c2d00101034614000100202000132000c2d415100200070021034075081000c2c0c0056801c525134144401000541c1c0030355071711445100b261a60000e6901e0f1005081c1407001e003443d14801000400001c0704001c00c1b14040503d000d00fa01c00f0380c00400c0e104a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 865365269 1250 865364019 865364023
    0xf020d051c03020c0d1407170a0f0e09010324110721020d030b15030109021201050d05030409110f13030b150a23090a06081203090a2a17 60
    0x250711241410750800481282040d12000e05150020074810280c00425070707504900202c402182e4001544441c068a075034000040d5003200e0542d2012551650715144078034003403072031901c10020060421406030308590311004012007100c54913002500d0050b01c1d130b240e00c516001d160000108490b40075155840c5040003081c40d50344207500380c040c0a90040124045a011421840390840c5040100b6540710100106011006400c840465554040008100c00846800401510040b04040b081590321401007203421043c010008005038800c12080090314404d401082c102000c81d064a0300303144000d800300326650b00103560540f881c44502c0c420f10800a40c48001c5820803228540c0b88050003a000220f070301c42c1300303501880242a1b0070300d41140b541c16441307030310b659a61009032142c1d0440c10019840005002140a980c05074016500452014511101902c1c85a1440380040c450444c86459210b075441c1c00f214080b40c01c003440900d054100220036000c0f030040000341d4801300d2030025071a04074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 865366519 1250 865365269 865365313
    0x50d0f1403010b0d1a0a030606050a0f05010206190204210203010e030c0a1b0815010e0903190e012d1b030c034d010b13090f020d05 58
    0x180e0840014001031000d0104141501c0700000c8184002030001c908072403060080059503043c2e68082054100441003007240e07048481118015074003202d8540d01c03820303260516043d45c015240146e00040014159403a245207189519290010051a040d16003445840c44c50795011907819100d2450090421800e0904c901eaa558030508055030400c01030080864864005010213415090f400319a07100342d10141203054002c2900d003048030720320b0011b40ba00020482092040000804041000403500c90000c03003103602c010305040c640d20350b860080c9010354074100a518054100244051100010080000882d500c40d00708161254070b80c18895000342801c0c02542d500001311050082d2200084c1c0000548500d66414200b5510101c0f181c00c546601c0c0302c0c040f030000340060a1001d41800da45042203800f1550700c1c4094003401d98030b00340c40c602d42600c00b0600d0083d04900c2d01f02144002c01d14542c41f580180784103400681d1030705803540025a0408242800340c3e0543c01100080752144540c00c41d02e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 865367769 1250 865366519 865366547
    0x7020d0303020702040207230a030e130f05011403120906040506030a0f09350405150c010c09060305090c130c030f0e060115081303030b130f0f050c040e0a0b01020109050d0f 76
    0x10100c9d030f0f15550f8020111080400001e001e1903954501603480040d0b034002100f07604550b6010841c944e5105020001c030036604a1080c000c2c0a03040100950362000340484841c40000b5040c1d9203410303d404103024465100030310b41401c1c00d90303030002c400c130482180c022000030b08d0042020003944162a0b500900505100230f442c0b18940203174094442d8841d4490175941201e108a40c000c03c00034004507400854070555040100c65460072118010143c2c2012602054411603035081003146d640c480c96503500c1e400016415804110100283c04820311500220060000d0345008900f80d401c1ca920a0309545980e8081c0050750000380040c00001a103004d03042005006240103002802d007061a61800280458050200b40e1520b00501c40380d12140c9140e8a05005c9400c1008010640f0010400400c0703c2481c2c568107e081401161f10100b4800a58068807502c1c244071069844455821004041040546041d5503c401c00785c800f02d030081c0074041c003020185d152078009440c9108002c140d00680490307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 865369019 1250 865367769 865367773
    0x503040f0210030b01300b0a120c1d07081305030c010c0504080c300111040801050a0b010908030406030e071d01060807140909060d05100b031902030307020d030302070204020723 78
    0x140c0c98101001d21020180e41c0c84400000e41e0600b2030380880d0300303031101e60040303001c19401340344020400051403426411100701d082d80c42f01c4451080040c0a41e0101a1001400102c2000c00704400f0f8904030410b0612134410030480f07142183c0ea41c0d0503070071341d40d43c84060f00120390081010088158103204c554402030048030304e4a0769000300d4003926980361488458040091f81601c00001048095101c80301ca6020800b1541c0c80b00e6859541a0281004803035a00550b410840c504071254018030100f810340d00e404024600b02820600102c004001c4010140a03602c184040000d25011010440c0c074a010071580c0d4004541c1455805844204017801c4030040280d0844034504031449001543c1246104445031800e0361281000503071050b43d05130707018140f13010390301c1004441a81540001c50b402d400754151003141507c000f503103c3d2010507650203500354108009030001490691001001244a41001814090781c3c2c3c021404a070400301045480803501c0104800f441d92051541020140c9100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 865370269 1250 865369019 865369067
    0x1410110106060521060307030f0c12120e0102071a0a02030d020706090b0f0c0d09030509120708010e06090a06020a0903150b18060a090f0f05150906031c0503040f0210030b01 76
    0x801b00f03545400501c8090640c801c420303059010069002e040600422030052210042c0410741000540b10011010040109248030242029035001250700012903d0100412007941c8205a032080e15034050146001103003c20800b41514051078406428078134010140001c01044038542070801d21005012034000711640010484290625401c90f000c455002202040e441c040d03240942e028080c6038140c40c4c1c4010f0741e8134004038480340000c03054115045a0020300c2032604a0002a89481058518800c6900004803400118101d40c00425000311503207000d912640c1e907901c0f203c85000021000c202556182c01d400d003039500e0590180b1440c0b01c1402b8418505060a10009020180e54458001c40d103855801c104419016584111031400c12010188014540001e500446044070340c6010300c80c5c001d0101184040c2000074020400203c10380100038901500c20301940c0710f800c001d1003200c0150044940700010307112204480c0401080b03803404111071082c0c2001509600400e600c01c1d040060301e038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 865371519 1250 865370269 865370281
    0x4050a0203070b2d04080307030819020f193005060111150a0204050402040e04060606050c07120f02040e0d030506060a020a060b061605030a03050c041410110106060521 74
    0x5440842001c410700401380600000410900e405294131284060001140f98010b154106d040c5e244608105031a9002484c01c0c04000c0d01240507400ca40e00100c60148118070490f28181f43c040600c3c04d503410401b022000d21400b206035012101802e926403004500001038030429030081740e8000c4001d00341800d03090680d00f140c43d80c0c0c1719484094000d0ba6142c0010410403980e61341243d010b0f00e0040d20955403551900500e40b030081c4203480803142e0714030301140001d8080c0704006644480d165607014000051406882540040c52500d080c0d031001d4800705a40010396030340c4109004020050090071240c10311a8001d000c81300024211030044000b0040c00d1a0158041500100d442d4010800180f0741c50007000b003411030095821803400d00942001b080c00340940000a813036210955a001d00c219030394184a40701e280114072660712400c10035020f03400a881d0404011020300da0f540781c0307425840e80c6403047e10309582c00c07503024802054000030f00400905101c0c2c079180d010000c0c030000c0801d9013000c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 865372769 1250 865371519 865371547
    0xc030f03010b21130303051e0901090209010b040e010e1b18010f080c0409020c03070c060e1c05070302010305191b180b12061503070f090909050c101704050a0203070b 73
    0xc0b13038006080650321070004a0350001078000d00c046101061501c40c0518001100500820000d00c05038440d604070400000d0511100c0111801d07900003100c0042c040c0d10b060007100100342c0203022200c2e00d520b45020260203116140c007038075080700c0342c0c100c00e0000e294440c00034101c15800d994030010030400b0700801c6100d49000382143c0881d1065800160b075548125052804c6000b815002492000c24a000241459100d80307800700c50441182c0725030a030741c003960349120b140c0f82c900381c02030081c0c008a1081001d51300035801150f01000c25035800084002401d1500100c555200100c0b075000c1c0c03040036086c4443d0748040d8001041112251040c0d0032400c01d01081040d0042190340480c0308240000145d00d0b4503a5080c1d0081030030f01410322a12030610484c040c190b03001c50a2908001841c2010010f6944994003920103802c0c2c01801920200b044c104c184030395262820443e000384080201541540c40d007915403603100d5030094010b072407005424410142025a40e50000740005010701c01c100b040e200b1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 865374019 1250 865372769 865372801
    0x20c1509130c0522090f0b032805060907080c030307030903110105041e0e0106020f031603050c0304031109150d0b04110d1406060d120e011e030e011116080c030f03010b21 75
    0xd80c00d01100008180401e0180800742c081c5c0c018054001c2f85e042c81120794001615606441045040d100d281e001d40083c11356a000d941005000550030070000c00201f50760380e91134071141a042c903206142035250030600040108041c1c40f01e1205031100c204201074408201140e0140420384050301c0c0c03e582d0909810f6480c050f42d0020201c60800003c401c0c1094012022100c032101c800c0700b0b0300c3d00c0e981c0c1d0b4140481c9460840e41d290313000ea800c80e00040d0040c107030700080c4400024000c10400b60703000c45860700c00300300c00010002c82c1c035504880032074511a41e40420b482000e80c0b1440400b149618440c1170141407180240c140d030f0145100c0f25018000405c001c01c00c003d00072691508110002c120b030012594560f03024201c0c2000d901c8030040421030355040c3c128012243d007460080c441921050321085681c4141030003400d108811014183c001100680108103881403170b411203041641010303004015500a900600c0001000110510346004840d8190901040905220a02d1829034007020722444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 865375269 1250 865374019 865374043
    0x41101120b0609132004290304060b030c0301060803130f120209130f1a060901081c050408010c020a140a0b010905180706020c1509130c0522090f0b03 66
    0x44d401030741c254194a900000d0101d414500f00c96103d0750301411480142d02c98010030f00000f001c0d500c9507071109150480e2289820188900358595a11922005e00401207544400d41c1801070100e254041d9509001350f20260100c10081c40d62170b01044080c541141309540203c1030f000340c0d03035001c000c41e090b0030707000540113a01a2915082c980d1041c1078000e07501000000213042100903504181441841c0c10102d0b000d041e0851a000c140d200d410170002c14031000d02c107145503507020030001c1d1407039003e01880d001164a103091041c14640c0303407110942591054100c204c0181c0c0b0100c201e10074440c005070f05403030000b00ba4002c0c01003070045489801d0f0200050043d403942d241c0301c801140040401c4c5000c9405036011005039410246c0301d800094641c161045150321139105801e80030002140042220090b060041c1240801d40706c0440d40809042541005400d000c400c0c80f40c0c0d841c1e4102ca10261030305010302c01123503454900b400d040c0001c03940c00c0c40b20744203024a403010004081c0c41c00100c50700d09030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 865376519 1250 865375269 865375279
    0x80c09010c0524010f120203060121080304060f060f140d0807020415090b0109061d010207031a06030123060904051921031e0e0114041101120b0609 65
    0x4000d0815502c0d0583e0380da1420715907454490800040c03280b00c00034034180e96400300e400c03509507910b03040c4030602941c01348069410381100d0010090080c480d9480c42c044140c10f40221119070454881982c2c0380c00840301500e0817a00c810310155200030608c900d0001d84280310701c51019074144910000000d0360108200c0c080e841802d460070621580d80d040d6050941d000740144447c800c0d18081c0c1413100a28414106002e0520b01d081035298025001c80e8299001681e810300d503910410030352948940b1802ea41810340c0220308010012a0302c05090304a0400540361010035070a0110501d401c691a0b039032140c05446800f880c1c00c004114101d0301c02d400036404c4440e40b40700d0300c13141412030401c0e4842075401d40310a010104682001b6440b442a102001d00f0300c0c00021002040e80b06405940d69159202e81e41c600d10b040f0f90b40010748a501090702e484a41c2c00014218509c03d004203e81802074800356001081114890400d40c0c2c0a002101c03100e001d14018042c03040041c0100baa0340c0107034039200380f00b2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 865377769 1250 865376519 865376537
    0x90903030a0b0102100207050a120302031302061b030310031a040309060807030605220b0406030c0605032221031401060c0602120a09021003020906160204090b0a02041401080c0901 79
    0x5038400c200003080c0c12170020085507501201d01d00380342d44040040084903480d02c503601120783d960203442560320a010703606075000c258006500700803103a4050032100300c05004141104452810410281d0322070340010f0340e091000d0b030440c200b074800000b08166800c9411025810440001e50044940301202d01e14101001c880d00d44020540c040c040325040103811520300042100317044d114907900e04128040c64010440c07664001d0034417041d604180006000ca8400003400c01106106500841d88400c81c0300c50300001071a0f403a00141c0410454100703551000200c100340785858818803011200c041e09080400c46c8030b02d94610501142414400c55050004008505d001d01110703030111100350030702040c0d5108900c2c1001c0c00d1001003404c1d620036030081e03071101450460540030b48212000300c0c2000b424241442e240340a24024100c4090341280c115440d4040e020000ea000d048140c050703d0404405030b21507051640403400c20301c0a03c03e4504006518003800a103d4114007107030780714a0700713103029110303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 865379019 1250 865377769 865377791
    0x70c23030a02220f0614180705070312020d0b13090b0601050c0a06021306030c05030405072102030a050d02010b0a1410110a0606050a0f031a07020f030a021605090903030a 75
    0x82903d0b80c100001807a0502070039001442c410340c07050303003501c52a07804410700342a64001c2c040d0001c41100d07220808041d00d00030071b510a0042019200040c4030746030200100d40b0304541070040e85c001c0c0d41a210410349802030f0107131514008041c1400d030540100c04103c681019101d0036030001000c0c01d02030510200144101e6029005d00101581603040358080d0740d1001c10b480c0e0007a217000c6c20b11800c0c000070318000d61513121520500450b40210307001002070010714102745a50024115486400205004414110005803424404401a980908068185883d41800c040d00356500704108074401e450f0b101c03003842540d132261450748500702c007030710310200c81e0311015016283c0da0840d5150400728868145000d04004140d003100080e1102a190b01e00351642c1c51002d00000d16440c00700504440400880c6400c01480a8515610254620481e031102d02a04803450850344081d010701c0050300107141150380c40c10104402c9000301016102c6c0c0b051031511111a6860f800702400e08118583ca07103100c405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 865380269 1250 865379019 865379059
    0x5040602090a031a07050c07090b010e0a060305070e1f080903131206151a0a021c050c0129091302100f0806011812020307030602070c23030a02 63
    0x40e000054003440002c0c0c0c80c0e003011820000620150141c1c0300000340001d540c030344240e05560800060310b0042040509101e2418050036400700a01d0400840c0c1c1c0120b80716954000030140280019200003615040200c00202000c5103001220300807008500540c2810031082c5d0a1010700070749241240b055211007111609600c50300b80c0e0140d030100f00003004503005c11240c54503860b9606c1841c0c2003100c074828012719516007200740300da100b00395400305001c00403a2061004100032400c620584221040300740320080070f8045560b070040040c501050362802c09500744144111150b08954985001201c0c84024003084070501009000c1c20400e0003050701034140041e8118031640c020101c00c01060954001410355088102403070000c3c14002c04a0f83c0d65000d0054140313001c50020503454a103003000e0000a0042e50a803040343c0603c100c1e00700001044c26031000d040140d2143c3c1d490080345141c03d02454103198510000b40e1040c244d92810720316542c0c00a5805d200303a0303060301c0380d80c5010102d40c2d0b010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 865381519 1250 865380269 865380277
    0x30a03090602041d0106200d050309030c060910110c070b071b15090914010501200307080430021302040312121506230c0d1706090c03060405040602 65
    0xd0f00040f441c203a0342c04c0c210303e103616440c169183c940e0350701c591441101404810031501101b0180d150006444a10f445100384000c43d84400106c0459103480c03600790032540360103001c8491a8194004800c0341019003114003a10391612640545503040801502244e504c4509034840d0b080c950800050b02c0e01000200c040c40e20800b400c0c0700030000d00940c0c940c01d4183d00b00c0a2071000d000200944001302c1e44003128401c1015061000e003441e459a0708042c015104801c0c525441e40e403e0100301d54083c2c1c026420030003402d16900c80e0082584451400c0d030701d0302c4101c084140d540c1ca11914404100d10310813100e00455001d0b901103da0034221584484060003c1c820b41d000541190701c03a00c040c0c4111504004030a411035580b81c820010444264000f01d480034140c080d40d40068403000c1c40310000c035408000541c2c1a120095510300d02140c88080e986008117040c0d24030049140a102104c00012041003030354410001d44d050b00c114034107201440c400d88002070500d4819a65100032a050106590542d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 865382769 1250 865381519 865381529
    0x815040204110a080106120c0c110102070906031a100b070f020112140f0a0204140d11090f180604031b0f080d09050106090c08131119050111010e030a0309060204 71
    0x860303840d000f4580c01041c00809000c0c000c00f20706c13688030507000294184190f142101d003a030340f00d002100b007aa03509200c00c5548422181144101100030954031920310442c1c00039403084200c506444004044d440000d00000c0034070304000968202007045034020303811030398071690001141d0440c01261005840c2e881400380000300b200c0c82c0a205604102c1700c040494001c65910500803555501d81c4600400d0303101ea0b01910b092003071240f111a1480c24181c3c0105c03c802c0c410a458400510440c0c041003d0070b13001c070380b41c9003000c0d03614080c00584142d5543c88203220071500080c118926141d04c008d4140289045400ca00c10030441242c0c061041102e10085280d611001240c0e40f400340c1f00b260b602030851840b0542e0107500e4414000381c0d4408034403170600401540c1d19861100c0e80c030108410b07d204106502034441d40e446044002850741c800d8401ca01c610444403d858203103050000040c0005441e0400019581c94a9007c03248648000282c0d0b5445c091307031801064280c89840c000d000fa000e25406 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 865384019 1250 865382769 865382801
    0xf14071404031505011d070e0d050a060504060b0a090c300504032304140f010507120305070305060f24090d150b06030f0c0918071e02070815040204 65
    0x20b5469103ca4603045581252040a000c0041028194450b1040d80060741d040e004916115801207050900c07540b00c4940d28060415165000c0321030b10342100350360044800b00c4070b1640d580c4100741a071410407105405440062410003c00c000c50b44040c0103561002d800020303a40c410b41c09441255503034035a218104a130020305018506081c82c0103050320944054400d0031440d02000d0101b080080026201200d0700324004100b051028014081914031281203a07040010410916000c6480c000a00040e0342540d0380000311490070207030080403181c0103400b641c4941da0a130343c1a1216038640100803680c0d82c103440d41d04c607811030728040024103200c1c1002540c1c02c18110309641c1c0900407070038039a03040600040003d101074100c4908120541c4400c0b207a40c00345415080100e0341038100791002d020b6106000d808030160740304550040121311700c12111100020340031440345044034000c041d1101105014001004028181414a0b40310841503412908401e07003000000d056580390f030007d21440c0e40c1380304c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 865385269 1250 865384019 865384043
    0x90209040b120708010c02160b0f120c030604051e16090f080313050604030201021e0a0206030a0c020d0e0303070b060f040c09090c0c080a03090309080304080304090f1407140403 78
    0xb82c060303101d2003c2c0c4641d0000c0c0d464a106900d0550020850940c103190700c4c08140030140c01c00384186a141c00004102e6403155080c4003900e0038840b8980c03260b01921468180320b031a41382c0788007003105075031004094001803c424603600c51400c1d000f606041e0483c10040030b0f250b07010b01c1050111906c0d01a580b00721900340c4241400294548080020044541c4441d1307462400e070f071940280480c9110f60300c0000d0040e440ba14030012640382e1780d0110040d000d180c070199184910507400185d184d42054800211250303550f0314403040641c04205003809082282003000d6000810000252a4002c414015103190030340000505140c1d9001402100002c008000b0030901c601c85100419118480c080c0c240e02d1440c0a280f1030645018841070300c0c080341d1080c107962a15800300d41c101c0180502207000c0302400300c01d0134003151061b404e001030406003103088000d586891401c1c2801003503d07503000b0000c0312540313020a01004404002d420310b501011500340404540c064010002c118451a4000340c03003651030364 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 865386519 1250 865385269 865385299
    0x30606092106111b0706020c0d11060403030e030f01090b1603180303050405070e040f080901020f010618060e0405070b0c0f0a050c01111606080604060b1204030311040303020304090209040b 83
    0xd07004d0221064600000d070915180f1400150781c890359400741c0d50140e44410710030141850b00c130b0755180754244a40080b0201100140106040390410780045020901c030040c410040c2c201007081e80d15511004009010b129800c0c0c5401c0020f01001d8111034a16104010b48218140642c226041000510840303240003149401d00500505003500e044030030303009110300014100600e07842c1c3c90040d0b410204051203621641d958202650080e0701e07c43c1540925002c05908800c203101d50001000840840301c000941c80340e0f52000c841203504401d100001da803050002082c80090407100b61000d101d1800c7d561038507400c600707103000c8020454070114400c03407107100c04000c40410492070040080e02d034265404101c140036512000c0d10201e1000c1101c00071410032000703106500c055004071000d0400150251621098031455200403001d41500c600003050004041d4584200315842142010300c40c10141035540094680c0318501c203203050030390081124046a9165070003803c2c1358000030303c0d01c80c05980704 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 865387769 1250 865386519 865386551
    0x1020f0d140106080c180d0b040501060f06050c120c032b050601030c0e0f0a050301091a0c070339240510030201053016030606092106 59
    0x29071541c0d104840e00000840034010004540250700d009003107070501c150b1040c28941040e41549955210024864039008290b0001c0c01d0350243d402140081805400d100400340c41800c3d561100003001410050010a030401181c03410104151408003a5150001c0c0303a00313441d60041d10500e1040d00c100d41502801031840c00c0a41004008008051205a4600c0c005404a0b0301c1c0c82c0c00b44010030004a1010700c1442c00fa5008510508000c0095040c1520343e4086802c44141102c211503049440003411000b249a04910f540061410811481d00c0c51558006050108803540d0a05006410400ca031340d0603548400c60358000405c510344c80a070b442c1c17424000c0410b01122070b00718543e0b40c0c0c0703007000c42d00c14018001c1c540304e254040d041c0f54115245900440b03940d07120210002c4c2d02c0403221085c08000036040b0f58000008000d010000f0315040490f45040e6140c88003800c10141850070008024194004078842d0848140e441c0340550301d649441c002c13542007c81c68005224926100b411441e250003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 865389019 1250 865387769 865387781
    0xe0a060606030612110109030602180a0f0602030f0f04030f0c031a041e03020f070305010506090a0c09090c020a1a1902071a06030321012c07050c01020f0d 68
    0x11a000d104440e55544140e04035040c1c0d0040c44a0711485039412000301d04d190032100d241c0350041c5821104c1035079a0300c40380e04a800407280d0001c2c0442c100444003041c03030070501c0f00000c0d00d94104510009490700102950382c1c40344031a44449031720007042404040c50840c0940b0021a0803105c20407100f1228a855034183c4c41750301003191350b1614404110300c402003040c80a4402e039408100c2c440512100c80e46041d012800c8a02142180b181d5240da0500c0c030000e0001c6002544240c001140605000c02040701040009040f60202468040c14200382c6a106a009080b141103900c00194030a81900c00ca041845a080151400c001c2c1000003401c50140b400c501d2103660300341501124121402880c90503440b0b0b050001d001210006c202100e60f507a01c11042e070f001240201220310381098100b402d15900914040311003c1025500100078140c80a070b042c440c0040c102d40544007110583c0001e07502d100700034010f00d04004002c0340c8d4060811f0258101c035182d40300100559142c0194200c01c1c0c0103440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 865390269 1250 865389019 865389023
    0x53f070f080a030906030203090304050a09020918040825120909110a05180a1e03050c0108040218060121050405010f0501030c09090512040e060a060908150411040e0a 73
    0x10031a5001078000d00c0071802c5021280e044ea148508546002d904801a40014081140d1030000f04000502a07490002002c010095000056281e00000080140601c5424410804500c00ca0b081000007007418040f942070110800410546440803040404004108a0001c00440f0a41020202d07180c115a01c642190003e00003070103048240328030f50a039400765034545004141c1c103100c0c03c02d80d507062803025082c644001e00280e5141c1d50b00c29040000201490558038016603052040c0140301044c000301868107400c1c0bc100c011400e181e404180301c248480004005139100e0350100c4c0090384185600c004071286910340e0310b04114030001e13060040609440803a81c0e0341c078101414514490a000300350481c0d40180c010300038103241421f808d0103420006422117aa0140f10f000f16035507002c110107070001d458148003c41c01031031314805000120040341c10a905020658604000b01000002d00340e40e4504409080f06060304c2e50b2a01c10f20a19100c208141c0c81418068004c49241c400651151258 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 865391519 1250 865390269 865390289
    0xb030115140c160501020c0a06031a0a0f03030305060f10030b030c10021b150a080705130e040201030e0c03070909050c121606080f0a02090d0b07050c16053f07 70
    0x1130754a50059950f002814440e5401040401080042600a90144040c0a1240450a031b80c11a51001420142541d0401d5210760724880e000d00a240d81441b81660208080daa90031500050400003481c541e6100700c20340825441e05070b008541d4506115005c2500d41c041c002d041c1449004c10f010f916884001c54a5010401e44030107071803517240041e07154468601040f80c862510740d1a0300100c80720117000b002c0c0c1d02031180c200a0b044100d185c03e111800189400410405281881e00c0014243c0701c103c4c08554107580f004103001e990780c3d0003081440848001034000a00600c42c0d203001401d0040401015500c1400400c8644a0800100d40c1e003920303549211901511a44030070b816115580c065031003940c9040c010001070204481030740108000700000b80b0140110103030381d5500004c40001c5444074006400401c2580b0023090401070060503200a104444188e800d10001c00c06100c0c1418642080560100d44590038612640c0e40c80070070b0200b00c8080140b4824040b0131699603009101e001e200c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 865392769 1250 865391519 865391563
    0x507080d020102030402090f060d0c1d0901020a0806040b010e03010e0601030201110a031b21091503020414060304020f1201090201120e0c01030c03021b011a0603010b030115140c 78
    0xd48103208680c030903a401080364405031a4503400182084008018a81110f0007400c400080340c0704c1b0500d4002401c4025418507840114500d0303050204002e00440d40681c018050303000c06a40120f40710703500c910140c0300020b481030454012940441034110140d0154a40190040400c01c0414000d06072030003030f211070400200c0c200c0c04540e03940c400c40c030207000035400744640218806400c880341c0f44140101e014200041d084c000c00000c55502c0084040071580d2000200b0a03c81d03070b104800950002c0341030844c1068038110340c62403036180342d1211901c111000400101150b5842d001c010410300d001d0410240d105500c003800d03000b054a40300c1070740811804e07003002c120104a801015112300f05000a021003c82900054000d400300c5004441070603001e0101f030100304090341524044007210300c00850505c2c140041e5848919081903030307038010081000144109104503007124112814030300c203404065140007003260b11129800d8058070405002609100300d03480001d17404141000854a5814 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 865394019 1250 865392769 865392793
    0x40506010f0312080c0708160b01080f120f0409060303090911070c05091e07091719030f03090605181b090703180b0f0f13080d11120103050708 63
    0xa51105200c010100c8843d50000c000081c400c0040e039070003080020303070b4604206076541c982c0050b4011000c815165002c1285002c1800114540140100304210107403140000c80407540d502c3d41140d41c00814400000252801e40210000c01c68000b00000e05007007002c0ca4136880c0003840341ca01d0b8880c505502c2d051500822000e005442154100f90380b1001d003801652070501481800a80200820540021074900c1c010320340c900034070340d032191003187d440010b002c1c01c01c485140704140b00b40c00d03d4566481150003c02c48100a121000069014203003501d01001016044002d0301d01180002c04a505041c107100c29002d0340300c010440e82d04140c0a84001101304a840c2210103001c0040c15480044030011911450181d80000b864500444403000485c1c2d00c0d49a441e100802560f0120018a507802005130080c5219501c039000410020810138030481929010130038080c1c900201d0882c0c2d83e0f4080b071311806011400700c0b001c00e419800403440561b500e06000da102c0c0340501c00c205841c05041c00c00d101c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 865395269 1250 865394019 865394039
    0x1d0306070f110111120a0207120503072a0b100305030c0a02010f0e01080a021b0a0b0a06060f02120f0d150306050105010f050f0c010b03030c030309010b01050403030c11150406050304050601 83
    0x100240c040513010f42003040c01d0801d00402c00001d0304010707203140d080154101041890440c03003084090340d107603103a603420701c52401030001000010303080c02101d11000c00c09400100410001e5000e030000702048040d00d07001a0781e0109403466200810911000940c5410b00c2da01282c0051007a000341c8900301a5000d0071002d450302d465105000740010035410008411149645c054412000340703926a125411071040103524100307990006499801c900810031450000b0b44c09030f80058403d9145ca0441c6040820340659201c40701027401c41035110101e4031206035030221064900741d4610303100030700100140a18009034010f46000940c0c101d0700f850000b10b01c550189504200d0801c05a43e11031420401201191540d0019480c8031055501d07035030100560b0740d040016040c003840f860040e66685c105048404d08440d40c110405051000a100c10130200380c000307080300c0c0e0107034100419134056000320300010855462404d65200c20301e03010802003400b903404005903125500c61002c403041641c9542c1104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 865396519 1250 865395269 865395281
    0xc0a060f050306130e0d02011d0102040e040b330103141b13080111030907090605010f0807140307090303090e0121030e060f07022805011d0306070f1101 67
    0x10030002c0001c5540e5083c80d084000d14007006540c00a0101040c02c006410102409800b5006170345402c10110710142800c3d1030084070000344000c6181c170b450084800000600284041c010340c080a000610a141c0086d000c030400000d04a8588224183e941c1c110051a80c10030700d80c002403811205051b081440400c060040716000c0c106016040403580150603071344002e1445248005641c00050f6030107003400341010720354030074090f181c9034a00001043d2801c11140e00c107500050818070100900d98000308032a2440226103801c1400360b880ca041500d00900020042c1c4102000000b040300c10b81c2d11030b0035402628820398920480b9a0340d84110505aa001e00409403141012904507860944850395084018401c0c10013042180d44080011019003080b02c40349011500041e000702140380600781c1002d0303020a08440c141220403802000c0e51100d1074007070749040c0804c2c01c0d950788034004109006a61800b005046980510340300000400d0140a1281e040129070110144040144103004031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 865397769 1250 865396519 865396547
    0x103060b0306070e0d02040f02040801020403051b0112180f03021c09150f021603081c1a220f0b030d050403030f0305191a0108070e0f090a0b0904050c0a06 68
    0x80c4e425442e444003080201149048200d034400e6a0f1111080361521600152008201482c001a121807950030064205448a580210201d5040401d0000d0b6a0051843c6143e40ba61a01c00603505085c0d114a440e90585800050308041840c1c480d40105980041d080743c0d00ca000400c5140d034007a8480701500d0b005164025000800c40c0d411642d18024800c40e000803100c0101c3c0704641c00c0d40162413078421585040d030003d40314031340c00040d1300000650203040742c025000070315000c20000d001040401d43c84400894464030030340c040032402c0344a2072880c080001c3c1e0842c0342c1081144201d081070f500010038040c6132550107400360009008145000b1000d03141180c1c0c16403580c00300c891084504130003c5c240185030b0700c89441c0e0030040e04001c41c200d2081c01e45107000c802200c003100f202c150024017010710090080f010000754034080800e503254010840030040301a20b00d00e005450300c08400b000380400900d07190300b002c243c0c0208030503c07600290300e00c5510f4054030080d10140c0c031207a00302c0b01d04200040e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 865399019 1250 865397769 865397777
    0x513061d061501020a14062a0306010e0301112205040e0a15090f050a05010e01020f070b09010902280806040c0323010f020a080c0403020a030b07091d0103060b030607 73
    0x340b00d4860b400e032070003a0954140b043d142c0701c0c045030342e55088a1301200c0c1180310950120041042994500b10440201c892540380002c4810003501d40350b01e903100080c0158100143c07140280001c0d2025040700c50400c40c0c013000642c039240015103034031325142901c0d06000b50140c050307800511402d242c4600400041844003801e03a0300c1007902e5000e400c6c01c08013a032411076565521500c000c034086c07142030450f80c4e1240300500025a01070400c1402d44820800240c0c19910400003200664211350444a416074004c0c1c28a40c10780d1046c01c1340340104000714010b07400c10f0744075004c07030688811121440c2c1120314a1319407901c1d15441c3c9040940e194021100104610301116090000c90702c0030340425041d142d00519034101d140d08204160941c1c0308280c102450725000310381a01c1c85c5412003402c0d40e2021070a00003500f4246103400103984c00090f0300c4058103a060910106003550300c503842da1070142c070318001c10b19600080120220b0045509100035030b0745900d01002051940b0b404a13840f0f01600d029a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 865400269 1250 865399019 865399021
    0x1b10050a050c0a0512190306081f060b030c04150e06070816060e0c01030b1522090c0804020a0915060f0c0606140906010203031b0d0e010513061d06 65
    0x1100380d0301540b1121441041e846080c001000040c01000401281146085120340f1344864240c0b148600100100000074542855424040c42c680010181c8503202941d072280d4607440a404a0001800190031074292010000300b00002c0d105994024811915403060300c3c000003401110850b840e000b200c030600ea102000b001480041403885003d06018200e0400303141100445aa82608a45814045400642044489241c95a018820300000403000e480c00390580815810124161082001160705140d503180005a110207900300c50000e02004002040019aa4403003c1e00b0b10f00201e408a108200722500403885000501400c48041e5204100440c02d90510100350342c2c03103900c42480b1081041e83c0f011003000c0b4a0600583c0f0040113541c094802c08540442440192000141000e041d0342c8100140401000c0b0a8402c1281e05800c1007111384035443d00b041d00d00034161901040c03915600b00700030301c01c008400d2042094031600c50b000c10050031500900508150010014170040b540040e8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 865401519 1250 865400269 865400287
    0x1202030d1d060d06050612010f0b070f0f03020c0607200a03030e09151c11010c080703030b061e09032802060d021e07030806010e1e1801081b1005 64
    0x4020700310398542c540c00401c4203178440c0041599504889404a4074080340c000400c60802e084407070102405441c0c00740e900d880f28540366615449034460000b8902000c0000860602d8800d008901d1100270090003103983d607501c0d081861401140f82130f90b440c1254490f4920805160540b8202c04680e0701d0344034100302241142c10817041d0b00340109503400e6403040910284499841022080c103040e40c9076a01c042d4540542000011200443c00d1981408250000c51000c00c42410a40fa80c3c1907240c500450815081c01c0800c104d4007c44803025482d20761000c508004082c42d1014148288054084440c4104c841000c0044410b40e10070600403180b40202080150070154010000c2c54040b03072015203460b0311035114500384c41c0559002e02103480d010441e04205a40101c456400c40c40901e00500d41c1e00c1c0d00d500180d044141024002c0b4200b0b150b400c101b8041e12007170741c1800c40b907082200c03410a560b5a03400268440a00e0400425a00c6c500324601c100c03031030070440b840c889414556640741041845 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 865402769 1250 865401519 865401529
    0x3020304030e090c0703030b060708160821220b011a1603020d021632030610050a0902130e04020a0b03040f030909140412050909011202030d1d 63
    0x54815801c025080004a06a45841030401d0040d0303c404d107155920245803d0040450f003582c081544110030803c6840040307007840c0241c7d03490311500e030800f0320005000d1614060070b102d8658880b803551a5200c050703007540c8400070310f988640510000c100d080b40042154401000c49940e000b040d1f00c009070010b1202d41c0700114003d002c040b14040c2c0c1403400a2080251400041c48101140141e12400c03c1d03045007581880300050300c00803070000780703a00303410b05105032403000800f0f62042d0a85002d1000030501c0110400c241c0c40c0d0340c0042d05840f450705110b0300345400c03001c00f401480e0040c02400c100158401c101e10803594a4104403003048881070810581c003803c91009403050703a0158948c0804946d03099400e00450043e4460b5828070100c500718030b009020607a0a030b00441c00d5a01e07082e8034629132030102e08120b600c81c1c1e02ca1411211040c010354191460b020340107d042c1c221040e8000400e2203500c8003004040307540210110341819031005030403030b441d1000c1d03203140d00e010070307010200f005074144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 865404019 1250 865402769 865402771
    0x2100314070f1709010507020f06011a030c090d0605100527060a0e01170106060e030d0e01120f0b0301110c19030309150f0b0f060418090c0b0c010b030601060807030203 74
    0x5549042024814280d01081c0d10050548209071681d54a030706001f101c0750100203108070444180c019101a6240c04980e00040c8071044e03102d007909000000080c1018007031421140c00a0000b05140c030386030164181130005100c00c03206615100300c00706010840386005403155040d00c0480080c10b00e98152908020600c076400703040d0700e801044002d0081259101c86034814041d040016000c032446903520180380c00e58007158000070074040c4400510840c0e803004143d44032204c10504206d40e03264110b000484034269803645034a1180e1a045000c1540505504510041c5100320300a10141200c503121080622401c0b006084030343c001d6455900c4490038a034040301c0345029003000140f22109071100c050100c0714000303441d074140d51140c90112460940c4144801c4032001e480f034101804000c4046070091299000300d0481989022505100070400e82010218651103c41e00340c61070303950080c240c0981c008180100c2d0b103500305002a03000d41000900d10303040b601c01c0e030b40742d0707083c0d4988442c194003e500c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 865405269 1250 865404019 865404047
    0x1501060513050d0501060902120f0105010935070602010c0e0a0e0402150d050f0105240f0d11070c051203070c0e07050c2b051903020f250210031407 65
    0x506c4840024400d002d40c8050410b40c40c4070703001800e035860404000d101086050300701905211501c1814894007032040c2d01680c601c0030700100e0108104d40490520180c11061401c41d2040c4103000002c958a41e06412070740c50100c01e911000507071291003041000c2c0406500803d401c85900400003809450003100e441f000e0b2000003903040c500200c105d8002d094604c00c58440d2032110000e80100460f0030008000510722000b0010705e5a8400d400700140494451500206000343c40800c500348500e00690020901c00c8045007025650220740c85c00c0c150040c0d840c480d00b8843c0064451150042002104688200d50f0190340c5140352410408550684039000c0e043e10204101844509088001003000c16840b481581d0466901c060181e2002550054280c2c0001088000c0c00b11b0094010302e43c16500d60b141d000e04016883d01403030000442c00b800b51900d00c20b142118604c138005c081d284200d0860486000b528000d100c2c462441042d0242c0f5210a95140b008100750009011240701c4c1c03100d580001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 865406519 1250 865405269 865405271
    0x1109030309090403180323010e10050c0f1809180a171224010201091a060d05061911070b070e030c03010603050f06011d0a1a0603091501060513050d0501 67
    0x8104105205c600041a001259151007000440040072070540000342c1400090300280034000e4a194103d4030703550201711151041d5140c101140c1481c2c99501650107204540e1724982d01d550008400c4502d890b20020309078000e14500000c80c580513031035240b03030301c029600700020040c6410345c1da03031101244c5290004e408505014840c042c5031001d00e928960050603c40c0c411503140c0d050185490503032014040c1181503a242c09400c41c001028080e410a400300ca2101d442615030300c020102e0f0f00744020540003803071401810200460034030a10040d42a070954030104020b10800200046083e06c00e42c03001510584074400000c0b40a84207116101032082c002d0306440d1041c00382d10219080d074640b40c00440350ba4001e03664808520204102c400c1c0188030414000602010104c07200301c20b414098003190006171a070b2840340c400c00c03444422001000002d05616030b05c1c548440781036240c0040c6010003000d14118000040c100381b0030003d0302e4090b60321428000e20030349040104040c20300090f108480e55 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 865407769 1250 865406519 865406537
    0xa0e0a1706090c010915050c0f0f06090c220213080105090124050123190f02011a06090f01020a020d0615090c0507081b1c031109030309090403 63
    0x59611000600309508800010711840c141500756a00303101a11494a040082d0b02c1020045d444242034500e40881c25406e000740d8640401201c0d078140302d00d21800072000c1c441e858404a0100c0002603542c441c1e21302c101543c1c451031141081080001c1141000382d00d03020440d68840a500b4158018081d104850b90041e4400e656010001d0a4540403603104105035900d04040f2066022003003800f00e1001c61004c4402d4160030080081c007100c00104c0c068181c5d40112500c40400302a07641110500082040003100d14070504c1001071084400a6800300154201240e5224402070030000007480780e001400d442c00c08000c48140280407400d000c0c0d0300d0442c0b040b00c290a0250702d0b04040f000700207000f81c42c04038101013407018028400750654024000705240c0210814002ea00c00d040d00d903955405500d56980d20281d40300942101111000850540100070254210a0b10041800c103500c40c6601d05110200d6000000c1c1e00d40e0080c02000d5406402c1008414a149001801280d125100e4208440c071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 865409019 1250 865407769 865407779
    0xc05090a06020c1201090c090213120f02010f05090d030e06040b0d090203011b02060403031a030114070e1008130507150e0316031e2d1a06060a0e0a 65
    0x40d880380e40c00007000d600102070003c035606102c1201c4152091303a6000f4030203000590b58074942030b405841034410309035003c02c000241d039a1099129000700f402c000b45807081c204c00d040504420a0a90b800c901003141d00c01070181e0203015009844114500401005038900151402c0c0d6260140a032000d9010b0b5040001003403c0c01041c014124655581c40c000402001a2060608540c6154078004032941d1002e80c013011640e0004481d0b0788950315290200e8184042c0000000d0406441410750341942010b01c405555886420014031840d603541d84c10890501140905c0400c20708041e448000a0b8005e0025102c586c2c501300300c03007501c0d20640445016903030303400c80000c051502e9210030780050705003240d404da9440c0401c1a83c0c43d201200040185480c9944e440020411803195060150b01c1485054002e000418180b00300d800c2c07205143d0003420240c1180710459003403050003120400d11f40c01c0c00704200c424070f000c1d2034402d00016010900d0034503841010b9130200c5c1c042d542144d11104409010031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 865410269 1250 865409019 865409029
    0x601230d06020d15150206090d1d090c0d1409030a030504080408070b040306050c04051c1b06030207141903121b0c05010f0e0d0e18011203020d05120a0c0509 69
    0x48010a1141084c280c03030900042c40000f465498103401158403010502c0b03203000000c1020741c0c002803181002480800a08203c600802a0b01c0d03100b584426282d08118040040300c000380b4004ad41d1307030000c204102d008807100700c1801064403104d071203074003d2010070000d6000e5805141c201e8054104030f4101507550200614044458003d440d9620740482c0030400c0000c0741c010142c02140e0116000d007014107050100c0c0181c00106680440d500d8010000703000c4c4194808410340f8140b107a40c001c1e6401d41c940ea0042c002c0c0d0300070f80e8100c900e0149080140d0700c0800100d651102d04281b84013080d03c03031185880c2162640425000d00340d0603541d40704104140c0440c407010080c0d0405035100d240021200d82403460866400d010071811036400c0500b0311440710350114102d00e0b12051820b0144d00040710f10049080f50341d00c6010204501c80c004004a844d00d005003889c43c44600ca5400c0303407400d080046003202c2e24002d02900c40da50f518042c010074248041c0f9048103032902d100d1b10700301e0300f0321200d200020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 865411519 1250 865410269 865410281
    0x1512010e0a021807140d091b05030d050702060a03150e13140c030a02060c030903070f0801150e04020904110405040b0f010b1201030b07021c020606030601230d06020d 73
    0x180aa408141504110306011100a11403a5500041c0596142448010b0050f06221040c2140c0160001b0a1040c01c5000d502c5406510340044e0020080c184c94000c01907101c440d405038501c24803482041e42150743c4030754200c410040e409803580d41482d40040081d030140588d490000e49140c6d4460340418252050714116205224103001220203c40c542001000b0704c0410900c01080d4204429041c20f5444c0002c1c1c064140340d05417280380c0d40715207544860742103000b80c154040d45401038030000180143ea204d0590300355400c24008001050b00340d000d070800c02d45188682d40d445115540010007501d0302c1e11085900a02074030700d803c03818103c600042c0031170780e04490448041c00b250f000e0252185903942014003416407000258940806502588420081480000c14400c0410001100c0754400d021407180581213554044000c051620085d440308e000322401f60282c032440000141100c9208030000542651340d0070900e08103404010320200c0c2942d0307401515599001c00415110302e2141c4a84 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 865412769 1250 865411519 865411541
    0x31b050a1b0b120405010b19181506031802090f0406052215060509071e081009020c12040f0905010815130f060c03050108060901090803151201 63
    0xa00040d980c5403511119910403031041100014404038140b0648490208640d100c00c070515402d145a82d5518200307001d05120507146400510504000424490881c03031107041d0b07040b504594910382c400b05d580408030b8040300c00ca4160342001030020021640031394003080d00700c02c051901c4a0010450f80109480840580302e0000784008102048240400b510030320b034104110301c03070100c0403051010003982400706910307001d80819041e02d070b41c41c5440b40d607610500c02850040c01c680c0007841c0510700a403e0061350202c06024036501c0d1034032100360340b050200a100d007102e4900d0524039410105000020740020000c211584140f900c125811b10011000e0001458184c3c00700324810300f0700201d5015204107a210454a17070101c1c3d44c1074003012481401c0782d4404181c00c0c4c0305c007441441c0c0c00d100716490000c020180646203088d911041c1154140c0015040e1034030316003184c0c1a61a021111805c07501540f1020b0601d040c1400414811005132400038815540282840c003010080660f40342102c00e10580 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 865414019 1250 865412769 865412773
    0x10033213060e070e0711010e120f07060c0e01092414120115090b030f1f031509060e03120103030e010201020d020c03030709230d020d0b130b060411040e04031b05 71
    0x800041a41c0035081b00a2010003c00a00802155084041d6580200803028011520104505650007090029101c4aa0308100140b24800c9091005041014045159130008082d91404260313174066460b030300400320030000700d4105001400021110800140a048211031007000603103803040500f51654007904100714281446139503200040c0440c0b1855224441040c1d09004020042104c1182c07560304c400c6903201d0401d1075031350142a80700b00349544c00042542c0c60b14902410300b4080b6901c0f0300e1080b4070a000401540104007072031382e520700606800303403003081854006000003440b40b8100701d640141800094140031016071008240e030070a03545601d4540c070100800000c01c2e03200c50300d0401090900701781080c0c1c00d001c2d03021000030300300303603c1c0f460286100c03152010071174540c0c075041e020507a08031240d0003850914160b1500c2c100c0c00c43c5400e03a00043c010003c22541d00e803d214004a94004410b0546054076250400c40d2a0700001c009400748028400c034200e0024034130340181c0580d481100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 865415269 1250 865414019 865414021
    0xb182e0207060c210e1b0102031201060903061415121e1b0f0105041509090e01020a08150105040311030a0602070302060a0f0606080a02070c0510033213060e070e 71
    0x40800204604100f0f51304194148190075401c0c18000c42c00f015540c0441a0103030b2800c1c65407005038a98440d502c0354822a000c000300005046a101c221041074070b04c6407100f0301828400b04120201d0380001d4030034030340810b5460300184039442e00c4507031007131003c000c44250b5142c0c40940081c4000030351080b041d03103101d0b04040c4175616031105c0d802094024501c11250100d1444401c000202980a60700881303441500f000b0f000d0500d94040c1c2d81e00401041c03213171814481d4410800e0014003030b40040301590301180c6141d001c01c6130240076201810340980c060751014241032079a1604001c0040589403190540a00c1c0f0b217980208000740001d005141c005c2c4c004108508100c030556046440180ca01c1c20186d00c2c0940072311006a1200e500ca0b04040503000c00340c0c8030302c7c10b8200b541d6594140c1e0f211039840249110707040d440301d4060304000d04403c80c0700d02210460001c0003d42c5540ca20310031100089080c030f0030001d40c0b1150a024031401d0340d4010100000d4405040500a1600c900740e0464214458114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 865416519 1250 865415269 865415297
    0x40b03060a141308160303140115110601061b0602040506070b040209070503090618160e01050a173301080c090c070c0608070e04090b182e0207060c 65
    0x291081c3c0d00400c5a1842226240d00368482c01064010108103a0600c5e1007440c0c01014548a50004144450f8600e007011065035156031040711807000b00e0040c0085945030000c181100d101141e094103c0d402a201c180d0341d03003c2c445e142d420f8040c1103a011a1220350900c00814907445d50300140501903c110117080340390030140100486c042d0000e0501003080b0007001088500c00c03001ca811a000306c10301e854034210401d1910964241016100e00004900610b03500061580030302036042e0481c0c1c000c3e140200c219442c0c8040c1440d03001e00d500c040015501003844e801054064511038441c44903840b481e40d0140e070903040090000c2c0000e034402103081c1d204006030642864a40304158020003003240700c62030203140341e4070701540110900c1030034144001c550014013914003c803503140328000002e000300302031700d0745140c101c1081e40700303481c52000103109981c1390408450005075442c03c60b441078540750030511129400030201075018490752015409010980000d01c03a4018a4104885611072001c000304079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 865417769 1250 865416519 865416551
    0x5070816140d0b0312070819090e090a0c090b010212031e130501060909050d0c0c0f0e0108010b030c031203061c0803040b0a020a1b020607050d0206040507050306040c05010c02040b03060a 82
    0x44500c0c102c00c0c1c02c0400c180c000040c007c00c01ca070052007089032aa240a10803000503070b0040941d0740f288c50340a000384100714010b0350100c2c1eaa500c2c10310902c84101130f652600308402c1120a1042c555001d07074032103000030f82d48040b544040c55000b5a40e6040d412038032000100d1018445059462110040c0d14911040c00c1003000e00a810140c070f041c01d010801f055503900c0e007940c0c0b400c000e034401c0d00f404242e81c418001c2c0180c5c1c0401c08060040e88450b8117000c2d940381c0f03e08113100f209200d51511035207860002c24541c41c02040021081e800240206020781101e1107070700391070b4800b800c031a070b10400030016000b20440c03903840300104a00401d40107480e4a03040c2040502060003c1400c1213030b620400008074910b030003001d0301c203806945200130804401d0a01c042001840740c41800340c403911810201d07120996000a1442c81140702c1c0e81070303400090b565000d05540710030603240180308905030103040c13080d03500c0380780341d00c18581c002440442c101d201007000c0b83c1015020388007040d40d5901c2d12031000b018480 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 865419019 1250 865417769 865417783
    0x160b0703020606060a140d0e010c0f030b061306050c100c050901030f050105060d02090402071e03120e120903160905070e03060105030d050304020321030f070305070816140d0b03 78
    0x709070f0390380d850a400860011b20302e9030044080004a80041904003800000f80e200c1e1072503114140007004540b68190b00501500c1401851100103070910700c203240e1030b0610b00e06a86049508004010000e41803020076900c58101c5141c0106030f03c910100c29102d480c0d00d0190191315102512915580d00000d0700060035103190222101490381440010011500c42001f1280c04800c111401616000b0441c00640a0710540710058640d08605c0403191070340503c0704c00520054401e403a1615040c0a0174000303015242071240c9001c0c143c00c402c00b4421080d103d0001071445120080903a20030a09420300e85407055426040518442d540c0e504000701c1b2500241846000d940c03c4008100540c50100081ea0318a00f02c541e48042080100124045443c20002d40c0e204100321300243c0e144d04610407800405030800c607071740b20301c0c00e01d004041803080c1c0c0203105030340c02000030307540700d100d9a980c50641d0200940c0c0e10700408208640d102c0410211901b090140c10200e820110100340d42c24190101480c00c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 865420269 1250 865419019 865419031
    0xa0b07081608060a0315090b190501060c080403030c022e0e01020c03030706200c0a0b13050d080603070b0d050402040b010f02150a0f06080a0506090601050d0b09160b07030206 77
    0xe4182c20b100b8070750303146440b600440b5440741d1150511840040b4030809031244040041540c0135030414072520030300554840605400b140c20070030090707a0340d150480d10b01c0e801e200090300c021001c00046c00800d10400711804800e0014203681001001c030700c289a840060b821011184003003846281c048543c1c0010011026031003480241407000408001030b45900c10050014051a0b5825000c0030407084800c1d40b41c3d500071010140c41d103c07080c2c804050f0b00c800f1001382c201d41041e8070303100040091083c0c560044049030004010102040c40d10002e0b0b5807100013a00d1640e042c802c400d03000503a1000c010041012040c00c01002c14141014414001607480010080d814050903000c50120305500007450810443c03011561b00b010b1322451221801400c100c40d4042416041c0380021911140000e4441d5010740f083e803c40c2c016a50300010681c81c1d00c000e0041a612405404201c008510001c29840d04001c0740030075102d003014116203810304c10121303900c031080c0d031308000c26500c0605405001c00781c1e002c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 865421519 1250 865420269 865420277
    0x1a0c1206190605090f0301140f010f03080f0307200c010912081606182306010303120c0512040507080f01060503031e0c0105190b0d1e050a0b070816 65
    0x3040c00c6103166580041c034007031442009400b05400e0301d2942c0f02c564069102d40044c00800c050009010070341c1c440c20702284c80c20341766400c0000000d02810708a501004903504000c0e05410541c0802c10481540d101420714030030040d21429444458092004401c404441c160080420759651b4001504010b071552024400040111540b40804c030000c00310350120003100d103020f80814041c9415401000340c0c0c1c1c0b005003c00b003884250410072400a0514043d4041d401c0d0846909910701111980d417a003d0000900080718041810000341c03064005165000c560b0403d141448601c0c14584429441210103940d10b9100c144d042240880a0240400440248000788401810840481d59a00c5084000e940c050030601c030954004011400f81c03514088400300038025810308540311240503c11007031b40102030345030080541c21841e0480070a2361a9910070240c0300300040d4086042c0c58002d0801c400e54540c062413031000d002800714070040f8400c1d50302e80c07500103090800d040d40886c03400c602020036040c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 865422769 1250 865421519 865421539
    0xb0a0b0310060c022e09050f0a030204020f0705011a01141201140a35010204030b0606031f060f02010c09121202100603050c1c02010c0f1a0c1206 64
    0x11902080d180c01c02e449035030501c03072060403482c40402c01e81e0324100c3c2032809507450710140790b0482028500460000c481c075951500d4561f11030341001301e04804100718541c00941500d0801c018103140e0050400901e0183c1510b05061444c0c8409080d2000a1141307604c0104140000e900c071340e04400003500071092481014203000c600d80c00c1a140e6001030040c10034241e000c11502040d42e989011601c06000340031040417200140d081011801007a0600c100d21081c40c542c240460000c051007982c1c1240c1c0c00124950f115124013050010541c409005001c4407816020052b0010b900c044001c0000d003140da891342d40c0c283e04090004d0171a25032501c040104040e5041c02c00000b1030044a0203060703a0046d00310b1603600c040f0101640703480c2c86101c207080e0b5181803020003c140140410303071040d0064140c825803014200c82e81070001c181c101c174100a0106001c030221070080741090f500101c0c00c912600307658483c0c1d12090012000c0d2801201c0f400f0190000280a250211117002455041300c0e040d206040e072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 865424019 1250 865422769 865422781
    0x60302040315020c0102090604120b06030f0c0f03120c060109061e03080c0f01111e03071e02070b030f04050d03090b0601050a020c0622080f03090d050309130b0a0b03 73
    0x34030340902c0302c0000c11900410451140701c820340c1110b5a00700001e001c01d42c1d0359502e43c0c10701c1040114020940d120141480010380034200400c0d600c0c6034030617007409040408410010042c42c1d0054580c589d40510440c414980c042440030014080300f120a0001c1645624000000c41a5003d40c0c204151410812401511800340d00c42800182c960002046031120b2286007840e1034241c10f5a4108107960920a01c414031714a100e00420490300702e05800300c120204055480d180f8807060322107400280207245c04039a550003044180c0e100342407601c1071b60103140d90740304c01e40c00701e0304180c40000340080c0d45000d020410204209103907030340ba01410144006e8956031140d0140400007003001c1d040c0a4002002d00d85c0758070034409004551402002c05840c0c2c22884040b0160f0701c001719041c5a842522600410001c10015082c07644191400c0114500707400714080c403408440030038080b01c9901c003d01560966655150801d00b01151005c00007482c01c840108002e00d01d5016400388400302c00070024406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 865425269 1250 865424019 865424033
    0xc03060a11070611070c0f0513020c070e04020a0312020d120b0f210304090509060601020718092f1f1b030c02120c01030606080702060a27060b09010603020403 70
    0x1400c0d4000d1400242c40c248500c0c0710113144140c9800420301c03100c040021038001c1030300100074103a91080c0c900700162018400d03080300701c0c81400740d01c40c1342c0d50142008110751401400510b17030152004d4101e4902680d40d58402c0b11460410f00a5070141e082004851056039100c403030500702d182018014000c0341d120a02090418600c414841c0c0207c80384440703043c50652070030000c02100e203e2022680e8540d5585e19400080c00142d4051380240103038408588c45600c0050308070143c86062000000c007004c00d429060040005d081c0032601d50040f00c82c42d65450040b150700141d00000f104d50303a01c0d60500d0030100140107401d125101c4001d41e036540302c10701d51980206100e400726a286400c4440e00b05c541400c0d59141d440c03990081d0301a01400031f0140c451800300342c1003400343c030a0700c05112482c0c4030340040c1c444c0308080b1603260043e845a0005500b039480780e000001c8140c0008242c0034001c131041c021315034106600909481d060707119540100a0700b085407030703280100050b2504506081c10360784e031a9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 865426519 1250 865425269 865425277
    0x815010c02010306210215030f0a09060b181801050112140a06020a090812040e0a05070c0c08071d0103020d030c05011401030b090607320d0e0c03060a11 67
    0x90400161031064401c41e4001d901400150540e0b045010b046008001d1000c3c5440006008074040d02140706480e02e021410425680520103005c0424055034680010a00800260006860141d10f52035520f0383c40c0c60300c00302801c4428407a60714140c0d41c0740c10905200c40301400390303e00d50180e00d0640100000c0318005203a89003554400c0040e8048148503943c4d61802541c007001400861000903070120f280d4000c80e0381c40445611304141c40b0f84260704d401c072030182d000358811026000c500030000740405101e0b41c48180c0c0130030b860a19119084064441300000c02c86600f10021940c085807051002456200c0203103240c044901044c41c0a604560200d54078456090000b010310402c01070000c02c100080d000310022401c0646000d41540c2d69062000d0749010a64060030719004690104d0102442801503046003107034501d82c2149198403101e1085904021400382101803014040e031038072101940034120094440314000e10104451104141c1402d40c0985021000d40c0b41480458000103550251 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 865427769 1250 865426519 865426561
    0x6030727020f0d1508010608030417012d060509040809040e030d0c090302130b09040b06011101090615050108010806041b05060c070f1a12070c150501080c0108 70
    0x54000100c1080990040c0c050003a03040402c40d00843c51404024440e8030a0001e84107185048064a130b40794441402c8a6081c0150f080d1a002007009200c070001451240040c0c109000c00001d800098807086800c4001d0015001e000402030581203004584600481000d4941254500300310f061650f2802c0d101d10a5580c81c5d03002d162181c0102102c00000c0c01500c6820a016030107000d40e1020040c002c1001100740012403060300e8002d40409002c0c3c40b482003219048000d0100e00c840d40702c0761120100e4401c01090f4504000c16001c0654160350203008079400680b0a04011a40c0d03500400b0031100d00c5640c0d00414100848000100001e400000b0340039006500a00800c019410b807146410200b03034660030640c1c01010001e40003130010320005d5604200c4550b440340045407503d607800591204418605020007510507c01505508a070440f800d42002d1070b404d0603003c4408a0b52140c6078140c0200c041d1403441c0d6213000400050038144801e488001302440c000c11245461003440c034440040e81c4103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 865429019 1250 865427769 865427819
    0x630090318040c0224090d0f081b09040f15060804020d0f0f080c100e1903080603010f090f150c050304260c01060f0b130b070314120906060307 63
    0x92643c07814028407048164a4403112400c4d512070300c166503030041c8042550f00e401c042c810140d600103840d2051401030311072182940c2c0c2d900c450b00c0d07088840c1c09084440c03812901e080d2007000341c0c0c41e0590f640e00c21400345070f00d04600071540c1d08141001c00d80c9541281c4c03040c81805080b40800005030b0b01d50660103052544661180540d102e942001c0e508848000030040c042200011401c00005001401c03411141c5070002c20f00520040c140d51300d80b0b680303030f03441d00515560b82d10300350030300081c001d0051680c824800340001800c481c2408110044d10020203095032203100001444042c001c401d82e0032034055005141c1442102581d60000b01a0721005001400d010b855619144200c99410601d0044030748070741c1c000c0d46503c400408240282010300c075056810a1000001910707104100940e19910144001c00b10102e140000d40d051903400440304504001c0900355107907041c2e00d00c0019240700c181010404c401d520300103607400c1c0741c00c80180206100340d10107c410400c180212542e90603568455403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 865430269 1250 865429019 865429031
    0xa020c0a08011404080d0615080f0a09031b050102090409080712020d080a0207080c01050a061e0f09020f04090c08060103060b0c0d0f050706140405150c04050f063009031804 76
    0x1c45e0000c0085411021034410b548d00d10714001070307114801c1805031220004038825500d510968004603203140c5402030205040080e402104000b201c6034003551401a0009481e01c50303400c0001d802c89404c0c00046812401c040740010500840200c480c09410290000349141d0061a20280040e00010320100c1002d400188010410002c1c2c4183c40c1d1100703001c0000e00013818590b480c0b0000d0441c0340245448180c103402000d000030500b00c0d85404917885008108001d600b0003031101c0196003c03d50b0f48060807410840010791840501c101d8500d01c030382c0e5a0300c115608104000409449031640000704a08003444810502880031031600d0103980e40303040042c2403c03621a429100b0340503602c80584040e103040a8601c00721200046144039920460940e02c60000703404071001350340c0c426120701351000c50900052010b41811180a1504540105620305080c00142e01d8226841d510180340c0829500e0079034034564a103503411040d0052175050180d1f0408103590b0007a0240c468200005100ba51165 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 865431519 1250 865430269 865430287
    0xc020d0e060d0b0d0b01180204182016030f0804030e04151a03150303120a0923011a030f0c0613030807050703050c040c1b020103110a020c0a0801140408 67
    0x83c0c4100c0d1500405004c01800744000e08111100a2091044501c843e0000001c0c221108540c400c403010703211466004070000094605400041c110a81401c805001310034060b1111141d540180c40f483e5403000b403040c1049040d02d0024184450452120306110000080c440081e4004891030b403203000a9a00060003104403d4456060441c1d034084904540c070010504101250040114420301c0d014440340c100e002d1100c10700d1382e42c2c401c040d2a00203140c404400301d4682005904070b064460b0080385082154500d014003c00708084ca16482c902c0b43c2c3d5180500e1038403000304045440440401c500ac0d080240300343c48030580f2400c84e0403d440c030030400040e100c00c0400d42002c81a01560704011465100c101a10701a0343d54901e6020554aa00c1010a088014901801000c0515906580701400050790f031060750700111035100304905054990f84c21820449840b40944103910881d070081150341030301024001c0404890300000da06d64105202e20490b4400f51407100d801581c020743d80360b5951036103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 865432769 1250 865431519 865431521
    0x221404080a1d040c0f0e060703080118020d0c1d010206040b070e0402160302070e0a050c270909010b01120635151e07020604060c12050405060a0c020d0e060d 69
    0x7800968000d150200742d08a180d480030f400405c0100c00e45800714a40c03200e0040181c1340c080c4102c01400121100c0c01801003000e1088600d9500200d1500541040740d91603903e800e440542c0650000620300102560050364120207404051800380027511541c14151151070034000c0050245040c44959003500c04a501c659040b00c42b21424120342e40c07001029450029100c031307800c3c85031000030962100440c548a1a80c402d007409008081b008500d0006803040c0e050380041c0104005644400e0082406590b8071500303100c1d0b224900806c000942ea400d4440007411b4004085040b200f40340c81c00c2024400a500c841742030400d01408100310019007140d4031107002025040f040001e19000781c84140280303001d410409801004120141c81004902c02134410380c404007140c018005a0201f03000c07801140b843e40c01012581061310346000703419405070020084e14001c1d10f04032980d5205400b0449003054510400c0f2040240b4030161900b1000d10304000c24054910450b544501400990f07414104a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 865434019 1250 865432769 865432817
    0x8090f0105120c0a02250303030507020d0516080403061505120f030414150c010203060a060c0302150c0f0a020a0215040501091404020714100c091d04020a05221404080a 74
    0xa4290006440c44414240e40c0c2446c0341c4001c4000c24180000b00e5013440c000300e0941da280311580d8540b410104844446120840b6040e01500c50020030840400819118050076414980011000442c54508420f208121070147c1070100c2c10b4000f29a0400c902201000f190121481d0140710300860342184000f441201c0d900917805848040042c07400000c81040d0003070351068104481c000940f550b00c100030341d500800c005008005811540c0c1c212180f195100b0701c2c0d40c0101080c00c034a81000036455660f18558802481c14000d603000d40d4165046150003580c01140104070704040f81400c0c9070070006400708490f801000440301003200f80c4206521281c1c150343d001a0003000c600c050110013200e40b521002001c0800c4011400d15042c503c03c1401510890110351584010704405100112010800a0058070480e0300a18001000803107585260301c4407960b0095520f003c8540d0504042c250880d000d00c0d500c0c01460f108641004007140c404d1050b01c04003a5941003403513115802c08103040e85001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 865435269 1250 865434019 865434043
    0x23220b0406091404061104350d05121302060313030e0306160f1e0f0c020312041e0605160303020d0515041113120203070b040308090f0105120c0a02 65
    0x3182c07203035401d00d07805a0300e421130085008020422204c10064014a07141c4100d0080d40c4a5420541240582107103048001811500003044d03440d50f80800134040d0704000c1c03509644800a4400b09401401104030200a5003004402282c0d021003541d43d0702042c9980001040c0c408202d035030310038120a141c002d00a0291004004091b01d002c2e2420800c000411109001141e001403100c140054815000d100c292076110000d12022455080010007220f0540c4161200070402541c13010400040c5c80400c4011071507030b10308004949590800c11401c04490300005110340711004424104001c5421000704d902c00042030400742d5000040307040c2a0007a110713222103182d0f51032801041100f0303030110400000b81d2800894040c440800c81801d1a0054000c00040d000c4032401b8200c1003000c40d00306585200080d201400399141d480c2d995041c0c0d91290000d40c42a51103250001d4040304a2034500300a00c8001d000342420b50401100900104c0e4650005025040c886800901c540042d8001c005041c4a40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 865436519 1250 865435269 865435271
    0x5070e0a1428030501091e0507090e1006090219020a08120a020f070309060206092a1f02100f230603010f021804050708070507030507030909020423220b040609 70
    0x60382c1c3e0b1624500802c032aa90613100c01d01c000b41c1001d4940c0d00075815a50b061b400200522031242480b98005c02000d090f00100c4092040c890f55400c3c0716074500850006200b60980140c030b4030806801c2840c1c21038011001c00c00c64005e0380d050000034000005072403803a111a0b41c0d442c1c840d03450180f100002d100b000d480540c8100007180e164105070740038186006807007403903081d0340c0c6903150709069030303554106051000c0c6042d44001010003201000c01440e51080402800210711800101102d411500312000740c10068104010554504015005a090080400d00304024180311100c8000c401006002012440d034080d4000c1003042d0b409400c00b0304603c0003880c04640c0c40394003165206aa441640046000f141003c002458040c081c0c1c140d60301c607071030a843e0b01c0c1c036149503a170f0216101d6100c0c882c11001d0095004020414540c030b0b00c080d0000d4044145a0440e01c80548548241c4200c10000d1500c900e240c11070400388030003011401c0c010026460404100801a040080d016003001e8005064032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 865437769 1250 865436519 865436599
    0xe0f060c160807060b1509100302070204020f190e0102060c030f2806051503070c02060703170c0304020415081b06120f0f0a0921020c0d050105070e0a14 67
    0x8050a5400088220170445449510b000001c50314061030040c03107860303170f0711030010a5003886240c020b07001802c2d4035200a00040c0703841d459020061443e08114a003a40c0900c00c004042c5520b43c008020a4151900b40010301d52440e0095030a500f03444000d0064011400c1c402c0070030800c00e484000246a503041005102400324020560310041c03020303224030791003404078405046400b103090080303902481141d81da42410440d9a003d0002942c800700040303080104c82040c00e4022240401c40c2401000700c100482d44e43d0078030340100400c1d00c00d900d80404241c0040c0e00200608080004c00c0c0c03a04d0051024500000b8122400140c41c1d40641030744600b0305924681000402403c051040b80304803c020903510740f5407103c03c5c4510841d43e0b0040001d000b4441103000300ea00b05640c1100030021540c900c1100c403500c16402c00b05807901688441103807641c0d103070014801020b8011030000070140c0180d600161192034a151001748d0414500384034000c0c0c080002240485803100040710007400c40c00b22040c21 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 865439019 1250 865437769 865437773
    0x121060306151d011a0706060303020309130209180a0f021c1503030e0120011a040501120503040302240a02070801110301180c0302090301110306040e0f060c160807 72
    0xe00700304021060340185601002c02c81c0500d0784520760714803c005100307148603801c00500721607030050b005806942100c203100e501c0014510307002d008051846580a161226003010a10000440b501c01064075540140200001ca440304c40d90101c14402d10b03c20ba015503218188003000600001c91a00c41c00c0f400018681030f0a0079551060360401d0303540200b00420300324031440e07044a0540c3c0c080203000509003a01c6807415031003410080740c4070310401c0c600b803848000c514a5900312400000e0700111b000c0300300c5580d480c52819218103401840d00851002854a4a58840d40c80744903600009101d9020600c071502460401e8100e00c40000c060f110003596011414406503450713600748202c0c0303415803c04400150028800003540d0482c0d828070314040700301200401c0c94000c1d081c40078100701010303405c0c400d100f101da80900030603a1441c1e0385500caa540c0c1c00c00300180070a4902c0c0d03400355442544000d4554210007000100e42d80d1080c2c1c0c0901c12a242c102140e0800d0b1000000da0018050301d1004c01c5a41c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 865440269 1250 865439019 865439021
    0x20d11150705160603090c1517040302012c03090105210c030a291c0c09140f0411010f1106010f0806060d0503041815090e0607030b030601050121060306 67
    0x282c1c007251681c0c40f8010b0755032202141034400c0c10341c5c020305212130600204461303014004013040744e09080c1460b181c0c007018140a510f020360b00303c81c181c3c0180c1d100c4c1000e554108010f80024904002695801e004801c643d02c056500e110303942150b0304200001a16442404a0211044924500b4030054840d0300b0b00888965081e041a5900315001d460008401070055010341605c1d09881c1e044000c10011084038204040c102da15042a000100603007003500006000751340c454050034550100140c0d214415604130340a082c0105845400716881003070102051392500d070301032108000d10703065040310880d1008a82006000003070000b42c0c42404000700307a075001f80d019107064401400031039172140d49580c200070500c01c0d40074029100307070800c10081c011a0085428042204840040401c9200c1e1244070446403c2c5140d01034044030340c0e180306030b4041200a1101d6a008542490107006941c1100002629840d0610446051040c040680d0440d0f02107207003900c804c0c0d0484081000361594030b0604030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 865441519 1250 865440269 865440283
    0x1260901050711060402180a1b02030c120f12061207030b04030f0e0127050a120506091209041a060706050117030a14090f060c0102040f12020d11150705 67
    0x80c0030480703800102544580c00601d0030300c959001030100040d100d0034401508000d8004c1d1150001e6034403404c0580d902e102002d029882c2004581c02541e071334040349059814840c5035080c00c0e07208001000340b51003940e01034040d1844845040002230003501c8420000d644214500041022130103520000010310030702100140c2b0030340c00707511110495801080220769080c032060490340803d0455503d48180104460180c8030074030780e41c490030451a1210005800c02c0603039072100e024014a050742e001004828040d454200120400800181c102e10680003a00e015a043d020300860b0741e100c2c001e403501c3d00c8000955951001600481d510021414200b02800090158040443d54501c145d83c2043c0300008556150302ca95035000040c50743d0041d8000c69604c4408142d0303005a00748600780704c40e9540c5c001404402ca0306030005a4440c0341607040c0e41240041d610809400314030244403005626480942803040b51b0200f40e0a003035281c0c1c407002030f00311866413000384146503000c1203c101f0040002110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 865442769 1250 865441519 865441531
    0x40b090f0a030b09071d090a200d0f0c0b090a09230123090603030f07061506170a02030411011209060204090f0f051006180b0316180608060126090105 66
    0x1086c108800a0710f043e5243c3c20130384036049641d00c4004440e011408501078940c51504090609449961a100003215440c2542d4283c40769217841d4041001c015010380c401000307101018400742000041e000051420b80c89101310f200b0607440c0c024240c10001e0300d02c01c002220304500c2c5480c0c80d80d40c40b102020080f103c0b880742c1c0301040c0d0180e0311602441c5480e00d0304622603000103000f580351880140360b000c4146c009a200b01c0c0d405440b0442c00c03208100302d041c9040036003640da41d04082500b61a480c400a001c2c06000c90100a00c1081400040f443c0e20303071408513031038013804c045e200480c9000c1030000a02d112100030f4001423000c2800308403880d6640042d458208a2202404045c25030302401c0c040790415030310120100107201c010066503016480c000c0701024100030f440240f580d0b503855142503600c11a101032000e650701c1c44031030030140c1011030700426030103450f0318958003400e00002910b03005014152070306020b86074030f000385028101d2211a0310380360182180c2d0b40314200400e00c0c501804040e030342 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 865444019 1250 865442769 865442789
    0xf0a08060f03070302090118110a0f02101b08070e21010b0102031629040804090c020309180a0207050a050a0201080612030906030402010e0d0302150705040b090f0a030b0907 76
    0x5401c1924001644406030b07a0010060f620366460000c080c4c0581c0001d168860382d1a8885603004803411925000d820400d800740c607022a64080040000c0c1400607501052500d949000074040314003040d01c0d1001c1700b5203030500346400c1d141c840135016180c02400071fa00c640d1110740d2400280240803020429410801d07607070000e000113007010005a0712030255020100810380074000352008140c40000004c80c2441300303c0031240804180d0204000ca04049405494510f070000701000044210302c124040901544055400d03c08800000354501440c448906a07108262001c0759100c02c01c0d50460755990b50100840b140801145081c6840b95995142a40441d1500001403000e0038154101c41c2003120400195281c10703100c01c00c105103a04013500c1a130401c204400b10301703003d032505031081c2e0917180240c005107141c8148214400621000030a1141040000d110800c50040d20409403950340c1d004550216106841c14042240140d140d80081d0170201e044007807122855000c03c5660554140c415 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 865445269 1250 865444019 865444039
    0x10e0f070617040213060803070803040209132f0d051608010c0f030c020c2125170c0910140312071101030b19060e090402100c05030f0a0806 62
    0x3002e4920030707500401c01001d41c21940c0003400500e800380c1d0032103480181001c0003030490380f600b00080c80c64200c040d088420301070010900042d850041032680d88200422460b140c888229039883d440c000d4591450007a1511a4010a400d100c042d00301c1801000c005d007544840005600344181e848801c100b410504210400b40421422018002c8844c2a031090319082541030700200c040740104102d1120b681180684051500345689200d14202c52a50500d10684a4035801401c1414815814503102d00384e0640101d42e1400030358084c0c2c480c1191070307445003000881544411a800c2c80d1280b483d03294042403240030001d00343e040c40c00d4131054600c20300d62640702205807400d15030340320020341580280c65010310124000602c1c1592283c0f107030606150214940c510180072440540b84945101820041d481c02400a507910850044002004a0344403545080540208010158050405082049001c005002d020082084031013040780401d1860781d66101039401000201c058600c01d21400d6124 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 865446519 1250 865445269 865445279
    0x506040c0806060309010f06060e130504020a12060f1b02120406080408180406090e2b14070507080a020a08030c0c040b0102010f020d06090e0607080402130b03010e0f07 74
    0x120a1280100306074031144800d0315400108069504010910501036481c1e0000d4042100503025201c0200380e40e03112481a01a80b104010341045d42c8418019028a010b08020150392004103400c1101c00544400c92401c045040c140090501032030603441d420b0030300410722010b82e2600110090b0040f503074240ea0880114894a55240c4101d101cdc00300061841400308000c035094200400943c54150b640e00709980e00000400c0a40c3d881d6440100c1c100da031030110201d902020705c20020301d000390001014180d415050005101000484800104804151100c10b00385111007202c00700c0740c000b012500c0c9560388040c0e00740e0710001064102e0003600a48400146103a0010990704c0b000c40394400740100328607030002d10005281d400504c50441d03484810f9004045a10b100900c00010114804594035090000807419034800c0e00764441c580d80304100b00b1100e07079070104610350865811518409880c08110080c0c0190440464103649540703050380d80900b090f0006a400c01c0d808100c0185d030300c42c50f81c84d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 865447769 1250 865446519 865446521
    0x201121b1d030730050a0305030a2318160b0906070812061309111e100e0306060a0501090e04020409060c050a1d10050d0e0f0601080f070f0603050a060b0307050904050604 75
    0x3c0130b009125a104000a9000a00440203075512092030000002c2c82c0715508801c203200d0010039a881c100d0380450051160310325040c0703d207204ca540660000d041d40e82d4140c904001b000154410704401042c085908100c5d83c0e114400c60305013581120065803201d4001210382351000043e500c0e40c0c40740500610009407410507028210032180c004c44010007030001001404000d1313217441c0707000d0750907201c04004007403a964041595110003e107546a080c40704810060500c1c00c080a0301e0315108120900c1c04014681c3c1c80702060003034507803040780f000d41038482d840403c001e884082c000801c3c803802c10301c0301001280c5c0000a40410840c503900c00c4507034010702c03a586c40d4541100d101d0136000300300d0078000d42a290240c0014107810030318410001e02c83c0040401d06040141c0007070003c4050f04060300400a82c8010448212030312200c0c0040c1c02054600702c1c00b05032075a424480c010030b15807200700056804400341e101788010801d140c2545d5492620420042250340f18403110b030b02c1769107010081042c1c4d05103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 865449019 1250 865447769 865447859
    0x41a010320010e011d0109090e030703080f0408220b0703051c0b100c050c09090c1018090506010c02031c120216022b08070201121b1d0307 61
    0x8182c554100000800324102e00c03040ca40c07882c25052081020700042c410719184903101d1027141e00700c042d503150001868003c00020f0080c0c0074a544810070001d110114034003404898000c854214100c94195000d030036041c403030745146e00c603c40946000c66002d0501d90450020234026003100500303640030101001480480f500c1340201d68010080140903442d140c00f55003038081580c029400c07a0034070700c9041d001400108040380c2c0840e15420020280070b540c144000d01c4800d41101d810302008030240482d48080e0768419200310f400e4541c868020550701d034080d030442c60803680c02070140c440c8100c980c00500c88a9080d5011003000a1550915440354010351007a00e01085145070710010030780c41d90f0208110a481c0308111710a0344510101403a0301c0a58204000301c00c1d106204040c0c0300c03061070001408460180440500f440d003084049200070300104241400d0349014180107007400032040110344864804124590140704400700400c28181d184800c00b5581007800c018125080c0001e0704401e0654 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 865450269 1250 865449019 865449047
    0x31507020736020d092306130b04061104240206010605090a0308070c051002010c02100b03062707060810060203120a05190516092309041a01032001 65
    0x616000c81142ca0b8045400802080000c1c03240400d07141031588030355152948841d0200407038070200c044c1190b016000d001d090b41c01003402a640401800341d44586540000c01070000300000c2c0d43c1c0084034048142c540685001c0c190f405905400c103c0c103182210344185421809001600c984d070000140e07544650300303c911002c4041d01c440d00da030340b07196035180c015000300004a80351466002c011031243c0b00d42c44041640c20156002040c0d0003507030100a82051800d841590003035041010350081c030307100060325075008540c80384040104025070100072400c0210341d903030107418080c8640000710240e1000c141ca02a00350781160403c180d40d40c0030305036520302c960684441d100201500150545465078401d5900c903000203e04240031040c0020042120070445000000041038594140c500d033f031008900c4064222560800001180001e11010a86c040b6048a01c00d210344c0c80018200590309083d1142c00041002c584c0d0079503120b14200ae0326040f420701200e4808202581c00e040d0390b00c2406140002c0c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 865451519 1250 865450269 865450349
    0x60f01060c140c030f031809011208090d050610031403030f0c0304080c071805090d050d0b010c05012d0204050604090e1c120b15090f0315070207 64
    0x84660380c900c00c0340003110715071008600034128150700b10340742440384031317854221400503642d80c3c0c00f24807005a0500100c00854001d200400051080b842c0b82127440000c903820070036040d280c104043c001143e81d03001640050060003290140540344403240c1e00300e805d992007a4103001400100f813038080e640307000c00c40d0205001c00c00d07000450b00c0810783c0d40045030014015101c151820414483e450301c0e1103410381c8001c411445840307400005e0407052140c6504615003402031b1914001c2080000e20701e01902c044407903030640c1c0318207201c4d0303580c09282c1d8040d407158014000e0101c100d8820101d41440065a00149010080160320180c0a0341c2c1c42254151200100443c5c189400d205151000340f5091581c0315961103040c0034643d503e0b90600c09101c1b05c8142d40d8811000d8519950700c1419100040c0c0841c0c050b1828000c1045103000d101e060b01d4801d00c00352103111205e8031500c0003901d440c200b8030f100c2c40700740114000c1c8107440e603006c02c03000142c80b400440b41003884402504008201c420b110001000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 865452769 1250 865451519 865451537
    0x2010606260c041703030f0105030a0c03240e0d030506060c073b01170a02241608070b06010908100c031104141008070c0b070210050406090203060f0106 67
    0x2072184411040e004065041c9243c1480d855041c1014000342800070100c2c0f40d4408004c2020078003602c00202d01410056000c1c01111002d683d421020030b080d400010040000b0342114003158aa2507014440c000a0000a00087c0400440d0750f8640010050900029003001c00142450602c07204850000b001180280030003407601e8450340300c1b40040100807030880214070300c1602c500c1c0500518403020a404040741d84551401c10302002c0c2d404803411003501c0380c0101180d000940c4d2031345c1c01105041c02c9048c05081080d59400d9164007886001045002640f002c0c4070203003840309010103402a0392141415086a84502d401958001c4862080aa4035800b9242013281c1d00540c0d040310554420074100445c12030060103072110640c000b80c121013403074103001c41601411720740201d801d1220021030810380301c282080e600c001e0140c2100c1c0005000f0201140c04035482c14401c015504d071513006503004100508103442d02c2e0000d46410901a842841075102090220381e038030b2502c0b030494100342c1359003020b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 865454019 1250 865452769 865452827
    0x5030604030302030615070317102105030d060f030c0e010506030601050d0605090108030a23090105071109041a0708010503030d150b130303020709151a0d1a0102010606 74
    0x10b13501c0105800d410035010000c900555282c04c010700140b41c070030748420f0b50320700300741440840c02c00b030040160b480c158807140300300032040540381d2001c1c0051182c0080803102d80306050440c558403440341440f03c251b10f800c01c0050440c4480b00980b0503240b0a489040c040c90741d8406003040e90100307008465000104201040e591360045000303040030044007d020071526a40c07030000361181001d81c025002c94000296052019074800388004841201e0304909030031103041200326040d40601104039051241c000784103001d01008203040100090020301d00d0b45030b89030a10b041404d10400f41100c080d050007074004a0400c9000e0000349050b1000a03000714104950911b5820107003074190401015003143d04008100c031050f000013014600004c0b8101e140a40c03075482e0080c640700c11940104050303803800c40e9070300105950a400303c044a0b20760202854454696070290031070710400e845041400c0c9004040454078528402010340d0b01c109800800ca550b17074400003620100e00701d840000b500c002da050380b100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 865455269 1250 865454019 865454021
    0x2010b1f0f051602040501030b060415080c0d0c0f081b01020606010c031215030623010b0423061b063d030b070207050f12300d0e0c0a050306040303 65
    0x1c05003c000400c1400d10700360f03008503003203400030f80042d25068035182c20410f85042030f000e001003011a540e050b00c40c81e07140c12000c1d61504000c0e08031900c02c0005503e25814400203201ea180a40200800c20b14000d43d1202d41a036516038642e401d9400c06c1071481d10100c01e60021031071920445045e1650403456503e55001c803020b05184c80130f8100e00d5520714110551031020340c10500654418000040c50300000403100c06011048250003641c0704200005002840c14141940c0465040c03403080050641c050802003142510030780710581107400490358200030030740c02c5407060703480607504190b410b1512280d80c19620201d5144882540c1906d2651034851000080400800041c51584400b00036441e03541e41c0504120507501e80f4010b034400482403080349070002104480c0a0219400b0b6042e812564002d500d401c0580040450030010300495007a0504110a41c1d08402c882c4545a9660700c0c441e2a0a0050485050b1031505228001440200c1c1c14010059001e95000070300402c0c69a40b40e40e4210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 865456519 1250 865455269 865455277
    0x1a010b030f0a02040b07030507020901080f0d081504110318010606022a1804060c02070e060906040e060a1e050c0712090302060d020414101b1e0302010b1f0f05 70
    0x600c0150f00700300c0040d094010201800e1050310a95650340c2e130b80c225004100100324182c00002441d040030089003a0031500280a140f21801c41c100f201c11551040c0104c12131074141d10110760001d061540c41e0388407845410081d131007a0112410b170704030b0180680c4c045080750b949001c0c98000d80d000390716420f542c40c180290042107203020305e40441080c204d4004a006101038001d41c0110760000360070311040081502648506100510050000d01d00d8100c04a10050001d09468000c07600000407950546454000841b81500c1004481c0342e4204102c0503002446080300c02e16000401e00341c1441d080a01e40206401010701c034420340d08040b4a0f482c1c03006041c2016600c0b00500c4801d039400001a190040600a000e165882c0184c450b8a007100c0000c0038003071420200d03c41c010150780d240d05a500324400d6090016482c07141d880c40099450541c400c0d03882a0f50341807005511441d1601099815008588040c2080d02d035011803481161610349a403000702d0b00075001c00c80c40d00c024902284604050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 865457769 1250 865456519 865456531
    0x10603053303030708040b0a110114062106161214070f050c06010f180915050a091709031c140a030b041a040b0d11060a0e0316031a010b030f 62
    0x10744d103800031a40d80c1842c640d2041e4401442800080340404035a50880b4021101d9005c1500a0004c7c00c0c91003101c0014000040065106030f0401c0c0c03c4810b4060440221600082c000c42160f070941043c100203000301048540c408000703440c400440c0080a014000d0040030320348112002d0f10307515aa80c041d1000c001d80000750b400c0207001d100300ca544a10421101d4024165031103050001800d010746030340042c1d0040420042c0c581019852000a20140e050360401c178401c0c0300003c0d894807000390003070140250078405440c03102c14170812200600d0f02402005203010403021103c04d100e51801600030107040c2d80454001c03440b800d034080b04040201c401000d160750949000101da20316000014201e032a81300d05041012400d001e60a078500b414821300c40c4401d8219803603442000d05170b6502442101c40601a4010680443c403c00000e000300d04441d08078100900f60b0302d588840042280300c0c04061320003601c004044070f1400400082e48001d1038142c40e900e100707070b51640c1e4600200350701c40f810182c50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 865459019 1250 865457769 865457773
    0x13020906220305061806060114190509030106090513032d02150c13050f04090803040503030426040e04110a080c040609060807150c06060905010603053303 68
    0x3603a0005580140304541203152141070140e800d40c10103920b800c0000703091614007003110b41d07522240b0f1800900c1035401a02480e050480100c0380985103181c0c00741e200f03844400c0585540070068560444054802501c0c185c0080203681d540f00c05210a07074105480d1050480201610722022921400340c0940726403076800100c012001080300904200220311040d00181c01c01e94210a01c0411499203135003162040711010308000640d510102c04d100244226441501204e80051880d1140d400854a06070030482542d140c0ca040e0402d01d80fa58401c5508564012030b0781c010441040c0c1e08800b107000407034099001070615007088240c4580d10701c00740c410780c2c01b120f1a0b00c002e0400e50742c4460803806416160043c0c01210200c0703041c40140c0755039401907250303203041c0300702440010000100c1c0f208951103862405004200a1000e8031120304241c030141079542449008101c1d16466000075040305c8080e034082105680d001e00c00303a0800c9203150b8041f040c480e40515900c840100b00b04001b64401c009003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 865460269 1250 865459019 865459027
    0x4020108310605150406081e0c0607030509090a02120a09020301020714100c0e060f13210314073c0c140603011d070c020301152313020906 61
    0x944420645698801254916111002c2049410134100b200300c4001d01583c050040c942040034403503d038050403800c294548450b2032441e42024080015466a2030044e0070a540c0324001d003001000c6d5482075901c14010064031021400232101482280d481c0c284004210204d41c88103441d80c0050300c0489410f80c0e0644d028007114000c0b44d03a4018150040303010070000c040c10014280d0800030703031b0300780c100c0c4d08240f040d000509902516140101d038600b200780203203660348117070310180307000c1400a0f50040c80052580e4100d0039480681c0700300403070b103131800b80e20398001d140e4807807400031140d1080701e400403d0b9440d0f550000418002c084e40701e110703401600c1d004c0d25400000340304280712691400c030103603048803142200f002a4a070755114022254000c1e07075203519541c101945407490b1100c039070030005802c540c480010451481030480c5000c240e0f000f80244010203044c51984d8003c1e00c18001c5120468100391898940710440c8070780c4d851300401915843c1240d200c4072056000b5004200280c3d00850100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 865461519 1250 865460269 865460341
    0x21915140109110a12022a0303011a07030f0e03030f0c0601170f0312040227060f010e0f060702043c02040509150d06020307200604020108 61
    0x30040c44814080c0c00610100d561500d0010320076200c4038600461866000c00030b89004e154000c2c10008040fa80780000340c1c1d51201c0f41d101e00101c4078107864580c07185c8890078940c102548080025030481c1c40c102b02c465550001d6100d50380252107418002004a082e1641442e00a4050081c07a082c00c0001000d603401d084c8640c01c0c0e0902580441404005500200010300800801c41089103000843c0c0c0f0040c400c0c24401d070300c2a81d803485800f130f28148188000c0001000c554928508010b06da49080021030003c0b443d401c400701d004025680203124000d00180d2441c154403811200f441088000c0c03035082d50360030440074048190701070070701a604951200642041005046c041000c0d40c54007100d0303c0307001d11258107164900316584e07440e00c3c503e50040004025954911044641004014a210f11718040510028400740c04120780103102c503001108002800d41c01c0307148200e0b0b00101850702d203001201e0340c200f0394a60768201d40003804503401c45c020802100c02641108900b040d407c22042c6420303901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 865462769 1250 865461519 865461521
    0x1e0804031101063309030b09010b0d1103060f0412050d06080102040e011802031b0f09101e0504030b07030209060c0109060b2707050a0e150309120a021915 68
    0x941101300e20ba4945095540e01c110854001c00c01d28258015000004540706401841c2182911002d800b01060b20042410407100b94400d1000c6d140041400c0745c81011450603060b00710704455035074130a00400d40018030600d04240f10768401d6512444005c600b0312410740a485642110420340315103584c0300c4004c900e6003024801031028003001c40414065602d0492581204000c1d0700082c20750a00601c01d0000c088003545541d6510500c610ba22603c0ba440900516028040d50090b02d03440302e84aa142d18456801c42ca800c466800030180b10209200c82110541701c40c80b0300d210003440003991070005a1810300c03c0d80900207824008018602d043d841d442030900350380d00344806503505603942440c2949490726408160070440b04611203140065031041000c04200c00a01d070a05001d800503071100524854400030300b80710700c0100b51801140181c51070744410703001102c0c41c100d503218030010f40340e00c0c1005005481240715258018108081c2401b0713840021941c0d80d1003102c8aa9400c01c29000c9a201 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 865464019 1250 865462769 865462781
    0x92a2012030901051807030c140d08130f1d060d03180e090c0a08060402090a061806092a050a050d0509010c02010b010905030304060315051815011e0804031101 70
    0x581c800410581080890450406000c0c1741d0811141c1c0200b01c208000385a00b29071600f280d04031034102560a0024003c1070160401400003005220006a5009a40006c150150555040c0b40360842544d444a0b80c05a501206c00301c0b06101c094401e0000c0d503503203000194a0042442890001041c058220600064402c1504980e010040a80401c504102e040090414400040720013150580c50806c21984801c0060006400780880c08001034800d65203802001c02800101581030340403180d501b02c0e4000b04003a00034415000e04195140f60441040744130003224811034000f15080c58068001695203901409006090050501103170308409014403074107200b80807040021402d4070540c0ea000342120310190003103052040c115014007080c1c4000058500f034540c0c6040014070244400780e0001406001c7d400325520000103400c0171580202d00c0e0703c1c1400f80c00321200c0a0b541c0b519000043d5021020700b03010341c00341c2041104047c12584a001c400b900a03000e41010389902c41031031002c03420741e50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 865465269 1250 865464019 865464031
    0xd181b0303020d08010308071b1a07050615030705012703030c050607090e071407050706020705090f0601020309060d0f0c090807060905060901141201092a201203 71
    0x4510a800c10900d501800400c41a00081c540311009604559031443c190181d400003505120301d2140c11303d108032594501c20041c00c001e860030414141c40c240b49500c1940140c3c0100c600d40503001c00b0840514130340d03452580c0840000d000e42940d5052000442d01c20558440c0782002035680b58803548130181424810001d1806640c0b0030150304c096060240c68100007516800c10000d04c0d12081007103224141c07d42ea0000c000e0700d80751251341d204040009150040c038501800341d004480d4002100d540014403070085170425100300c4030b960f850a43c501403500c0c0c1210398a015802c104044000c0c0e2070701c80010515900702c9030000440265a091410031603014041040101c1c842c2c2c1c40038031070132108021820081090f071030480c00d45401c0401103081070280710314a6042c0450081d940ca91080207509031403403121840032803459503943c1c4501038041d2101104c24040c10103281714844440c0410300000817440042c0c0c881c1191b1400500c001c200d80703030740d10816000350302490303524907c6209481c0007940624 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 865466519 1250 865465269 865465313
    0xf191206090b070c020a05040b0d1709040e030a1202090a0b120703180c030b04060e060f071403061810050301020406030510140d03030911060d021201080607050d18 72
    0x90300c40e1402c400702c0c20025040c04144880d802101c0b005035681982e40d82035a105480220b00100c0031000b08400c4884010000c3c200900501051120307e00c9101600600308125402e03c04011400c50181c0c50b40700e40380010000801d015488100200550001c0613180000352451014603a14440603600e90071428040fa42c045a21051002386a0316016143c2d4564881e1a40080e60301d40781d8030034107240780340c0c440100400d00b0140060305001c201d901030041071011500741c0b140b925090702110010342d801c0b2440c0000c550ba155172344005c0702850307054030310891021309105483c0b501c12085c0607081800920804d502d282008001c1102d0b00c01f03002400080441da01c011074142486900788203100d00c190000a0142050001c242c020380d00c40d00d40c200825050704001030341416900b131810900104078090f03500100c0011340342c0c940030020780c010480f000b000c45c1c017510541d0704d5070129038644800381c8039400020820312800190450030f6100070b41c0815131000740d88103c5241e6550001010104010750200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 865467625 1106 865466519 865466531
    0x306140904021503041202070e011a09040b1201061a071a070c0501090b090f01052a040305060f180c0d03030e010b0a0f06021b0f191206 60
    0x743c90b1071039a20ba41c0d140c103081100c040744007105060010f10412500060665207000c0d894141c4200c20302c4124020f124209404a035004190071035030007a0f649020008907500d05105038400004d510000c22854904180c0034182800304400c42d81140c000c000c4200014005140701115001c41500003241d0b031101c1c0000c85041242d000010b20303135842c02010009120201408521035405682202d50440c240c00409007070b100c041e1441000001c10a002d480f01840c081400d40e4000b40341c0304107600349940e17511252718050b0151030849540240030305000f280b40b21419829082c2150030700422a0ba021040440c443d0003002d1005401c1541e14103280941c15005e420111184000030042c002c181c2d191034040001c21114421b140261184a40b40064010380910300302ca02d2200500010090381502c0910424050101011107101d80008021031612107230301da030148281c040c000c0041c203 = true := by decide +kernel

theorem cover : BRFrame.Cov 865287769 865467625 := by
  have h0 := BRFrame.cov_init 865287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 865287769 ≤ n) (h2 : n < 865467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
