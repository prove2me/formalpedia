-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0868
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:17:48.689291+00:00
-- url     : https://prove2.me/submissions/58f4b35d-7359-421f-a15c-0dade655f6f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 155935251 ≤ n < 156115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 155936501 1250 155935251 155935253
    0xd0312020c0721050a0602090d02190617060d1707080d0f0c080f04030302030916030f030e0306070c03030c1106070207090e1f02090402040302060f0a090b030c0d0b01030f1401051c 79
    0x905c5038402c1c0001390206800080c981d040e071301d40b0501d007a40c0c29406084c0b1090402d5407519180d00310046d00844001420000300c1c010b907580000c6c03140b07000f900000c1516003400070740c0d940d01c1260200d103507868050070401d00c2600c0103d04658003410088000c54004a5103800041260341140c82c0c8030955400c6c014048180700202110030000c0d54000e070300d4200143e403600d03004110b07482c00b0b056002800510551090200401c8076844040ca80e0728401d896080710070441200b096125a030480701c550000e6003018210011030b100e60040c80c4c1504071390410003444075170310f0902c40c103015044400b0000341c0e03c81c850801224106e80305100301511810041c1041d400341000100d00084840001c9407030300c1d000b080da00a41d5440764111801181c1c02030050b0340c2ca00b064a02100b243e04402c81e01408980700203400104403081008032403003141d07070b01d0720740d450184602001c100401d4034104050416580e02c0e28510f6070000e038811080c1c0c60290b201c4101c4551300d007030704200744980494283e00518175160300d050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 155937751 1250 155936501 155936503
    0x60315070c020a1a030610020c04020403050a0b151008070e09010e070212030105030a02010c0501060509011806050d02060304062a050418020a140a03090807080703021b010203090d0312020c072105 86
    0x1030340014084600b0800c2d1070340c10f47d00704d14200d4900a00f681c0039100040000c20081e0004841d03000c0d42c0b0617505040595580400940f6590b44c0c01481a004100110b496a1051083d0004d0740c1c010864100001202072943c046070281009030850084220032105000c00717141c040201034504400007492524640c10b0102003600c40c007100c000241803020040d0710308200102034120310040d10000d0325a01084d030b03643e4812100308040c01d1210070460302c2d2580210303e5007000f00421031a690080d209500d1510760395a90002000118900d03c17200c030680d403540f84106000f04c007490074403041e541e400d6102c1c0e00300100311b80107401001020903858410410030701800e401542024000880762005501d84241c14404d901410071050002c20b81e0301d00151340c504000040008d07164442c003a038201d800700c0400b50f004484007a0501c3c0d0300c3d03001da03206028802c85450040d10800d950340c480e29140301d0111031714580005a81050b15241641d400140050000225108000350600c0d02d010450080210b41e448007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 155939001 1250 155937751 155937757
    0x30302220f17010f020d05010f0602150106050702040207050708010b030c0307120303110c0d050d05070503070c14070503060a050106030b0105070b0f0c0418060302010207050a0e060405060315070c020a1a 89
    0x1010081c40c540941194030303429488615500748428055503031b0f000000905006240034060201c1e1002001d5000c903c0c1031001521200040b914440e080541e401c1c403038140c495400c240360403039200e80c003008010300182d0f051100c1401010f08000125600208204041c1001e2a81078214025440120100102078070a08000d035a150142800109144142c038114800c0c03041c1035a100341071282c00380e150318095020000b800f201185410030000b0741ca9500041302c0c64401070300c0e1440098582c1346014080707a109900f05080505c10f0b803c48400b5030b90303a800321b41420000c9558800071940c400042282940601400948080910704a8680070300d5540395451644060080003c8007850390003e070702d02c60104101c40107045220500600800701c160700d80d000d0300d42c60104a0041c0500440001c13182088100310301070314413250b10080556903ca05000040070014036080d4107200d07042c80c1e502c1c1d0002c0f80f030102d030081c0c0985d601c0e50407450f070a0052204007001d543c40710041422007200400190054001e07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 155940251 1250 155939001 155939009
    0x30e040506012c0406270b01110d11070f08031602012001050405010b030610061b0c08030406110c01050d0b030717150a0e061b0408010603030302220f 66
    0x6681d403200d0004030b07010b000d4010105032121a1500a00d41d54441004001d8000421101808819240d034441c000c10245a0b4076450401e03041d1600a29080107500000003851041c9450b4036403031441403489241840c100704003000300b5110342c8003000345403003401003802401c40400421940303860201c03941d80d00e10914200d621800c0818400608580c450382c0514490700b44550b20b0307000c000c40342511030b00910007070b20101c50075171071314070420003c3c2800318021340706003030000100f04000d2502c02c0070381c0c00303d24529500d00c080c0e1a0325500720000390307682846009846408025a1074508000b00a403c0040a4040c614a64002c0b82000e005a034048101c4034040040c2001190700c070400c0011900d844a1600120074002c0c2ea04007425800c0c00000301114542001d905100c080d40720034040000b10ba686610b07020710360304414001200c420030620000070f10040e2050046ca800d56a02c41c0034211400c44d0030880009030001000c042425011020030607103003103403100c1d6500514100f2584286500c500c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 155941501 1250 155940251 155940259
    0x1202152d090d0201051c09210206100b07030509040221010614070215090d0b090d1103032701020a08060103062322091103120a32070302070504050112030e 68
    0x80e034078910907811495005c281c1413034102445081240c0c130b031a004502300041111103000881d150001d00904c0022120300440030b00d00c09415050078050600002e1b0700500f0190f0600500300500c000d1911a031004205070051840c8140450507a90300100c1c0c0c909042c0d20010410070010304243c4075500c45822203220700d40c112410005611a02c841003458050090700c586e002280140200c14881c0030b02013548112a000195605004080b40076200030702c502e0110074040d0320a10000d6004002454450080070b00d210010105a80c081c0350682682d11420500000624860900003107582500a0300083d2690a03698204010f2200506407203000c10040315100381c030305a40c03d49035041c0404c0c034020b88008070401800f650031030342410304034541c111070128024480c10040000001000c401d540745040721f941ca0302451044408020358000b006501200c03103040a00c1d500000650980042c400d45100350043c200441c54101008215001644400c2e005929410703003100083d8050020014032200315 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 155942751 1250 155941501 155941507
    0x151801060f021606030b1c060608010b01030e0307060504030215011203030b06030112060c0302130306090209011a04030b060118080c090934030b040c1404060f1202152d090d020105 79
    0x46c0024600f20480d020340f41c02011004981400c0c80000c0d045803017038a189a00901c0301500040c0118204d0700d2007540101c00e0f070001d02842001800640216810500074412104ca103010088058071103e42030380808400150320316240b00301034040c001c4018804003100c8441c219032401c003030b000403582c00306402404a5590414050100d0081d4140e5600741c0017154890150354881c5000070041158050a0303104906040001859030003030f0070a0700030805509842800c0902e180e0320b031003201e08087c02050500984164410f003012098600c07100401c1c07403000414013440c07200306001904201600d0300e0929000a0030700c00c035000e43e00740e0804030f520304000c0008001071642d41d00507642480c0d030002401052000140700c140034907130030800261980700100340d0501840c0c5e000c01c0110b408522501c10359070b000720310420400c02105a02d110f0580054237458940c85010300c9604a03500c0000c1c50350300070f8800013030703051060080084103160100a003603a924180082c3d0018500c01c480c40030080c1044000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 155944001 1250 155942751 155942771
    0x180601061e12061502010b030c0f1e0d0b070806030a030f050a0507050f21031e0c0903011d1e0304050f0d120309021e01090608151801060f02160603 65
    0x561481c0081102ca00d800c012903900c82144a040b00412500080158204080070540d0300c0c0100395540c1d1054020085a05240c01c8002e014040e04400e5400e512419510174070341c2c0c10780b0b44404035440c1d0ba20501c40c1c03045518103480f02801e88000508400e00035400045000c00194010342180d228409a0034002c0e2038810781101204c00d48030300c0d0030060142c0102030318011040c0001940105928012a40490080a41c50140c0180c0402c0712884000c001e850f0008019242d042c0d809600203c05000c03141ca0015880c1c0401e095070140c000311180500c2c10840310440c04010f001d0003c5040d0741804400340716080000c140c0d60380c01540a114400d2a101c1c054880660f40c00130441c01481d804100005151500740010f002002e007184140d000d40303003034000b903950107060300c41c4080520301c143c40d190340c1507007070081c200d62a05c4000c011003000015110b00c85165039900c2c041000e407442c02940c80b40c941d81418001050103840001c590150341c000b114030402c000e00b01003400242e424518002580c0041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 155945251 1250 155944001 155944007
    0xf07030609120509010e0913140615031b010516140606010e011722050a050708100b03060403030b0a0b0705031e0c0a11010201110a020f070b040612020d060b03010b03180601061e 78
    0x203e01c00041003000300340b800c0d0b20b03601c0000c0ac24910458410110343c091205c994240754590141034011f00900810f840020842c3d80240044c040004040000e00e85d24082666001c482d03134001104a0780aa001c0010040d140d03900c4150084091000e190840c8207514090249145000260042040900c8036980c00c984600c07210703000111a4024007266030325912814400e480328128095041c071070040660000c8590758134000c410100340041c008100c15503803914120014a29600740543c0076980c900c0006c1e9071000d45001d860450701440c0555030702c03040e5032160050300041921010b0801e0081c0484a07d1800c045200c0030202e401500420441ca407000040b0300412140c01900641c49020400141e411381c00070b480180905100101c0e4085501c3c1c400c034041a01980c454440000d11494a003940742220760041e094415030604080340303864071040309200c15042600b200750303000310100401074005045843d01c0700f06502000070702255410140001c00b04100090300d07608004d009041c2c8909030348 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 155946501 1250 155945251 155945281
    0xb03061b040e0421120507051309051803040f0608010e0405070312050d2a090e060f010c080712120203100e040201020c0d0506061305190b030f07030609120509010e09 73
    0x2c0004c000304404010301c80c041d005c1941560502c612078500307170000d2050790042c1d0480d00d40503030201c91000350074039100810340540700040c16540610000c40c52803040c01c10404c050400340105e05038840415060481c02451900164003159842ca00c01d010301000c50340100d04031061f02c1e000400d03461190310703c50f001e68991080c0000000340d0f0780b0304000c0030f1258240e000d806000c403044c40c0c14007540c800c6201044031445814000c01140b94040c80104800703150000e0203000c403044c1030400005103800f58481e00c03e6a040402c09442c0307202140e40d008010760b0f0200f180010130765180c00840c110b0030718158205038240d0b14001d1180c07004042002c02c096a0080201c00342d410300003040030010700c030030340303400364445400f130300c205028240c00004607000b68428000e071407003281201d00c2454420018100701014204c20104950540101c07a24100040c0050080b44090f5000d41c001041c629000d180107580c0d484490450001c006090003d10942e0780c0c00000d41142c102d0032a141c51498507030036454203000b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 155947751 1250 155946501 155946533
    0x6020f040e101a070c0e13022101061a0f03040c0b0c0c010e0307031707020103060f080a15090b0f270a1b0b0319060b0c010b03061b040e04 61
    0x3481d1207003080144030070602003205459849844081042051441d0a020b0113002e100030054042904140300142e80200c4059104454004040d80c0c140140c01040030006120320021806400400b50131b4200c1c400d00508000b048a00040606001d68134030a0200d40112602e050710a04000041001d01a10145243c040c01d0030121590344d0b1489031160f150b5807504011324902064a492a4141503e004902c2d81c1c2141d03081010810b04640c2052000c4895001130030480c14503980e0880864490300581100c000b506064006110b115503900781501d00d44400c1091103255420007254000080006d00e10304d82101c02e02c1c42d0408582c03034441c011845050421030f28005c0c0c2d400108003064821000a08200c142d00490308460b0150b40b2010312840f484c0c0d1401517503c002d4042002c00d01e00d1001c131414108092014000007181c64444821071000c0d4001c0150380c9843e911049106071a01d000c0c4040350704041e1040041c6d00d413108800c54076005018520a68112200403030000703052088200144500c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 155949001 1250 155947751 155947769
    0x1602040c0206150a1406090310021303260406030c03060305030c1609090203120c011503080c15010e060402070c050301061e0e0103080313030c050607080703140c040306020f04 77
    0x302006a00095951104451951428103108000304082c102010004180c0d61081c0c2850b03d200c085c0d500703000c8143e011708085905481030050741880d250891024000d40080c081c01280110701e1801c11694401c00d020715000e91a2110707003c00e541400010480b0112440c500300030500d03aa0100c0182c2c0142100d500181c92800f00103005c0c1c104034400300e1841c1400000e0043c07041100d0300c40045c001240e00c5004020341650201e20034000f5101c4401c080c0c00101c2c0e0031400401c03940040642c8000f4080b00c0d501c00c450384000814228845241070105803868081d001060b00c90791b1510040070011103010304640d000b268005014400e001c4070070400405000064024041ca0b982c1d1450252810840301e940030b4854042100850031002000916048a410a446500b1a1144034000c0d41000b8511011401c2c40310a18590740000c505024062203034000b0344940c403051074503440c040c060701c061800072846034505030100a803040c078220607281130381e800020042c0ca5a8813104001910f00c0740d07400039448 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 155950251 1250 155949001 155949011
    0x5011a0f1e0c06150102070b19270608070e040504050a15020d02040b03090c0907050a12020c01050f0a0510030f0b0c0906031303030f06030206092202070804080c010804050a030302160204 82
    0x4c1d8003071003010b9140c039103030070b130b0854410503907604c1c0c050f401e40101000c10310500f00319840920020712a4622034082c07410544650b501c1c070108480480f54407543e50015010a128008001001e9000100000031301004c0e07d041c0401c1c50103981c0c0c592540107440000b844502c00307255590080303140b070f4156201511016021560340b51180309404694000300c403060380c188511380b085402424407500c0b0a01900ca551100c600b84805101c041e070b078107a514101c0020761a828490300140c00307001d0045a01a140203000096282050714003a0305440e8010308182c980140c10104000091030785c0e220314042c5d900301221901544410702c0741100380c030070b2299007603010001109000e540c40d00c141020007040d10036101000318202d022160010340b499440040d520000a00c01e01c161400c1030400f5140030f000c114080c0369a01e1a84401004074ac0181d2801c1c0d4621101103000d00202e03030704000c0c11050010900b4030500354901030380d034113a40d900b60b017030014109a0040745407a01c92258407550b0a02d154024003c0c44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 155951501 1250 155950251 155950261
    0x30a030201200a08010e0a09020607111201020901020c091005210d08071407050c03030409091716200303040605120a09050d110307060203040605011a0f1e0c06 70
    0x40a40b080d41030b01c40e41c0d02c28000ea6960010100b030202e5515075050788a681490f860304180000100c001400071070056180d400c02c1c40113a4400004100940c0300c0c0c0301d414081132a403424480c1060071403034000c001341c0c810011201c00d60f0700017801c0e662070340d8101d805008603a0f8400d04e01c010441503600c100d42201d400200400543d1900240040c03014150048500c0170440301ca0841e80480d050301c402d808a400c3d41000c090b130300c14000040400c28092011a860062941c010034690703072103640038440003561078003108200145100c12403100c80c5240040c504220350040f8010b004412031500605440c0c28203160303d02c3c260b03250703000307003540c94014143c90700c5698130034014110740c1c1320f00c0070440800c042c000007501030745e41071003042c01a5400100800c44455051001c0e64400b81c40403407020548030501c81c200009400b400110b200b0340c0308100101340c03949000d41580e030200c0981e10800346440c00f4440c00700864545001e55005c2c9035100c0c1100b01c0c6030714001e40e580f400c3c890006540c00e01c0c0552803c0003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 155952751 1250 155951501 155951503
    0x5030109050120071208061207171b06030c090a0906030b16020a030e06030916090c180605030c07020f0d050a0b16021213052e030e0303070f030b030a0302 68
    0xf058244000d40b00a07061604018004014440c6100040c6080300d5103105000f858400c054041d4007841c06015a0841c0400111a030f19000e032591104101461700348040c0012078080c0565041210414000a8040b404030005515404001c1c0b0b22400785401003007001e0103640e02c0c1c1d40320740100fa00a60030441c0036100e0a003617002100c11107548448085106401e11881d10026554207659056a51b8034210f40402d4100002503201411500703007403054032030b042080b80309502d14600030170009038002125100a80003500f80c502d040a1885c860000c0d0b4406c0000c180c004045952107954001344541d215030710710004800c4103071488881d03006584074100d01c0820070000317072269800d4094042d00c0c0465503140039050030004c0000c0d010340140c0103048041c1c0e0720f145c5880501154804000c100c010140c655020a113030710a1040c06805900366500310500b59000d0011854a9640e90700c0e0510000c4a40c00d046a92840041d203848100f21800c600c040181b44240c1c0300c03800c4004018181c60312071410741002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 155954001 1250 155952751 155952761
    0xc03140601061d0915010302130b04050306070203030c0304120c0b070c1a0702100b0a05030a030c060b01050307090302060a02070e0a06030605011d0609070c06090b07030e01060f140109050301090501 87
    0x2c5010030100c4040c0c0205118503540d440c06040014020702c0030f543c3e0310800101e403402484610f030505070203124440341c5c0890f500800d0060010160007548451600c0f04040c5803981c0900b1940554008109200c0e09607021011680e006800100010720721442010488000f1001c0070050254403058042c40705640d0f203c0e5800c0b0540b40a0650b103403c032440c006415417000f00613110000542c0c080d01d141e501c0012241c10000700404001c3c40b00030600c1c0d444001c01c1c2070442c3c2c0701040700021003000203c07080020751721610714851801c0ca0503900f5490300d840007034281c070200d01000c1e02c540c40101e0103c0d002e900c00c01411000c1c04100380312400600301a81050054242070104640090801b000482c030200c204a4084149645500a800c0c41c2c030343e00240300f042e0b48058811006c0290184401000c40d40e10700540045610a640c50f100e80d14003003000804913445481c0350a06a41040c03010010301d503003041c030202541e492080342c0200e1103280005035061416940030030340650070003080d041480717419800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 155955251 1250 155954001 155954009
    0x20f030108010f14011205010615110610050901050607060f0606020c15180d05101e0b0603040b04170903010e03090108070507170714160311012a0c03140601 69
    0xb4460203d0907034041041c2d800c250b410500c0e0b0303003092004000028040b030b0542001c0740036000000d0017686689002e41006c80204420010800c00c8294441900301007040660017030f0952240c20b4803d0a1000141980506210309445600c001c0751140920050742d10840381c852500342c0400100d85d13071300e8005e51034000c1c40d1010b52049000c03200c1010b24503481401c545181582e1030b00c0c800100034074010400c3e51440c0900a90345030cc10003041841140d00d40c81071745a0a0b40805548541d0211750341c941c000c0e1103908400c14080c03182401488009001d46005d07541240c0c2c4003001d6a510010340c2020042801822140f40d8903609113036014030065004001000b402c00c0031b0344c60b0b07040d51761012803e58082c410305a004018400d49420710550314100801303400303244d2042c403e031504004211041840c050380b051104c0e10500c0d400d60100100305000e108080c2c0c410003030a1a00580f070b5410741400c1030743c88d548030000b10341d05020f09503000c000d5000c00d4600030356480044e9503041f551300c021290380c500090003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 155956501 1250 155955251 155955253
    0x20c06071106090304121b0b0d020c01050a020408060403030b01111905010b030a020d0308060d080309030306010801081605040b0303160b10080a0803040f030e03070603021e090f0121020f030108 85
    0x1020a04440d404405c80e425502c0c0300040c54900f9072295190100b040414100010038500c0080200e00b03441c500c001004541c4404201613212640030f042c440c21a0f80c0644146201c510401040040c0e203404108154001d400d802c0000354000541c0040e900c2c800f841101284900618100d90403a1090301103c0a11138002e900800c1412104418160340f003030b2251029500071102100ba0001910881c54a9400310018000e01001580d030755600d00b040c0c10a450002468002004015881d42d03c065001d005103961300090078002e0b1000d0380c40c500c9207414010f03a0701840c1c442401d042c15407010000c0b26242c030b0751110040c5a8601600f402c550000c0d00b601c1d02d43c0c11564051000074103582c001900d140c07041d04800043e2440c2c540741d541c9170100280002c01c905101d12030741c6040c229502404031b90020041601c01690315003440510002c1712500c2d0900d030614401c140b105920503102d40c16100e004c11400c1c00c0c81001030b0201c0309201303804c2c0c46844103000504d0000640a50214800b0701540c1219101c034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 155957751 1250 155956501 155956513
    0x11202222306090405070e07020705060f0403020f010305040c170f031306082818150c090b0f04050409051002070c14041a010305060a080312040b06100210090204020c060711 76
    0x203010000f9818003a207014100350f01c204000c2c00400c142d040d04640041032801150700c9107541c3c8001c52403542200301a00d0401c2e101190030002d5041043c0742e650210000d01e002c1042c0d1170241c0e07410f8032020041c040e409003803400d54014801e0140c20050300f04410107189c1201c0e207a0850070849240918a80903407000030f40b010b070220b411519040302c1d03014500c10811000c8003411003c1c2c2d0450003000c003400154028003090784408041007120b001c0300460814002c0103d084080d558000d4541c2900342d01c00b44001004014241610305802c042e00e06030703071382150007180121042c10030354034011703180b500b41045901c0094a0340030000204a42d008440fa1504181d402c044614100012601f400d290351700b40c84a2180c11450961080c0d100d150b00c200000c065500c0c46844508840c40c3d5003041042a0300080100140014007009040c420b600900c00c03120140e003680e02c005c2c001d40b201200e1681041640d2100b40e036404554031034054401002600045856030719100d00000c211692a08500000380030314 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 155959001 1250 155957751 155957761
    0x308030406110703050304152a0f050403020105090d0f02090109092001020a0b0402060f0a030506130c02030d2007030c02040c02030c0a0f0503040b0c03031801050112022223 76
    0x1120540d02a240c058175075500310390b200d4030fa03282001c4e4030840413035141d41d5840e03100b082d10460400004100340101a0345821240c899409001d01900503902c50500109010400060382d00600310f560245043d520321100002a1074078000c00780603001e009500428070000440c0e80d40c0309910601405014000328000c06544d80d80b0b05102012040a02e401030300851b480101085015906a81103480900268174104184c510040079800400f20b400000340ca9030140806890454004180002c03180420041c9012024019640b40300d00c940c80d0340001e41720092801c0800c0c412241041401881c00301c00d6a80c40d00f0f1800404903001454224840d61802c1d842219644c4008240c0302c103846094010100c0400c69156001440e08407041189d26102c00c12003c280d20743d03c14040e0202c407440300004d5480b400c003503031400c00c0c12940c00c2d10131000d68540801046480400c0c00c0d41c2040540583e80601458a00c1e003900681204e81403548004a08001180b0700b03142144100128000200c1c2c401d200544030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 155960251 1250 155959001 155959031
    0xd020c120a0f05070c0302100c02060a03060501021506011e0203070804030b09061f090b061b01051b25080d0510050112110403141501080303010f080c0a1a070506010308030406 77
    0x104e00d0003038002d680f0810140018107140d8000c07a86240c0c2da0a000d40312540c240d000400d2a07100401940000391580700820107941c04000d20000120849040686460024002042444041c807500102c3c00b845052624203402401203852007500680d10941c3c070354490414151100c000d84041070320f031040e11300003508040d0086918594118040356002c02c42d113030455070b8000d0400d807411240c0c0881c0400058480c2c06502c020310b44030104c800000700d040c0c0741c910101e0b48004000418598400c8003040394400b070140c0c1450150301da9402c01c040d12400c007c141458240340c05142060aa90751619045c00b070340c581600681c0341101e00998824108103401003416050b541550310801200d042403000740002090082102007407044002100c102d000a01d50b040c203051001e0f071014001d82c00c000018024816050409806005a44000e00703640101c5000325081d80401d01c80c841c20720b40c4407079110b054030080070300f00c415168004c01120403950312403c15409070380c0161011224189494121074007200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 155961501 1250 155960251 155960257
    0xb011403010905071701060b0c0706020c010c0c06180302040f061a070b0a02072406031208010806070f0917010b13050907030303050916031101120515060d020c120a0f05 74
    0x20b4001d000d880128589482c1701c10a0840f41300b0003656540f503020104031100200007034104100c1d054018403040c0d1034034134061305000b8801d00050400905010f010040740c50404e180e022038030135240076000c0e2038414040b0300c0c0c21038031038000030344c0b240c1024440022408107800200640d4440c9400b504440708101d118441c6206500e0010801010403000031300010440d030281070007a010351200b03454042513040720301d0070002032010013a030140e46007801d106000c110f040030100082641050350345075041002482da60800140060100901100041d001d43c3c49046408001c041c040c1246c41e03180c40c1c0e004080d0281c0110104d643c0581135840016180040d0b6010715070003104503101400c421811600c040307025003401858640c4030f224120305807400c10044071503940218003070000038040c03001d002c0c001829660340008555200e070030041440032200c2c50f060b0716202c0d2902240d40d2070b525184040e100010707020b810081d142e0360045040e036610451041d4010701c1407980d1030b551491545012481512940 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 155962751 1250 155961501 155961503
    0x24060120120c010e0f030403050115030812152710060813030903050d0e010818060105130603020901061e080106050910030b04150510020708060f07090b04030b0114030109 75
    0x60700901a48489401e0003008000809021002090351805513154a251420507802ca10320ba900000302002800300070710035103540034241242c1e0360f19645943c031041150f00a40340e0307141c1e4881502001c00c19042481040f1150305202030318131b070fa052000302a102c024480483e1100c011291fa540040c0ca00e5044190074000d6600b507484605454490416403001811004c1d0220240111960003002113002005030b26801252991a4041119035000040c100e5201a202403030f0891082c0645148080c0402d0341e03415a00280c03a41e503220340203140440c000e00f0090340082d4106411030004680154842c0c00c0107449501134951b41d0040c414450126900d0000f40300300c00000307009009440043c580050061200001850301060300030103400014211443d5035004440e684d0310303503030030062810150ba101d8858100b0b40050803400745030000042d12500e008044d0b0440010143c0010441409581caa07405081603e071465261503c07490203950600c0300b03000e45103045190300800c00c100d140c14025075040c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 155964001 1250 155962751 155962753
    0x3080406030b010206090a0308180a060b1e01020d030b042307030b181302120d1206061809050c041206020c0c0d02061c0f090501090c0501020304030b0408030924060120 74
    0x404181c60480c0c924101030607072031440f49800b006d190b012b1000c109461169014003000501e4484d4042086510703004d10301c209400302921a01541641c0e004600042515420f08000c01e034000c1340c40000f00144440440344c680d0381d03490700c90980491080c104852007094241c030200b000802000c100440340c6406024081e0f174a01a90009442c20700000c03840080520241003d0000c00c03c0c1d0042c1824002059800c4c800510941d4841072185501d0283c4801000035052181a1442440e13a008001072075008113285991180040341c0c1001500702141d004183c180c1003042c214a0303926046019500400300303100d0340c0c0315040c13401031036151a83d03044080c0c547c024012071400301201200c10148141d00c1c0d02c6d1440c1d0b55200c9001c402c45643c4d0040c0f03c0c0c020310440000036521068039100b41010140e400c014111360090009000140200720256041a08080400e480c2d9540c0c0b144140381400951003406880b14111501c0d0070503c0b10b035411307801580700b62034441041d0005040014a030740c00700105140f03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 155965251 1250 155964001 155964013
    0x5210405060d020f07080c2b053016030b0a050a090c021c0507020414060901120807080a1205090d1b1b08070f061b0308060d0c03080406030b01020609 66
    0x41040e241e4018814840440134035800c000032034858040070b4000e8000c0315040c1c0c0000d40b0b01c54420090705444481d0b50722004443c940d0f00c0311101c0042044c0201104060919140f0840e40e26500c00c8010300001ea044a010549062034219409114800b0045507880400d0030011010340078a031401d0404182d48001d02182c0615142102540141c40d91511500550041d04801080007200201005031a5025154180c1d6240d030303441800100c403100000c05201d030004000340170745030307032849540c6d411981040203606a903c01414024020720482000600c10301c0c0c001550700080c1d80000355980e00d604404001c200c0781d614022055114500d000f0750b80d001500504140301104402110000a81e00803d6101d02e40c1e80001400345c1000016002280300741c8c072500040000341c0c0e501031220060700d49480c0c0711800051050b80702c018100310700d40040138045c04500059060b12481e008421168000640402403aa6418000000d511030300500b00000d04016111540e5400040c5132070048211a0013820 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 155966501 1250 155965251 155965267
    0xf210908012318060c040512150105010807090819060f09050703290910060f0b2d0d0c030e01090c030213090f0c080c09010302030d1211070521040506 66
    0x1c0d03031034070041c1079241d9500d401c40ba040240f034007040124404c0e01d103201a2030340c0e182000200100b1001c5240c09841c1903100c0c0b8078800d00c1485200c07943c0e044907404e00300f000441e04c41d000c0907100c480198100c80c1c12407141c5c3d8151103500191b60800701103280184401c1210f012003d1810301038480d40310001d465540221010400280740240ba45608042e102d1107602c194100035521800910648030003410754481058040140c035a0b100e042c00400755061032001c4149400c0c1e904109010b80c0b40d03c1146854501003401501500c040c000d1080c4091100845c0e03291800380c0f518001701900d400e1500000d00c0d000c0741c0340821005210340121182c0101c05032001615560030400e041d0400d4041141e00e40d01c0381c4003600056140106c005101d03200d18008440641400c908610380b042d441c41c1c451003001040010030150300d000c42d940901c11070601d01116845200c02c15280a0060f5080304280e12900089403c10301c400410882608480d03000222540f009081e03080c1da160181d4000c855004030304101c2c1c02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 155967751 1250 155966501 155966561
    0x4021c110d030207180603110609150a03021e0304061103190b0f0301021c050c190e1906120612080f13090501090c08060301050405030a0c0f21090801 66
    0x590442c03080c41201c280c41d46070b6441c1400c00102c0c0d84000c444030749600080c030401000c0804848841d00940d04c0343d0401043d400010a4031244c0551654880c1d0001038440c1c4041c0b10346c04030768150510f11403464020030121001e038030543c42240c0c141e4410303250180602d9408620f000f181d0003240b075807490000103900d11403944000c00c00340103840d60100d841030840d0007548080c00a0308184c0d00d0383c1103584c1d40390041c10703840c000c1d110700030566a0380d03003005c00020103c1d602d01d0155212102284c5071a01c2d90082d03a402244005000840c01a407040303403900006810341e409003400f80341110300300d8240003403a62401c6618048815400041c991403080c4907031115520381c4400303480c032890603191388811240c0d40e13000c401c200d82080e00b00d21650b6031070b880b88400e030b150042500c980280094008124515094441d1030301c034040e01100804000103840a0020710042d070484145c0b49410084102e0100030640140d40100c50300505c07034000c1f03200d444001540e81c0c410b00c5118106406800c9902c0c10040c894642 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 155969001 1250 155967751 155967769
    0x705010906050a03090b0c070215030112110d06050c03101e0312050d0c05070317130605070306080f01020903010501061716030912030b0102160b0417121204021c11 72
    0x4c141c0d6402d8460082001d58001c18080d0713540c80d410340d90325081801804903c0c120070003000301030307003040004100f111054000310101a801114182e6002811400030348500121000a040d003400c1c5002d004048503000000c5003d10785003000d16116594030151210550140d4180e05c0c1000d00307245080002c00c50a03e40074034018030f98507101e032514098040f100100c2e402078480600198011501d813040540000200b001001c80304e1400c0c1d070a2810906550b481017810100400e0952102d022502990090304048042c0030458281c8000f10782907440c3d18002c0d04080f42c911710960030000002625400390340000508400c3e0319074100c1558404061001e5451412080802c06648040c000c02040031040c0f51440700391165030104840302c80000091401c1c4003041141031404000f0703400c000c2d00e04010102c030111076507821281c1c54004481081070409416503100a4000000581903c003800100b40c0948154030846030020910300b10740c505000b0700c01302d2400a00b503140c1040300305180e1400303080c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 155970251 1250 155969001 155969017
    0x8040f0618050606030d030e0c010f23030412090b0a030203090a080d140f070507020f030c0405100906140109050f12030c15090c09041b031704030311070501090605 72
    0x1000c1140564004040541d1900840940b140d030400024010f26190a00141043c0c0403d46014480320003218146030716900c50450340c43c1808510f0582c0d00e100f03030107a561b19140c2d0202c0610201c030780e41ba01010141c0c0381d00403201160050103144000b40c0c81c41c0142e003c2c4003518403840c00a1b00780070360203134140c00950000c1e14501141c41603091301800981d002c00208105038007454041134484d00305407424048600a4050044195507204010803198000305691180e90129220300c04070040101203414818000c2c0b105410500b403d041180c6000004000c7c0100c8929200420810f80c0e140c000f4030b0001c49040c5070500107911032104010320f2500c01420100d114000388580500100d5205040ca1640190f1041400e07030400d0181c0032107003161a000e42d501200c0c15001d4150b090150000480905000380010720081503101d080c9a0448001800005150300c010880425008106c40405540041c032080740000c50000400c2c1c00c00c90003159000c1103e5060715503c40c1c00342031071007d4a540e040480 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 155971501 1250 155970251 155970263
    0xb0a050a14130314210d09080d0207080a140702011707120c030f0c090509070311160501090c0b130b0c0a080d0912020604050606040b0d0b070305060111010b0108040f 73
    0x148110b429040b120a0000c500c10340056a40c00a40c502c081c0c01d05415251086400c040c030071543c42000700e402e0403200b035883c5101002030410004d1401c0c6030070b070003580200202d80b0b1021410381d0030005d80350300828032041c0341e444e02c0000300f456009004113442003040c028000707141701804c44025403403c2c0748180c1183c01c43c00d1a10300d482c0148050800c6035541341d800d800181c3c4500702010030700700301d00c0741c549100361030b14200d540d59083c6404200c0c0190701402c020209030750f03002e0400060403803070140c8440b0745658030b052101614600704503001c1c02c82c0030815034100694010024000000e501110803c00e022541903281c2880c01c4031080e09a007280005410074020710b0f9090000580e01c100401d94956071441c001032a21150400c0c7c40200114075100702594040310a10010030070000d060740d441035040380c0209490407001c0101e03403c01600c2c04010018000070f0288040a900341d000284510422390b10b005148409003c00341c00e0b036242180560128030300c4030228010607010031660548a000300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 155972751 1250 155971501 155971507
    0xf05040903140315040b100806280b07060c03020403110d020a091112010b0702030a12020a02040501060815010504060f180e0f090114060a050609041508010609060b0a050a14 76
    0x40468022a80300b1202020080c00320381e801e4065117014410300030407103019280ca45100011880103400c41402510403441080b2000380d0b1300e1003001803000c003015206001c204040c03165641e09142c00c650014201120401e003040008040381d0301c40e20030349080701e4100c45039180c056210028041c10941c02c8030213a8104030712a10101c0d03420007501404000c0c1c1d500c043d070955a651b0641000c4c80c6040180c100404d0350f13108014280144e500060b07c8400c140c1c1040b85072071140040c1302c0980c83d000445078001d400504000c000150a82c000c901503200b451800d08a0805182e4400111136900c1384d03003d84008a410012204e004a00c85c4012012110301c060704401900e40b50300e041040e01c076085a041e08000718240402070910800e010300c0c0e2607405c11004680e01c90404100003440c1c6031450081038040c40011a81c1a0141d403180c10011007641d001310990382d41d40d02c8200140c040c203440e00404110364144000050f1040c02c0c001241e00300600c941c2d40b2070400c8900300c0200e504c1014600c034415004028 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 155974001 1250 155972751 155972777
    0xb070309030905150405010305090a1a09010609050f06010305100b03310f1208040c031e0c0e06030d0903080f0702010903050709020d050c13060503060406081e12040f05040903 77
    0x1040f00000304c032001885036504c0c0c0e803904000500780c0340002d200714802e07089104100c000038000c503554202c21115410f540e0240e40d40204080c010308869100d404e030700382800701340306291002850050040c50207903014841503940c04000c004a40c040e124000300e03201c04000045141c180341e01081c80150001d43c00342001c1454848042d8034040d00700c025038541c0407512000c410000000192803c80d82c4908003080507140507114400c40e04c0c0c4901c8068943c00c1c40c039160000f045500d4042d1803e940e4003800c80195103440c0c2c0312100f801102151000c0c0a0320030502182807584c00303450200c0880b94000900342c42c0c0350300e1b00130341034050f000030f232049051102030031010bc0040d000740070403400f03002e51890058961603200c1e80c2c0000e440e009800440802c1003003001c0c115186800703d245060f1080b609207140c1e00e45485001c10000d21507640508854020714640c4034208042500c00404164201e04984403103642a000b19101d106900c01e102c8524080c00301002242003070340002d1000c5020f4102203444042c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 155975251 1250 155974001 155974009
    0x210212040b04060e0a1d070e0904050a0c09021204020f0303070503030106080f15030a021e0d08040905061f080403050d02030c0a0908010b01050409051b070b0f0901090b070309030905 80
    0x8150030000c0c407140302140a0240c40c2c1e000c1210f02e41000d04a030000d20b840c0c80c181d200b03002e80c403600950721b1500b22820300103007403580901d0255a0032200502100014a0b180c00c00036161a054241104c1190031100009080c42440c003c1c1c0781b10030001d41d0340d05c60540301d036400c020304207a4055205405010500c03440010810501c0030314028185901d0300d851030314102c0301094403407400600c0c507e1448500046c00741242c4000416018441c0d05641d1200c0d0310300c0080841c1c507800c1d41c400c18103074040ca001d81c0c10340c02c10800340301410443d00791000030300c4191982c40c200b040000c0741c80f6408001d086083c02c0c0c1840540300d03009030b40d00107000742480b925202060008070141d03401141c0c04000d450b0006489103245a00c00002001400e5800081140490100c0020114800d922030000c2d065100c8005c1000e4004000304036407103201c204011540c5952a26004844120480381c0c020011426400100308a030180a10310712103600443d005079035a204442903000741920314040d01002206035010a035925 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 155976501 1250 155975251 155975257
    0x106030b130c0506280e04020f1e03061c060902030601030c050f121b010509030f010903090905070c03110c090c03011815060f050c0a1b12210212 64
    0x201004826802480742041c192828055014074028001003202101141788115811000c6203984107038074941c015100f04407610344801411507802480060b07402e1103155010020844a165000304008207a4406c9052545002c21038000d500951440d409003495080c0e14802000c06100b280002002e5075170ba008245080c009070801c440140c4401d6061201c0d1411079041443c40004032040000542c400c00c110382c50301101c180400c10200280d22941490b0300540c180c1d8007200002d4200d076091021074003214080c2c1082041078021880000c404251100c181c000c4034801c050540740c2030080c90380f43c0e90032110460841c600e004207004180c00c501d456903c83c1c0d080d500400394100b189480394100564200381c5a8004216501680341240740030329075040c840741c842141c00c64244034480d8086101d050720340d8803403158921640d0040c0c400c07904c00c01c682d00298a03002d250120080107400d07260321601c00081802da1000e0404080025080480285038106c00502002881030f80c03900403030700c1e42105045d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 155977751 1250 155976501 155976511
    0x8040b07050a0204050a02160308060a1d06040c1103070b0a0603060504060b010e01030603110f0111060a0e0c0a12020405060402090616050d03140c0703140f0c06010e011a0c0106030b 80
    0x2d0016042901545880d019054000c5426003003107141003c6d40158203824103200800400f4088000300194040c0e903030360300d058000e1807880761503000ca405c6404040d003a07003402c072070141c070580c035266914213214401d00d0000c0d00c9440704c06c0107624014580d2603680003088020950f10740c0070b450f90004030006030780b805041d00503032044002181b81c81c3c08c0d10001d49178420619902d8101442d0040410200d0305c19a80042c5030407045c1d40c01d900300b1504d60012561160f801c411803041e4030803007003800070f41c105992091a0f0403840c502030f40d004142c00805c008801d0301d5849070322001d200d0324800e04094541640043e80003803005000601e03040c100340200f0001c0d0080340d00e0300d0980000000010a210b410722030076105405528040040f95020034800050a001422481602700c0c00314546003050700920022a80341c101030b403800d407210180781000f40d45900541e80d00c08103024810001888403415003d0034140c0c0d0714032030681c0c6e01c52040e501c0b4224980080d080240599203404e03000001c40d00c04c041c850701131 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 155979001 1250 155977751 155977753
    0xd0f080604062601141003030c0204110a020f06060306101404091202010903030615020a0b070516080403060f0b0a090e0c28121101080402010c14070819020f01080408040b0705 77
    0x61a03003041c10741c21100000805c0f2003a0321031608001c0138260008190003030b2540f500340401543c41b00d00124000f0410020051800c54002414441e441e40005500341800e014100702c0754075036560418140c6511043e21052224403200c001405001a00c1c084030208503000b610001d00701c0c14503100d025179080680c48600250f50348440e40c20505600d8010000074110440c140045944060b000035995203040c440940091050070119414904c40c00448808503030300707040c00100e200142401c250300e41c41840704031169450014484a1248180501d1441c0c0800400c0102102d18010b9030402030300d020001c03001d0706d01650110307007034507560317010718106541803403041480c00188030f850000b0206468000c02c000300c44680310007000407241c800b5042654803c0c0380490682d1903910040c2d0314810941001888420032100284180340c0c00070700c000803103031641d0171650010420b103004020390014450207900b007814040d1028041d40a200e056401500c0745403094540b039501d10710200c95030081c001c04c0f521 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 155980251 1250 155979001 155979059
    0x5040201020c0a0b34020603280b011b02031c050c0609030d060b030f07050d020c010c110d030902031002180307030c030209100b180a17010207140d0f08060406 70
    0x14904411070640010340d5000c9141403c07980c54101c0c012110744e8681c00903c03039400000094140c1c0c2d5500f4002c41400c00d00e504649d4003260050340035000d02075400c5213600003889030403144105014601400f40107038000e0301405080740c8074a081080305c001c907000101031050800004900b11070400146110ba42e42c4009991102d500c92a0b41d01510010b82c810210400180705120700000080c00d00c540040480c1006541d400c0e100070303054042c1c05407d5041c002541392451024081e500b060317003520441190000d40310491380000040c1c0031207048070b4010b034040d80200c01a00240003640d00516607201002c0203c4103c015420000340b800840360001c41e8440c951940402c11800c003101c400386c000b50400c04070300066082c080700c07903202d004081010210307060a08596050342c5904030303840098030480107107095020142a0041c040c0d8401070080b510041d03502c2d140a5003450200309001c52003403655030795805841ca860200c0d07290102515855101d543d866000402d24040c01c01d980d000920000001c2c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 155981501 1250 155980251 155980267
    0x18030305011403120a03021e0a0c0b090313060302071103060103050f1203060105160c0306020406030218040b01021f18030306061205010b1903060b18030714090a05040201020c0a0b 79
    0x1a602d03060400700360080e40010940740742034002005507600d04c50686801611000ba020301c0900e18400c222551810b0040017840d074860301e40c4607001c086501d01900b0f0820240c0c40e0340304c10301d40c2ca10400340d0303810750200d00c01c43c1030110b18400d8004020060107024902c4142d900640024100642a030080705e1070ba20283ea5540c6000d42840038135104190349043c0e9041d4900f43e400a40213114401d401003001c541c280700ca00400c8042c004034005550800001c6455036182c00e4060003d41c803030074005010780080c104822603403a140c014000e82d07040603405048559101d03801024011441303807440c50107039190441d0307545014200b40b010800074042c1c1e4000c2151450000040c04d6a40c0c40320b121012142001b0041c0041d0039a402110311000b541c3c110014400d03003080342200140312a40051000000c00101b2041d408448103000741c0315042141a600003996410300e41c1505405900201e400c2854200090b03000300040d84480d5001d4010700549000d02019000201e00e107805400100d0b0096010564175 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 155982751 1250 155981501 155981519
    0x4050609060405060d09140303011d04020607200307080102030c070204091505090c01120c020a08030a02040b04170c01080f01030b06040207080a030903110a08070b0907050a09050f061f0e03011803030501 89
    0x1c3c7e4100350750300903601e10350400c44904283c82d0003a29116580b4a40c0010800719110482101c00d51070300181c107040204010320701d0001e0480c000f44031911038881c04c440428001d5042c13080300d000c1c404184d441c51070081d603982880050704101c203007514007815030b241c42c0c0c6081040307016031481080048c019141019980c0c0024103401c9408007164819440c1000d015075042d00000c00c68041600400300c0f039100d66a8046040c040d10a50700710340704080001c140010600b99080442c5901c281c040d05882d02c0480d91401154054401c40f00b4502d03050581c00100041659a0320440e00140b020b0000b602c0c01102d5203038400b20b5888141d4101c000f0307a80742031180c180355000c20045808071014000d4010000c9640b503c00c12405082d40107090f8100300e10204112034400c00500c0d0003483c0203045660b805035101603002c01030000704c545602c80880500080c1052170302c00103445245280003184c0c0420411100c0886000c85400f125642641d6204000714404801c80d041840caa4865a400714180d030600b0f0541e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 155984001 1250 155982751 155982773
    0x51203010504111c090c0503010603050c090114010c15140c070203060c03060d0209130c0b0d0f060f090e0703021203270105090d0503120a050a0b03070b04050609060405060d09 77
    0x41d01c403e4800b03000ea0720300600c83c10030009000c04000000724450303905040c030f00c0e0001d80551140d0f500d5840c00d20000b04221003c01c1104502d00d01301c8075040c01d80c5e6942603e10b40b05402070100c500043e0500110000500c01c42501e40200691000000300710202c1190364914140030345807944088004200c00d011880c00300301e070944c881c0d03a01d14854103600700719010680808035841c00074400c14505000482024070605080301182e040700005019a50390504201d03258054030701e1001c19030a0403030740741e1642c6880c0580011a0103001d40038038600c0c50200c6480040c050840d004031207001e0840f001015070b8031802e02c0340312404503030080e42c4c0d1182509000a4000240c03d645018070049503454070880c0e82020560307000c1c2c24241c4140046240500c1c0c428214801d0722000f800d028000800e000d004503460f40814865108001c6c20403445100360101640c0b4102d5104119108008001c14081410040094150300d07002504041c1030680710f00000e04250040c1014006003079503071946005000da07110403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 155985251 1250 155984001 155984021
    0x100f0504060b030f0c06090d02060409020c0f0601050a03061a030a060e0d02060f0406020702280515130303030f02041212080c0c06011401120f0e0606011d120109051203010504 77
    0x2c210308004d010301d10b521181032001d0b44e486942e0100c0c0301603d9848643d500040303190f00a1109030b03925201c0405030029003000d6841240c030310544144036005080064171034103807640101300c0e07580e141c995500e0601418440d021040d44441c81768a050190b2810031202c217000784510400310754008984009480c209071400c0f801c003103622007402e0000250405c50307030a4000f604100302603074402c51350004c01e0b40d400e040503411103850a85043c0810b00d54000c1c002d1026100d0803569504102180d5880e000320f8005c2c1e003042146c9a840c018100000f034000c2c1d0195000950482000d030400d44d40e46c80b8500d044481c0181554001d02c01010142115031280406a011043e00d8030282007448a044003540d030041400390840e0b42101c2c4602034000d0b0b008408034a19a5002e6a003030040c48803107100d80001e403191401901180c820900403e009600449107600d600006103403608149500d54100807103092190071220080d5030f66100300c00460414043c034100d040f440c03165241d036035242c00b09020403070f404620 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 155986501 1250 155985251 155985253
    0x9040911130b061b0307021512060105030114010c05121308010c110d0806010210051303020607021c0e06070c081506041103070c1a1911040f17100f0504060b03 70
    0x4107119075035480405135a8420300403600d403024180c600076003034a14482c05030041e5221466080d010905080c48004090315000703004540866100c100064440f40004e0007080250341c001000d07020a03500c101d5171110118011012074904801c0c10481d00c0869002c05580c6507544a690401d00c4180c009006400000c8102d00c0d22620002030515400d4a9040441d0201d04220114001c11240e81c820030401110341081d43e01003003a41010300404e010300e440c0e104114054007416001a2005001003075480c0408402c06070300c01e04540092088506821242d85254001818410b000100e02070410b0340015204a00080017105030351030b069422045c00902c000d100c0da003007982d00c0f400ca4a080081d2070b0408013504000302c0d03c1d849460513079034040b103140c40d11030302c68111003c10006a25800c40e03904910300b0a001040030345642400d62103240302d5030051402d6903481c40c800b004040c14080d03100b1040305d28107040e250040b0ba180d60000030703a0040b859000031140c80b4000d010502181f80300784036444034220 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 155987751 1250 155986501 155986511
    0x6060b0c0f0f0706050f040b131d150f01030906020a0806031612030e040b03120306010e060702031b0d05010f151508072001020301031a0c07080f07080904091113 71
    0x71031040c3d0320402c034000c600420a020981801d040d08010a4038003401700c0010b020344401c0b0455105403150418410325401091032820b003240e02719500066030040c07108100e100741e43c0c0a03c6080c016100d00d0034030340c0303410181ea40c0e04002c0400d00e648054034200318550380709211810f100c002c00d4607029142e0080b03900b14010400c10040008240c1030200d09952600b8040ca004001c41d000030002d217030074010541c0600448070b5081801099100441c4030304401d89540278a951000240025802030810013500b40e400701c50220076010001441000c80b80c00202499690040340c1d44041c02d46201e01e41c407801c850f80356070030020030108100001000d4080041040c51b0319505010052035030001030100c40038040854000c40307004102e406800c1e580903d030802550380b56500c0c540001d5000801e004e500f031940c0194042001241350394115030056410954550030002c404070b0003080c0c0da0101c4401c5640000401c070301d60080d00c07140603085d03070b85000c2d04090002803004001d000d603c14001c0039200c4020b00d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 155989001 1250 155987751 155987773
    0x3150c08071205181c020d020c0a05040e120c0102070308150603070c0c080a0320031c050c0405040c08090c0406060c140307170703031107080a180306060b0c0f 70
    0x154000d144407a0544011030383e529210907219180d2040f8001115a020b50b01441c00601d040c414085185072071642142c01410310601c0482c0c4400c002ca050070344c00b0120700e1082289140c141c2010713605500c0c0c00709841d00550030b03444085503a4090303a0201410303500810700e5070500d0b4002010940c8501c104200b01000a80000011020f100c0104424148070107000c5e03010038012040703050030280c52880100c0324843d2140c10701809010410a100c0e168074828207850303540c02c0f0048142d600400107400c0e00c00311025101e8070b2070003030000109003021a400a01002840d0355450103401c401408079103c0e100c0d20f05007168014203082011501c0b6002d207007001010801030b1740c01004040541e030403c41048a903000c1030001425846011005040d0821030704c0d2064002c0612401400d03654401c1d201001407003544e642d244030720b006a6030041c0030043d0501a95001c5401114051421040d0302001c103401502d0b991580121000c9411407140481e01150f106103c0e08100558000d400410f0000c007503d182e1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 155990251 1250 155989001 155989007
    0x60503040b0403033308070312050a050904060e07020d0e0609100309061401050102101a060307030f0c020102131a07110102032704110910050a02150103150c0807 71
    0xd00000e04080300d00002405143c03203030b0700510360107050b1900300c60764201101c40c0c86183c0000b0200450810360b5910000342030680000c0440880703500c0100c2220400082d4029201034000030340c92020301c102042401c540765200d1240c40040c01801c00841d1807410403070002031600c04003066003000d20000c0000c002c070540c1d41e14142c907940003080743d01602441012004a0140020840c0100060b05290030401c500c40825542c60584a0a0b800c0701c0c03403c01d5645018065420103150b074040c02c50b5858a503441400c20000461b804102d60401042510040503a40115110f0350720200050350b02103161340754864181002e20080414410013202d03541d010540002e81c0c801d1045c020320810344c241001e2a9a402881920403100c3c0c66540c06200744030581c0c0c1803c0d980300c80b03641641300310310b010036042c5a41c03030300d034261042c041010b000d040c10524660800d8403030764802c10a00b0300b0340c490500040c00ba0f480c2ca105060207140f040b40c200c40b00d00e40745140b1a041d80c0081300d050f000d0000d0f074020000341d603074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 155991501 1250 155990251 155990257
    0x60f020a0c03060b13112d0306090709031a0609061e04050a09050a03020d140301030f02090402130606030905100b1806060d06171e0709090501020d020c0d1101060605 73
    0x2800050020303100c511940045c06040388405040d644505200704440050015005800c1c0c4082c040340400c4a60000c0042000350080000c106480720820f2000c02d030682080c0e0000d580c42000f41c14a1200c098581d100d0000000b20134034108855032408040042c581003403641d840e0098006d5424107110301d081d18200c8000f8240d03441b403031b005580c0c0e880003600c80c845903008900c50781c1e00311040c0e4004600c7c0e07040003519080403001e0791020540300304415040e400c0f40c80842e412282c000c404c0d45894070303041d402c2240010000e0030990344000f40000c0c02d000c4404601c0b481300140300075180001c0803040c528280e07090154a071420707050706250050390f404d291114500b44c01c1c1c2003d215000000e81d45c44c0400100140906180c0c9800b280c94254041000303102180c1c0c116246010707400700c2d5016250104c038007010368141380e040034480d00448000c11407101d16810004905100b80e0006d030a04281c103080004a0300580050800c9900003009540b006810101c0390a00c80e65482c000d1107541c1c14071401400b184 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 155992751 1250 155991501 155991503
    0x13050402040b0609150903190c030501060b070f0f2a050f180105060a031107060204051c020a05010507110d110114030106050313050f10061701050402030a020105072a060f020a0c03 79
    0x5d030b0b00203071703100d02a0740c2440440040c40103940705884240d000d04004024010704c0c04129003643c0b800070040b502c032002100b40c07242c0070740c032840240c000da40e0399a540359280509401100c4424043d00c142c40c5003200d1002c070182d109641c0080f80c241c2458101000304980807100b070607001d01517007040002600c00003452076045d100d09803541075070365520f89821401003200c81c84003c25080041009420851640c00900031201c045902102c210840114500300003100940298855210790301009954000d0019105840c0a03a80c40001c0c01c00f12004128111801d540c11144120700e441c0c51882507801c49410701c204d0cc2440d00d850700315030628030007900c04d01c009000220381039044d21001c400c00404000c40c0942046400503104100100072015001d81103d00409003410b41032105241c0880c01440b41a2250350010014590320f80207400541d001e0340501e0302a1003200d2090312520b0b45c4419503c0c00204040003545c003040035454200004c140ca503c2c04c2c0040219005800740750081949400d0001c1a0707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 155994001 1250 155992751 155992789
    0x105191103130f06060b1803010b1305060d060e0606010f050705070605070c0b0a03090c17150c040e070c06050a0911120304080109050102070b0601080f0412030b13050402040b0609 79
    0x1d0202800c0a0001c201043e0004045500746100804c0c0713049040043e051030030620940310380c54072900c1c1c00c141c26160101c0780144c101c07841c0384040307a8500160300320680003040a461562264815108c040c103455480580c071010390300074001d12500b075030305c521040044186442d01d00d06026040e40c842d51286c0003481140b0400c4404248541804005140080186408214103139901089280038010300541001694541842c0c00c001800905464000b403001000c90003502d00313066032a99000b510030f0003610019020700e05001c0440d650351300041142c00f5010036166a0f002c0e0200b460701c40140c0b140184680c0c06039080c001110001800b44038444200f50007110503a240f1640f00d0882461400f481c2d01070b122542c00c180e04601440703419030090408501500004501c0e50f00d1000664444100f41c8501c02c59074040000240450b109106018900440386008605050309400140782107074010b401208250b0b9542c244011071403d80715545200c94250b410030f0500c500c400c001402070203180080102 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 155995251 1250 155994001 155994031
    0x70803070c1b090507021e0d080c0d0528110405040e0f06012d05010507080d020706060b040819030f111e0a1a0c161b080105191103 58
    0x1c01210303042d40030b45844a0788400301195600c80025001d1324040d80d840016000d4003050100007a0390f08035500041032080c00518545900c0041160154001800c030011482c003800740420f0340307109000d0710740248610f820351112540e020360200c0c1603820040900d504249450041030300c540c440010b8800f201c201300d40c00940b640840000e181400740c100f11000c040d001c2e031000843e034520b00c1c8110304404a880c60310808448220040416021014029203000c180c0a12031200012917160003041462417004000d0b060035441c0c0c0c1c0d200c090720103030780040f2541c0c81d000c2820f02c00c61404120040307202c4e90342a4107140852803624050704694180050b00d00304484082d03170b4441c45408109903840d05140106031240c0b03a0800d6100c81d10707030060100841c0e2018501601c1204010501000d034000c03034a000c24a407074460380003286210721910500c112201a02e50411840e00c006040440004200c5a000070800303103403524000c0030912600e03c2e00300103a460700398090360355480601560f901c020007403540d0700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 155996501 1250 155995251 155995253
    0x2060c04081203070512072a0b0103080a02030d0c030506010e04090309090b0414011706060901030b0c03190510050901050307210606180e0606060c060a05191103160302070803070c 79
    0x143d9104003415600722285540911900903480181062000c6000d4a81d82010442400802311160040c0010b4950306002c1300510110b06004000d0030f140302a40100c0e0300c1d101e0100c0500c0306036000c03c0000c0003c40d55070000c1104650704a48940e1502204881c10810b42c40070b540d02401030078175409000000e59480c0c0064141d6141c0e80d00c114440800b180c40d2144030f40c0e452000000b180003076901c4514a0080b94081031107410142c513154140c80d03000c0c10750186079544004032002500b00a0100071000a08003a15044403070358403819010300c0901d100e0500d00d80c2014144520400180d201d41d00950040038100506286042070110340060561f10a04803040c0d800d2810251180b85c004050f0036850744504d04100d20650b201e80304100d2000f041d92a2551441c041002c0c0380169100c103203c0d84c0104d00010040346850340300d981c0c0078030045405003110074003c1000b01210400c03642c10f44d0303030440003051000300300411280e18802c000e98a020751030180030341d48000c03060001409480500c2800d80f039180c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 155997751 1250 155996501 155996507
    0x15060130050712060902040906050a06080f040f06050f0603120c1f0908130311040501050d0303020c0f060a0c0905030303010305150408160c031401050f070c140604030f02060c0408120307 82
    0x7044051040400313214840d02d403901c020003940584955280e06203080d0300004c550418003a4001115803944541280741d4640d0405443d01400400442e8005441c105210020f10ba80c480c00c0d01900150300554800c0c505042410700d01400048844848a028030145020000000311648808200104664440e100724200c1019240c1250020102030000c43d1000012541c02c070f84404803409906694408800352040c401160000e0240a800400c6c0b02100070129000742c009103050002e05049440150905248504101c402c0d43c3c0200308540350034564502c60b5100b80c0f00c5000d000c007100a545554903581d00e11b5a64192a8845a9a0b2014100041c24451888151826880c0c4002c0e01c0b42c07080c000c4d140c440c00c4a0020301003101c0c0c8189101070605d0054052080c40c1c4901c0c0116440da07801e4903091403d5582c0c0e100500120350f501c80d118210711035000d003030103442d008a10903210051120240d050103402e184008003412802c000c00e020030002c103100040d507060f03880b4409072107075540d80340c03a9411 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 155999001 1250 155997751 155997767
    0xb06030a051c18060804030f03020f1b031603080907090b0604030201080c040e1005010f0e0108061e0d05010912053621011d06041103010e150601300507 67
    0x12000804480c030001130144c2d00310100c4d0348106d110742e40ea03c003000c10380d100c240c04900880c0e2485a4540742800a1a100c10fa8200c0c40c4c80d01c8003014080324284400882e0420030a242d500049000901000034800c245000704180300190402150a0041c5000c510101705940240e20029040010072004100300c0101c0390201d5000e031140d1021410700d864100941c40c030302c0d5114401d50780080d00d15640498024071a1509000014050351241542d8482c4020020011210080c000140c500d0121a003440d0380c40500586240f4821400401c80d1081410b0241101420040e220107100e81003000307404c840d18003841d01c03203420201e4412408484800514122900c0c04881554002d1070000242000f5183e41310008040340308000280290307128002d014001c103030810707404801948500040b900142a041001204c4000074000180c020551480070b40342c009044580c40c0d840902c102070281c5c550303110701c41d081170b1074030480b00486d259503da080812080180a544c0c07003007039842000c00c1c00b081c860709003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 156000251 1250 155999001 155999027
    0xa02090a180f030905090a0507120b030705030d030608060a090210050a21022d0405060705190803090705090709050d030c02060316090f0e01120311030409090b06030a051c 75
    0x4a02c41d07048091030050041c0c07115010f0f5034490959500003540003084da01856200c1e4070182c6c2c40c00c10b0940002008000342a480360800d0341401031940100e100c1d02c0400034880351002c5aa004036420b032130100c0d05820200051b0a094206041039070308409a2200c410740403001c2441d103001a81c81d40810000c80f0f612060f200090303404040c0d000e03905150071054001e0301401c41e05610190a0030880c40300841c6180b6500102c500b0100107100401c014071340000984013150242017960302c0110b001c1a14070420070901d100301c60755003000c002d001c0b18100803c514805000c00750754042c803038248104054402c0300a44502841040c8012001c01014407444001e09d50650141c801d5489003070808a0b070f04445041031441c800200160000540b803803161181d0001c65075010500d8542d0b90030401c3713419015510a4054091043c03120703080312010020002040100f0b4040c400041903490b0780b501c140c0031800a01000d2003a440b04c41e1007030229001181c1c0c03000c1d03407511461405c144250b801048d0790400d40c0c010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 156001501 1250 156000251 156000263
    0x406060305120306040b010207062c040204030311210306040515090f01090e03040b03040b1b040e010302210601090b01030f0e151f0e04020103060e070f09080a02090a18 74
    0x2e4149080440e02000e98041c80381110240111200c2100490340c4403000d200748400180501000c603100403400025020016001ca2044c10300c20f881301c00704041e0780c066032088000a01c01d68a4143c03169050000c0c1d06604038085074200381c012040300b1150346000c05400c16108036950740c04290f940034110034032404c14801500200142c94141d0400100344424071031046114108219822507003404012136041e181c507403818506580b50b60300c4450f8044802810013044125a0f150000c55134042009000204032070500350500d5070442c81840f00c00c12401e1a50035100100b032035030026011022030420f05440c114080010408158401200030b0620501e4402e100c074a881c1084104090110740142c100700710302c000f8811902e0b90070141e00000384d01070022280d244564414004083c24801d87d64119005160105007030342c681d5200581c01e201030f6100c0000c0380c1c903a007151505582100400d001844001c000d410b1548242d004103c1c4101d0082804c48541ea59451000d9140f0381007403414402030b0020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 156002751 1250 156001501 156001513
    0x90302030d030902030606220e0c0904060c0f050403051915020706090204061202060307030e0304030c080f0c010306050319060f061d060a050d080d1103090d14030106090605030406060305 82
    0x140301400518640381c040c5d0183c064400011898140941510680003903104041d0302d007680c1148102c000d105000c0c007c402c5006a040070041565080403413805640140800200440466000b03001804503185441c00e101c1d00340010004940013254503a0600d020020002d02d009403840c25030b40c004001d01c81d628200d44042401418031503282e000c40d80706c91007528200300260701c03103490a130146149100254008010400604120301c46c0e0841400b00c2c10b20800c803418a5102e5481481c03921081d001f064a03944010041021641c007080010b00d000000c2c00c0400c105130400d00030a84030b00c2d5081000c4483c0c1d6440d441c0340c04000e083e604c41401b100d4070714410001107807226403da01b05510420803100f1540804081491490400000001c4035001002d50b080d1818551310b540c0507030850501c00c03020564a54004498008a07402540708524010142000b00003500018115440c208080700502c0014001070020341c0d04880c07640d05440450810b56280d0b900d6142c050040c0c595500024850b00540c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 156004001 1250 156002751 156002773
    0xd090608072010020a0e18041e0f0203030f21160e1903050f060f130609030302130e0939030f07030503070b0105030d090b09010c06060305030702240a030c09030203 72
    0x4104000701e403c5d811210380e81d6220101101f0150f0035000d542c086d050020300e80c82ca80901340c0a001d81013a25108407040a4800070740e400190564103c2e0000d07503042c0100181030500c100114610382449440120102400d08000e10304070001010802007000b4022040c0c00055a03a0303070500d051100741900131401084a40300d00d040b544502c14484d1a0f0040c4c400d440c04079800343d41000c003c4d0310940221403000801d00c41c1c1d1711054003812603a003058062681c200190100c55621291200240c42c51503840d20712401c102e0801407406001d90030b29900c2c00f5681c054801030411011030111608020310b81000d90145010021b070400c10307501d201009502c24000000100413000c80501320180c018021300c09580ea9440c140341c5c8483c01e0101031000142e401d48140020b0119201070101c041c0e042c50888411a020364070001142c03034680081d202688041080d004503d802c84d02003148440000d4020f418002c1003c0402050040c0060708003895207500200c000b09100307079120802950010112500701c180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 156005251 1250 156004001 156004007
    0x120c020114040c08010e07031a06040b04020c0a0c14010503040b0c0405030304030303061503060501050d1d0a030c0b0624030601020312010b07061406010c020f1201020a020d090608072010020a 84
    0x3c62145060650804020b0b460144000c144002101e40040005861400000843d1446203005148542c03195030b07032500e40342d10f480e544050181c1202050003091020601c2c10100440c0d101e179800b24200d181c1c940307044040307641d010058070b030032642c030110005680d201c20b204641580596040f150701440045400820305a00d0b4101c442111fa00007030130480c1450046040781a2038060003000e0100307a00300301b6804006029032204001071a00401c80400c0c0d05810005800c001425070203800081010045030705121613207144581103d0100c80c280094190860100907940040c202510350090100000d109a4000d208a82c0303c1c152525558803607685a035030250300d0340c00900013071b20036910382480c041c5c3e00300014002034002c620507102d20804005d030b542045428024035600d00c1e0404408184202150402d002409500070b640d00030344004284124014040e400c0c030390100e402c00c40079105100440d504401010140c034070326109640800c0c01601a07514004500c1280e40300c0c144002207640c806a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 156006501 1250 156005251 156005273
    0x21810020d0305150d03080702010e0f0d0e061206060c030c060f150108010e01140607080414011b02060d02090103090b010602071701140c09010c0503030103030e0a0b030403120c02011404 82
    0x18182d18200a162600c54001c4050200c00300b0880d048145560010b0120307004145a80c0d1210302c601c00811801e55440c1c0300c0f4104805410109a15807064402541c410b421403440b90000300103442c01e07420a40d03d903040241d0804064003480c002c0800260b40210406d0a00480f41e0a11a0404882c102d0074407000d20420068210b417920031601c00c0b04a81c400540c8100705640c100c8140019543d550707400d184c48018290748030026681e04c00c80c00c00c401000152002c0141c0000c0103a1b4406090019a050024200d072083c6104003a08800b98070001c070060742c0c0c00c41940c2508034003100c016218251340d00103074010a09a000900700b52020b100002c0c070036900050500549070600c800c490782c0200240380714240d5000004000d4050304032800202d0030341151015100c0e40d030051422030f82080007a100d5608650003a0030940005086040c00c80107810102403041c000c141d0483d000e45946050b450040c041826000c0f0f040ea05621400f034180281e1007504941c0b40d45a0701c5410f090075060520b04064414 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 156007751 1250 156006501 156006523
    0xc030f0c060403030608010c080105150d0e0c030f0a1502070c080a0606031202010b030613050a1a0907140f1207180b0916050703030e1207060212100f0902181002 71
    0xc4c1c05c1c40b202245144040c0199100740085888804150f42400200002c803010300e040344c1c0710100b09010810050019005040050310030350003418208580600b49800e00340280c040914650044020100085032042c110301407190030074006884503128985081080c0076039200c41903910400d809072040c0403995000030210380c420000b407601c0c044000302c00e03804e0b01c8082c01501d42c590058000200c403c1c6903c904a118288228107403102440303560340e61441d048650403144140c00b04103041020442c001c01002d80645000f002ca8102000c410b40010041030404d403002d80182c0520b028034120031400c1141d000036200750101ea038604201c3c103078030000400a03811803611a101c1c2c80b0104425000b0006040c841000560341d50349030004588042c0d000c1c0040104109251240b01200001c20010030050040301d403180c8409030707894100b141d0284860324054401c0c030ba2150309140c10001b90520a5020003150740b410300150716000b2820703810704071142e0611105d80220940c6d4110790403d80c0840c90340307110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 156009001 1250 156007751 156007757
    0x1111f02190512010614090603130204050106090f0f0b0a1803141501052e110a03050c010c0206071b0302010e15100603020301031a06040b0d0b010f05010305061003020c030f0c060403 80
    0x20345e9864034119040700c0140f2649004113420080d00e43d03e03090060055501c54801541c41102401d1540460f045800980c00030b00000c0c00602d0501c05010343c20b9080c802400ac0003a10007245007401e29664541c0704240c118000d1001c400c032984480f030a80c1a41d01c00958001e60079003040d4103040c0e0120740b42c904040707440501c101c00c400041018945000d640c403804103401078407047c10b00b1282e04035581170310075411002400f04501c034020141d503040280101103031180d581c00d510b071641c10032420300795241c00f40d01c502590008001c012501d130f400740d41402c0f0b1003001d142c0c2c40401d50a6040981c01880400000b201c140100c181505003041006080e900610006600c0e03071515941c0d00003101280020300005050b0600da9520302600440b01c0000c94100900500009203079981d500050500011032a0031104004903000402280c40002a070304000d110070700301400545071000001d5401e01c0ca400041d0103165000ca51110451003c0040c0e5141c01a60401c8680d90981071a803943d460908960483c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 156010251 1250 156009001 156009037
    0xc0e25020c011124130c06030204060e03012d091b0609050102060c0304030309021807021f0e0c1509090903040504052413020c01230601111f021905 65
    0x10000c00601500c5a0640b001c49800442c1c0003158140139100282901e80a80c840d00c0401d00414910751180d00200580d48006994501e000000b600e05031050124a2099251040c000328080c2c2d00d0b13104030080050fa491301100006001025001000c41540c09000e10100d400819135039102c4000b2007058a54a4840392640d075a01e000481e41d540d400c4411040d03101042c408100001e000e03405c8004114030040042e1003e03142092013840c03200f4219950001640150348004801c580d0038468403c2401c00030041c0f10034101f01d43d24550340c2d101201c2c41d6018201c40710406820101441c1503803450b0000424040741c40c00c2801080f1f550b90000d00030306100b180350101007103241a0860344400420003010300c52070714686500c100300d1280f6024482001c0b294080143c4c20501000f8424411595000c2c07a054540d1000c003030800211100090081c0d040c09100200d40080e100300161110060440c0ca4607451004281031841000e030180948503c8a84583c80c102c85809400c2005805141d001a0040300c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 156011501 1250 156010251 156010277
    0xf1413111b07240203041401030b270a06050604051302070f0503030a0c02011e0b010e090a1d010506011e020f0601060804030e0102010c091208070f06140708040c0e25020c01 76
    0x458070590700f4400004d40d008000401c0f4a10001c541200351150504000951400484c00f0a00541c1d805c45034101c001800304003590b40b1454102d11030313042803185000b00480d07410700b03003c10038910940c00350354485d0b01000004103e030b1440b50100c400072548540c1c18003e8002c54945a41d40c1d40007034076104405801c03c3d0a144181e8814426007091290500031b1141d54801c80d87e900d0001c0c80d03030300380c0c1038100b1800021407030742d546440f41090300511100d4070010b1302c5155544209051410912900e8540c1d060070140716140e0ba10051044c0c01d5807081c0b140700a050030620041e0300d4000303045000300450250740b0000070341680140c9414425030094540c9200321100b40c004a08031001101e0101c049030690b00180000c5c0305680d0005003031131140e03504d239241141c0394541c0144482001021981140c8540100244101990120350014a14140480c6a0809a440002e01101e80c09044e4a070200c90001910304d107d240100d00e98540e03855080303880304201002c004c1d156144142d400e800314403680e001103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 156012751 1250 156011501 156011549
    0x501060602250303080a09140609010b040603080301050105220b030a060e13140c040608011506022808160b01051c0203060a0c02070803040803040f1413111b07 70
    0x4403019140311842e04410303003140d800751078901003e440840c0380b942d0381d40242c00140c2d46803003002c4c1c0304002600521051400580d807a00b56000a94840d0180b800c01508000140c81081624155142424038584920b4010b0110011400105200344500d08441c3c0001d541c440e860001c6000e18041c090900003141c403100e1685078a501920140003c490120031034020910f40c20200394031203448419030707210148400000d015075000d80c0296907265540d40d110410300710f80c010010f00608403030018001c0f8021500c140c0324030407030f0041d518103601459212001040b10708006c881e03000943d6050411201c0c143d0601c40f405403004d026141c0a503100c10312490740b02c203014010f10b80281d0300030002c01c2d480d500c6d041d548020f016108102010741c80740110100310204180080d2003e46020f01c02192111f01c0c015040608402d9036001d07007021007280c080c000b056124590100d50980050001044890715858805003e2046081c1d6005454403880760402c3d21300c0c041802411144041081c00c20406040980 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 156014001 1250 156012751 156012793
    0x503011d060609040c030e07080f01050f0115030e030d0203011d09011109060c0106050d0f0b0a05040f08090d0b1501120507050304020d05030d0908030a0c090b1e040801090501060602 80
    0x119440003040c4600c82051030142c0004171101c0081c640481c000d03140600d46840d020a5810200c0c0d1034102101c0001e0601d800d10a4035881003000e041c070075503949482003070464140950124003c0640b01c01307a501c401801081119203001c604c010441d42c96a4500c0321042c2c0c0b281d04d01050400000c00340200308900414025100c080782d0b10140b0f83d113490000c000300111907112401c42d0580d9504c0f0280010313181c0d901d142d0402c50394064100d20704510341c0c0b41303045107042c1c00040c1010760f0a4500420700c800301d0400091006034560142010303030b4502410001402e483d46295008105c4a451030400203070f01032000000600c01402c0e2103040402968001023010f40f031013160700700e002407801e000090244c6444c90201224a01aa040c2c0e0f203011b2915080c1d0341502d0360f161094564030400414071190030b03118801c401c0038507014903108a006080402c8445103105a03034050000c2080f105030f101030444500111002002c410000300304c401c0107813070981e010700800c5c42400098014205a160842511004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 156015251 1250 156014001 156014011
    0x90b151806012007030b0108060412020106030b0a1a040e100b03030906120402010507050303090705120307020a0b0f04050402070c15050f0a0305150622081605090403031b0503011d 79
    0x3c06100c09030303912401e07028204042601055101d65140040842d607540c050318040e10f44000a0141071070b103400c0c0302c2c5000d004003460318210780c0f50005c104003040c88591600d030400d602d14408500e0110100c400c815030712105905170750161901c0202820000700007902a2105074186061149980340f07010141c44e80504030300705820081c204200542d0700d520b00c98940d445481410075a0400c00942c80d140c0c51504101d0f01c001040e80301c40010b10080c0351507418000b420140100441ca04807180d0302150607085180704003581c002000c01d00d95000c00b10b0310281c501500004e0011910b442d01820b1029801d0001d1199440c7c10000505d45019103115400311a291640d0940c02480d118228034124028400207000711482c0c800c0f42c01c000e026036030781d100410030780381c82048914442003108801c494000555210440ca40d004a140e020b0317803900c44168104842c1c0c00c0320102480d5880342015005403240f4071002d44200345c4e038881c40d001550802c01950580c0e07940b408422000c180d9101080300f114051761 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 156016501 1250 156015251 156015257
    0x1051821121303081b071202030c04050403020a021908030a050d050601030213060f09180203090d2a0c05030304032303040303080105060d0b040510170c1012090b15180601 75
    0x90a00c0450a4000107080c211404040c030856a1103c000780c0d81801c6c0076030044600c01c8810b460750345c290324040265a50b2080202c41c20015070810b654080d64442a20400030701420130fa82985d40c240824154000007016a1025280c1d0b50b900d085005049600251010903d0341c2340c8004a41c05512920a54404203205510840c2c0716044c1442aa20b050080605030300f002503100003c00e04a120780c10b021040c599000d00582c49041c001101401c05401080481c10000350303144000111744400d25614110b0b400c4040504010000c3c00e00c1c002c08403150700516010310002400204210050009034103410096003c541020740c6108a192280300c1d510029000a10079030051000b40343c900010490540c0004000031001e541401280c00e9980449005000400010040101c044007288005d411528640903080d42d101e080006800581142803035801c11461000180401585500c00d001d1650051001540741c503007908070034140207080440034040e4040c1d20020242140c008095402034030b05031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 156017751 1250 156016501 156016537
    0x2060d2c0a02060721050703030506011418030102040506030c040e01080307031e030b030d020705150906030723040e04030908031201062f06010311090112020105182112 74
    0x2800b081503130780005009031001c0c9036800c0c8040300400d00101d03c00701d19400340c555548070b0016003070250858000810560502c82c912426201079803852044071100003c0203094000301103003402103402030007590441900311200005009150800102070070441e0014803190020303030b0b00c62a03882d40344d01640f00d008000c5482c1003200c059980001c0c0300701800e4030311803800141c0c00c50b240c00081c0ca811000c40f1420096041008103205904124010386902008540400d2809003034102198035484002d18080402038806014401050520300701010445001201a00d03a61030341c0015100081c207440880208030704000c0000c2c4070101100342c40043c0b04080f80c1c6051a0720b0100290f03008030000490814009030306801d686040350018602000c01d10f860014a010b604520303010066407046440c10b40704e6103503900100610501141003800c00c40d0b0a2030400c0d110030340118040350001e223803503a46502c03003c51a04040c0380244802682010010b400840d81141c1030740c18041d03d60b106002403420f45040113 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 156019001 1250 156017751 156017753
    0x906020c100e09180105060103020a120b0102151e01050d02010203090d02030f03041d060d02030a030c061d010504020405100f0e2707060306061403040f0f02060d2c0a 73
    0x520707407034030107001034145110030042480024001c16400c4440418919192407042c141401c24451240d0000c400e0034218070308410440c0103003401c4a0f00e400754080356101c40301a80360741d02c01d0040950301920b000b0b0104650910045d01400c0d82c001c14040140042802c00003c1c00e86040200e5015040d01038020314907100a02007403003038003081c40100740c1e010700c141d544038541501c00b0001400201080c084e1000c3c038070b104102d00d0340c401d60007400b601d01c1402070001660140c0e8010500119a81e854207012210800510340301c0081c2c4103203a510303002000303890400c0750700e1007040d0061072142e0720131502003040c0e0707592291801050a187c054941407052204052214004210a081d003001100d203070a4040b00d90000b281c0310f9450342c60300242594102110410082ea05400b4035005404641007440d001180360901ea501c40c00010400303010031910a0200c002e0007844908655155000340000ba0b450300b14484d07800c09400010390454071061003042100380040f01b440f10b0078025600001400d40030010f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 156020251 1250 156019001 156019009
    0x20d05040e0420060f090316051021020a0302040806060a180b0d0b01031406011203021911090702031e0309060402010f120c080406050f07020a0204021b06010b070606060906020c 78
    0x2666000309000c0c1c1001c10680c00c4d5840c1070260008212000400c1c1d9254240801d16080105130282c031400c92085660030700c502d980700308c5a010580032038a0040014000d80120410900c92420440ca540d440014102c481036403540051040d10010320031614991201010f20031020100e201e00c44100c3c542d1003101c190940503400015000700c000b0710604114686403a070825071301c0283d208807504c40d000080202c02c03100a0103018010100030302618000c0685480c0a5203c08411000c20340d48448410a00e0030000c070000c04040516028180340b24a150055000c0d40c1c9a10071038004010302006030051000f0b525600c02c032071103014104050485901e980c1d0040d201c0144000520062110030b220182880c12a8403451503820b04a42d00c80c0b0560800c3d040070000c880d000380603104055074140400240b0358000400b428080c0c3c3c19540143e6502491001180f01e401508052009000d20800010105070b0000030b40041401803504002c019a07030401911003486c1e40c481e10700541c01c5104003a8051038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 156021501 1250 156020251 156020273
    0x6090a17130816050d050c0f0a1e0501030f0608030d0209010e060a091a0307170c1c06050406140904030305091c030203040507090501260313060f020d05040e04 70
    0x20000c511982001c09400e40c00c60915410b03008901103034000620b045144100e02c00d008001d281c01ea1340c00e0384e9100b1949440340c03620103000c50203000e14202038808420342c4850301524000c2180694110b20703400e0904101c2846501361160740d000904081710042003000c01e1003060121494140218901403242094902941000f00d0150500801c9070030540592503603001408880e0443c1e461080c01403c10340601280d0407045002803910109108101086800c15001d0000509086204146580324001c00d9070510440e08014641c4408182020a030000c41d001042174030f50442d400e21500c0c1e1070313440b404903d06072502070640c403030b0072003002c580864021381c001da1300a01d005054980c440d8941d4001076000b80b5840450300000e50000422080c03003c00d02120700501144101031005500d44400078036041480050029400812000c041380700a0400403030740e0340c00b40046002da100360703954000751000001ca409100076004e0420403903480c43c072940855003070340d82a600c6140d181d1119111a21288 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 156022751 1250 156021501 156021533
    0x521060a03020619020d1706010c060f061e08030a0e090702010b0a140f03011416021c0507031403090601060311071704090b1804020405060102070e090d0305060306090a 74
    0x242a5200c0440540c035404000c0c10002c9140840e020440d660041c024a45045906214100b00d40406041f0320545100900b41d0000002d10b0a0841411b403800e001c402421416240301400d0710340b038000650b0350901000f4003001e504042120503115542c101058403071145a1040000411202c000c8115141001c0c280d5005001d61000088682c03456011511612103a048110703000c6640300758601c64505004011014402a4001d01c1072300c0c000c00407480705401c06060041004082d40a07003800c64820403c2866900340c1c81040703c0c007107680e07041c05019176100398001c1d4006003162040d039166000030402c481c0a0042d903801000260b180030011001404045090203000c00c0c01c00220340400c55a1030300180340900d10400315521803404910308115400200281d025000e00d045441c1d0b094007070380041da40150151000b05081d0b0b00c40340100e04203034043c1c0101047c101080c0c14000742803800034030000c66114030340381004180c650304105039680400b1100403140368441248040040d0301d00804003501 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 156024001 1250 156022751 156022759
    0x120a0215070b0408030f1303230f040e07081012290907150c0302060c1b030706050a14041112010e030705030909160503010e1314030702030706052106 66
    0x8a2119512894100403c1d02c00341e5220b0404014810040b01c1c00850340d40044103951244618040f55030701900c440006c845460700464071845034080080c0350002c84056144000046a559485010544061409807510800036000000007440b03816041d04034419143c807403051203c25003042d920f444210012015081c601980c4620301080580c1034001c00380941e14020161049605105100d10500200781ca0350341048402e595a0010036008594940c12940042102c1da03140d201085041034020380324804042444001885030a02125a1044d8000c196144051250450b4082c403405030b41802d0f54080d025950f080c545110030300e800704150b0786c1211958000b241c0300c140110150b046801009041e1541e0b00006035002c00c61411b00050703944200401084d91448840c0705005100780814040c00040360350440c0442d04000307126400001c556481092600384ca004a100c85840e07421101040340684100c020100f030300c42c05081654040c02e05184140940d2021000c0001040c0000c1c20a07504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 156025251 1250 156024001 156024007
    0xa06050c0d0513050c040203160309021219060b030a0201050406050a020a06060605070c170d0f0908030f040e060a080c01121503050322030804181508060114120a0215 73
    0x10800d405224403c0c142c0b064540156071070342c104181480d01308400c5500c2103104000b0001c84510b80481405482914540000e440340c0a1022548100b546210001e19103c5d8150310a01481180f080081c0c01d44110710611104020b0701c1815501c407031715940240483c1050009002c0d103071050303000e8841407115104440078111551908800c44810707800400000d640000c15005104920f080c000c014039094600b5244a000b550b01a030b12007680308a21020400014001c0c19441c0c1b181c00380901034442c09068179076411100d0f400c580c1d1075105204003841c0103000000a2818507041a00404031100c200244c0940800040110b50350180c0a0b0014003650780d403642d203140d021380d103240d10014511410080d07940d80089814108441000c40071040754421400341800050460001d4404440d42d12400d14a0560040480805003000c41c201c50b00464640000103038826002440c01c0c122992003462205640c0307a01c091158503013500da81440707070740d000301000c00c014100090040c0a011320405641d007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 156026501 1250 156025251 156025267
    0x3060d020d200a120f031202030a0b0111060610050d0e060405100b150901051308010e010b010e030a1e0204060b030703060303020c011b030e011202130e06040b030a06050c 75
    0x10049031111800d0325003811104502d10803249584012078054812184152080d182c0113019160a00000008103045504030303140003014042c0e40f5400598000d8182035403030b8a441088400105500760301c0d103000450210222240c0e0f003010800c03d00039600a41200503400301c00c1400d45055000c40440140389583d40c0441080103c01d0100c3c5000f0b0f8440e8014040e281901e400e00800c1d5151811807034494400004000c001c040500b00311215224282007081d202d520341415002c0002c0a90310040e06542484111140b0945c107601616038000245c0b078012496084000341503849020b860000c107680500042d4000300d00721180300e020404d20041c00131420340c4c0c483c50143c1c450307002541c6900200362580c5e014420941c05011102c0d410f00d0030710b05840c1010f0700c0310301262001c01c502809402d005402c86c103d84907074030807000c1a948504503841559030b0440040860102203542c407a1801d480345505c0440e11910302801404200c403c0100248294042501c80000901000e404c1d42e091010800000c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 156027751 1250 156026501 156026509
    0x10e0a0c050c0d050403110402040b07030f020c040603141b13090206040911040f0801090201120f060b1b0c03012a03020403020901030b062701140604030501020d0c021b0901060503060d02 82
    0x4420400141d43c0c0a45642c61860300e01f515410040c0c0c014891801800300384050031842c01034820319900361a00c0c004081041206070708044031000015001802d280010081c41000140a07058100c90b208035012a40c01002c07c2d60b000305803482580d400525101141105030890b0481882103000030a80e914080d80c60881d081251046000540d00b6040402c042241c103643d002d14034020002c0b80028843c0d00708550000300001d12002881016607070310303400e000341c0d40038a41c0701101503d080303c00e20350340f40d40704121000e102032281c1850913584560309c803201c01814103005511410342100303c02c450a4010701e0400c9030301903440c00c1240070140d090000201503690281c10345e00841c018103410360355040040c1840303048000b41d43c40154504ca0420110304802146150504481c81141030850000e070000004809100d0f070790020303200f903001191014124001d540100e800f06a81e400322900a903110071a68900601e88034560344c0281c0e2040104016401080110740c0010002d00c01c00d42400254009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 156029001 1250 156027751 156027763
    0xe0f010f02010e010219110304030f0f0501090b0103052d0303010e070212071b0e150906010309081308060f07121a18060103050709050f1203070b042009010e0a0c050c 73
    0x40811125840c401d051b00394010310120107254411024503c3c5c1401c40e242e0204a41c4130754801000e001c0c0303c5d01380400340300c805e601585c10f040c0d0119040c40701c0d503075034182140d07070b1003c06580034400f2044c0c1410038840c00036140d041c95091102c42c007550450303207040121150358a0040608080d4012034000044019080000303042c01c2d803080848880103c4142c20000050100d43c200d00010200081440005260070150701c00c81441243c10303441d10790b10039004030090480500011700d2031740040303882128080c881c0702c40d10540b1526000c4070034580c1d90720041501044242e0f034a2000c1560b03024903124244564101c0c0c89051a034029900440d0320f1031000c540c01100c001e240c0541d4692030700502c2465a070600480c1c1d0041902e24181650a0038440080c00701c0030380a000074030505900c078801c00c0b03200c0c0500603502a150060020f280600e020701380344507005506414000c8001c41c10ba00200300d0301c0c10141c0503042e560072181000712661600c003550000c0c0040310f816003c2c41414422906185810041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 156030251 1250 156029001 156029017
    0xf040203031315090603050903030402120705060406080a0e0c090a02090406050a0e190e0c011209060608030a0806090c070308190501140f030309030a02060d1b03090b070e0f010f02010e0102 83
    0x81c3c201c040000038001480754a02d07400450030142007206014060b0000011341303070480d804482c001072125a2144580c6000c540b80d2020b5040000403800091160300b0454107031055100d41d10900000070030107502c617160027590300a550700500000c041400d41c109540540842c0d2005000000c20a803074500003180720350154841c90380a00da403010844191400c5040144500d0b558906001d4a054104019102c40740c1d020168104521810380d8406080c881d045006100d4100c90100122500c034840305440707030701c00044040801e032410302068190a1024603540f084065204040c180402c0d9601294840c40140680f4107280c2540c808551b42a014070078a4005c10124859114441d042d4043c40b88007940c41c5409880307508140900b1019031404140340c4030712941211030755a5007030003a43d10030041a0300c41100541d25280c541d25800b594242d4007184080e0b0003108401143da44402c4105ca403080c80ca140c40ba0001c1d0600c00c422015401600c0c0c40584000303078000172444510501e54a402c9800c2032007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 156031501 1250 156030251 156030269
    0x2150307080c1806120703360303020f0705160605180f010e04051006030b06090a210f05010b09061c0204020c0a0b0901050103020a15020c0f150a09090f0c080f0402030313 75
    0x28401b903640c16100311003506081c2548440854000000c0c1c1c015030481c41001129402e1603050482010320984c103c56a09295405483e02c0e8805414250b41c1c6001072440c01c00c14440810740803c54a0140c4281c2c0d04c000c1c1140c402c0b0ac4108850380c103112009414084950500080582e07a110540e194004c0301d114400b05000c00301c02a1502c1401002e464071154641e004480c20801c00c0c02c0c40d1991a007101c1640c84490f0f144040c650042d4050f0302e0920310b01c00260001150306415404c03c50190003a000800d030858448940d43c50310320802958640d90740142588150384901c6030300500301038001d0400c007402c10302a2080c0851a40350141391040403200d5121703d0b5034071001481180b4188031580c01806c0b100784070700750130016054043c3d0740301041144544a02c0340000c01098503a0380a0003224610010074040d03445244240c13000d81440242e01858003414200003400510350603511411000d2401a91065240e449610740c0324a04940035000b0f9800d800b00301b026480441c01c0d8400ca80040080360 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 156032751 1250 156031501 156031537
    0x2030a050a06060908031602031e010905010c030203010506180307091a090a022d1902010f06140a05010507020a0b0f030a0c1e0e12070602070302150307080c1806 71
    0x7214060031107070305410a8042c00000c54051116500005c280e9031885103a48441e00b180c0c01e2800002e140460114201d8455a1880541c40c22280190410304507103114000910024070030840507800c1c1d0000340269034100500348030003000404035a0718003c0e05c4801800b55401c1a40300d0010600752121000420720250f01d1101010b0141010b0051640c030018404003107041a0b110802c0000c0510300040e842402c0d940b18502c4080d0011200442e5060010074003201c00b85a0081c030041d001c1c18000b9401c4182c0c0e840d10f00000b520058480c101d1040010060407070018078100310064419400060081e038122044c190003044134203c4000600a00f004040d00d25100c2c5400c001c404140e402454172403080084043c040040c1000540c44501c071180c950410311610f1042001042160030b0b1150650060300c28000d00048898010500340c081d03a000359000300c0082058034000c00584001e0390400001144100000c80c58504c05019003043c40800c100ca140e141038440000d4032a412452205124108003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 156034001 1250 156032751 156032761
    0x60e010b072f06030405030c060f0f071403181006030503070c060c050307110429280e070c051605130513030518040509070e0907080601050d0c0902030a05 68
    0x1542d55808107108111521540320414041c41c0c5034041241280c040c140c04404501000b1040c800d17a465501104220396852a18880c43d0408050a0311529000d0801e440411215881100a0050124000000391443d01c542c42059158140c1a10540759800394440d03280baa00c00b5070040c0ba0045004400460700d4004505046034135030560f501a4040c05150000b06002402c08400d4900c05500300c2200c82018801700c0c00b29000e00301c0f00c1c15152640a03d400403280c0c8103102503803240c41a00503501100503c411031005180151481e070380c54085c1421040422004003031090160340b0106c1481c0000c0b00785003d80e10145012400c16070560003540400e000e010a003454001403481c4150090103000d5810100c0841610090b00a006001c10174006210070100614030440d003001003000e0803c001a1070070018050b2103801070301901c2010090080410b86100d40055000c00746e842407006010181d10382030801c00d4503102880110348182a1001c0001d605a191018600c02e60b038005003c42e0b94a00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 156035251 1250 156034001 156034013
    0x6011205060c040f060309030309020d060903111609050405240603010c1e0c0c080f070e0f070f05030a110a02010902030115060e0405061302030106051209120f030703060e010b07 78
    0x80104075002c9000180b200f007051900e03800c40381045131424200003a400302941811070203400720034070103504030064403c000e04204142e44034202c16402a03590510071390009801d80d4440c4842000714014150040043c03100401c507a01c8643c025100703100300e400b2403850f10400600d000814218410b5040860100149070800707008081419400349410310301256205200000564200d8190307040100b03610168042120001806010704031501c200c90100c035001111583e141498040c40041e040391074045440b002450307102c14010b00e81a20b0341d0030035005107003007200c00340c10040024443c5a21141056108403401009190403041c9074004122803134103006050948a10144810350306101c04003c10110b580842041c1c00c181c02101d0105983c1c0301c480000303941d503034020408910715100100020b80c0d01d400000800100d0300c1c90f54100c440b5607490507000c2d2200038040901e444c14034108902c1c41521044002190b00003090304001030085d444070045448000c00341c00444004c030300040d6040078482 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 156036501 1250 156035251 156035263
    0x7020405061201090b100e04030917010905070f0303031805030910031119023c070305071401080a021306030207051e1e061014060f030f010f050f030a02011d0306011205 74
    0x1f89210001d042640e00103081c06002d03c9040040030440011403d804820b4010b001c0094103c1d04903810141c6804902c0398001031132004801003480e00c0080050a1100c5411071282d98200f006181400514011b00a885000d07120301c0081690311481d880225a0300d0340984540d00c400009011240c84241d0081d14050031000c2d5214101c4c11101c0c070030350820410050101c07522400102203454070031241c4003850428640c100a0035030240d80d102145042d00c81254076200c02c000d90781c0301159100d00d05224101d20501c514110107454180082c0121402a001442507a02c40c0b01196514201d0780c01050103840300000440b4640c0080030650514106580c0d445684220a0007a00440c144100025010304192091924204011501c04079541c0c4100946509590240c0d40903a207107440c031400841900e0034010a540d03c011800003051505081c0082030005402030010b080700c1009400648940342d00400c0b0202c003100300f40000381c030707034406200b030074002c010f220380751142d030107151230083d007880 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 156037751 1250 156036501 156036509
    0x506030a1a180c1f120938010522020c0106081612020f120607020a03030c05091305150301020a0201020d0c0c020306011a16030c02120601060507020405061201090b10 73
    0x180c09071001a410b030703407000b40c04001c900c04a044060304e441d030300d1419103019480c805501c14144c40d245000e4244450b19030030490701a4048081c4540001600842452140005e0780c1d1989014440c0180700504048244034801c00c0350401c8080b038429001c100009983c0510301d0803041e651900d5003040303560f0041144401001901d0301010b000e5091400c0525a01e240d044003a00c103c19a40b0f100400307071904640c2d41007010118080d50f83e6071a003400069940c103281042100024030702180e403c0854816400d0b5114017500034003101d20641c0c807400c400058040a051141580380482d102c030358566091008000920068001580700c0c031900e450308040380c58103189182400745001108005980201d00300f4150ba40c051075210507545402d045071a41d005801001040c2040d03440014241600410b140041900c2110304030722500b03000e41c030680ca607a402c1c450b50000c15402c0c480b580041ca000d40095621040150006102981011419094426038407003525610190300a0154a80410a46a02074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 156039001 1250 156037751 156037753
    0x607081210150804020609100804140601030b07050c1e07051503040206030c0304050106030c030309090507021b10021c05041809050a02011b0b07050a0f020a0f060506030a1a18 77
    0x21490002c10041980d6400b800d002046800301c002011950b03403000713541c01200f01070440c580400fa034002c094000b40303050760165096019135504080f0003d0009096060301c1d030050200c030164a42040542e02c941003500e00208138081d445110008100902503000d2101810000b0400a4604824080c151612908203010100c0070400c1002680301c1d103040380e4004d089a2181a603965950500328010001034100600c02810810300005050f0301c02c104034141c40d807901d020015900d5002043e81d49029803084202d009503440160b4440e80b811150b108481d41036401554402d401c0c000081c400c0a02d140000e070003140c4007280600003a40d2954403550824001403040000c0e0f03d082d00c860fa620880c045d4000c2c100104603001301c000e564408820100568010310200d00c50800140103001500500e45c100c2c0020600d041c0803003d2480098041d02e1183c0000d44182c1800460b10b43d040070b030100034a0359030181300e06140780c8001540c1d81c99202644620341844002800c009242c0f08411201750481401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 156040251 1250 156039001 156039031
    0xc1806110a0f030504090f0f0b01030207050c0f06130b0309010c0504060221090907020a02030609070b220e01030302030a14090127150e0405090f0a08090f06070812 72
    0x204a40008804407030582108085070070b4480c526080743c0501c120f802500c0c056060803900c61901001c0c4e00024a000d886101c1800b60310010b0004404900581b1b501a1040c1e00401c08240e05083c06101130030700e05405070040d071070000030100601180d01c10381d1240c0b1b000b40d0f0010802c140a0004e100341e10a118062070664603203450120b0003980c4400c034070b410069132845083c500490354658800c0b0340700014054803000081c5004c00010f515101d05031000d0340640034042c00a02c81d580d0204035941500d4000380da15090070598641922442031814036461030814151020800740d482c001464000c512035801142d13141d03403a2900030a40980d40304242040c0d42d040c81a01c003a603030090109140e0020b07141606440c0c030b2600d89081d000200e04d03030148014102c10400006030710b6000e54400082401618240541e4440b011100da03550400300036042160041106100041c0560300102412003000704600a110414000190726600030041114400d03400a92400c01c11504601d0344e510040515032022 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 156041501 1250 156040251 156040277
    0x14040512072301140403050909090c2209020d0b01031a0609011202010c0b01090e060903210702150703050403171902090409150204030525050d050f010c1806 69
    0x190780b40b5080c016400489100201d224101801d602100603540341a00c1c0800a08150801034220f511801c02c0c5801464060000754031100d002640d10384018014101030341821203801c40e959250215450b40490b43d40700d03114074001da0790b0000d4043c84103001e00340d80030700c41d40b540c5402050740000d4812158008648810440c099071080001c0c0d04407003516105100c40e98851004035480c50114000503d0400c81100206005000b036001703411080100045600b180c844d800803035600d018403414807034805840b445000b605200e20a0294200e881801162001d80c9044035140d42c10000b22075000000ba5035004000600d54016400101c41d00317202e001b000b0701d0400240c00c03000741c00c1041120038255000206841c40351181e44c00034440a0f00181150003d424401120380a5030040c403043c0c40b5172041103803010046000241370b0031080c041e00c4142801c9441c21050182d454404202030f6040c0c019111450407a00b401c0c060005620100e0b034802e0808190310301451300d01061a00600100141c02035081 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 156042751 1250 156041501 156041513
    0x61e0709060e030f07090b0a0602030403020f061308011a040b0108060f101418040509030a0c021c020612010503011805030d0222081b01110606010e0f041404051207 72
    0x1d075025440c0000c90440300a0200c1d203030007450041401c0714800c14000103180310580d400b00300d962500300c0307024000e15a01c0c1412a0f4130701403804042e5200604002040c070034a0700c00c00400083c0e041e0140300784ea003a958440c017400c40d04001c04661034001501d5081c0000e05d002d01c20041c1801c2c003424160b03000c0c206000411801e11a4054660098100406106019009401c8103203001c00190074180c1c3c43d1001401c18245a03440b00700c8602550500010a0a0390000f0056070148005d0f9034070090303000a5a001c02c004245200009030510046400040241c0c4420004000c4001c002030840b21651402092508464012144d151124100d142d00070001c0c0010040754140d10500d01c01607114031041a0000c180c6000301d284554190b23a1032000111043c1c08224460f01404180202030100002d4005407041c81e20700707501c20099044480091060b40c0144c4031104424406400540020f0602d40030a045815804103451300c01c0160080000300b190800c0311401d81503001e104281051050ba40d10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 156044001 1250 156042751 156042767
    0x3060b0c190501020c010603030e120105011a0f0f03010306050f06031b040e0708030c0a0507090c050702041a0909150a09020d0210020a02220e0c010207150309050d02061e07 76
    0x105203801c141c008036081c00025010364003a100a20020084542c1c0e0345005420321492013040c50084c241c84140342422281842103504a801c0c15040304003440c864020702c940340d8484944c070707807600c8810f0080c48030248420380514080c0d48181000602424542030090710640010f02c036078429801a101022122a00404034085120a84012480300a0100c9150500e445600701c3c41c0741348030101c1ca490704a5400070f80302c001c05020340162141e494503012440207030b1303030424103c10100e1020040035005040075406949040c800903900000c03102c008001074000c510554130035035194809040c403103c3e0b100c1c806c0c20b01e8200603142c0081004031321590109000703014180d40607108003860f20760800c025000703000340190150b004052540c1000d80040751030103410f806c02c0c0078803114038040ba40c15428200103881c810f007e0050300100301c001c3c070b00700c105400c514a420600c402c042d100c1018800044040000100003100c98000d4840d51921403060007040307215510000003c1541414019165040b4000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 156045251 1250 156044001 156044023
    0xa03030f050c070504051e130809010503090f01050412091d0c03040503070803040501150501050901080c0d0b270717060d03030e0a0b150402040b0319090c030b0703060b0c 75
    0x800d640b280c1c42c0c020000e05190725a408550454141400c0081c0d000d5601b11580c184054860f40e05510340b100e2419059246040070000c1200760100010f420a42c0101c0155502007401c0e000c4491009002a8850a50358161406c072138125140040310545a000715000c0301a0200e10214030410140d01f000c1d640292018054001c83c50b000400708040c000d0a008883c0900d800880c0b1a50300c1c142450036900814590450040c5008200c3c40842c544d8440c0c0221844114140c2d00d800250303c510b0881042a480000041c0c0865900e2134003005684944058420304005103048a0030340c55410001650303400020003c9e803c222084440d00c0086004041050b00103809035036039002d800040c54103400411444a085c4480e101e526100d03010000d41c030041500c40c0c1c0f4081c1d58088806020014802640103c0c0258000400302780000380140750350100000c00303c508554042404202901c40315801c4405400588903400110208443c1d207409d801118002c10040600714644403d100c080e1340c4a11306511 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 156046501 1250 156045251 156045257
    0xd05030408091c0f020307060807080a0507031b090906050306011d0718140f030c0a05010c050c040606020304170714040b0406150c030314012d0f170c0a03030f 70
    0x20b100d11554a54410142d5040c0f5400109202c004003414800c0000310745900c00c910a1151201c00710341140f007659510700620701030700d0760000b0340c0b2510303d5003015003402050241099512040403800e8681624900d4040702c1700d4407903100f298204284041034403003a80101c1d00030b50001004202420203000c52030314003c5038140350780c440d803256042140d005012403650240140c1e0360402148090028411184115085a03541040d00561040c1511002003007441580480140d50402095000302040e5000034030507000e40d10303000c0d4107a00203000c440741d503044000103900101d0203019140c0115030b0220784020100080104502d030088542c0d40e100c154054600a80d102c215054040c1c41c0c507000f04014000011069000c00c012000c000e160050001d8150700203400c2c0300060049424000305103050300c20641c0744403000261130110008007881c030390307080c112104107020005801c009400b80c9030103401c22009500b402030562100a103880000d00d40c4a00c1820441e03c1000000d40158150fa58080182 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 156047751 1250 156046501 156046507
    0x303040b0709090507090602100c05032403030708030708090303040f060b01110f010203060a062f0f0609011e1a010827010c03150b0403021905030109050d110d05030408 74
    0x918102c5000c41d40c2da101d224400c0c01d06040c00501c6822055090070b80b1002d80c200e800114544000f00141e5022003800008120b08001280c220040c6095142e0906002c09000001d81d90b02c1c00440d00d149d02c061b81c1940c180b407012044c450754a5100407220b81000c0e0440086045003007513210424032008040c5c004001c0c1d5138a4100a0035640540011120480190700f42c42c0e03035091102d01030b4040d40c03040359400e20401117160003196550140c0100c03002c840000900e2010411001046918180c845512942c41e101d01e41c130603a00c0c5d0310100107841c80b50340f08a0010070000320b130010704035036400350240e1080a00d0a046958110585100125841000928222259071188085900d00816600c01c00380c42c0d12603050380509409054008c0c02284440d0b03a02001803000c3c101510440b044580a174546401e000c02c010005440c0c007440c15180e00401e2521070521607507038030009085501d0200111070326000a04e18008194002001e020300d048000041c01680c0108000100a4070000b031000f4082c0c4004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 156049001 1250 156047751 156047761
    0xf090632040c0905030a0b010e0c07170c010b090a020702040b040b03100c1202070605011503202107020c030c0910170a120908160e0103080702040f020301151e020303040b 75
    0x1000f98000901c1c0c00b9003942c401450038140310f082d5040901030502c80d0048a800b04002800b40c8049404958004c0c1802c145520300c40c1c007a0b8030f56808002c4142c95517480e6079112030326036070f900c102d18020050140d005a03070300420300c180001d0720810001d96100340c0c90448407540c10b850100b80d90100001c5040000b0701c580381e102042d642d404000e142030001a1011039444c08102c040d501080c180c03491070305840c1040c0d0211808601340d6031811080a210007201060980012242001d040c000c0c1341c0c80444528411007103c003103c0e918003101c4480069010556001c842c1c24184045080000c050f43c01301001e14240181165402952040f00c070307084400340340c800c0045018004681c0e842e1b0b1012040c0c01d0b0301407801c0d00030803584030381c05400d41e6401006d4214080390700002d004000c0341c9040d040d9a40c66881c0d52141031658021460680e08140c0b40c0c004084880d00d02e10083d4041c100b040c00001e12107008540003000c0117805d0071440020008150401001c3e50000143ca83c4241d000003245002e03550 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 156050251 1250 156049001 156049007
    0x70b01090209132c1506060a1713050a03030902040c03090209160e0a06030501051320091c03091406120105090414010903081902031501030b0105040f090632040c 71
    0x104414140701c180804540301c03441a005c0f500851082c0c400c0071190300c5481c0c0300c007080030714031414010781d02043c0c10340c00c464540340d05103510540c0001201c54581c6031001c2900da150600844903011400a0303039416040003140b03818401c585619849107000c00c031202d040c1e40810315001d0003401158445015400c801c0c0154480d149141c040030010309481c070401da80b100007401800003800346510400c8002070008034003845100e40300018200c00a4140e00321001854810154060f0b0f81c403c0d0086c1c24000107503003420340c620710000003078801d035543e07400b0920700460004038503a04034010744907810800900c5408008460207030305580d0126501103641c2c0f1649001c0d040440420035240f00d5500301002401419001039070b8503c40c501a0001d1050881d081c0418012480200d4004561021401d080840c82d440f984c000d15000300181040e41c50b10380c4413108500d00341c00c540e0001c0781e103a450700700a10000d0030349060100d02e854141600c4042c5114640282550300c11014840e00655881e019551507a01c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 156051501 1250 156050251 156050291
    0xc210f020c0309030c090903070615030609050c0103060803070317181b0319120c0302030d06180606050301030f150902060f030f010f080a0303050901021e070b0109020913 75
    0x1145a004550300c0a6450715a602c0ea0000010b4604c82e0041066940c414200f040001c0c3c41400c0441c091031a000341b40e510f000c0180084001032001101454000c80015801e00c602c0403030703a0140005001c045104c030001800d41e003643e04101100d42090000e840003035007101c2520301d440d00640d80c001090369041000c180790070324920000d545208120400290f03150465800701c044106800f561210781d0001180440070308804001054240080300301840d003441340d080300898921a1042d40d1604072080c0c040e10a488180e000340300484407100380890422118808d0000400c400e00304642150b1440d1500c4080b81246070300a0302c515110305503440d103504980c1c00b0300f03d000d43c002d0103183c942449401c1211181c004858004000d003c81c800801e0340840701b4010b41c01c590b880c2004090140840c2d4080340030300800f0300007080310740d0240704104560f000004d0400d44100038603002e80d214101e0b400d24100c03010040e401154014070412680c174054a4500642114041800b008582c2c20342c02d02e03581020b56 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 156052751 1250 156051501 156051521
    0x160503071d0604090f1202121204020907120c02070501080609041218150503040b0a091502090301020c011407021b1509010509031e01110309030d0e150403020105190c21 74
    0x2181c5d4840f014204500d860090340d507a202507017112000403418001006030300c036003120072201c60411000100180b07821500740e64000c01601d0034888506544d04000c0958284c01004d0000d84c20001041c011568481c034081d611030400c0360400780905094850140c900c5c10080180b04001d05040b01c0d15a1141005450000b0200c0b035804004842c40804024003682054504031032040b00c03c0046144100c2a01440040540003e0900850800c1018400095125410321909550240038140b1849000e21070a64a180c600c00121044d191600001342005004280500c0c3c51170030342d101d031251752500134078000c2c11030780c4000440d91411413900681c0c890082800300c80c2d140c450310010b000d0040103680b081c1f078425804d40090003041c101c514034001034041140e04000a51003131242d45001841508251000c5c03a03028150b51040f04540c9030840300c1c43c400c45060740903030b44940900c403d40e004101c0324051900211010030201804400050800000548074240101d9001019001105d0b80d4031465640b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 156054001 1250 156052751 156052763
    0x7170901050f061e3007150207080d08070c080c0c01140708090d020a0f0b091f0f1d0303040305010f14061c0302030912160503071d060409 61
    0x61604014180c040c1c00c1c12111107003603910b400003141d0a42880c2c1d182c0c2e0700310004103070103d801281290034040b5120041e0f07107a07400c031203d555060444003e02c5c25208540701d803c6000d4401380b0b04105030145c030300c081d0140c1d81003194000300d0200800ca001042501e044a568a408040c1ea01c0c0c1c060200c0b45000400005810070000240b180720b12040000c070b41103128421788419a450882540c051454042d1000141850008004030100c80c6004d40b01644003a2009140f940e580d40c9a8030004025180b680150303902c40000900c0d00c07894500000320141995402c0301c080310381d0390403140c010603110103041c00c801404000035952410340c281c1d4404072505e2001404503070300c64bc2e6a05289000c2d0690050b15034080b0f2500e0b0082d2030710813100068500c2a17801400001e502c2d01401c10303411102000c1e10064045000601a9074215541d0484445403455000002c05501304003441b07041c40d81c00e81c1d0340000d10991110008122003865008111040031012030099401e07600c40c0045030241c011a1720007001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 156055251 1250 156054001 156054047
    0x206090a090b0a1517040f080403123002030a0e0105070507021e060301060f020106050a031a09010902090a0f090503030a02070b0906070c020d02060d05010b04090b0105090a03020907 80
    0x18680740d610001c403010080300c51064159a810107100a00c944000070300000b0040d403030740035000722031550f4140c100d403091150031109004c0307841b802d080e50400d800c1124425011f0300c100700c0881c0d005200314038202c6060029403a517050310b07003605d0602d81c1c91000a1082500400000c84141581e8412100b82080700024805450040b00091541e0701101c002ca01c03c8000d81c8210328130240c485004551800c000e041c15166900b004000d03240b0040100d4034400710764071400c000c41d454940b4502c00000314420075060104c1e0350740d00030181444000502c60303041a89015106800b43c2e840e1007110b50491410100043d1070300206510340003800c0200800307801448000148059a1031940c0204001703401030700385130040e4503000d0441d0b480306010750309030b400110079200e050058944944080e01e1184010b1100e440c1840c8168080182c80342640421070b56100490108850541c1c3d02940752081c001b440d00c0e61504000381c0001c0e009140d82c0c000a80105000c2c0c0c00a0300c0b15000e6001d0146100c1d500e49184c01c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 156056501 1250 156055251 156055259
    0x30905011d011505150c030d0e03251106090d0f1101080612060a1119030b0f01170117070305250e06061b01060504060b0705010c05190c0206090a 64
    0x19010002200c8400158a000503d20f07070741d03021a0026080d1000103000c80354041c002c5080110581046001801d680002c01c041058801c041c8114050721031554059511082c504540c900c903031349a1040c01585441e8403600303400140c846481c43c00e10440803101c098075480313540086030001c000000000d1803e207100710f0540510031640900e120306802680c4120669a80c1d03024002c070742c4012604080c45900c500042201000b1a130000385000003506226800c000d610311503440028400d0b00044d010a03950030740d1890070300b000a0512001c80d03003800e24071080d00764009642e060100510510740300c04d1001c81202c01204090040100540c1c02c4030031186d5104940c1e40d8000e081a40001c1806568402c180c0051070742142d042e0b551040344020030300c0d07040010000e4103202c40495800d51803d40e5603100408111592203200e40b10180a807102801d4449416140403802c480040c0810000c1c0901072140382c1c2c8411100b4180c030b00500407468180710000303c40c80480d0350b078090f0705003103070303000403140700100d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 156057751 1250 156056501 156056531
    0x90f1f050406090911180403030b060717031b030c180307080a1407050a120305090a03050f0a060b030102070f030f0201021c0e011404050705010f0212030c0a09080c030a0201080703090501 82
    0x4c000380740100ca00000c100a80020080207490041c0422000c0b0210300000d00843e010340c0c048401d10101030521490035180b41d40300348485090010300d40c0307445400320a1128103007583c5105c1c0402464100d02914500704100b84540a0050300e1000c2c07561002c04000c40617988041c40484000c1c01a8402c80304000500c0ca080c0003400500102243c071403040d10300006007450b244413803104440c3e0560200c2c0c6030440c03686003203501342d1040106a4025083d180300200182d010403801503210384038009403080040c01d117081807d0b205d9488440f4031030b078014409500401d900040e110f1280c1da040c10a0702680341c00a00c10b9019000d0100d02030400c8501c081c0c1c40c0742c03900c555080400041081402000f0720500011140e10040d400d4034054030541c012007050150354050184026100200e00445d01d03039030402e0f4007160181d4821a40940f0070140440c0500e201900f0100c41e8028000b0f041c098890f81e5062000310303960b01071101e006030400c190032022aa141e4000d80c001c0044c0740d0014001c0c095030440007504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 156059001 1250 156057751 156057761
    0xb060609061b060108100b010503070c21020c0109140a060c030908030304030201090b060904200f0904060f1407020607080a021b06040b01090207020312070302030f030907050f090f1f05040609 84
    0x5d44024040c0e541c03500c1d501d207424814a151154140c60321803d607102d50f0411a6150000c00003155044500c4a0300c10300303c038140d034000d0b200150f640d005245007a41c0100040030031410f940500100d0101d44040711003a55064a81030a880003440e01207801040b07800d0445240080ea84600d13283d000c000248001c1c103506411103051540151780035103c91311072005010b18404122400340000420b100da021561520011510849070000e101c100400341440c001203094a05440489905640720700d140b0795080240910030102d82d100c0c404040515260101945503007000300200304111090001500c01c0b01140d040d14814000070188201101618081942d1140c040e90140d0780c00c800000002070412150084529032540600500700c40b5080104000c102e412151b8201d00354001440102050381205001c0c0d03210742032007030081441c24600360620070848131440109001d0300400041080c02c400c100d91040c0c00c1b00b5000b03240e9803845512024a64428020f4018070781c401d080a20000d1540b441b038103e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 156060251 1250 156059001 156059009
    0x8070305120408060411040b0406061d040204050d08090118171018080309071d0106030e0a030f1d09070504050a05040c270306060906031b030b060609061b0601 70
    0x480d8100c0d4a015129651030045210f40f42007584410005000100482d0240b9202403001e400403400320f00e40d500003002d40c0c1c05070f0458400a800c1d100381d04080713950349410a140c6902600c046190a0514002ca640c440500034040e0040c0c1000502c480305900c00c440c0c10510724901c14074201c00d90f84030b240f902042d54999a11b40c0c0706200c0c0101210f0390401c20b1003200280b00940c809068030185e507545144807504001c281c103ea501a00740300080991460501145c0f41c40c01d04601d038010340c10700601030102c80d11b0b4082258194051000c80b0000b0750410800001c44600e82010703500c201d4040c054408a43d400c5840d41d170041018002e0140440d0000e000d4807d03180201e813000d600b0350320b4a0500048070706003114540051042c0410780b5003a5184891100c22041d9211407103102516a100c440641e801640003524480e9149403c10502100c0c0c0014051900900d42006a080c6152140e45280c603000e000036100f00400203200a0039501d50049038071442100c0901c4403024166414070740c8030b9009103d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 156061501 1250 156060251 156060253
    0x6040509010e03160606090203010b13090c1d0303070f03030501090e030702030a140a0f080406200601150309021201050402120d0f0e150706050601090b090a0308030c040e0108070305 80
    0x808141248810302600381145400402035041554402159213001003014090355015551000441e0024241c0000c501a00211040540d140001004c00064505552128880d02e03d803102d240c030450b500c000c500c0356443e1002c2510307010411400c002421442a800000c2c900704880900c1e104041c0c00d40c11841c12a41108002c100007040d0101e03003601d91240d2180258190400399140e80001d2104210704140310301c3e401201e0310010744e6a01c0a0307401c143c0401c02d95007510081000c2041982c8502410552514200f5000f20325040c0c0403851f91350001802820409030110700c0310403100740721390311820900ea0020504091f582d10005003600030502a80c2c10382c007903c13607042c2200c2c01040009010700c280500395a440d0744484010011240c040035042d2442d80f0107a04a40f096604440101924086000701c0c0001a641405000034042c2d00d5130782c0c0701d1880341e01d0511003500380d03544d01412002203a80081d45176603203079190041c0004a206940180c044126494004214100002040d01c143d0384208 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 156062751 1250 156061501 156061511
    0x60f272112030b0d0209040501060b0a1701090b01020a1119090e0f120a08041a040302010b09060109141509031203070216030209010b0a020106030803160e04061214240604 75
    0x250110181d60340010f92640098207040d4610050500442599005025000000d01e60713031610b45d04003099001d8810301e800241680c00600b440741d00341103564014201801d08201d04a00200040e40314164004050400349146804005544642c00201d03018240044180340ca6a100c08032a4024414221003c24a200d030158060083e40d00080284ea8209400e40c03981c2440090301040f80c0c03003200180202c4641d6651624140080d1440c0341050140b8800e400228481c858841444100400202070604100994904002103420044203e254510a0391408060035454000000e40d20501741e04035054414000721117050000600650300502e210b80c203850340b00c2c4042d180d460401e6698080079501c01001001003103518074100050442030254000031030700c00e50782e4451402075003003100c04006030f000c070768045a6031541c8159a11805101110208000e0b41804a24a11203056982c0101094100350512050b001d04211810613444d44841d0614001c4045540401d00481a035146000714140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 156064001 1250 156062751 156062783
    0x2010b03010c0c0b0c0c0109030c2001091a07020d1109010905040b01060c03021905010501050a0504090c09020703050705060412120e060601030510030c140109060f2721 74
    0x10b01400350300c0d00641e541c2c90100300c0e507601d810381281c00262014210071020419641d5100c02030150590240c003c1e01e48614200c03050902074003907049000a107508445002c518070307003030382c000c116501500e40ca8083c0580c0c800a1100300c514510035110065400661403c0a0302009290820f00c800f40720140d03692491a640c0e60000000e5a0041d83d0082460445500610220f44500d40881d1078078000c0c41142c0c113201d095188600c5e601d02d80d24003034131141d4480005002a051003403041e001460240c0e81002044400c1d1601e800781072243c040c0400b02900011321800b4184180c0940320055000029180380c1d00f8140f91500020704103a1003c00801d018211072b22000d41d05108a0f400b0034526800780449560310b10045000b08001018006100450309005c004a0060f105039800f0340741c00d074440d04020521000242900040303034000400c004c00e80141136410350703102c5210a0809040c04104401d1581c0340101500a020342c2c01180b01107001c1c1e04d00c68210081400c103144420f00504090b080a011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 156065251 1250 156064001 156064003
    0x212070f080708030702040b151c0b060a0909090201020f07080706080c04030b0708100801020703020f0111040f06050a0c15150b030c1204050a08160308010602010b13020a1101060f0602010b03 84
    0x2c54440c01e0950340043c4100005800e00c0c2d0490341e0051f50040c00301c0c03000c034440c0035810703690b40208141d00d69a856130401001d80796454440e040f24a8001c42e07195007011514a80248014054011480c98503120f500100440e40200301d040400103840c0140da0035103403101300d41d03a40c0b44c48600c81d0100040c440808108000340344000c8600f40c1350483c01041c40c1e99120001074518200242c0030050320602814002290701c001e20113000194840d50181c8541c5004c00505801d45c1c0c150040070610440c100405c11208101c403841c002121550305000d51100000701e0700340c50a440c030080c042c0c00002090021310f01904240d11000c007200e04041d0407a5115103881020388113000032101001000c4c82008171038541d2154840b502d40c0705202d5821110404415542c408044c1c220b503010320024540752184401b01900018250b0142103180300810514a41d000084c51140c00d50480006080e07000400c0c0000c00d00c41c0d4410048050f49000a001c0d40703548106041c1e011902c0e204241c01546000302c03482003494 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 156066501 1250 156065251 156065263
    0x80f0f0f0324010c031803050106140f18070c1a04061e060305030a1101090804080606090a020c0309060d0b0301060b030601120b09340c1101020319050c01090212070f08 74
    0x806070358804052a04c4e9400351010312224140c3d00342d91020400000004909016404c00703400700d01040703e0012407000034442400c0218261a1280c64100e03a541c0e620a00c4114590380310080d441c1041030722800d8100030308102403000230032284010030340070002441100e82210030407040d6001803c01d00d500e903014940440340f80f07003c014600c1d0001c10141a106104150030a55809000e0000405800640c1e84200a0b48141d100d1403180c1c03c06800c104241c5002711046502417040c850a40c5004c4104a105481344a046c102c07620a41340851000805450350b1b004042d144000790003000015118529003c86810888800c0e000480480c4c00d20300c0d03070343c90f805030403900000a480d1203055121100120070391140400c0300c0c5034070611210000d14016800401101140c841d44030a220500c0038203101d41200d0000c6411415507008000900101102c00e00214406030241f03815038131280340c16101401340400c0e10001c3d41c48000c0c102400030b440e801040c0321084801021413004d005544882e01f54640f2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 156067751 1250 156066501 156066571
    0x5030c01020618030c010504060e250b0a030b03190605090f0a0206071b06081012030804060f06050d0b060901080a05030307050a050910020c012307080f0f0f03 70
    0x70300040c0215400d4648490b640400a0003c020f5030304091044402e9800c42c3c1c8200e8042d07400079140ca21400c80078206200666648000500c0d6014581445100740c0c0100c0c014130a81c4e030003510000c0c03940d80c450b10962000c0c0507042c00070150754aa403006c8619400c185200c400949165241c8804550800c41c0007484400f41483c6038003a01c2058200c1c0c08111942c0c20641302900e010541d03581c240141640b01c8807404c049e203400c2c1c0756000d441c105940350030113017021030700310032a2030518248030800309070010f403402e80c06a44038801040c2d245088103c44040c025a034011a00860030540702ca04101040c20f00d980314160686115071140c0c1d85800b040e07550035071440d015045030000c00c0842c03259486031004003140c403100d05101c0e180016444c0422100b0007041030103401a0062740b0a40d440f0740e484000440d50242c0c0300d0301403904028807420b5a01611400c200244005070009141641c04540700582e80449904140d0684410903900d0649840d4001c07555480e00b06014103800c60b10300880c401d4801a8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 156069001 1250 156067751 156067753
    0x8091b030c01080a11040e15060304080d050405010906110a1205060904291608070e1e0418031e0207140d020f03070303110106170a0f020a18050403080105030c0102 72
    0x41c1403160054030980c202a082040c01916200007180414590008000403c1c00d0a14060185002007130380c030a019500e8400b0303119501c10024000460000da0030744403c00c0c0707040c80c00070712900e95103409401440d910400800da1400c2c00c4603542d4841c0258060701a0080d140c480b007200741900400b0000319a42161241e60000040010801113980ca1003011038248408202031700590148002d0b2083d00e10442e810710305101d00301c2001e01542e03844500d403a04081d45082009035184860b00080d40e003030145001114043c88007061701d2296a44e5007000c00ca160301c025051100e05402e040c020484418950500034403040941e00d00c0c8407910001d42e81003110701032200c0e1710f420300844040000109020405990221a103482d95219a80034060b100c02948242c90300d41b605248140e9040c02d40c3d98170b500042c03500060000ca03c40c01032000c15121400da40c00804241800301c14030018907500e02c80d811106000c03400c4d00f0209040e400700da2200d80190301030707190155582e9a59007051303038402040c1405401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 156070251 1250 156069001 156069013
    0xc06040303180b0907090c0e090708070203070b0c070c0503070b0906160204020d05190b150a1e0302040501140f070b101805100807030c031113060608091b03 69
    0x2081c031a900c8541c601c01c804018038400c500300c0d00d80000c10281076624005940110307908110000f0140305184a00b80c0b68200521070400340783c00640c20360b40083c24a000e01003000001090f06200f4000c03580c405a1128440d403d07820b040e4000d240a400c06070040700d003180d0303200021605280014a0008880001c111545440007202c00e00005804c101e8805401c0d00d8440440300040e03850740081d21040d40c40c0c07840080c0501c0c2002205400b200581c4104183c103283c1a52862940c50780f03500562101c200130040d9584a80441007100ca81101030703e030002d2000740b801e20f04c140d15810f4004204441c800d0ba02d002c0504140c1d5a03005451017000c080710001ca40c10407800c0e000840050141d5406080754445a41441e0344111801e0901128525080041d54810070042c13584480070f000b5002d8910400282641800d564502d900c00011340000b0784042c804803c20032441d5204c0a02440030a1541e00510845a440304094186807040d21041464044c4015003911302c1c10000001101c21002002440c4e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 156071501 1250 156070251 156070253
    0xf09050606090c0406050c070f09050609010b0a0903200904080712030203010501090618050402040902041a070302060c1803070902071a0c0d02070203070906080f070b030708010303270602010b030c060c0604 90
    0x6402d5000d4041c038001401060000074109c5020070102c0003c1c07454100126076850003404102050318143c01c0700c10940800c0c40b140c245607900040143c25260722802d01140600d10351420300c0080c040745ca030345e54811b003903c0411040020300d001404146220300301e0b03413082035486942038060b400f09029041c00034211200411010b0300c03a4a00307004a01f0050001240240c484000c10103030707449500302c134441d1500010200549941100c0c002c0030710503005149802c0c60b403944e600a4480002404081541d5004545210f500050744540c0c040310714001c0c1140e00c11682d0303040300741c0650005002a511200751740417072012960300458503442503503101ba04602d013880e102e4001c402500003540603a01440b4010001c07401180512600c400707400700348001e10440000142662400e0015045000d01c0001070050101c0c0c29000340100b4196030f45030400164008510602d1580d000d01004114095030b080c8000268058041d401300b00302002c15029a04040602401e008480c4221082c0c41d0141d84903c0010f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 156072751 1250 156071501 156071507
    0x110c0108062e0203090102070b041d100909050a030f0e01080712020c03130f120305030103060b220e07050a0e0a05060a03020d1a0a0513030c050f010f09050606090c0406 74
    0x1c1c0c15080800110b001e085008121500000180030002d800341e800040c40400c03030f41c2c04110300710003030001301905403030181414452003804042c0c044240216882c2008103582c0c82d50400c4001c05480d12007020410b002c0346040040e5100c0c00754006070040b600c0340c1d000a00c424892a03c4158504042c0c40e0749a5036103d40008aa4185c51080c1d0003001070350038070146001d01c10510040c4102c4003046880c0e85500e040c201c00a06a0210ba842010090700313082c06e41c4002600038007a81d0460f07030043c00020381c00c0d0703007040480c42654a1510256242e5200d07a41d40340f03a18040d41c4062071031008181111110341e01c4805001092100d4000c03461540300400018a00069903081a68444406000100e010355640d003c514004540c88048039602c1d850240550210f20340c840c1641c4c0040180410f2001c0d0501d080e50018031140c002d00a010810071444260900030100030070a00074585100810800b6100c0820500508c5162011219401030380c000c2140c40c6081c0100d10b000300c01d0103440c1c40c54146410341c16 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 156074001 1250 156072751 156072769
    0x5041a07020f0d1e05030609011703090a0b18010e01020307020402030603070f03050a03020c011b02060702040b06210637090609050603010c02011a1c060912110c010806 74
    0x2100861181c0c0054841512040c80f00e030728907600755103508404101010509405540c444c04503020020140108215035440a10369411031300202017908003104149119402e601c01c607101035803c9a9648400500021007030010b0042d0b881140085040741c980400445200342d0007003809006070710900400025140c19070082d47c010340002c04480310f05030341d40b6030082c54000321b0740191040d800030000c950074140c0500015040102c00d02e0710b020040412606989007500454000c1d016000205003a421911b07244d200b80040000200015210ac0a20b900c1104405468820100360031580000c5000c40c1088003241811016440028a00d001006510f2682c080e10070f00602c0d02c628882030001c0d000d041482020054200c80720003041500e040000e050030b48d00039000c01e07803c680c50011043e464450f1043e03a281c00010072500c0101d164900e018840110b41d00e0000a4009407401404100304030002c0700c114002c230443c0d01d94052400c0010005a00c47d1907080f00039003c100d004000880c075103000011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 156075251 1250 156074001 156074011
    0x603030906130e15100305070c14010b1f020c010215010b0c0a0b1302090105010f0c060c0203091f090605041503050615070507030201020c0d03050d0506010203090d06060e0a05041a 79
    0x1144603440e40c0e030803c001119400d0310380c40354500d4032214094403414001035407041d41d02e407403d0500a50400c850000e00410b003000000d0b25070120840c4008080c002034108440299005101d5440f503400c601d01d50813404400c001d09030251045080c0d2242e95400840c0e0117580c140b50714200e400e1030303203003040c0040b03503620009600700c1500840f2004800250300b40b0300700e4064032802c822402e21108074410f10a2000c2c1c103801550601901c05680c0c10025400250310b0426503014201190840402606038614042c5418141d8030200014441c44c6014000c1c8800780e000c003141c0d4508100030760b5180151818030550045a41081c0c1003110304001a00a0f04025002000038101c010740015003009400507410103002200c01c0d4106071003c00943d81c0c10844007a01d00012103103042c0381500f640d0041c00c2c40c806c1144107028036440300001465a8000d00944001050141480c24210013514207600200710b1809011000e161560115002e070709d00d03100d1a0712690703210351501ca0300c6280201c444602200204 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 156076501 1250 156075251 156075277
    0x8010c03331a0c162102010311040315060e040302030d0e030702180609090303092107060204030c090501140105040915090e0d030b03010506030a02100327060c03050603030906 77
    0x44508a0ba1450701e034402c1034450040d141c0d108004000c0c00c0c110340c2c90301e560807004548030074452910708000444040c1d0020403400802d074840d10040c0c0142210081121400174046000802d20501d6401c0100000403214100025a00d8111032850100180d401a0042e802401200341004d8a45e03c40d8103140c00010442c0e051100e181e000a00f10f0f03904c00003811078540180c00303018150500000309c0c2d0700400c41c100610709502e0076003d0103503203140501002902ca08011904054803140b981102c08541d008081550354545a06043c4800c0c1038030310500d414549440000a05d202c04012a241c078180140d4035240303468501749604010f40751540f0101c18004e021100040c0c2d4000078400c10a6201c010340103000b10440c1004040d00321800111664001d904003801c101c0190b0703000c6910b1400c0341d8122110340d400c0030300da0412001002e104041800002522001c0c1c031200d484200520b00d0f10b84120707000c3c4001000250304405541041d07640d00e41642c4140044102c03031500c20064040110180 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 156077751 1250 156076501 156076601
    0x4030c080c0319020607082e0915081213171618180804034d0301140a0b030a0f0c030b010b07030c03050306060702040c020708010c03 59
    0x1d00c89a04560080303043c3c0342d842c40320340c060b1206540c05104055003c4410b0404c0c00d02403421198403242d03140d209801d4075244154804000d0f280503400d0150010b807114000400c4454542e5006501c00d003024001c02040e84160769070440030b80b51b01e0080f10a0b02111648890040c0e2030300030105420700c54807111041c1802a0200c4c0060700c4a011010802850072421503030150820400000071a28a80c0c00381c0303192000444080d0100b03860f60120703000c40380d0120b5154100d902000181e40e00d080c940024490003048000340074120b0078000c4090b0100c90b403070096038280503a06c40400d4200e890500c0d9502440a01400140c0c40c0085944480c59102c40902a22198281d560356004140001102215070041ca40001c0c000d100903480c940380502403080c004c07450191951000340c00e0b44078001f402020408004005070880c2c843d00203991046074058024482c102c00144040e4942c0118099800d4661902030803d0a141c480d0061000c600c05440890310b00b80c0800404901c014036036065601084942 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 156079001 1250 156077751 156077767
    0xf0e0a08060405010501060306141507030201140103050c010305060f100e03031902070e0a020a051206040902040504060207110306060a06121b0c1403120f0405010e060a0e10060e04030c08 82
    0x40c031600d8482c0384a0400040e46604000e001380445e003064110145500381000327402055241d02c83c01350710903002c103a440c5840e62094a401c07805000c41ea1042e09032905400c00000400c0000589126006800d88042c4001e40c0c9040c180901c0311403000485911140d481c1c00c504d401070003016260150b49010301507d03c0d0444011b51030040c850241d42600040e031000d102003000304441026140c014400003400d51510441d0080241280a00351b03c111102502c0004540c8654656001800d0554003409c01e000501d01400d0080080d04612001e0302d084081203c0510355140104500303106143c000d00a40d48035003480700490b202e0b410319401c0110b180d61400a54140d0b69441c2e03521344100081d594100400a440c5443d00313a251036a012240380750302c2404588200e5510300b5180d0f621000a0680d010780d99118103105000d084082804001c5000740b00034080c8440458104100da11140070449040580d0103940000f190403510520f00340e0b07400c0d07101240009216111030520180244242400c00f0a1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 156080251 1250 156079001 156079003
    0xb01110607090e010b09031c180b0903010c21020708090603010906050117040c0b0715110a0e0f0904030c03020304081906060e061003020f0c06131407060f0e0a08 71
    0x685075030002c5403a21030200000075010304807501420010368401c1c00c3c03a0701940480c1e038407a15075000380d14000e002d500100b1094410400030380682c004160144400703580d24400307400c50f40000c0c03900d8080c4d401d048503821564040c0b010706900144800449800490308124080290041401120110010003010445590384400346010307001000d030004800e4a80400500600900e0024030700072948081000082501525403400700d4590402c255564a502e180c00e00452410300c500d240d0305890000c02c2002c0c40320710000f41a10316400d4a810700210241800c020032002c1102c400d5034015444000100000d103d280360741c0c0114428012641010b032503130041410805d0a403410340340e10009000240500c0484d020364801003a440c80d01d091103003050b00c00720343c80d204911284800d041d00040d201040798880c00c202c483e0910350310b0507600e090414a8441c0826240814240c0e410389135500003401c3e070040802c4240c21074a0580710410801d20a81b425210640c0c010300715580440445800a25000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 156081501 1250 156080251 156080263
    0xa03030c0c06021b19080405090c040302060c0f06130f08160c0303030506100c1109101d010f080309101209060c050a0f020111040e09010e0d0507120c0b0a0b0111 71
    0x34a26a031aa40641d200d002c10346032542071040c030000411700481c5c00010900c000100c0d010f5030b0b03007911703844a80c0d560660a010107104076071000f9009500000d60003144100412a550320b51050800c1e192942c0351070600e00412044082e018144000c209132800000310741c800104180120300b02c980007441c205459440100145a00a80219031601c003046118a8400209250940c09090080303170780601b0748500e04004101007404d07002e501d2035000b055009000324000320042c07814442d006000b4500300940e1181c50000c0c400d08012200500d4003242402000c0309807041c0d0301c8090908016210707018400c585000c01844e842d441030343d40b00c1c42c21003c50124003d42c140c20302c3d15120780f13503100c062850003407000c1ca01c59540011039260100e058005040041124200e621a1041c403110b5140c124600f1300500c07200903594900e02c1002070341202c2d03030381003070261105034051111510b5540b40c406082e80c440c10f03030724001405069445c2c000380d00c41e880c95110b07142010040c500000701700a80c001c4640303041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 156082751 1250 156081501 156081517
    0x50c0f01111c05010b0304060c030e030c07030203060901020c03120c07020603010306091a010e15010318050c01110615061803070b030117010204030503070b041b0e070f0e01020a03030c0c0602 84
    0x342001501042c0720180702c229401d0010100c1040049600d00724890f980f40c04094070080c0901d448420050442e84290401c0225090b0207060342d5a5607226100303140e42d81d0851008030300900a080026001460602c01d6800c1d0001e60800341d0320341440244251080c170402003c441c0380c1042070010314056103039030010390b001e90720844000511014906111009406e40c4492504805801b001403000c0500c290200d5000208100550380710361850740160060064601201c0c00003060382d0354001404400200707201c4c815020f80f1384200c0180342c10a800d0710741c00111104401701ea20040c0d0180b450400400400c3c40c07182c0c2d00f100714190401600003d00b02000d5034007071014020040700605c244054283e1114580552000031071030280345603036603601ca004803203000d00100d4944d000282445803000071402914a00d11081e074006031111481c0b03024282c151034881c00900c42c0007070600d02c00d00450b0301004841c016001005581003d03a01140034180700d007075050402c1a0030742c98000080c81030010b44054 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 156084001 1250 156082751 156082781
    0xd0b06131a0915010f121e1d1507051e120a0e0f100207060e03070b040c0603090b160e030304030302070510080403120f0908030f040204060f15050c0f01 67
    0x116094800c0090b03075070340540080b050001026110f5001e0b0b801c0032800c5540100ca082040392903a5200500000345400841d980f50141201606681e5039a590f02c03018881415050340c9862020311511181e85840305d0700c1c129200c03004040490b001e81e0003040274140a40b0002508100601384070301200707a5811150503995030100e0002480040390a50040c003000080c20002007030501060610140d683e841e400003802550703400150401445215003000c1d802501240c2107a6450f0000d15080380016005c40e81590201c07442200424064403900880000540000c218043c9442d402003210442d14101c0400c01400104129140c141d10144040c200030350294018080d00c07817418062082c00c0081e2900034082100000802000940081d003124203000710020004101d1540c1e404200104250000a48079030804420091602490300505100b54420340e01445801d0703459a20f4140140c640c007c0c58421340749e50030042d103654401d601030107c40d12528100d5450740b114031342e02400c59403001124482 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 156085251 1250 156084001 156084041
    0x15160f0204110403110306061021020d020408070611030f040306021303120210230103080c0703050a110f0a0b09040e12070f0b0709030809060c1015061205060d0b0613 73
    0x10750715047c001c250b0301500580c2d05110703c1d01b401d00c0080241540003024404000c1c641408240e414442d41070321481c50400e1011541d0f20f0321000c00c540d440400d44101740008554106030039a40a011080c0c81c00303038400c200c07014101411030783d40c60701039006041c041210f002543d400001040e41203511610004854016041d650940742c0200d058480c1503120107044400300d1140b00b0b0a802c4036040a0450f900011309540720040d13010740900382100c0790b0014001d071048010407000e01c04d07811094101024100c43e1104c8100d182e40501035885443c2c031551605d03640520103200103080603040074818260365016200801544241e8540d1604103504c01d88100c0101c07107821040094010940d03400c2002801d15007241803840e941c003d02d503c1020080b81c0501c1000c03640c1c000c00c6c00c0803c908008111903510134440c44d841016108010368262007000c0025401d0900800030510510a440c01078001806000c0f071200c298650306034202000d0b00c120703080600381c2d1260500b00881c0c414801d0741c0751280b0031011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 156086501 1250 156085251 156085283
    0x10c0b04060516021930051305030a051b060d051e060a1404020f040503030711240403080307050c0d02010506030c1f080601140d0b15160f0204110403 66
    0x2d00fa0200044440c1590b10070402200c081c8100c100c0a9400340c0d01c20fa01c1070321402d005010800c0f079180001c00c0c034031483c01103d1520001e6000000740081075881503840d500141d41744201903455201c000060010341000c401d81148212100c4048a66a809809185080c010301468400ca880445070210b203000043c0d01840d0030303e01e101c600c030380045003210701c0c42c40c00781010303da042d2000100da1814499940081d0f03141d4805141c5050b94002c2800905594982c0c181e1b003000e0000003056805188200c44a00c0d25000c801c08480c180b0700401460341c145030403d402d41e40c4513a5981d0000d131060091100034000140f030b00030100400060766002d50f0012a090500760240741c6005010142144034442400100c1407a030756450750105c9002003843c10304070384c0c3c6500380140c40201d81c1c00d0005414420015014816101e280c000ba48210025103110441032040002060039004100c0700070104984411643c000c034400c001980403480c002480050038000c0756403010080d510580c4122450510746080740 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 156087751 1250 156086501 156086521
    0x2031c0b120a031202090a0302100c2d02011101111b0d03020708030c1303020a06030905060a05090c0907030b0901030b0601020c100206011203120e0c1c0b0f06010c0b040605 76
    0x9542029a60042c0100d41e1143d8018040b080481142041c155000c60b0082c126510b08401a00840c1c001e4a060314024902d44000e115400071517003a00d2001c000440c901020000001000066046400384402403ea0340c1c01101d0010301011198260b41d01d0382c2c0b0f41240c981c846001003411034003c515000c0174180444c3d00e5804c2003c090001024140b0502a0710003080a603000c903a40202e82081107a50340d440000c000c1c0c0000c2140d000a50050182d01c1c003c6251501a0301050040b4014401c0b50f5040d5a482d8180058403405c8030b00b0681c0fa0444101101d59003132902c0c2c019004042402c010510041c03a40c04111004401d0388192010700c0014240002940c0610010700ca02c802514030300351080b0180c402075a102c03818031030b0f20b0713441c149210f1040505114140080085240750341c18003250a01140c510741d14010b1a01c0507204451174882030384554154203034800c000c0d901c14226155561240c60b90f40c001540100f000d41800a0285000d0003d25010810fa100f80d1040e6400207441c14030901d14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 156089001 1250 156087751 156087769
    0x8060f01170d050405090402040f050103030201021b06150607080d050a06030c05060307090509091f0e01110403050601030803070504031b06020c06040b0f0d110d0e06330102031c0b 79
    0x42a10b0708050302e102c0000c1da0000c22035080c0d88065031402055100c0340b011500916601090b035a5140c0703400000f108140c7c0c10740091120960800d5030900c003220004c03086403a0070081e62110410140d50080761020701707140c030142030950f0203900c042d410444000095000c4c0c1c4c40807100d1050141e95030400348200704842c035000c1d002c1d00c03082d00c28900b1480c02c2440a4440d514038061184203100e402d0025151441c104054495041c00b5108245142c05680785000a0108070500c155203500300000704006045075001c2d80c0403250030070024105039185480c0e044c0c481c0e00140040080000030000400421900080d2120003041d000c401c99405181100003400d083e5220102885900204002c04c119040c220503901509a50511666680e0860b00d001c0010300d080d02d105c451480c0c1c00318450301038220341c0e40030949038a240c00c00d450342541c9000d44e01e01c00d4208010b421410303001e80f02c01c2d074101103803840380c15501343c10600403685481c43c140b00384030511142045032490562121402903281c113004410b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 156090251 1250 156089001 156089039
    0x5010905060d030309110a030b01030210030504081b0a1211120301050d0b0a2004030506010602152406040803090a09020a0207120303020f0d0605030114071e020708060f01 75
    0x10400550034030800140d4109400b15000c1d08264407514030700c05105a00341da0056001006000f010700d6640c03840c3c4502c1e642c40911060f8482c1c55586804080c40e8042d016242c4625446580649401c00000f1a00100c055010188169100d000c0b28034001030000c4550300904000c1e9209d0a021441c5c04500918043c02080072001000040c00108155220700e10384d400110b5010b10300c130b241550340494038401000541c0a15450f18042d5140110342ca400600400aa03406081a9a416130b00c500080e40d07203a014140740010f2080400003d800242408201d45041d00004640b602c0c140c80080050055042500808190b4000080c070814902d0002c0281d0000c1c4004c071015410b1440204020751120094801d03010785c0702c4000a20000c05100343d04842d030422840b0260354449003900340e008000d140034000d4500030341ca020f003d8004001442c4249114080035600c4401250808000f8050300702204407000541c89120f40c08900c4002c14007074144100240040c03c01151314058080c10084410381c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 156091501 1250 156090251 156090269
    0x71a30090d0203030601032310030308011d060618090c13120b0a020a050d0f06090609020c070512011d060702070b040303170717040309060905120718060f0303120501 73
    0x250740501c1030300401907a900070401d003070014545481540000b0402111070302d01c2c0d19604100c04003c005c018100d54501500e0003581c41c0002c1c0da07201c4d04c1000d1142e402c0c0f0000450014060005002882c041c07000b004004a00100b2041c0310b10010301041d1098410f840d111030012021a064000000464428004040480071522080c0e01030701d9000341c89401400c1460001d8001038084e10640c01501100d8041030f02010421a0518001c5080000c000c40d026102c08241025170014682c0c215000b680c42d8641d904015140b050b18010400c00d0080200e4004601552a07054420f64540340342d0301010844480d0018004070b00c0e04d00b1000782864415040f0301003441041c8418408179521000c3c0c01c091051f05107248104d0340b40c400c030644e000580c10240208044225040008040e40050f0200c01c54505171101101d003500c0d02d00b0005940d800340825409070b030003104104007e00d2400005252110807900c00150140c0340d50300400802100c0e00140c01045248903200c02d0044c29100b000d00418000c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 156092751 1250 156091501 156091513
    0x2090a050406110f0706020c0106050a090c030b1e01030510090f020301152604020d0b0405100b04061404021b0a12080603010606090e040c09050a06080f0604020102071a3009 76
    0x101c01d256070140170f00c042c14180e40811002c000038425401100030f000014005002c0326607500840300600341006500b0002070402e0428401401c0808031078164210440904848142d1800110020000140b4068080f1141c88000681d8202c910074000c1c8040e20990260703480d030400134059002c1d5800039546080007802549019071140440a040c0d000c10207000344400c0313444d10300000d07680485c5054050044c5030944103020400400080e0001c80c0c0c501088203010044401c1c0401c8102d46551140c0c05107071109144031220352915500a007002080c0102410700d82200c0d0b215245000d021000072100e5540350095001140e4110703413800d5020600300c000384601c3d418804006c00514080c41860304130710201e00418200410408c01c00c024103600c00040215150104070f87d009007585100e4240700340150084450501b0021465030320075038041c0c0003400c1040c078191049a402c120301d00d0103c041a0b040c0078424140e00018007228501011200009800008084003102c0e081c000c0c1050043e58069 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 156094001 1250 156092751 156092767
    0x8043507020127172401140306060907050928061b021003020d390207030b07081306050f0a05011e06031d01180b0702030c0601030609080702090a05040611 68
    0x103c43c10400c0c0c9042c800540450f681c0c12110500d400c901420084180e05003260203c0a58160b500c424100c449250300f0241e002e100b002456154a0f0503038a02d41c11543c401c00098400740603100400000001400051185500c420a0003540310340070605020082030f0320041042c1580b010034a80548420221507003102c0e0664001031059500c0383c0380c0c000789600801c0940c8181d005520a42490b031032001720304108001508800081001949040d03151400c0c1c0c483d8480003440000d100c0207981e4440640051629004810b075514031004182c0403c01200147c0d0000150544c02564040c002c8090300103401d05181c00007405480e8160040248680c004101441e2206416844001c0b60781d00c0c1800a100c5410b54400da00d0a80310b01d20f00c81d460360911403164002d100b1445030400c2035000d084104019100d0023000c80c0c42e407042c0d08541b8180e601801c0140007180320750f401903070b42a114804039880d0550503400710700d030401d048800c80318480c1e5030000c100901906001c0c0d550381c1d40b40d89403a03d1038000c0d5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 156095251 1250 156094001 156094067
    0x308070b0c0c0d0810030f060e07120b0103060b0316091a01110c010806040b150d140609010612090606090e070b0a090311040e120c01060501030903080435070201 71
    0x8144100e801c03c00401d000c541700019614004000d5034100283c298030003901d007005e80250800912224492140c400c0002e884030704034540c0c181a0b030748044080034903441d58590b41c015100d214501076140c020b000c1800380076602c010251005168801010a02c5905000e010b0062241252240d06009a40884803080e010200d56500c00b01006d0034030741c2958075610081030052040218094000100e01d669030703269810751005d40441c0b20424014810341f4840d4000c141210010f41d2002d82000340240144050b5000301384030700d1008111000001c805100762104000d684d840d910000d1305da80d0b91000050035180601c003520180c00340041c06840c02c05d4503000100303200c0c020310000d40b440018190120155031240c100e111244602c10840d514607250351882002640800c8611030290720705680029554024007036400c910b5099201c007142a42d8684544c4186c480c024141c50703121003681080300c601c100280060081c1221001c101e07403a00182d20016000d60036621812814111615000c855042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 156096501 1250 156095251 156095263
    0x108040303051305031602030606041b0c061103040b06030c010c030203180105130306062d03060506030a0b040b071409060708130801060909060f0e0a0206220308070b0c0c 75
    0x390500d400a0103a45031403a51040910300340f40203045010008200f078052400d40031b0703074000c14001c60680380e0179210300b41004100d03406415400302c1d0210b200f009117080c6015100c140200c5000791800320361551242c04036440d580c8221021201042c01d1401d21880b030804011844400d102800c2007250000582c0b4041c1d0342e40070300380d806405840c0303d1894408a91140d81134500050126101d104034070340380d14160015209601444142c0a03d104028181ca00054040c1c400b122207c07c2c001c0c00142103455020140c60300409041c1c1620413541c40c00300150101e85224071031030082100c2d0741e481c100008024005555055403c005507004c0c001040c140d640e10381200d82e5184c0c00304400d50f45d41600c000e030322000001d41e0300003c1c00354a40040003820000540040701544d00c658030400906c03005109820489618581c2114a940020260b100609204009003450140d2b40b0381d220700e08140c20f120b944080e409130011205a01c02240e80c2c1c040141031101c50350080e1032940440c1c1006034050015a66503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 156097751 1250 156096501 156096503
    0x1031401090b060708031006030c0f05090d08090d050616020708120304020a0e0109020702150307051c0608010c0c0605090d02060a05040314190206060105091305040c080102030702100b0f010804 85
    0x203590704085001c0d070395603070110380c1c4c0709031701c1003040c0d03281e191038089581d40b040c180c451100824107040714589200d1044214001d030304243d07224182000f040341c080c041300c5104072380212041e800400c91280742d50343d81e130a6028414850001843d080c54401c0c0f004c2c2d17180a442c8030107070665000d2902480400400b007003c20590700c4502e40191a42e46900005e4071f8100960720900c501d2641800104d1002400d400420380709000b1349030243d031520440034004c0544000c5076100c2c0004d4007880f1071440e051450320b0b200c1008055440110700540c0b6251540d0865100c03800510214516030486c070100005c1d4000c503580070b10140007902281d03e034084041e480d8a80184024080c61b0b49600040c2010b000d403514020162502003d40c1c0c4611414080815414180c40c1180142c4104c01c0095031070b610500c11a041040060100c00c0d9034410035403070001502e006803040318002a86100802c00000901c080c0d4400c81a56000349410b400c3d041e1080120380c178151115000c0c1032641e1110002d039070455010364100d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 156099001 1250 156097751 156097769
    0x50d091401030504020d0609050616020a0b15030a12030c090506040302010509101b030504050909010e0c0607020303070506130c0f050906011115040501020301061107050f122b090501031401 83
    0x90b80d44d03031000035084414004010318040c640300c54a014800b001806600c140c64420410181080020701a030b5100c00c030510051082d54404009807100004030001003103010701500302e0f040008607503a04005801c00510030300c002561000000407095206040000501040d07805514007070443c0c00007042e910864400500601105007688482807107500d000050343d07483c2e00d06a03107003161450000d060360300602c00ca51185aa80011540f070000c184100045070303035420f004000303c1c03200c41e05201c2035801c581800c0c0c2c0c0c140000e02002011803011b1000754400c2c031301002081502c0c5041c0c0b038400c0c0c0707250301c40d007150828444070801800700e525444d5925400481c2400c00711950300c1030b51003403071a0107011450b404680010740144020043c0540180d4165149501c030040b00070202042c05603104118414968440051040c46840b800c085108543c0c03c410340e01640d5071030140107a00484007049507042202951001e10081800b64000007031005050b00b40703424001100c030000c58001000f4180205281 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 156100251 1250 156099001 156099011
    0x6050109030209150a0f0602070e09060f041e0c140102010c021c0305190c110f0a1a0702030c0304080c0439051b0705090105090c0409110904020f07050d09140103 71
    0x2541c0c0c44501c5c100043ca008a11140d0283c0c5402000b51039013454440e0b5030443c084400850000c8002042142c407a4881c40000c038070755030340d64480010901149594400100c2500036800100f0b10000818016202c070020072401c903c4e94030300081c21503003000400d00440d00301e06084000c0300420702a0391443d80c9145004242a01c0d02c51000068480c0303034140c032464618048500c0b00c0355802040121102000d6000da540c0130a0b400d0415403908440071008103050310080c03040c4101e004921a0a41280329841107030304001000e6245440c42c0c1c0a5000314261b41e00040c564103580c5071900648105001c40186500c64203031f1529050190304000b08030503a21003100c60f511182a2085c4151170064060401051324820080e200c00e8440e6038500410380103410803c000728060034810a41d9000e00f00008069242500e0185920024078180001008190040000f0000c0c0d070384a0001e05580c10082c600c0c075030b4400007850024500300c0b03140c03020301c14030045001c01c100c207a500018510046e1001c0c00c0101d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 156101501 1250 156100251 156100291
    0x206010317090f060a020105040201180803070b1003120809010e070f05060d1113080136030306050604090507032a030f02130f06091706040f050c130c0306050109030209 74
    0x3e03489400b4804203800a20114080c80080d505420090049000b0b89510307018140003ca074007605400e40c000d03004180d10070044070000440e000b1206a00c042170300d034807000041d100c2d55540c0c402c081c01d1500310001242101400720400703080c4518000c03c1c928034002c19100749043c40f820b001800031b2061500c40c000119420b841c0f52116000321604084591140303603140075400c0d42d12440221401080c0041d072800104030305585880711000500c01c408940da42c410441c5800c0e10402c060940c20440806454120016941c0c407003001810142c59158030214451034a86c04c000d01b201c2e039124802040320100140641241d41806403094010540d10300406c185014910150180c819224011029424042c000926800203400d01003600c8041e543d240701107940e4060758400145407103040d001c5070040000b09000904100618510030700c100241c4010306a4000060111580103078110301c5182c5515000c40c001d64544910400f070b0a00742480b0a016081d0b80209145203002400340b00320104846001c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 156102751 1250 156101501 156101509
    0x9010e0f040e07150f02030403110f03030c0601030602030403110a020f120c060309010204030302060105010c08041503090818090709060503010b03100b0f041a030f060d031e1707020601031709 84
    0x401c109a0510444040365661203003120103040c0405094002204801002000c46c070100484048035000b40c00e0201d40c940c91000c02c0008641c002035190716205c20440b801e0b4001c4107202c601d00841c080c0d0f000503140d1516040c003600362052a01081c01039009124039100503900c0c2c401c2e01c8620304003911282d0620311010101d502c1c0c61019489a90300c94808400c01c13002c0d01054004106480c4217a00703032407507640c2e100015035204254800084c007840702800144021009003140c011407407094a4046085560f03078591440b036900282010b00405506009a20b003810310403101c80d00700d252450101074092038844000c007240810700175188091000400b00380d1b210005036210014059103c10607903164001c264401d410f60061040d108501031016424030031010100a584c41011000001061603a03500d00b04019018482c00480902c92040c03142042030304901c0c0740b140e41500540380e5150303602011032240e6030400c00170280c90031580408011b0001420048030004c894803080301045c0c545200c20002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 156104001 1250 156102751 156102761
    0x80d0f061a09102102070c0e070507110a05030a031d0901060207080705030d0f0f090b030c04030501050604090f170903030310060305070c050606130906020403050f060c09010e0f04 79
    0xc184000c04040c55010a072510001d00701d1007401c8480310b40c95084694241d41640d16030240718000d021040081040740d203282c00400150340310741c2c1882441615103040300c02c8040241c03591000680041100300410640c002c0b4110341c40021a41d43c40c0c000d28110009950340c50810b070080410039000008185a00c0c41c2d01c25254401d0001d120308010342e100d000003542d4035400c0c89810300c00c0c4500f420000e2541004160341e03072082900e68842d040c41c28008010b07034081300c80807860410042d4815001034120020300145001d108010541a0341c0c501c1d508140b4251007005c0c00842c4074915000c040000100c203070110510441d4080c0c200203100701d090f091904540514042540c041c00700108100d54038114441410643d00252002c2001d603c601e201120f401001c454018030a500080108607a40391142c0765040c5060690b801048032500c1c0c1d92403205903001030344100c038294000000391b882000c0030700c1001da0000c142c0341e07024101580440000d20107c02d51941c10302503031640060130010748480d001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 156105251 1250 156104001 156104009
    0x7110406270f050108011b08010302151c0905010c0f03020405090105041509020307030c03060e0928061b09050108090307060203040f050a120906050c1f060e070203030406110403080d0f06 82
    0x20840380d179440340d005000e01040c407404c070b1240c800400c0d14841c0c1e50040079258140d0340c02038098000038184044444956204800740c10506100800100c01e514041c051850201c1c400e4002054111010202501c08600003070210145401840f0510007078880c0c005841c1107580885002c90080d80d072542c008012038680c2c000038101c1c0d000108000c0301340e425030441c0701600001d030380c00c11280f0f80e29812484e4000301a128950941c106820081c502d40d80e011320a08084d03c001e0520040410669400b41103502d100514a8030000800b01c000000e80c02c800c07610001c1c1000e00f0600c00790300c0d143e0074a58580c400d00c1070050680f6408004902401071500d4041c0100d640417084641d119110300b4148842c8807034002e007400180f4040c0e80440c80621070b800303445400c02120001d000200881c020300e9200f0607000588420103031380d06030000c2ca0b01c0c00e611034036019095680107543d4074103080c108042a0b5080380c1c1c0c5411040402c005c200300081c44c80040b1205900d081300300141440501e00d45801404803544 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 156106501 1250 156105251 156105281
    0x30207020901090203041b050f0409060b0307080f12030903070b0705090d080315030c0f15210709080a0f06020912010c020708060907050d021c08030a020711040627 72
    0x80049900c0c02241c1c019405503025181881f000d00190b40401580c546030f01665810513000320358101030303003044d030480d00c245841000d000c19603001c903102280c98840c01e544a03100c3d50b4000b40d60b030318000c00d0601c101407a4200c4140d100b40ba40c0f805030141942c1c0e00c9000e45c01004071040400040d4883e20400548860070700c0140032103c809468144003000c2c0d0001c1d100d0040e680740c501d150742603038540001d0760b5856682c05042c0c02c0000441c2820001c0d4803507400703800315058004203c801c00b6500c0082008a440007650040013a6081c083c0000b05401c01350b03040008580c1c0a2200b410114030152400407185da80b1030f034050b03652914080842c4501d020041300f244650700744001c2c0d00b610f54010540c00f06450481c0229101c039529001c155030341e0300e5280300360ba42040d103440b0050003504003ca0b010346400301c0e41400040b0a402ca03601c030509540101c0d00760444580c0840c06c0d4080103114200c0e01c1c4880c9048034280412400c0c4002e662001c041c05900840c000c8039401414204040e40d0070520030020061 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 156107751 1250 156106501 156106519
    0x90302060112030e131406090103030813031101020c010e0601120c03060f1506020106090c2a02120304120210020f071701060504051302040b03070303051204020f0d0f0b0709230103020702 82
    0x3802009409129190146d6803030000010780141854039140f0b049a82683d50030340a5154014400d1503d1b0042209504102030540442c2550409000410f03028004000000d080c8607901465410000181c22803c0d01d0b40f0b0754001007000c40c0c000301407402030301d0304108001400f416201400d401044607103509810050380100005409406601910071928112028040c0481ca01340454040c0030004135004414180d404d1312a0444a82e10815161840900000c0e020a800340e801403542d001a03114205442c40c0014800031820b041c42400c08a6032a400242404e104031100306886680c140984140f120301c0d165242020b0409401101c01004e014004204da03007172600200520300003104007139002d14240070ba08071075800c0000702381048131f8041e620387c1d060404601403100d0341600500240d910180025800c0942d03990004020b07800c0384299240c4140e4030040c90b0408000f00024607000502c00c94040412203040c07001a80012004002500103240640200607002030141d0700c800f94105280c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 156109001 1250 156107751 156107779
    0xa0809100206070f03270c090c03090201020a0b0402040908030408040617090a02010e03100e0c0312040602030d02031302090a09060b0105030105010207120c030506070801230d0f060605121f090302060112030e 91
    0x5150500c288c0c1c14800c402d10a003440804150161041c0220007801039101a800e040420700240143d07400510042000c18408440d441d202d1310780e001500c00b9680801c0010f030400ca12a0814030003014010007030074400a615000e6642500c410504601a050012101024815940901402003462201d08003000541c601180117552502c840441501a01c034040c01a845101d442e000e4608442103039004514040401d942400a504040c03da80595500d06040d000180c0e902a0782034414030100c400021540b04070309120080c0c1d00ea54220906112041005000c96603001c075400301030303682e007440001e07103080c05240614070300308260310190041c0140000e20103a264401d184504882003441c0703241111f031405880d0308081c2520565541d10040101d105d44c0018202d00c0d40c169618054840000d182b40d030788012801c100c07000c406005042e00205d005288507000d40750355842140c0c03081300c20003e45803c2c3d60060756611042c0601d018507a8202c400c0e104240c0708060f0140c4030200640001c0b140360700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 156110251 1250 156109001 156109013
    0x5010b13090201030b0603060a15020a0f030f03180b070c03020a080403030314090313060804140f030d14010b0a030e160f050406060201021615020c0a0809100206070f0327 75
    0x44401c00300c2c0007a041818940c1240341c0002641c0c01440e0041002032164078244506402d0084024240c05501070265540e000ca480fa16410311078601a448500c00545407030b00c0242202c42d1104c81402c6040d02c0034099000c50a5100c2023944069a07051600e024502d604060389051800000201080300c000380202c101039164102503454001d00741c1d014243d0715081207090f00c90180005440f5104424402003003014484d80d0020b0f0410300804880d030981d013040942508002820903140f003140c2c4001030442c10b0b4a00c501c582d0046001c0a8403100195040103040e800c075104101c0c5403010940c40e1400010f883c00f040c4031000f00740700c1c0d4821158041e0381e074020b850003205561050314481d602c1c0002c00581c50740103008030369000703012071035510549100395a2465100000d0425010301a8203002d00040007908014441c206400745c1102516015944200240070303284208041c1150000310a00c240b0f2303500301285011600c100c2c240440c02e4000149248400172443d032680d205840d082c0701c0791040c01a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 156111501 1250 156110251 156110261
    0x60e0a0201030605090c0712140d0507091d011203031b0c02010f030b09060904151104090605010201060b0a05090d0b0a1a0301110405090415050709080f2805010b13 72
    0x3200303032010b0080564903030401c07010a90485024000c1d000c02c0180400181c054001c1a9044d642800d11244518514412800b030740c1002100b091075507542c60610a0b00c039001000840106600700303180320344031548001c1e01c0004006201d55101c58140d80d840700708043c000c0d00b1901c14000c45510740a518a1400300080c0314200380d010590101c0c03242e624601e8190f01c2400348000d03103000075140711020b8513098180070491900403c15500c41c0c0b82100089000b0099000d0500c2131400c030701003680c03500d040c41c4008048803000e5000905680c9000c40800c00141028180e0700300307400c1410000d45400e2043d0100d941c0d03440075034000303000040200401c54100001c4e03000d8840b0480ca003d110f441e40013031209241c2203071981c4448885448051000300920700d0914410742d44070303106000c940401d80d0809001b10a8a400340c0d903641c045024001c041c40000b000704078010780c0c110940c0c0142001d041d900707400c4182c10b403002c04411140903107606c1d0b101800303001d4000340c941c1c28024103821014041310f404600201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 156112751 1250 156111501 156111503
    0xf070e0c0712021605010c08090907030b2805090108070b03040c0801051009050f062808010603030e03060906100308090105070f060501230315070212070f0c06020105090a0308070507060e0a 83
    0xc584580c01003461b501c200c10482c40e49038803009491519140f08100808690001e022004041d290003403900c02d40c980010192409001030003880c4079100c41e11102c9844980b03070308200c0c0202d90110040000c8040002c602c0c00b2110030204980d900d4849040440705850943c208a015600748802e10103030858050031942101c0702000100202d4843c11403c00a480084d1600ca41c1b1032820880b07104650803800c020b2007126000d8500c11140d60340e07882d48a0030340c0c030140c0c800d80c003052141c01c4150850170103103e074139031045901025002c545080c0d4500503410f2a02c2c0000b402d070321008945020075900441c11100140d42162513450040810300d80503000d401d0134010a03480d0410040d02040f1500210100d42d07001c04000c0140540a0441060220030403004041c80c08500c9111007200c00071410400030001c4500442200c07403801a1418105410ba0079580304d402160314002c1040f03414040407032066005640340c5025403170760f200c42d074017141c0364014072201504151034580e01c05641040010000602 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 156114001 1250 156112751 156112783
    0x13052b15060618031712010902030402010f17150105211909030c080c1603060902030601060801030809150d150e0a02030118020d02040306022a0f070e0c071202 70
    0x1c0c0c0e11014111680550455140101c06480e0414400242494203000e100c00c10356207031a00348034007401c0c2d10300d560900703034058140c256000003844190b50740000020720210041c104000c2c490b1030070144100c0b004000b040c0740c2040d401315004112036071207602126054012241d1490007a008500d010302d2112701030340c0441d0000230900130b42100801c18003a2444207609134450300160915500d648403c1e41c01210105c2d0b00f4082c517030035240078503c9030020304099400f410002410213030600c185840c10f8010b80105082c040d044c4010000035842034100c2e299480141d8140072a04101c0c0c007040280c1c01032039102e02e0081c0c18190344260480000000c0d2088415581b1002c1c000d4466415807402c92100303000b00449a0514124035003c014150000e10150040c105c0042c602541c0c0e451717000132604038510802118004450000b070795a00c1c540da5120030040382010f00382c1d4a003844070f11a5a00300e14456075861817507440008010440c10301c1030303c3c040ea40001609001c0b0500688c02920348a81e051100b41c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 156115107 1106 156114001 156114011
    0x7021002030a0207020604081006091a060a12051303080a0c1e0c05011d0c0a0b0901030e070302130204060807050903030706090f151a010513052b15 65
    0x8100701c08c090100e12165112000c19505258024030310300d814500c1c4045201f5102190200200044031042d80d2418070f088203540014460800d2000d5600d8102080440c9a2040420a4251003542d50421540e16111000221001d80b0880070004101a086c00402c1d8048200c50801d80150309040d465440c9a80d241429201030f49142c02980c00c1d02030500c00424410080c0e11300d165000c540d5228198140800602d0342d015202c5540d04043e1620100401e0f01c205100e04009541c001c0c00b0f50003041c0d1408041d20180d400f600c10000010000000902070910403c181c60031540700902840c5414110b885840103440c3c4003209541240104c101b860019002d04026038510f20481b101250410a81c142c00050041440b00c050501c00200280e8401c0c44070213031004242d61049403400c03400c106800b40083c005040c1e8001c11141d01c003501c0074030144035110000640c0c2035252401441 = true := by decide +kernel

theorem cover : BRFrame.Cov 155935251 156115107 := by
  have h0 := BRFrame.cov_init 155935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 155935251 ≤ n) (h2 : n < 156115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
